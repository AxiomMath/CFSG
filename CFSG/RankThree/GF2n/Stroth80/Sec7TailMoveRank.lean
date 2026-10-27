module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

theorem opm_char_two_aux {F : Type*} [AddCommGroup F] (hdouble : ∀ y : F, y + y = 0)
    (p q r : F) (h : p + q + r = 0) : p = q + r := by
  calc p = p + ((q + r) + (q + r)) := by rw [hdouble (q + r), add_zero]
    _ = (p + q + r) + (q + r) := by abel
    _ = q + r := by rw [h, zero_add]

section Rank

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

theorem ker_opm_eq_orthogonal_range' (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate)
    (g : E ≃ₗ[K] E) (hg : ∀ x y, B (g x) (g y) = B x y) :
    LinearMap.ker (opm g) = B.orthogonal (LinearMap.range (opm g)) := by
  have hle : LinearMap.ker (opm g) ≤ B.orthogonal (LinearMap.range (opm g)) := by
    intro x hx
    have hx0 : opm g x = 0 := LinearMap.mem_ker.mp hx
    rw [opm_apply] at hx0
    have hx' : g x = x := sub_eq_zero.mp hx0
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro _ ⟨y, rfl⟩
    have h1 : B (g y) x = B y x := by
      have h := hg y x
      rwa [hx'] at h
    rw [opm_apply, map_sub, LinearMap.sub_apply, h1, sub_self]
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd]
  have h := LinearMap.finrank_range_add_finrank_ker (opm g)
  omega

theorem finrank_range_opm_mul_ge (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) (h2 : (2 : K) = 0) (a b : E ≃ₗ[K] E)
    (ha : ∀ x y, B (a x) (a y) = B x y) (hb : ∀ x y, B (b x) (b y) = B x y)
    (hab : a * b = b * a) (ha2 : ∀ x, opm a (opm a x) = 0) (hb2 : ∀ x, opm b (opm b x) = 0)
    (n i : ℕ) (hna : Module.finrank K (LinearMap.range (opm a)) = n)
    (hnb : Module.finrank K (LinearMap.range (opm b)) = n)
    (hi : Module.finrank K ↥(LinearMap.range (opm a) ⊓ LinearMap.range (opm b)) = i) :
    2 * n ≤ Module.finrank K (LinearMap.range (opm (a * b))) + 2 * i := by
  have hdouble : ∀ y : E, y + y = 0 := by
    intro y
    have h := two_smul K y
    rw [h2, zero_smul] at h
    exact h.symm
  have hmul : ∀ c d : E ≃ₗ[K] E, ∀ x : E,
      opm (c * d) x = opm c x + opm d x + opm c (opm d x) := by
    intro c d x
    simp only [opm_apply, LinearEquiv.mul_apply, map_sub]
    abel
  have hcomm : ∀ x : E, opm a (opm b x) = opm b (opm a x) := by
    intro x
    have h1 := hmul a b x
    have h2' := hmul b a x
    rw [hab] at h1
    have h3 : opm a x + opm b x + opm a (opm b x) = opm b x + opm a x + opm b (opm a x) :=
      h1.symm.trans h2'
    rw [add_comm (opm b x) (opm a x)] at h3
    exact add_left_cancel h3
  have hA : ∀ x : E, opm (a * b) x = 0 → opm a x = opm b (x + opm a x) := by
    intro x hx
    rw [map_add, ← hcomm x]
    exact opm_char_two_aux hdouble (opm a x) (opm b x) (opm a (opm b x))
      ((hmul a b x).symm.trans hx)
  have hBm : ∀ x : E, opm (a * b) x = 0 → opm a x ∈ LinearMap.range (opm b) := by
    intro x hx
    exact LinearMap.mem_range.mpr ⟨x + opm a x, (hA x hx).symm⟩
  have hC : ∀ x : E, opm (a * b) x = 0 → opm a x = 0 → opm b x = 0 := by
    intro x hx hpx
    have hr : opm a (opm b x) = 0 := by
      rw [hcomm x, hpx, map_zero]
    have h1 := hmul a b x
    rw [hx, hpx, hr, zero_add, add_zero] at h1
    exact h1.symm
  have hkerA := ker_opm_eq_orthogonal_range' B hnd a ha
  have hkerB := ker_opm_eq_orthogonal_range' B hnd b hb
  have hle_orth : LinearMap.ker (opm a) ⊓ LinearMap.ker (opm b) ≤
      B.orthogonal (LinearMap.range (opm a) ⊔ LinearMap.range (opm b)) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    rw [hkerA] at hx1
    rw [hkerB] at hx2
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, LinearMap.add_apply, LinearMap.BilinForm.mem_orthogonal_iff.mp hx1 y hy,
      LinearMap.BilinForm.mem_orthogonal_iff.mp hx2 z hz, add_zero]
  have hm1 : Module.finrank K ↥(LinearMap.ker (opm a) ⊓ LinearMap.ker (opm b)) ≤
      Module.finrank K ↥(B.orthogonal (LinearMap.range (opm a) ⊔ LinearMap.range (opm b))) :=
    Submodule.finrank_mono hle_orth
  have hm2 : Module.finrank K ↥(B.orthogonal (LinearMap.range (opm a) ⊔
      LinearMap.range (opm b))) = Module.finrank K E -
        Module.finrank K ↥(LinearMap.range (opm a) ⊔ LinearMap.range (opm b)) :=
    LinearMap.BilinForm.finrank_orthogonal hnd _
  have hsd : Module.finrank K ↥(LinearMap.range (opm a) ⊔ LinearMap.range (opm b)) ≤
      Module.finrank K E := Submodule.finrank_le _
  have hs : Module.finrank K ↥(LinearMap.range (opm a) ⊔ LinearMap.range (opm b)) + i =
      n + n := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (opm a))
      (LinearMap.range (opm b))
    rw [hna, hnb, hi] at h
    exact h
  have hmem : ∀ c : ↥(LinearMap.ker (opm (a * b))),
      opm a (c : E) ∈ LinearMap.range (opm a) ⊓ LinearMap.range (opm b) := by
    intro c
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self (opm a) (c : E), ?_⟩
    exact hBm (c : E) (LinearMap.mem_ker.mp c.2)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(LinearMap.ker (opm (a * b))) →ₗ[K]
      ↥(LinearMap.range (opm a) ⊓ LinearMap.range (opm b)),
      ∀ c : ↥(LinearMap.ker (opm (a * b))), (ψ c : E) = opm a (c : E) :=
    ⟨LinearMap.codRestrict (LinearMap.range (opm a) ⊓ LinearMap.range (opm b))
      ((opm a).comp (LinearMap.ker (opm (a * b))).subtype) hmem, fun c => rfl⟩
  have hψ1 := LinearMap.finrank_range_add_finrank_ker ψ
  have hψ2 := Submodule.finrank_le (LinearMap.range ψ)
  have hψ3 : Module.finrank K ↥(LinearMap.ker ψ) ≤
      Module.finrank K ↥(LinearMap.ker (opm a) ⊓ LinearMap.ker (opm b)) := by
    have hfin := Submodule.finrank_map_subtype_eq (LinearMap.ker (opm (a * b)))
      (LinearMap.ker ψ)
    have hsub : (LinearMap.ker ψ).map (LinearMap.ker (opm (a * b))).subtype ≤
        LinearMap.ker (opm a) ⊓ LinearMap.ker (opm b) := by
      rintro _ ⟨c, hc, rfl⟩
      have hψc : ψ c = 0 := LinearMap.mem_ker.mp hc
      have hpa : opm a (c : E) = 0 := by
        have h := hψ c
        rw [hψc] at h
        simpa using h.symm
      have hpb : opm b (c : E) = 0 := hC (c : E) (LinearMap.mem_ker.mp c.2) hpa
      exact Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hpa, LinearMap.mem_ker.mpr hpb⟩
    have hmono := Submodule.finrank_mono hsub
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker (opm (a * b))
  omega

end Rank

end CFSG.RankThree.GF2n.Stroth80
