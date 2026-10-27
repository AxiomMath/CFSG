module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem rank_le_one_of_nonsingular_image
    {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (Q : V → K)
    (hQsmul : ∀ (a : K) (v : V), Q (a • v) = a ^ 2 * Q v)
    (hQadd : ∀ v w : V, Q (v + w) = Q v + Q w + B v w)
    (hB : ∀ v : V, B v v = 0)
    (g : V →ₗ[K] V) (hgQ : ∀ v : V, Q (g v) = Q v) (hg2 : ∀ v : V, g (g v) = v)
    (hns : ∀ v : V, Q (g v + v) = 0 → g v + v = 0) :
    Module.finrank K (LinearMap.range (g - LinearMap.id)) ≤ 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hVadd : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  have hVneg : ∀ v : V, -v = v := fun v => neg_eq_iff_add_eq_zero.mpr (hVadd v)
  have hsymm : ∀ v w : V, B v w = B w v := by
    intro v w
    have h := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB v, hB w, zero_add, add_zero] at h
    linear_combination h - B w v * h2
  have hgB : ∀ v w : V, B (g v) (g w) = B v w := by
    intro v w
    have h1 : Q (g v + g w) = Q (g v) + Q (g w) + B (g v) (g w) := hQadd (g v) (g w)
    have h3 : Q (g v + g w) = Q (v + w) := by rw [← map_add g v w, hgQ]
    linear_combination -h1 + h3 + hQadd v w - hgQ v - hgQ w
  have hcross : ∀ v w : V, B w (g v) = B v (g w) := by
    intro v w
    have h1 : B (g (g w)) (g v) = B (g w) v := hgB (g w) v
    rw [hg2 w] at h1
    rw [h1]
    exact hsymm (g w) v
  have hf_add : ∀ v w : V, B (v + w) (g (v + w)) = B v (g v) + B w (g w) := by
    intro v w
    simp only [map_add, LinearMap.add_apply]
    linear_combination hcross v w + B v (g w) * h2
  have hf_smul : ∀ (a : K) (v : V), B (a • v) (g (a • v)) = a ^ 2 * B v (g v) := by
    intro a v
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hQphi : ∀ v : V, Q (g v + v) = B v (g v) := by
    intro v
    have h1 : Q (g v + v) = Q (g v) + Q v + B (g v) v := hQadd (g v) v
    linear_combination h1 + hgQ v + hsymm (g v) v + Q v * h2
  have hker : ∀ v : V, B v (g v) = 0 → (g - LinearMap.id : V →ₗ[K] V) v = 0 := by
    intro v hv
    have h1 : Q (g v + v) = 0 := by rw [hQphi v, hv]
    have h3 : g v + v = 0 := hns v h1
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_add_neg, hVneg v]
    exact h3
  obtain ⟨e, he⟩ : ∃ e : K ≃+* K, ∀ x : K, e x = x ^ 2 := by
    have hinj : Function.Injective (frobenius K 2) := (frobenius K 2).injective
    have hbij : Function.Bijective (frobenius K 2) :=
      ⟨hinj, Finite.surjective_of_injective hinj⟩
    exact ⟨RingEquiv.ofBijective (frobenius K 2) hbij, fun x => by simp [frobenius_def]⟩
  obtain ⟨F, hF⟩ : ∃ F : V → K, ∀ v : V, e (F v) = B v (g v) :=
    ⟨fun v => e.symm (B v (g v)), fun v => e.apply_symm_apply _⟩
  have hFadd : ∀ v w : V, F (v + w) = F v + F w := by
    intro v w
    apply e.injective
    rw [map_add, hF (v + w), hF v, hF w, hf_add v w]
  have hFsmul : ∀ (a : K) (v : V), F (a • v) = a • F v := by
    intro a v
    apply e.injective
    rw [hF (a • v), hf_smul a v, smul_eq_mul, map_mul, hF v, he a]
  obtain ⟨Fl, hFl⟩ : ∃ Fl : V →ₗ[K] K, ∀ v : V, Fl v = F v :=
    ⟨{ toFun := F
       map_add' := hFadd
       map_smul' := fun a v => by
         rw [RingHom.id_apply]
         exact hFsmul a v }, fun v => rfl⟩
  have hkerle : LinearMap.ker Fl ≤ LinearMap.ker (g - LinearMap.id) := by
    intro v hv
    rw [LinearMap.mem_ker, hFl] at hv
    rw [LinearMap.mem_ker]
    apply hker v
    rw [← hF v, hv, map_zero]
  have hrange : Module.finrank K (LinearMap.range Fl) ≤ 1 := by
    calc Module.finrank K (LinearMap.range Fl) ≤ Module.finrank K K :=
          Submodule.finrank_le _
      _ = 1 := by simp
  have hr1 := LinearMap.finrank_range_add_finrank_ker Fl
  have hr2 := LinearMap.finrank_range_add_finrank_ker (g - LinearMap.id)
  have hk := Submodule.finrank_mono hkerle
  omega

end CFSG.RankThree.GF2n.Stroth80
