module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpC3Sound
import CFSG.Certificates.Kernel.PermCent.GoodCSound
import CFSG.GH74.KGroups.L33
import Certificates.Kernel.PermCent.K9741G

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.KGrp
  CFSG.Certificates.Kernel.PkCV.Good CFSG.ClassicalInvolution.Q3.TA3.Check

namespace Certificates

namespace C9741

variable {M : Type*} [Group M] [DecidableEq M] {C C' : List M}

theorem listAll_congr (h : ∀ x, x ∈ C ↔ x ∈ C') (p : M → Bool) : C.all p = C'.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall_congr' fun x => imp_congr_left (h x)

theorem listAny_congr (h : ∀ x, x ∈ C ↔ x ∈ C') (p : M → Bool) : C.any p = C'.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact exists_congr fun x => and_congr_left' (h x)

theorem noOddB_congr (B : ℕ) (h : ∀ x, x ∈ C ↔ x ∈ C') : noOddB B C = noOddB B C' := by
  simp only [noOddB, listAll_congr h, listAny_congr h]

theorem pairsB_congr (t : M) (h : ∀ x, x ∈ C ↔ x ∈ C') : pairsB t C = pairsB t C' := by
  have hf : ∀ q : M → Bool, ∀ x, x ∈ C.filter q ↔ x ∈ C'.filter q := fun q x => by
    simp only [List.mem_filter, h]
  simp only [pairsB, listAll_congr (hf _), listAll_congr h, listAny_congr h]

theorem goodCheck_of_conj (B : ℕ) (L : List M) (H : Subgroup M) (hL : ∀ x, x ∈ L ↔ x ∈ H)
    (t0 : M) (hconj : ∀ t ∈ L, t * t = 1 → t ≠ 1 → ∃ g ∈ H, g * t0 * g⁻¹ = t)
    (h0 : (noOddB B (centB L t0) && pairsB t0 (centB L t0)) = true) : goodCheck B L = true := by
  rw [goodCheck, List.all_eq_true]
  intro t ht
  by_cases hi : t * t = 1 ∧ t ≠ 1
  · obtain ⟨g, hg, rfl⟩ := hconj t ht hi.1 hi.2
    let f : M →* M := (MulAut.conj g).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj g).injective
    have hfx : ∀ x, f x = g * x * g⁻¹ := fun x => rfl
    have hmem : ∀ x, x ∈ centB L (f t0) ↔ x ∈ (centB L t0).map f := by
      intro x
      simp only [centB, List.mem_filter, List.mem_map, decide_eq_true_iff]
      constructor
      · rintro ⟨hx, hc⟩
        have hy : f (g⁻¹ * x * g) = x := by
          rw [hfx]
          group
        refine ⟨g⁻¹ * x * g, ⟨(hL _).2 ?_, hf ?_⟩, hy⟩
        · exact H.mul_mem (H.mul_mem (H.inv_mem hg) ((hL x).1 hx)) hg
        · rw [map_mul f (g⁻¹ * x * g) t0, map_mul f t0 (g⁻¹ * x * g), hy]
          exact hc
      · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
        refine ⟨(hL _).2 ?_, ?_⟩
        · rw [hfx]
          exact H.mul_mem (H.mul_mem hg ((hL y).1 hy)) (H.inv_mem hg)
        · rw [← map_mul, ← map_mul, hc]
    simp only [Bool.or_eq_true]
    right
    rw [← hfx t0, noOddB_congr B hmem, pairsB_congr _ hmem, noOddB_map f hf, pairsB_map f hf]
    exact h0
  · simp only [hi, decide_false, Bool.not_false, Bool.true_or]

end C9741

open C9741 K9741G

theorem certificate9741 : CFSG.ClassicalInvolution.Q3.TA3.Check.goodCheck 100
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QP) = true := by
  rw [elemsT_eq_elemsC, goodCheck_ev]
  have hL : ∀ x, x ∈ elemsC L33.QP ↔ x ∈ L33.QP.originalSubgroup.comap (evHom 26) := by
    intro x
    rw [Subgroup.mem_comap, ← mem_elemsT _ L33.QP_ok, elemsT_eq_elemsC]
    exact (List.mem_map_of_injective ev_injective).symm
  refine goodCheck_of_conj 100 (elemsC L33.QP) _ hL l33T0 ?_ ?_
  · intro t ht h1 h2
    have hf : (powOneC t 2 && !decide (t = 1)) = true := by
      rw [powOneC_eq, pow_two]
      simp only [h1, h2, decide_true, decide_false, Bool.not_false, Bool.and_self]
    have hJ := of_decide_eq_true (List.all_eq_true.1 k9741_conj t (List.mem_filter.2 ⟨ht, hf⟩))
    obtain ⟨g, hg, e⟩ := List.mem_map.1 hJ
    exact ⟨g, (hL g).1 (mem_l33PickGaps hg), e⟩
  · rw [centB_C, noOddB_C]
    exact k9741_cent

end Certificates
