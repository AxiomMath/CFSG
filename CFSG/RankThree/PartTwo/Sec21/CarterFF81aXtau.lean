module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aX

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G]

theorem FF81X.tau_mem {B : Subgroup G} {τ : G} (hτN : τ ∈ Nor B) :
    FF81X.tau hτN ∈ FF81X B :=
  ⟨⟨τ, hτN⟩, rfl⟩

theorem FF81X.tau_ne_one_of_apply_ne {B : Subgroup G} {τ : G} (hτN : τ ∈ Nor B)
    {x : ↥B} (hx : FF81X.tau hτN x ≠ x) : FF81X.tau hτN ≠ 1 := by
  intro h
  apply hx
  rw [h]
  rfl

variable [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.tauX_ne_one (h : FF81Hyp b L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hb₁ne : b₁ ≠ 1)
    (hτ2 : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) :
    FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) ≠ 1 := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let hτN : τ ∈ Nor B := FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv
  let x : ↥B := ⟨b₁, hb₁B⟩
  refine FF81X.tau_ne_one_of_apply_ne (x := x) hτN ?_
  intro hfix
  have hcoe : (FF81X.tau hτN x : G) = τ * b₁ * τ⁻¹ := by
    change ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) x : G) = τ * (x : G) * τ⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hτfix : τ * b₁ * τ⁻¹ = b₁ := by
    rw [← hcoe, hfix]
  have hb₁inv : b₁ = b₁⁻¹ := hτfix.symm.trans hinv.1
  have hb₁2 : b₁ ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hb₁inv
  have hb₁3 : b₁ ^ 3 = 1 := by
    have hmem : b₁ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) :=
      Subgroup.subset_closure (by simp)
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.1.exponent_dvd_p ⟨b₁, hmem⟩
    simpa using congrArg Subtype.val h
  have hb₁1 : b₁ = 1 := by
    calc b₁ = b₁ ^ 3 * (b₁ ^ 2)⁻¹ := by
          rw [show b₁ ^ 3 = b₁ * b₁ ^ 2 by rw [pow_succ']]
          group
      _ = 1 := by rw [hb₁3, hb₁2, inv_one, mul_one]
  exact hb₁ne hb₁1

end CFSG.RankThree.PartTwo.Sec21.FF81