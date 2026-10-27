module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryCoverOddKernel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit

public section

namespace CFSG.RankThree

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] noncomputable def projectiveSpecialLinearTwoEquivSLOfCharTwo (K : Type*) [Field K]
    [CharP K 2] : ProjectiveSpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) K :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).trans
    (LinearCover.projectiveSLTwoEquivSL K)

theorem eq_top_of_sup_center_eq_top_of_isPerfect {X : Type*} [Group X] [Group.IsPerfect X]
    {S : Subgroup X} (h : S ⊔ Subgroup.center X = ⊤) : S = ⊤ := by
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := X), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  have : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' b]
      _ = a * b * (c * (d * c⁻¹)) * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * b * (c * (c⁻¹ * d)) * a⁻¹ * d⁻¹ * b⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) d).symm]
      _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hd' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [this, commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem large_even_linear_two_perfect_full_central_cover_trivial {f : ℕ} (hf : 3 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (π : X →* ProjectiveSpecialLinearGroup (Fin 2) K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center X) :
    π.ker = ⊥ ∧ Function.Bijective π := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  set e : ProjectiveSpecialLinearGroup (Fin 2) K ≃* CFSG.Assembly.LowTwoRank.StatedSL 2 K :=
    (projectiveSpecialLinearTwoEquivSLOfCharTwo K).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K) with he
  set η : X →* CFSG.Assembly.LowTwoRank.StatedSL 2 K := e.toMonoidHom.comp π with hη
  have hker : η.ker = π.ker := ker_comp_mulEquiv π e
  have hηs : Function.Surjective η := e.surjective.comp hπ
  have hηC : η.ker ≤ Subgroup.center X := hker ▸ hC
  set ε := projectiveSpecialLinearTwoEquivSLOfCharTwo K with hε
  set θ : X →* SpecialLinearGroup (Fin 2) K := ε.toMonoidHom.comp π with hθ
  have hθker : θ.ker = π.ker := ker_comp_mulEquiv π ε
  have hodd : Odd (Nat.card θ.ker) :=
    odd_card_ker_of_two_cover_trivial θ (ε.surjective.comp hπ) (hθker ▸ hC)
      fun θ' hθ' hθ'C hθ'2 =>
        CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot f hf hK θ'
          hθ' hθ'C hθ'2
  rw [hθker, ← hker] at hodd
  obtain ⟨s, hs, -⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated le_rfl hηs
      hηC hodd
  have hsup : s.range ⊔ Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hz : (s (η x))⁻¹ * x ∈ Subgroup.center X := by
      apply hηC
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    have hx : x = s (η x) * ((s (η x))⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup ⟨η x, rfl⟩ hz
  have hrange : s.range = ⊤ := eq_top_of_sup_center_eq_top_of_isPerfect hsup
  have hηker : η.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := (MonoidHom.range_eq_top.mp hrange) x
    rw [MonoidHom.mem_ker, hs] at hx
    rw [hx, map_one]
    exact Subgroup.one_mem _
  have hπker : π.ker = ⊥ := hker ▸ hηker
  exact ⟨hπker, (MonoidHom.ker_eq_bot_iff π).mp hπker, hπ⟩

end CFSG.RankThree
