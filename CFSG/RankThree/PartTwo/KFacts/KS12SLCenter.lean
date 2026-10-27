module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.LowTwoRank Matrix

theorem eq_one_of_pow_three_eq_one_of_card_mod_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {r : K} (hr : r ^ 3 = 1) : r = 1 := by
  have := Fintype.ofFinite K
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hr
  have hcard : Fintype.card K = 3 * (Nat.card K / 3) + 2 := by
    rw [← Nat.card_eq_fintype_card]
    omega
  have hpow := FiniteField.pow_card r
  rw [hcard, pow_add, pow_mul, hr, one_pow, one_mul] at hpow
  have h2 : r * (r - 1) = 0 := by linear_combination hpow
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hr0)

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hφ : φ x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hx y]
  rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hφ
  rw [hφ]
  exact Subgroup.one_mem _

theorem center_statedSL_three_eq_bot {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    Subgroup.center (StatedSL 3 K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  set e := specialLinearGroupEquivStatedSL 3 K
  obtain ⟨A, rfl⟩ := e.surjective z
  have hA : A ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, hz (e g)]
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 := eq_one_of_pow_three_eq_one_of_card_mod_three hK hr
  have hA1 : A = 1 := Subtype.ext (by rw [← hrA, hr1, map_one]; rfl)
  rw [hA1, map_one]
  exact Subgroup.one_mem _

theorem center_statedSU_three_eq_bot {K : Type} [Field K] {p f : ℕ} [hp : Fact p.Prime]
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1) :
    Subgroup.center (StatedSU 3 (p ^ f) K) = ⊥ := by
  have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have := hu.finite
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h => by
    have h2 := congrArg Prod.snd h
    simp only at h2
    omega
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK le_rfl hnq).2
  rw [eq_bot_iff, hZ]
  intro z hz
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨ζ, hζ⟩ := hz
  have hmem : (z : GL (Fin 3) K) ∈ Sec4.slPi false 3 (p ^ f) K := z.2
  rw [Sec4.mem_slPi_false hu, ← hζ, GeneralLinearGroup.coe_scalar] at hmem
  obtain ⟨hdet, hunit⟩ := hmem
  simp only [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have hdet' : (ζ : K) ^ 3 = 1 := by rw [← hdet]; ring
  have h00 := congrFun (congrFun hunit 0) 0
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    hu.bar_apply] at h00
  have hq1 : p ^ f + 1 = 3 * (p ^ f / 3) + 2 := by omega
  have h3 : (ζ : K) ^ (p ^ f + 1) = 1 := by rw [pow_succ]; exact h00
  rw [hq1, pow_add, pow_mul, hdet', one_pow, one_mul] at h3
  have hζ1 : (ζ : K) = 1 := by
    have h' : (ζ : K) ^ 3 = (ζ : K) * (ζ : K) ^ 2 := by ring
    rw [hdet', h3, mul_one] at h'
    exact h'.symm
  have hz1 : z = 1 := by
    apply Subtype.ext
    rw [← hζ, show ζ = 1 from Units.ext hζ1, map_one]
    rfl
  rw [hz1]
  exact Subgroup.one_mem _

theorem isSLThreePiAt_of_isSLThreeEpsAt {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hX : Sec4.IsSLThreeEpsAt X (p ^ e)) (hq : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2)
    (hZ : Subgroup.center X ≠ ⊥) : Sec4.IsSLThreePiAt X (p ^ e) := by
  obtain ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := hX
  · rcases hq with hq | hq
    · exact ⟨K, inferInstance, inferInstance, Or.inl ⟨hK, hq, ⟨φ⟩⟩⟩
    · exact absurd (center_eq_bot_of_mulEquiv φ
        (center_statedSL_three_eq_bot (by rw [hK]; exact hq))) hZ
  · rcases hq with hq | hq
    · exact absurd (center_eq_bot_of_mulEquiv φ (center_statedSU_three_eq_bot he hK hq)) hZ
    · exact ⟨K, inferInstance, inferInstance, Or.inr ⟨hK, hq, ⟨φ⟩⟩⟩

end CFSG.RankThree.PartTwo.KFacts
