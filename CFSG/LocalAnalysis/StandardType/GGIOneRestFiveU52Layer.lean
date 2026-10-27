module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Root
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall

public section

namespace CFSG.StandardType

namespace IOneU52

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

theorem pow_three_eq_one_of_card {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  have h := FiniteField.pow_card_sub_one_eq_one c hc
  rw [hcard] at h
  simpa using h

theorem pow_three_of_ker_proj {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (d : ℕ) : ∀ z ∈ (LargeEvenProjMk (unitarySU 2 1 K d)).ker, z ^ 3 = 1 := by
  intro z hz
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf,
    largeEvenScalars_def] at hz
  obtain ⟨u, hu⟩ := hz
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    simpa using pow_three_eq_one_of_card hK u.ne_zero
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hu, ← map_pow, hu3, map_one]
  rfl

theorem injective_of_scalar {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 1 K 5) →* L'}
    (hker : ∀ g : ↥(unitarySU 2 1 K 5), φ g = 1 →
      ∃ c : K, ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = diagonal fun _ => c) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, hc⟩ := hker g hg
  have hU : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card hK le_rfl
  have hdet := ((mem_unitarySU_iff hU).mp g.2).1
  rw [hc, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hdet
    exact zero_ne_one hdet
  have hc3 : c ^ 3 = 1 := pow_three_eq_one_of_card hK hc0
  have h2 : c ^ 2 = 1 := by
    have h5 : c ^ 5 = c ^ 2 * c ^ 3 := by ring
    rw [h5, hc3, mul_one] at hdet
    exact hdet
  have hc1 : c = 1 := by
    have h4 : c ^ 4 = c := by
      rw [show c ^ 4 = c * c ^ 3 by ring, hc3, mul_one]
    rw [← h4, show c ^ 4 = (c ^ 2) ^ 2 by ring, h2, one_pow]
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc1]
  simp

theorem diagHom_mul_comm_of_const {K : Type} [Field K] {d : ℕ} (σ : Fin d → Kˣ) (c : Kˣ)
    (hσ : ∀ k, σ k = c) (g : GL (Fin d) K) : diagHom d σ * g * (diagHom d σ)⁻¹ = g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagHom]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hσ i, hσ j, mul_comm]

theorem layer_small_of_component {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {L' : Type} [Group L'] [Finite L'] {φ : ↥(unitarySU 2 1 K 5) →* L'}
    (hM : UnitTB.Model φ) (hφ : Function.Injective φ) {a : MulAut L'} (ha1 : a ≠ 1)
    (hact : ∃ σ : Fin 5 → Kˣ, SmallU.ActsU φ a σ)
    (hcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) :
    LargeEvenSmall (LargeEvenLayer (ggFix a)) := by
  obtain ⟨σ, ha⟩ := hact
  by_cases hall : ∀ i, (SmallU.cls σ i).card ≤ 3
  · exact (SmallU.not_isComponentOf_of_small_classes hM (by norm_num) ha hall hcomp).elim
  push_neg at hall
  obtain ⟨i, hi⟩ := hall
  have hle5 : (SmallU.cls σ i).card ≤ 5 := by
    have := Finset.card_le_univ (SmallU.cls σ i)
    rwa [Fintype.card_fin] at this
  by_cases h5 : (SmallU.cls σ i).card = 5
  ·
    exfalso
    apply ha1
    have hu : SmallU.cls σ i = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [h5, Fintype.card_fin])
    have hc : ∀ k, σ k = σ i := fun k =>
      SmallU.mem_cls.mp (by rw [hu]; exact Finset.mem_univ k)
    obtain ⟨hD, hact⟩ := ha
    apply MulEquiv.ext
    intro x
    obtain ⟨s, rfl⟩ := hM.surj x
    rw [MulAut.one_apply, hact s]
    congr 1
    apply Subtype.ext
    rw [coe_conjN]
    exact diagHom_mul_comm_of_const σ (σ i) hc _
  · have h4 : (SmallU.cls σ i).card = 4 := by omega
    have hS3 : 3 ≤ (SmallU.cls σ i).card := by omega
    have hSq : ((SmallU.cls σ i).card, 2 ^ 1) ≠ (3, 2) := by
      intro he
      have := congrArg Prod.fst he
      simp only at this
      omega
    have hbq := isQuasisimple_blockSU (SmallU.cls σ i)
      (TableBU.unitaryFieldData_of_card hK le_rfl) hK hS3 hSq
    have hq : CFSG.Assembly.IsQuasisimple ↥((blockSU (SmallU.cls σ i)).map φ) :=
      (TableBSymp.isQuasisimple_iff _).mpr
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective _ φ hφ) hbq)
    rw [SmallU.layer_eq_block hM ha (SmallU.cls_isCls σ i) hq hcomp]
    refine Or.inl ?_
    have key : ∀ m : ℕ, m = 4 → LargeEvenIsU42 ↥(unitarySU 2 1 K m) := by
      rintro m rfl
      exact unitarySU_four_isU42 hK
    exact isU42_of_mulEquiv ((Subgroup.equivMapOfInjective _ φ hφ).symm.trans
      (blockSUEquiv (SmallU.cls σ i) (TableBU.unitaryFieldData_of_card hK le_rfl)).symm)
      (key _ h4)

end IOneU52

end CFSG.StandardType
