module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLInner
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec4.Steps444
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.RankThree.PartTwo.Sec4.T444.Step453
import CFSG.RankThree.PartTwo.Sec18.Item186a
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Sec451

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inf_pPrimeCore_le_pCoreOf {I : Subgroup G}
    (eI : I ⧸ CFSG.pCore 2 I ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :
    I ⊓ CFSG.pPrimeCore 3 G ≤ CFSG.Open.pCoreOf 2 I := by
  set P := CFSG.pPrimeCore 3 G with hP
  set D : Subgroup I := P.subgroupOf I with hD
  have hDn : D.Normal := normal_subgroupOf
  set φ := QuotientGroup.mk' (CFSG.pCore 2 I) with hφ
  have hIq : CFSG.IsQuasisimple (I ⧸ CFSG.pCore 2 I) :=
    LocalCores.isQuasisimple_of_mulEquiv eI.symm isQuasisimple_SL
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3
    apply not_three_dvd_card_pPrimeCore (G := G)
    rw [← card_map_of_injective I.subtype_injective] at h3
    refine h3.trans (card_dvd_of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp hx
  have hDφ3 : ¬ 3 ∣ Nat.card (D.map φ) := fun h3 => hD3 (h3.trans (card_map_dvd D φ))
  have hle : D ≤ CFSG.pCore 2 I := by
    rcases LocalCores.quasisimple_normal_subgroups hIq (hDn.map φ (QuotientGroup.mk'_surjective _))
      with htop | hcen
    · exfalso
      apply hDφ3
      rw [htop, card_top, Nat.card_congr eI.toEquiv, KFacts.KS14.card_SL_three_four]
      norm_num
    · have hZ3 : Nat.card (center (I ⧸ CFSG.pCore 2 I)) = 3 := by
        rw [← KFacts.L34.card_center_specialLinearGroup KFacts.L34.card_galoisField_two_two,
          ← map_center_eq eI, card_map_of_injective eI.injective]
      have h1 : Nat.card (D.map φ) ∣ 3 := by
        rw [← hZ3]
        exact card_dvd_of_le hcen
      have h2 : Nat.card (D.map φ) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
        · exact h
        · exact absurd (h ▸ dvd_rfl) hDφ3
      rw [card_eq_one, Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at h2
      exact h2
  intro x hx
  have hxD : (⟨x, hx.1⟩ : I) ∈ D := mem_subgroupOf.mpr hx.2
  have := hle hxD
  rw [Sec18.mem_pCore_iff_mem_pCoreOf] at this
  exact this

omit [Finite G] in
theorem map_pCoreOf_subgroupOf_normal (I : Subgroup G) :
    (((CFSG.Open.pCoreOf 2 I).map (starQuot G)).subgroupOf (I.map (starQuot G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer
      (map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 I))).mpr
    ((map_mono (le_normalizer_pCoreOf I)).trans (le_normalizer_map _))

theorem nonempty_quotient_map_equiv {I : Subgroup G}
    (eI : I ⧸ CFSG.pCore 2 I ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    [((CFSG.Open.pCoreOf 2 I).map (starQuot G)).subgroupOf (I.map (starQuot G)) |>.Normal] :
    Nonempty (↥(I.map (starQuot G)) ⧸
      ((CFSG.Open.pCoreOf 2 I).map (starQuot G)).subgroupOf (I.map (starQuot G)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  set π := starQuot G with hπ
  set T := (CFSG.Open.pCoreOf 2 I).map π with hT
  set ψ : I →* ↥(I.map π) ⧸ T.subgroupOf (I.map π) :=
    (QuotientGroup.mk' _).comp (π.subgroupMap I) with hψ
  have hsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (π.subgroupMap_surjective I)
  have hker : ψ.ker = CFSG.pCore 2 I := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, MonoidHom.subgroupMap_apply_coe,
      Sec18.mem_pCore_iff_mem_pCoreOf]
    constructor
    · rintro ⟨t, ht, hte⟩
      rw [hπ, starQuot, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hte
      have h1 : t⁻¹ * x ∈ I ⊓ CFSG.pPrimeCore 3 G :=
        ⟨I.mul_mem (I.inv_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 I ht)) x.2, hte⟩
      have h2 := inf_pPrimeCore_le_pCoreOf eI h1
      have h3 : (x : G) = t * (t⁻¹ * x) := by group
      rw [h3]
      exact mul_mem ht h2
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans eI)⟩

theorem mem_map_of_mem_centralizer_map {A M : Subgroup G} (h : Ctx444 G A M)
    {y : G ⧸ CFSG.pPrimeCore 3 G}
    (hy : y ∈ centralizer ((A.map (starQuot G) : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) :
      Set (G ⧸ CFSG.pPrimeCore 3 G)))
    (hy3 : y ^ 3 = 1) : y ∈ A.map (starQuot G) := by
  obtain ⟨w, hwC, hw3, rfl⟩ :=
    exists_lift_pow_three_eq_one not_three_dvd_card_pPrimeCore h.isE27.isPGroup hy hy3
  exact mem_map_of_mem _ (h.rank3II_4_45 hwC hw3)

theorem isE27_map_starQuot {A : Subgroup G} (hA : Late.IsE27 A) :
    Late.IsE27 (A.map (starQuot G)) := by
  have hinf : A ⊓ (starQuot G).ker = ⊥ := by
    rw [starQuot, QuotientGroup.ker_mk']
    exact inf_eq_bot_of_isPGroup_of_not_dvd Nat.prime_three hA.isPGroup
      not_three_dvd_card_pPrimeCore
  exact ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hA.1,
    by rw [card_map_eq_of_inf_ker_eq_bot _ hinf, hA.2]⟩

theorem exists_inner_map
    {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s) :
    ∀ a ∈ A.map (starQuot G), ∃ i ∈ (inSubgroup perfectResidual H).map (starQuot G),
      ∀ x ∈ (inSubgroup perfectResidual H).map (starQuot G),
        (a * x * a⁻¹)⁻¹ * (i * x * i⁻¹) ∈
          (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)).map (starQuot G) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨i, hi, hix⟩ := Ctx4443.exists_inner h a ha
  refine ⟨starQuot G i, mem_map_of_mem _ hi, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, hix x hx, ?_⟩
  simp only [map_mul, map_inv]

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
