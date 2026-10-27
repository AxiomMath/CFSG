module

public import CFSG.Quasithin.Background.SmithB45U3Nat
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup

theorem su3NatModule_of_irr
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    {n : ℕ} (hn : 2 ≤ n) (hSU : IsSU3 ↥L n)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hm : E3.mParam Y < 3 * n) :
    NatSUn L ⊤ ⊥ 3 n ∧ E3.mParam Y = 2 * n := by
  classical
  have hsq : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hSU.2
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  let α : ↥L ⧸ Subgroup.center ↥L ≃* unitaryPSU hU 3 :=
    e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  have hperf : Group.IsPerfect ↥L := ⟨hSU.1.1⟩
  have hLq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hSU.1
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hLq
  have : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial ↥L)
    exact hxy (Subtype.ext (MulEquiv.ext fun w => Subsingleton.elim _ _))
  have hX5 := X5.irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders
    hn hU hsq L hperf hirr α
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
  have hevenL : Even (Nat.card ↥L) :=
    CFSG.ComponentClassification.Burgoyne.even_card_of_isQuasisimple hLq
  have hevenY : Even (Nat.card ↥Y) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hevenL).trans (Subgroup.card_dvd_of_le hLY))
  obtain ⟨t, htY, ht2, htrk⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam Y hevenY
  have htt : t * t = 1 := by
    have h1 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    simpa [pow_two] using h1
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht2
  have hidx : (fixV (Subgroup.zpowers t)).index = 2 ^ E3.mParam Y := by
    rw [CFSG.Quasithin.B1.index_eq_two_pow hW, htrk]
  have htN := hYN htY
  by_cases hinn : ∃ l ∈ L, ∀ x ∈ L, ∃ z ∈ L, (∀ y ∈ L, y * z = z * y) ∧
      t * x * t⁻¹ = l * x * l⁻¹ * z
  · have hodd := X5.centralizer_odd hsq L hirr
    have htL : t ∈ L := by
      refine X5.mem_of_involution_inner L hodd htN htt ?_
      obtain ⟨l, hl, hlx⟩ := hinn
      refine ⟨QuotientGroup.mk ⟨l, hl⟩, MulEquiv.ext fun y => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨z, hz, hzc, hxz⟩ := hlx x x.2
      rw [MulAut.conj_apply, X5.normalizerAct_apply_mk,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hz' : (⟨l, hl⟩ * x * (⟨l, hl⟩ : L)⁻¹)⁻¹ *
          X5.conjOn L ⟨t, htN⟩ x = ⟨z, hz⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, X5.coe_conjOn]
        rw [hxz]
        group
      rw [hz', Subgroup.mem_center_iff]
      exact fun y => Subtype.ext (hzc y y.2)
    have hle : (fixV (Subgroup.zpowers t)).index ≤ 2 ^ (3 * n) := by
      rw [hidx]
      exact Nat.pow_le_pow_right (by norm_num) hm.le
    have hnat : BinaryNaturalSU3 L ⊤ ⊥ n :=
      CFSG.Quasithin.u3NaturalOfSmallDisplacement_holds n hn K hK W hsq L hperf hirr
        ⟨e⟩ ⟨t, htL, htt, ht1, hle⟩
    exact ⟨hnat, (CFSG.Quasithin.H.H2_SU3 hn hnat hLY hYN).1⟩
  · have h3n := hX5.2.2.2.1 t htN htt hinn
    rw [hidx, Nat.pow_le_pow_iff_right (by norm_num)] at h3n
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
