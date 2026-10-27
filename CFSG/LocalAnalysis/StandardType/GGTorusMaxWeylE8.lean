module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxWeylE8Aux
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCover
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Adapters.LieModelSimple
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
open CFSG.EvenSmallLie.OmegaEight.Weyl CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover

theorem tmW8_isLiftable :
    (coxeterMatrix (isFiniteType_cartan Tag.E8)).IsLiftable
      (fun i => refl (tmW8_simpleIdx i)) := by
  intro i j
  rw [tmW8_coxM_eq]
  exact tmW8_coxRel i j

@[expose] noncomputable def tmW8_hom :
    WeylGroup Tag.E8 →* Equiv.Perm (Fin 240) :=
  (coxeterSystem Tag.E8).lift ⟨fun i => refl (tmW8_simpleIdx i), tmW8_isLiftable⟩

theorem tmW8_hom_simple
    (i : Fin Tag.E8.rank) :
    tmW8_hom ((coxeterSystem Tag.E8).simple i) = refl (tmW8_simpleIdx i) :=
  (coxeterSystem Tag.E8).lift_apply_simple tmW8_isLiftable i

theorem tmW8_hom_wordProd
    (w : List (Fin Tag.E8.rank)) :
    tmW8_hom ((coxeterSystem Tag.E8).wordProd w) = wordPerm (w.map tmW8_simpleIdx) := by
  induction w with
  | nil => simp [wordPerm]
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, tmW8_hom_simple, ih]
    simp [wordPerm]

theorem tmW8_refl_mem_range_simple
    (i : Fin Tag.E8.rank) : refl (tmW8_simpleIdx i) ∈ tmW8_hom.range :=
  MonoidHom.mem_range.mpr ⟨_, tmW8_hom_simple i⟩

theorem tmW8_word_mem_range
    (w : List (Fin Tag.E8.rank)) : wordPerm (w.map tmW8_simpleIdx) ∈ tmW8_hom.range :=
  MonoidHom.mem_range.mpr ⟨_, tmW8_hom_wordProd w⟩

theorem tmW8_range_le :
    tmW8_hom.range ≤ wE8 := by
  rw [MonoidHom.range_eq_map, ← (coxeterSystem Tag.E8).subgroup_closure_range_simple,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, tmW8_hom_simple]
  exact refl_mem (tmW8_simpleIdx_lt i)

theorem tmW8_refl_of_word {r : ℕ}
    (hr : r < 240) {l : List ℕ} (hl : ∀ s ∈ l, s < 240) {a : Array ℕ} (hra : reflArr r = a)
    (hcheck : tmW8_eqA (tmW8_wordArr l) a = true) (harr : tmW8_wordArr l = wordArr l) :
    refl r = wordPerm l :=
  (tmW8_eqA_sound (rep_wordArr l hl) (rep_refl hr) (by rw [← harr, hra]; exact hcheck)).symm

theorem tmW8_refl52 :
    refl 52 = wordPerm tmW8_root52 :=
  tmW8_refl_of_word (by decide) tmW8_root52_lt tmW8_reflArr_52 tmW8_wordCheck52
    (tmW8_wordArr_eq _ tmW8_arr_mem_root52)

theorem tmW8_refl173 :
    refl 173 = wordPerm tmW8_root173 :=
  tmW8_refl_of_word (by decide) tmW8_root173_lt tmW8_reflArr_173 tmW8_wordCheck173
    (tmW8_wordArr_eq _ tmW8_arr_mem_root173)

theorem tmW8_refl110 :
    refl 110 = wordPerm tmW8_root110 :=
  tmW8_refl_of_word (by decide) tmW8_root110_lt tmW8_reflArr_110 tmW8_wordCheck110
    (tmW8_wordArr_eq _ tmW8_arr_mem_root110)

theorem tmW8_refl88 :
    refl 88 = wordPerm tmW8_root88 :=
  tmW8_refl_of_word (by decide) tmW8_root88_lt tmW8_reflArr_88 tmW8_wordCheck88
    (tmW8_wordArr_eq _ tmW8_arr_mem_root88)

theorem tmW8_refl108 :
    refl 108 = wordPerm tmW8_root108 :=
  tmW8_refl_of_word (by decide) tmW8_root108_lt tmW8_reflArr_108 tmW8_wordCheck108
    (tmW8_wordArr_eq _ tmW8_arr_mem_root108)

theorem tmW8_sgs_mem_range (i : ℕ)
    (hi : i < 13) : refl (sgsRoots.getD i 0) ∈ tmW8_hom.range := by
  interval_cases i
  · rw [show sgsRoots.getD 0 0 = tmW8_simpleIdx ⟨1, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 1 0 = tmW8_simpleIdx ⟨2, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 2 0 = tmW8_simpleIdx ⟨3, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 3 0 = tmW8_simpleIdx ⟨4, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 4 0 = tmW8_simpleIdx ⟨5, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 5 0 = tmW8_simpleIdx ⟨6, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 6 0 = tmW8_simpleIdx ⟨7, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 7 0 = tmW8_simpleIdx ⟨0, by simp⟩ by decide]
    exact tmW8_refl_mem_range_simple _
  · rw [show sgsRoots.getD 8 0 = 52 by decide, tmW8_refl52, ← tmW8_root52_eq]
    exact tmW8_word_mem_range _
  · rw [show sgsRoots.getD 9 0 = 173 by decide, tmW8_refl173, ← tmW8_root173_eq]
    exact tmW8_word_mem_range _
  · rw [show sgsRoots.getD 10 0 = 110 by decide, tmW8_refl110, ← tmW8_root110_eq]
    exact tmW8_word_mem_range _
  · rw [show sgsRoots.getD 11 0 = 88 by decide, tmW8_refl88, ← tmW8_root88_eq]
    exact tmW8_word_mem_range _
  · rw [show sgsRoots.getD 12 0 = 108 by decide, tmW8_refl108, ← tmW8_root108_eq]
    exact tmW8_word_mem_range _

theorem tmW8_wE8_le_range :
    wE8 ≤ tmW8_hom.range := by
  rw [wE8_eq, wQ, ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [wS_getElem! hi]
  exact tmW8_sgs_mem_range i hi

theorem tmW8_range_eq :
    tmW8_hom.range = wE8 :=
  le_antisymm tmW8_range_le tmW8_wE8_le_range

theorem tmW8_rangeRestrict_bijective :
    Function.Bijective tmW8_hom.rangeRestrict := by
  haveI : Fintype (WeylGroup Tag.E8) := Fintype.ofFinite _
  haveI : Fintype ↥tmW8_hom.range := Fintype.ofFinite _
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨tmW8_hom.rangeRestrict_surjective, ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, tmW8_range_eq,
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E8', card_wE8]

@[expose] noncomputable def tmW8_equiv :
    WeylGroup Tag.E8 ≃* wE8 :=
  (MulEquiv.ofBijective tmW8_hom.rangeRestrict tmW8_rangeRestrict_bijective).trans
    (MulEquiv.subgroupCongr tmW8_range_eq)

theorem tmW8_map_commutator_subtype {G : Type*} [Group G] (H : Subgroup G) :
    (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem tmW8_map_commutator :
    (commutator (WeylGroup Tag.E8)).map tmW8_equiv.toMonoidHom = commutator ↥wE8 := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective tmW8_equiv.toMonoidHom tmW8_equiv.surjective]

@[expose] noncomputable def tmW8_commutator_equiv :
    ↥(commutator (WeylGroup Tag.E8)) ≃* ↥wPlus :=
  (Subgroup.equivMapOfInjective (commutator (WeylGroup Tag.E8)) tmW8_equiv.toMonoidHom
      tmW8_equiv.injective).trans
    ((MulEquiv.subgroupCongr tmW8_map_commutator).trans
      ((Subgroup.equivMapOfInjective (commutator ↥wE8) wE8.subtype
          wE8.subtype_injective).trans
        ((MulEquiv.subgroupCongr (tmW8_map_commutator_subtype wE8)).trans
          (MulEquiv.subgroupCongr commutator_wE8))))

theorem tmW8_card_commutator :
    Nat.card ↥(commutator (WeylGroup Tag.E8)) = 348364800 := by
  rw [Nat.card_congr tmW8_commutator_equiv.toEquiv, card_wPlus]

theorem tmW8_card_le_of_ker_le {P : Type*} [Group P] [Finite P] {Z : Subgroup P}
    (hZ : Nat.card Z ≤ 2) {n : ℕ} (f : P →* Equiv.Perm (Fin n)) (hk : f.ker ≤ Z) :
    Nat.card P ≤ 2 * n.factorial := by
  have hker : Nat.card f.ker ≤ 2 := (Subgroup.card_le_of_le hk).trans hZ
  have hrange : Nat.card f.range ≤ n.factorial := by
    calc Nat.card f.range ≤ Nat.card (Equiv.Perm (Fin n)) :=
          Subgroup.card_le_card_group (H := f.range)
      _ = n.factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [← Subgroup.card_ker_mul_card_range f]
  exact Nat.mul_le_mul hker hrange

theorem tmW8_ker_sup_eq_top {P : Type*} [Group P] {Z : Subgroup P} [Z.Normal]
    [IsSimpleGroup (P ⧸ Z)] {M : Type*} [Group M] (f : P →* M) (hk : ¬ f.ker ≤ Z) :
    f.ker ⊔ Z = ⊤ := by
  obtain ⟨x, hxker, hxZ⟩ := SetLike.not_le_iff_exists.mp hk
  haveI : (f.ker.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have htop : f.ker.map (QuotientGroup.mk' Z) = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun hbot => hxZ ?_
    have hxq := Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hxker
    rwa [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxq
  rw [eq_top_iff]
  intro g _
  have hg : QuotientGroup.mk' Z g ∈ f.ker.map (QuotientGroup.mk' Z) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk', hkg⟩ := Subgroup.mem_map.mp hg
  have hz : k⁻¹ * g ∈ Z := by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkg
  simpa using Subgroup.mul_mem_sup hk' hz

theorem tmW8_hom_trivial_of_center {P : Type*} [Group P] [Finite P]
    [IsSimpleGroup (P ⧸ Subgroup.center P)]
    (hcomm : commutator P = ⊤) (hcenter : Nat.card (Subgroup.center P) ≤ 2) {n : ℕ}
    (hn : 2 * Nat.factorial n < Nat.card P)
    (f : P →* Equiv.Perm (Fin n)) : f = 1 := by
  by_cases hk : f.ker ≤ Subgroup.center P
  · exact absurd (tmW8_card_le_of_ker_le hcenter f hk) (not_le.mpr hn)
  have hle : commutator P ≤ f.ker :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (tmW8_ker_sup_eq_top f hk)
      inferInstance
  rw [hcomm, top_le_iff] at hle
  refine MonoidHom.ext fun y => ?_
  have hy : y ∈ f.ker := hle ▸ Subgroup.mem_top y
  simpa using hy

theorem tmW8_hom_trivial_of_le_ten
    {n : ℕ} (hn : n ≤ 10)
    (f : ↥(commutator (WeylGroup Tag.E8)) →* Equiv.Perm (Fin n)) : f = 1 := by
  haveI : IsSimpleGroup (wPlus ⧸ Subgroup.center wPlus) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide)
      lieModel_wPlus_quotient
  have hbig : 2 * Nat.factorial n < Nat.card wPlus := by
    rw [card_wPlus]
    have h10 : Nat.factorial n ≤ 3628800 := (Nat.factorial_le hn).trans (by decide)
    omega
  have hg : f.comp tmW8_commutator_equiv.symm.toMonoidHom = 1 :=
    tmW8_hom_trivial_of_center commutator_wPlus (le_of_eq card_center_wPlus) hbig _
  refine MonoidHom.ext fun x => ?_
  simpa using DFunLike.congr_fun hg (tmW8_commutator_equiv x)

end CFSG.StandardType.FrameRoute

end
