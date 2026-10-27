module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
import CFSG.Quasithin.Background.Asc81cPfTrans2
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4O8
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.E6TwentyTwoA
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.LiteratureLocal
  (ward_kleidman_small_Ree_involution_centralizer_maximal)

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem rkIdx_fixV_zpowers_conj (g x : MulAut W) :
    rkIdx (fixV (zpowers (g * x * g⁻¹))) = rkIdx (fixV (zpowers x)) := by
  rw [fixV_zpowers_conj, rkIdx, rkIdx, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]

theorem le_of_isPGroup_two_of_outer_odd {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hOut : Odd (Nat.card (Outer ↥L)))
    (hAY : A ≤ Y) (hA2 : IsPGroup 2 ↥A) : A ≤ L := by
  classical
  let L' : Subgroup ↥Y := L.subgroupOf Y
  have : L'.Normal := hLn
  let e : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  let ψ : ↥Y →* MulAut ↥L :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (G := ↥Y) (H := L'))
  let φ : ↥Y →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp ψ
  have : Finite (Outer ↥L) := inferInstance
  let fA : ↥A →* Outer ↥L := φ.comp (Subgroup.inclusion hAY)
  have hmap2 : IsPGroup 2 fA.range :=
    IsPGroup.of_surjective hA2 fA.rangeRestrict fA.rangeRestrict_surjective
  have hbot : fA.range = ⊥ := by
    have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
      (G := Outer ↥L) (H := fA.range) (K := ⊤) hmap2 (by simpa using hOut)
    simpa using h
  intro a ha
  have hone : fA ⟨a, ha⟩ = 1 := by
    have hmem : fA ⟨a, ha⟩ ∈ fA.range := MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hone' : (QuotientGroup.mk' (inner ↥L)) (ψ ⟨a, hAY ha⟩) = 1 := hone
  have hinner : ψ ⟨a, hAY ha⟩ ∈ inner ↥L := (QuotientGroup.eq_one_iff _).mp hone'
  obtain ⟨l, hl⟩ := hinner
  let lY : ↥Y := ⟨(l : MulAut W), hLY l.2⟩
  let aY : ↥Y := ⟨a, hAY ha⟩
  let lL : ↥L' := ⟨lY, Subgroup.mem_subgroupOf.mpr l.2⟩
  have hlL : (lL : ↥Y) = lY := rfl
  have hconjEq : MulAut.conjNormal (G := ↥Y) (H := L') lL =
      MulAut.conjNormal (G := ↥Y) (H := L') aY := by
    apply (MulAut.congr e).injective
    calc (MulAut.congr e) (MulAut.conjNormal (G := ↥Y) (H := L') lL)
        = MulAut.conj (e lL) := by
          rw [MulAut.conjNormal_val]
          exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e lL
      _ = MulAut.conj l := by rfl
      _ = ψ aY := hl
      _ = (MulAut.congr e) (MulAut.conjNormal (G := ↥Y) (H := L') aY) := rfl
  have hxL : (lY⁻¹ * aY : ↥Y).1 ∈ L := by
    apply W4Row.mem_of_mem_centralizer_of_fstar_eq (G := MulAut W) hLY hF
      (Y := Y) (L := L) (lY⁻¹ * aY).2
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let zY : ↥Y := ⟨z, hLY hz⟩
    have hz' : zY ∈ L' := Subgroup.mem_subgroupOf.mpr hz
    have h := congrArg (fun f : MulAut ↥L' => f ⟨zY, hz'⟩) hconjEq
    have hY : ((MulAut.conjNormal (G := ↥Y) (H := L') lL) ⟨zY, hz'⟩ : ↥Y) =
        ((MulAut.conjNormal (G := ↥Y) (H := L') aY) ⟨zY, hz'⟩ : ↥Y) :=
      congrArg Subtype.val h
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply] at hY
    have hW : (l : MulAut W) * z * (l : MulAut W)⁻¹ = a * z * a⁻¹ := by
      simpa using congrArg (fun y : ↥Y => (y : MulAut W)) hY
    have hconj : ((l : MulAut W)⁻¹ * a) * z * ((l : MulAut W)⁻¹ * a)⁻¹ = z := by
      calc ((l : MulAut W)⁻¹ * a) * z * ((l : MulAut W)⁻¹ * a)⁻¹
          = (l : MulAut W)⁻¹ * (a * z * a⁻¹) * l := by group
        _ = (l : MulAut W)⁻¹ * ((l : MulAut W) * z * (l : MulAut W)⁻¹) * l := by rw [hW]
        _ = z := by group
    calc z * ((l : MulAut W)⁻¹ * a)
        = (((l : MulAut W)⁻¹ * a) * z * ((l : MulAut W)⁻¹ * a)⁻¹) *
            ((l : MulAut W)⁻¹ * a) := by rw [hconj]
      _ = ((l : MulAut W)⁻¹ * a) * z := by group
  have haeq : a = (l : MulAut W) * ((lY⁻¹ * aY : ↥Y) : MulAut W) := by
    rw [show ((lY⁻¹ * aY : ↥Y) : MulAut W) = (l : MulAut W)⁻¹ * a from rfl]
    group
  rw [haeq]
  exact L.mul_mem l.2 hxL

theorem mem_of_orderOf_two_of_outer_odd {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hOut : Odd (Nat.card (Outer ↥L)))
    {t : MulAut W} (htY : t ∈ Y) (ht : orderOf t = 2) : t ∈ L := by
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hA2 : IsPGroup 2 ↥(zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  exact le_of_isPGroup_two_of_outer_odd hLY hLn hF hOut (zpowers_le.mpr htY) hA2
    (mem_zpowers t)

theorem exists_orderOf_two_of_psl2 {m : ℕ} {K : Subgroup (MulAut W)}
    (eK : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 (2 * m + 1)))
    (hm : 1 ≤ m) : ∃ s ∈ K, orderOf s = 2 := by
  have hFcard : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 3 (2 * m + 1)) := by
    rw [hFcard]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqPSL : CFSG.IsQuasisimple
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 (2 * m + 1))) :=
    CFSG.RankThree.PartTwo.KFacts.isQuasisimple_psl2_of_four_le_card h4
  have hqK : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hqPSL
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2
    (E6.two_dvd_card_of_isQuasisimple hqK)
  exact ⟨s, s.2, (Subgroup.orderOf_coe s).trans hs⟩


theorem eight_le_mParam_of_psl2 (hW : ∀ w : W, w ^ 2 = 1) {m : ℕ} (hm : 1 ≤ m)
    {K : Subgroup (MulAut W)}
    (eK : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 (2 * m + 1))) :
    8 ≤ E3.mParam K := by
  have hFcard : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have h4q : 4 ≤ 3 ^ (2 * m + 1) := by
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 3 (2 * m + 1)) := by rwa [hFcard]
  have h9 : 9 < 3 ^ (2 * m + 1) := by
    calc 9 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqPSL : CFSG.IsQuasisimple
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 (2 * m + 1))) :=
    CFSG.RankThree.PartTwo.KFacts.isQuasisimple_psl2_of_four_le_card h4
  have hqK : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hqPSL
  have hFstar : Fstar K = K :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.fstar_eq_self_of_isQuasisimple
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hqK)
  have hLn : (K.subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hLie : LieModel ↥K .PSL 2 3 (2 * m + 1) :=
    CFSG.ComponentClassification.GSThmB.Cov.lieModel_psl2_of_card
      (p := 3) (n := 2 * m + 1) (by norm_num) h4q hFcard eK
  have hq25 : 3 ^ (2 * m + 1) ≠ 25 := by
    intro h
    have hdvd : 3 ∣ 3 ^ (2 * m + 1) := dvd_pow_self 3 (by omega)
    rw [h] at hdvd
    norm_num at hdvd
  have hLem := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.w4Lem7_4_holds
    (W := W) hW (Y := K) (L := K) (p := 3) (e := 2 * m + 1) (q := 3 ^ (2 * m + 1))
    le_rfl hLn hFstar (by norm_num) (by norm_num) (by omega) rfl h9 hLie
  rcases hLem.2.2.2.1 (by omega) with h8 | ⟨h25, -⟩
  · exact h8
  · exact absurd h25 hq25


theorem eight_le_mParam_of_ree (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} {m : ℕ}
    (hm : 1 ≤ m) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L)
    (hRee : LieModel ↥L .twistedG2 0 3 (2 * m + 1)) : 8 ≤ E3.mParam Y := by
  classical
  have hR : CFSG.Blueprint.ReeTitsModel ↥L .twistedG2 3 (2 * m + 1) :=
    (hRee.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨-, ⟨⟨t₀, ht₀⟩, hconj⟩, hcen, -, -, -, hoddOut⟩ :=
    ward_kleidman_small_Ree_involution_centralizer_maximal m hm ↥L hR
  obtain ⟨K, -, -, -, ⟨eK⟩, -⟩ := hcen t₀ ht₀
  let KW : Subgroup (MulAut W) := K.map L.subtype
  let eKW : ↥KW ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 (2 * m + 1)) :=
    (Subgroup.equivMapOfInjective K L.subtype L.subtype_injective).symm.trans eK
  have h8K : 8 ≤ E3.mParam KW := eight_le_mParam_of_psl2 hW hm eKW
  obtain ⟨s, hsK, hs⟩ := exists_orderOf_two_of_psl2 eKW hm
  have hsL : s ∈ L := Subgroup.map_subtype_le K hsK
  have h8s : 8 ≤ rkIdx (fixV (zpowers s)) :=
    h8K.trans (Asc81c.Pf.mParam_le_of_orderOf_two hsK hs)
  refine SevenFour.le_mParam_of_forall
    ⟨(t₀ : MulAut W), hLY t₀.2, (Subgroup.orderOf_coe t₀).trans ht₀⟩ ?_
  intro t htY ht
  have htL : t ∈ L := mem_of_orderOf_two_of_outer_odd hLY hLn hF hoddOut htY ht
  have hsL2 : orderOf (⟨s, hsL⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hs
  have htL2 : orderOf (⟨t, htL⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ _ hsL2 htL2)
  have hcW : (c : MulAut W) * s * (c : MulAut W)⁻¹ = t := by
    simpa using congrArg Subtype.val hc
  rw [← hcW, rkIdx_fixV_zpowers_conj]
  exact h8s

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
