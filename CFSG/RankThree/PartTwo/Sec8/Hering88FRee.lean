module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FCore
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeField
import CFSG.RankThree.PartTwo.Sec8.Hering418FCore
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LieType.Ree


theorem imageModTheta_self {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    imageModTheta L L = ⊤ := by
  rw [imageModTheta, Subgroup.subgroupOf_self, Subgroup.map_top]
  exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem imageModTheta_bot {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    imageModTheta L ⊥ = ⊥ := by
  rw [imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem noThetaNormal_of_isSimpleGroup_of_isPerfect {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] : NoThetaNormal Q := by
  refine Hering418.noThetaNormal_of_isSimpleGroup ?_
  haveI : Nontrivial Q := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isSolvable Q


theorem false_of_isGammaTypeRee
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n)
    (hRee : IsGammaTypeRee (L ⧸ aschbacherSolvableCore 3 L) n)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) {m : ℕ} (hodd : Odd m) (hm2 : 2 ≤ m)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) m) : False := by
  classical
  obtain ⟨-, hA3⟩ := Hering88C.pair_commute_pow_three h
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
  have hout : Sec4.InducesOuterTheta a L := h.toHyp81.inducesOuterTheta
  have hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 :=
    not_isUnitaryTwo_three_of_two_le hn2 (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex)
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
  have hIL : sec8I L a ≤ L := by
    rw [hIdef]
    exact (Item87Proof.residual_le _).trans inf_le_left
  obtain ⟨k₀, hk₀, hkp, ⟨e₀⟩⟩ := hRee
  have hRT : CFSG.Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2
      (2 * k₀ + 1) :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k₀ hk₀)
  obtain ⟨-, a', ha'1, hka, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
  obtain ⟨b', k', _, _, _, hk', hb', ⟨φ⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha'1 hKf e ha3 hout
  have hn : n = 2 * b' + 1 := by omega
  have hb1 : 1 ≤ b' := by omega
  set C := barCentralizer (Subgroup.zpowers a) L with hCdef
  have hperfF : Group.IsPerfect (ReeTag.F4.reeGamma k' b') :=
    ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb1 hk'⟩
  haveI hsimpF : IsSimpleGroup (ReeTag.F4.reeGamma k' b') :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb1 hk'
  haveI hCperf : Group.IsPerfect ↥C :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  haveI hCsimple : IsSimpleGroup ↥C := φ.isSimpleGroup
  have hCres : inSubgroup perfectResidual C = C :=
    inSubgroup_perfectResidual_of_isPerfect (R := C) hCperf
  have hπL : imageModTheta L (sec8I L a) = C := by
    rw [hIdef, imageModTheta_residual_inf_centralizer_eq (le_refl L) haN haN ha3,
      imageModTheta_self, top_inf_eq]
    exact hCres
  have hI : sec8I L a ≠ ⊥ := by
    intro hbot
    have h1 : imageModTheta L (sec8I L a) = ⊥ := by rw [hbot, imageModTheta_bot]
    rw [hπL] at h1
    have hnt : Nontrivial ↥C := inferInstance
    exact (Subgroup.nontrivial_iff_ne_bot C).mp hnt h1
  have hM1 := Hering88E.imageModTheta_sec8I_eq_perfectResidual_of_isoGTwoEven kF87Cent_holds h hUn
    hI hY hIY hcN hm2 hG2
  set R := barCentralizer (Subgroup.zpowers c) Y with hRdef
  haveI hRsimple : IsSimpleGroup ↥(inSubgroup perfectResidual R) :=
    Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hm2 hG2
  haveI hRperf : Group.IsPerfect ↥(inSubgroup perfectResidual R) := Item87Proof.isPerfect_residual R
  have hθL : NoThetaNormal ↥(imageModTheta L (sec8I L a)) :=
    Item87Proof.NoThetaNormal.of_mulEquiv (MulEquiv.subgroupCongr hπL)
      noThetaNormal_of_isSimpleGroup_of_isPerfect
  have hθY : NoThetaNormal ↥(imageModTheta Y (sec8I L a)) :=
    Item87Proof.NoThetaNormal.of_mulEquiv (MulEquiv.subgroupCongr hM1)
      noThetaNormal_of_isSimpleGroup_of_isPerfect
  obtain ⟨χL, -⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta hIL hθL
  obtain ⟨χY, -⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta hIY hθY
  have hcard : Nat.card ↥(imageModTheta Y (sec8I L a)) = Nat.card ↥(imageModTheta L (sec8I L a)) :=
    Nat.card_congr (χY.symm.trans χL).toEquiv
  have hcardY : Nat.card ↥(imageModTheta Y (sec8I L a)) = CFSG.Open.ordG2 (2 ^ m) := by
    obtain ⟨K', _, _, hK', ⟨eG⟩⟩ := hG2
    have hres : inSubgroup perfectResidual R = R := by
      exact inSubgroup_perfectResidual_eq_of_isoGTwoEven hm2 ⟨K', inferInstance, inferInstance,
        hK', ⟨eG⟩⟩
    rw [Nat.card_congr (MulEquiv.subgroupCongr hM1).toEquiv,
      Nat.card_congr (MulEquiv.subgroupCongr hres).toEquiv, Nat.card_congr eG.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK']
  have hcardL : Nat.card ↥(imageModTheta L (sec8I L a)) = CFSG.Open.ordTwistedF4 (2 ^ n) := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr hπL).toEquiv, Nat.card_congr φ.toEquiv,
      Item86ResProof.card_of_mulEquiv_reeGamma b' k' hk' (MulEquiv.refl _), hn]
  have hP1 := Item86ResProof.profile_of_eq
    (CFSG.Timmesfeld.Orders.profile_ordG2 (f := m) (by omega)) hcardY
  have hP2 := Item86ResProof.profile_of_eq
    (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (f := n) (by omega)) (hcard.trans hcardL)
  have := Item86ResProof.two_eq hP1 hP2
  obtain ⟨j, hj⟩ := hodd
  omega

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
