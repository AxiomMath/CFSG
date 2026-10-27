module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FRee
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeField
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LieType.Ree


theorem false_of_ree_abs {G : Type} [Group G] [Finite G] {E Y I' : Subgroup G} {a x : G}
    {n m : ℕ} (haN : a ∈ Subgroup.normalizer (E : Set G)) (ha3 : a ^ 3 = 1)
    (hout : Sec4.InducesOuterTheta a E) (hn2 : 2 ≤ n)
    (hRee : IsGammaTypeRee (E ⧸ aschbacherSolvableCore 3 E) n)
    (hI'def : I' = inSubgroup perfectResidual (E ⊓ Subgroup.centralizer ({a} : Set G)))
    (hIY : I' ≤ Y)
    (hM1 : imageModTheta Y I' =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) Y))
    (hodd : Odd m) (hm2 : 2 ≤ m) (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers x) Y) m) :
    False := by
  classical
  have hIE : I' ≤ E := by
    rw [hI'def]
    exact (Item87Proof.residual_le _).trans inf_le_left
  obtain ⟨k₀, hk₀, hkp, ⟨e₀⟩⟩ := hRee
  have hRT : CFSG.Blueprint.ReeTitsModel (E ⧸ aschbacherSolvableCore 3 E) .twistedF4 2
      (2 * k₀ + 1) :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k₀ hk₀)
  obtain ⟨-, a', ha'1, hka, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
  obtain ⟨b', k', _, _, _, hk', hb', ⟨φ⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha'1 hKf e ha3 hout
  have hn : n = 2 * b' + 1 := by omega
  have hb1 : 1 ≤ b' := by omega
  set C := barCentralizer (Subgroup.zpowers a) E with hCdef
  have hperfF : Group.IsPerfect (ReeTag.F4.reeGamma k' b') :=
    ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb1 hk'⟩
  haveI hsimpF : IsSimpleGroup (ReeTag.F4.reeGamma k' b') :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb1 hk'
  haveI hCperf : Group.IsPerfect ↥C :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  haveI hCsimple : IsSimpleGroup ↥C := φ.isSimpleGroup
  have hCres : inSubgroup perfectResidual C = C :=
    inSubgroup_perfectResidual_of_isPerfect (R := C) hCperf
  have hπE : imageModTheta E I' = C := by
    rw [hI'def, imageModTheta_residual_inf_centralizer_eq (le_refl E) haN haN ha3,
      imageModTheta_self, top_inf_eq]
    exact hCres
  set R := barCentralizer (Subgroup.zpowers x) Y with hRdef
  haveI hRsimple : IsSimpleGroup ↥(inSubgroup perfectResidual R) :=
    Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hm2 hG2
  haveI hRperf : Group.IsPerfect ↥(inSubgroup perfectResidual R) := Item87Proof.isPerfect_residual R
  have hθE : NoThetaNormal ↥(imageModTheta E I') :=
    Item87Proof.NoThetaNormal.of_mulEquiv (MulEquiv.subgroupCongr hπE)
      noThetaNormal_of_isSimpleGroup_of_isPerfect
  have hθY : NoThetaNormal ↥(imageModTheta Y I') :=
    Item87Proof.NoThetaNormal.of_mulEquiv (MulEquiv.subgroupCongr hM1)
      noThetaNormal_of_isSimpleGroup_of_isPerfect
  obtain ⟨χE, -⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta hIE hθE
  obtain ⟨χY, -⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta hIY hθY
  have hcard : Nat.card ↥(imageModTheta Y I') = Nat.card ↥(imageModTheta E I') :=
    Nat.card_congr (χY.symm.trans χE).toEquiv
  have hcardY : Nat.card ↥(imageModTheta Y I') = CFSG.Open.ordG2 (2 ^ m) := by
    obtain ⟨K', _, _, hK', ⟨eG⟩⟩ := hG2
    have hres : inSubgroup perfectResidual R = R :=
      inSubgroup_perfectResidual_eq_of_isoGTwoEven hm2 ⟨K', inferInstance, inferInstance,
        hK', ⟨eG⟩⟩
    rw [Nat.card_congr (MulEquiv.subgroupCongr hM1).toEquiv,
      Nat.card_congr (MulEquiv.subgroupCongr hres).toEquiv, Nat.card_congr eG.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK']
  have hcardE : Nat.card ↥(imageModTheta E I') = CFSG.Open.ordTwistedF4 (2 ^ n) := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr hπE).toEquiv, Nat.card_congr φ.toEquiv,
      Item86ResProof.card_of_mulEquiv_reeGamma b' k' hk' (MulEquiv.refl _), hn]
  have hP1 := Item86ResProof.profile_of_eq
    (CFSG.Timmesfeld.Orders.profile_ordG2 (f := m) (by omega)) hcardY
  have hP2 := Item86ResProof.profile_of_eq
    (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (f := n) (by omega)) (hcard.trans hcardE)
  have := Item86ResProof.two_eq hP1 hP2
  obtain ⟨j, hj⟩ := hodd
  omega

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
