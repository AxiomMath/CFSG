module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofD4
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofInvEltL3
public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofChoose
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2ProofG2

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Main

theorem invElt1118D4Even_holds : InvElt1118D4Even :=
  invElt1118D4Even_of d4ThreeASL3Model_holds

theorem comm1119D4Even_holds : Comm1119D4Even :=
  comm1119D4Even_of d4ThreeASL3Model_holds

open Item1117Res3Proof in
theorem kFact1118InvElt_of_basic (h45 : Sec4.Item4_5) (h117 : Item117) : KFact1118InvElt := by
  intro G _ _ A c L a R Y d x s r g h _ hlist
  rcases hlist with ⟨q, hq, ⟨f⟩⟩ | ⟨n, q, hq, hq2, -, ⟨f⟩⟩ | hL3
  ·
    have hXp := SetUp1118Proof.isPerfect_lie_G2 q hq
    have e : Y ⧸ aschbacherSolvableCore 3 Y ≃*
        _root_.commutator (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
      f.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv).symm
    have hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
        (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
          Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) :=
      ⟨_, inferInstance, ⟨q, hq, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩
    exact exists_orderOf_eq_three_of_family h45 h117 h noOuterType424G2_holds
      (invElt1118For_of_split KS11Lie3Proof.splitFamily_g2 invElt1118G2Ss_holds) hZ
      (KS11Lie3Proof.center_eq_bot_g2 _ hZ)
  ·
    have hXp := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
    have e : Y ⧸ aschbacherSolvableCore 3 Y ≃*
        _root_.commutator (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group :=
      f.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv).symm
    have hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
        (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
          Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) :=
      ⟨_, inferInstance, ⟨q, hq, hq2, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩
    exact exists_orderOf_eq_three_of_family h45 h117 h noOuterType424D4Even_holds
      invElt1118D4Even_holds hZ
      (KS11Lie3Proof.center_eq_bot_d4 _ ⟨_, inferInstance, ⟨q, hq, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩)
  ·
    obtain ⟨k, hk⟩ := h.pow_eq_one
    have hgd : g * d = d * g := Sec12.commute_of_conj_mem_zpowers (Item1117Proof.orderOf_d h)
      ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.W_le_normalizer_d h117 h h.g_mem.2) d).mp
        (Subgroup.mem_zpowers d)) hk
    refine ⟨g, h.g_mem, orderOf_eq_three_of_isLThreePi h hL3 h.g_mem.1 ⟨k, hk⟩ hgd h.conj_mem
      h.g_not_mem, c, h.mem_A, fun heq => h.g_not_mem ?_⟩
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [heq]
    exact Subgroup.mem_zpowers c

open Item1117Res3Proof in
theorem step1119CommD4_of_basic (h45 : Sec4.Item4_5) (h117 : Item117) : Step1119CommD4 := by
  intro G _ _ A c L a R Y d x s r g hbig hD4
  obtain ⟨n, q, hq, hq2, -, ⟨f⟩⟩ := hD4
  have hXp := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
  have e : Y ⧸ aschbacherSolvableCore 3 Y ≃*
      _root_.commutator (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group :=
    f.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv).symm
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) :=
    ⟨_, inferInstance, ⟨q, hq, hq2, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩
  exact step1119Comm_concl_of_family h45 h117 hbig noOuterType424D4Even_holds
    comm1119D4Even_holds hZ
    (KS11Lie3Proof.center_eq_bot_d4 _ ⟨_, inferInstance, ⟨q, hq, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩)

end Main

end CFSG.RankThree.PartTwo.Sec11
