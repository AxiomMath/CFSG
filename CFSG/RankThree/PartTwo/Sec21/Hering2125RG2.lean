module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125Bar
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RSL2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarG2
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec11
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem g2_cases {G : Type} [Group G] [Finite G] {Y I : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hI : I ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    {n : ℕ} (hn0 : 0 < n) (hne : Even n)
    (hIn : Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* projSL 2 (GaloisField 2 n)))
    (hZq : ∃ q : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ aschbacherSolvableCore 3 Y) q) :
    (InducesInnerBar Y c ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* AdjointQuotient .G2 K)) ∨
      Nonempty (imageI Y I ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hne; omega
  set Z := Y ⧸ aschbacherSolvableCore 3 Y with hZdef
  set α := Sec4.Item426.thetaAut Y hcN with hαdef
  have hα3 : α ^ 3 = 1 := Sec4.Item426.thetaAut_pow_eq_one Y hcN hc3
  have hJα : imageI Y I ∈ thetaComponentsIn (Sec4.Item426.fixSub α) :=
    Sec4.Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hI
  have hIY : I ≤ Y := (le_of_mem_thetaComponentsIn hI).trans inf_le_left
  obtain ⟨eK⟩ := Sec4.Item426.nonempty_quotTheta_map_equiv Y hIY
  have hIT : IsType424 (I ⧸ aschbacherSolvableCore 3 I) := Or.inl ⟨n, hn0, hIn⟩
  have hJT : IsType424 (imageI Y I ⧸ aschbacherSolvableCore 3 (imageI Y I)) :=
    isType424_of_mulEquiv eK.symm hIT
  obtain ⟨q, hq, ⟨e0⟩⟩ := hZq
  have hperf : Group.IsPerfect Z := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.G2 q').Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨q, hq, ⟨e0⟩⟩, Item1120V0Bar.nonempty_mulEquiv_commutator_of_isPerfect hperf⟩
  have hinner : α ∈ (MulAut.conj : Z →* MulAut Z).range := by
    by_contra hno
    exact noOuterType424G2_holds Z hZ α (imageI Y I) hα3 hno hJα hJT
  obtain ⟨z, hz⟩ := hinner
  have hz3 : MulAut.conj z ^ 3 = 1 := by rw [show (MulAut.conj z : MulAut Z) = α from hz]; exact hα3
  have hJz : imageI Y I ∈ thetaComponentsIn (Sec4.Item426.fixSub (MulAut.conj z)) := by
    rw [show (MulAut.conj z : MulAut Z) = α from hz]; exact hJα
  rcases KS11Lie3Proof.splitFamily_g2 Z hZ with hZ' | hno
  swap
  · exact (hno z (imageI Y I) hz3 hJz hJT).elim
  obtain ⟨K, _, _, hK3, hK4, e, hezM, hB⟩ := KS11Lie4Proof.exists_g2_threeB
    KS11Lie7Proof.g2ThreeConjSL2_holds KS11Lie7Proof.g2ThreeACent_holds
    KS11Lie4Proof.g2ThreeBCent_holds hZ' hz3 hJz hJT
  have hJS : imageI Y I = (KS11Lie4Proof.g2ShortSL2 K).comap e.toMonoidHom := hB.eq hJz
  obtain ⟨e₂⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
  have eJ : imageI Y I ≃* Matrix.SpecialLinearGroup (Fin 2) K := by
    rw [hJS]
    exact (Item1120V0Bar.G2eComapMulEquiv e (KS11Lie4Proof.g2ShortSL2 K)).trans e₂.symm
  have hcard := sl2_quot_card hK4 eJ hn2 ⟨eK.symm.trans hIn.some⟩
  rcases hcard with h2 | ⟨h5, -⟩
  · left
    refine ⟨⟨hcN, z, hz⟩, K, inferInstance, inferInstance, h2, ⟨?_⟩⟩
    exact e.trans ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot).symm
  · right
    exact ⟨eJ.trans (sl2_mulEquiv_five h5)⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2125
