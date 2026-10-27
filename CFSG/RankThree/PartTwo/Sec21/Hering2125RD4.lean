module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125Bar
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RSL2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarG2
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec11
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

theorem d4_cases {G : Type} [Group G] [Finite G] {Y I : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hI : I ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    {n : ℕ} (hn0 : 0 < n) (hne : Even n)
    (hIn : Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* projSL 2 (GaloisField 2 n)))
    (hZq : ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      q.p = 2 ∧ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) :
    InducesInnerBar Y c ∧ ∃ m : ℕ, 0 < m ∧ Even m ∧
      ChevalleyExceptionalModel (Y ⧸ aschbacherSolvableCore 3 Y) .trialityD4 2 m := by
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
  obtain ⟨q, hq, hp2, ⟨e0⟩⟩ := hZq
  have hperf : Group.IsPerfect Z := by
    have := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hcomm : Nonempty (Z ≃* _root_.commutator Z) :=
    Item1120V0Bar.nonempty_mulEquiv_commutator_of_isPerfect hperf
  have hZeven : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid), q'.p = 2 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨q, hq, hp2, ⟨e0⟩⟩, hcomm⟩
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid), q'.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨q, hq, by omega, ⟨e0⟩⟩, hcomm⟩
  have hinner : α ∈ (MulAut.conj : Z →* MulAut Z).range := by
    by_contra hno
    exact noOuterType424D4Even_holds Z hZeven α (imageI Y I) hα3 hno hJα hJT
  obtain ⟨z, hz⟩ := hinner
  have hz3 : MulAut.conj z ^ 3 = 1 := by
    rw [show (MulAut.conj z : MulAut Z) = α from hz]; exact hα3
  have hJz : imageI Y I ∈ thetaComponentsIn (Sec4.Item426.fixSub (MulAut.conj z)) := by
    rw [show (MulAut.conj z : MulAut Z) = α from hz]; exact hJα
  obtain ⟨K, _, _, q', σ, hKcard, hσ, h3, hσ3, hz3', hz1, e, hezM, hB⟩ :=
    KS11Lie4Proof.exists_d4_threeB KS11Lie6Proof.d4ThreeConj_holds
      KS11Lie6Proof.d4ThreeACent_holds KS11Lie6Proof.d4ThreeBCent_holds hZ hz3 hJz hJT
  have hJS : imageI Y I = (KS11Lie4Proof.d4ShortSL2 K σ.toRingHom).comap e.toMonoidHom :=
    hB.eq hJz
  obtain ⟨e₂⟩ := KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 (K := K) hσ3
  haveI hFin : Finite (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) :=
    Subtype.finite
  have hcardF := KS11Lie4Proof.natCard_orbitField_d4Outer hσ3
  have hq2 : 2 ≤ q' := by
    rcases Nat.lt_or_ge q' 2 with h | h
    · exfalso
      have : Nat.card K ≤ 1 := by
        rw [hKcard]
        interval_cases q' <;> simp
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  have hF4 : 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) := by
    rw [hcardF, hKcard]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ q' ^ 3 := Nat.pow_le_pow_left hq2 3
  have eJ : imageI Y I ≃* Matrix.SpecialLinearGroup (Fin 2)
      (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) := by
    rw [hJS]
    exact (Item1120V0Bar.G2eComapMulEquiv e (KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)).trans
      e₂.symm
  have hcard := sl2_quot_card hF4 eJ hn2 ⟨eK.symm.trans hIn.some⟩
  rw [hcardF, hKcard] at hcard
  have hq3 : q' ^ 3 = 2 ^ n := by
    rcases hcard with h | ⟨h5, -⟩
    · exact h
    · exfalso
      have hq5 : q' ≤ 5 := by
        have : q' ≤ q' ^ 3 := Nat.le_self_pow (by norm_num) q'
        omega
      interval_cases q' <;> omega
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show q' ∣ 2 ^ n from ⟨q' ^ 2, by rw [← hq3]; ring⟩)
  have hnm : n = 3 * m := by
    have h1 : 2 ^ (3 * m) = 2 ^ n := by rw [← hq3, hm, ← pow_mul, mul_comm]
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hm0 : 0 < m := by omega
  have hmev : Even m := by
    rcases Nat.even_or_odd m with h | h
    · exact h
    · exfalso
      have : Odd (3 * m) := by
        exact Odd.mul (by decide) h
      rw [← hnm] at this
      exact (Nat.not_even_iff_odd.mpr this) hne
  refine ⟨⟨hcN, z, hz⟩, m, hm0, hmev, ⟨Nat.prime_two, hm0, rfl⟩, K, inferInstance,
    inferInstance, ?_, σ.toRingHom, ?_, ?_⟩
  · rw [hKcard, hm]
    rfl
  · intro c
    rw [← hm]
    exact hσ c
  · subst hm
    have hK3 : Nat.card K = (2 ^ m) ^ 3 := hKcard
    obtain ⟨-, -, -, -, -, -, -, ⟨eQ⟩⟩ :=
      even_triality_exact_automorphism_normal_form hm0 K hK3 σ (fun c => hσ c)
    exact ⟨e.trans eQ.symm⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2125
