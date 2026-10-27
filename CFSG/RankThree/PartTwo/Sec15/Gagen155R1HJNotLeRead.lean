module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofON
public import CFSG.RankThree.PartTwo.Sec15.Item156Proof
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]


theorem eq_inf_sup_pCoreOf_of_cover_j2 {A L K : Subgroup G}
    (hθO : (aschbacherSolvableCore 3 ↥L).map L.subtype = CFSG.Open.pCoreOf 2 L)
    (hLJ : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800)
    (hK : K ∈ scriptY4 A (lB A))
    (hKJ : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hKL : K = (K ⊓ L) ⊔ CFSG.Open.pCoreOf 2 K) :
    L = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 L := by
  obtain ⟨φK⟩ := hKJ
  have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Proof1515.isSimpleGroup_of_mulEquiv_J2 φK
  have hLK := Proof1515.eq_sup_theta_of_cover (K := K ⊓ L) (L := L) (Y := K)
    inf_le_right inf_le_left hKL hs hK.2.2.2.1 (by
      rw [hLJ, Nat.card_congr φK.toEquiv, KFacts.KS14.card_nativeJ2])
  rw [hθO, inf_comm] at hLK
  exact hLK

theorem hj_case2i_of (h142 : Item142R) {A L K : Subgroup G} {c c' : G}
    (hR : Sec15R G A c L) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hK : K ∈ scriptY4 A (lB A)) (h3L : 3 ∣ Nat.card L)
    (hnot34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (hθO : (aschbacherSolvableCore 3 ↥L).map L.subtype = CFSG.Open.pCoreOf 2 L)
    (hLJ : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800)
    (hc' : Subgroup.zpowers c' ∈ omegaA A)
    (hdec : K = pPrimeCoreOf 3 K ⊔
      deltaZero A (lB A) (K ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)))
    {L' : Subgroup G} (hφ : Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃*
      ↥L' ⧸ aschbacherSolvableCore 3 ↥L'))
    (hJ' : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Blueprint.NativeSporadic.J2)) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      K = (K ⊓ L) ⊔ CFSG.Open.pCoreOf 2 K ∧
      L = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 L := by
  have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
    rw [hΩ] at hc'
    simpa using hc'
  obtain ⟨φ⟩ := hφ
  obtain ⟨φJ'⟩ := hJ'
  have hS : Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃*
      CFSG.Blueprint.NativeSporadic.J2) := ⟨φ.trans φJ'⟩
  have hKJ := Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hK hS
    Proof1515.multFree_J2
  have hO := Proof1515.pPrimeCore_eq_pCore_of_mem_scriptY4 hK hS Proof1515.multFree_J2
  rw [hcc] at hdec
  have hfac := Proof1515.eq_inf_sup_pPrimeCoreOf_of_item142 hR (h142 G A c L hR) h3L hnot34
    hK hdec
  rw [Proof1515.pPrimeCoreOf_eq_pCoreOf_two hO] at hfac
  exact ⟨hKJ, hfac, eq_inf_sup_pCoreOf_of_cover_j2 hθO hLJ hK hKJ hfac⟩

theorem hj_case2ii_false {L' : Subgroup G}
    (hcard : Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 604800)
    (hJ' : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (hL'' : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
        CFSG.Blueprint.NativeSporadic.M22) ∨
      (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
      (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
        CFSG.Assembly.RankThreeEven.projSU 3 5 1))) : False := by
  obtain ⟨φJ'⟩ := hJ'
  rcases hL'' with hM | ⟨_, hφ⟩ | ⟨_, hφ⟩
  · obtain ⟨φM⟩ := hM
    rw [Nat.card_congr φM.toEquiv, KFacts.KS14.card_nativeM22] at hcard
    omega
  · obtain ⟨φ⟩ := hφ
    exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 2)
      (Or.inl ⟨by norm_num, ⟨φ⟩⟩)
  · obtain ⟨φ⟩ := hφ
    exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 1)
      (Or.inr ⟨by norm_num, ⟨φ⟩⟩)

theorem isType156_of_tripleCover_six {A K : Subgroup G} (hK : K ∈ scriptY4 A (lB A))
    (hne : CFSG.pPrimeCore 3 ↥K ≠ ⊤)
    (h6 : Sec4.IsTripleCover (↥K ⧸ CFSG.pPrimeCore 3 ↥K) (alternatingGroup (Fin 6))) :
    IsType156 K := by
  have hc : Nat.card (↥K ⧸ CFSG.pPrimeCore 3 ↥K) = 1080 := by
    rw [card_of_isTripleCover h6, card_alternatingGroup_six]
  have heq := Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hK.2.2.2 hne
    fun p hp hp6 => hc ▸ Proof1515.not_sq_dvd_small (Or.inr rfl) hp hp6
  exact Or.inr (Or.inl (Proof1515.isTripleCover_congr
    (QuotientGroup.quotientMulEquivOfEq heq) h6))

theorem isType156_of_alternating_five {A K : Subgroup G} (hK : K ∈ scriptY4 A (lB A))
    (hne : CFSG.pPrimeCore 3 ↥K ≠ ⊤)
    (h5 : Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* alternatingGroup (Fin 5))) :
    IsType156 K := by
  obtain ⟨φ⟩ := h5
  have hc : Nat.card (↥K ⧸ CFSG.pPrimeCore 3 ↥K) = 60 := by
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
  have heq := Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hK.2.2.2 hne
    fun p hp hp6 => hc ▸ Proof1515.not_sq_dvd_small (Or.inl rfl) hp hp6
  exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq heq).symm.trans φ⟩

theorem isType156_of_on {A K : Subgroup G} (hK : K ∈ scriptY4 A (lB A))
    (hne : CFSG.pPrimeCore 3 ↥K ≠ ⊤)
    (hON : Sec4.IsTripleCover (↥K ⧸ CFSG.pPrimeCore 3 ↥K)
      CFSG.Blueprint.NativeSporadic.ON) : IsType156 K := by
  have heq := Proof1515.pPrimeCore_three_eq_pCore_two_of hK.2.2.2 hne
    fun Z _ hZc hcop ⟨φ⟩ =>
      ks1515ONMult _ Z hK.2.2.2.1 hZc hcop (Proof1515.isTripleCover_congr φ.symm hON)
  exact Or.inr (Or.inr (Proof1515.isTripleCover_congr
    (QuotientGroup.quotientMulEquivOfEq heq) hON))

theorem hj_read148_of_omegaA_eq (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142R) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {K : Subgroup G}
    (hK : K ∈ scriptY4 A (lB A)) :
    IsType156 K ∨
      Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        K = (K ⊓ L) ⊔ CFSG.Open.pCoreOf 2 K ∧ L = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 L) := by
  have hKΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hK
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hK
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by rw [hJc]; norm_num
  have hLJ : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := by
    rw [Nat.card_congr hJ.some.toEquiv, hJc]
  have h3L : 3 ∣ Nat.card L := Proof1515.three_dvd_card_of_mulEquiv hJ.some h3J
  have hnot34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    refine ⟨fun ψ => ?_⟩
    have h1 := Nat.card_congr ψ.toEquiv
    rw [hLJ, KFacts.KS14.card_projSL_three_four] at h1
    omega
  have hθO : (aschbacherSolvableCore 3 ↥L).map L.subtype = CFSG.Open.pCoreOf 2 L := by
    rw [hθ]
    rfl
  rcases Proof1515.cases148_of_mem_scriptY4 (h148 G A c L hR) hR.isElemAbelian.1 hK hKΔ with
    ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', -, -, -, h3⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  ·
    obtain ⟨φJ'⟩ := Proof1523Res3.lA_j2_of_j2 h134 h48 hR hJ hc' hL'
    have hcardL' := Proof1523Res3.card_lA_of_j2 h134 h48 hR hJ hc' hL'
    rcases hcases with hφ | ⟨hL'', -⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨-, h6 | h5⟩
    · exact Or.inr (Or.inr (Or.inr (hj_case2i_of h142 hR hΩ hK h3L hnot34 hθO hLJ hc'
        hdec hφ ⟨φJ'⟩)))
    · exact (hj_case2ii_false hcardL' ⟨φJ'⟩ hL'').elim
    · exact (Proof1514.not_isoLThreePi_of_j2 φJ' hiso).elim
    · exact Or.inl (isType156_of_tripleCover_six hK hne h6)
    · exact Or.inl (isType156_of_alternating_five hK hne h5)
  ·
    rcases h3 with hON | hφ | ⟨h7, hφ⟩
    · exact Or.inl (isType156_of_on hK hne hON)
    · exact Or.inr (Or.inl hφ)
    · exact Or.inr (Or.inr (Or.inl ⟨h7, hφ⟩))
  ·
    exfalso
    have h1 := Proof1523Res3.card_lA_of_j2 h134 h48 hR hJ hc' hL'
    rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven] at h1
    omega
  ·
    exact (Proof1515.not_isLThreeEpsAt_of_card_j2
      (Proof1523Res3.card_lA_of_j2 h134 h48 hR hJ hc' hL') 2 (n * m) hε).elim

theorem hj_eq_inf_sup_of_j2Type (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142R) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {K : Subgroup G}
    (hK : K ∈ scriptY4 A (lB A)) (hKJ : IsJ2Type K) :
    K = (K ⊓ L) ⊔ CFSG.Open.pCoreOf 2 K ∧ L = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 L := by
  obtain ⟨φK⟩ := hKJ
  have hKcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 604800 := by
    rw [Nat.card_congr φK.toEquiv, KFacts.KS14.card_nativeJ2]
  have hcore : CFSG.pPrimeCore 3 ↥K = CFSG.pCore 2 ↥K := by
    have h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [hKcard]
      norm_num
    have hZ3 : IsPGroup 3 (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
      rw [KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φK⟩]
      exact IsPGroup.of_bot
    exact pPrimeCore_three_eq_pCore_two
      (pPrimeCore_three_eq_bot_of_isQuasisimple hK.2.2.2 h3 hZ3)
  rcases hj_read148_of_omegaA_eq h148 h134 h48 h142 hR hJ hθ hΩ hK with
    h156 | hA7 | hL3 | hres
  · exfalso
    exact not_dvd_card_of_isType156 h156 (hKcard ▸ dvd_rfl)
  · exfalso
    obtain ⟨φ⟩ := hA7
    have h1 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 := by
      rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcore).symm.trans φ).toEquiv,
        card_alternatingGroup_seven]
    omega
  · exfalso
    obtain ⟨h7, hφ⟩ := hL3
    letI : Fact (Nat.Prime 7) := h7
    obtain ⟨φ⟩ := hφ
    have h1 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1876896 := by
      rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcore).symm.trans φ).toEquiv,
        Proof1515.card_projSL_three_seven]
    omega
  · exact hres.2

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
