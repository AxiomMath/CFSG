module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SComp
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRows
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHHN
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHTh
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNThreeShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentU
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsS
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SGood
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import Certificates.Certificate8057
public import Certificates.Certificate8058
public import Certificates.Certificate8059

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Sporadic.Th (J thEquivJ)
open CFSG.HardMathSupport.Dickson.I271 (thS thZ thU th_census thEps th_letters_spec
  leaf_closure_of_six)
open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words)

section Generic

variable {S : Type} [Group S] [Finite S]

theorem exists_noncomm_of_perfect {K : Subgroup S} [Group.IsPerfect K] [Nontrivial K] :
    ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  have hc : ∀ a b : K, a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  exact Group.IsPerfect.not_isMulCommutative K ⟨⟨fun a b => hc a b⟩⟩

theorem perfect_le_of_simple_small_index {C E K : Subgroup S} (hEC : E ≤ C)
    [hEs : IsSimpleGroup E] {m : ℕ} (hm : m < 30) (hCm : Nat.card C ≤ m * Nat.card E)
    (hdvd : ¬ Nat.card E ∣ m.factorial) (hKC : K ≤ C) [hKp : Group.IsPerfect K] : K ≤ E := by
  set E' : Subgroup C := E.subgroupOf C with hE'def
  have eE : E' ≃* E := Subgroup.subgroupOfEquivOfLe hEC
  haveI : IsSimpleGroup E' := eE.isSimpleGroup
  have hE'card : Nat.card E' = Nat.card E := Nat.card_congr eE.toEquiv
  have hidx : E'.index ≤ m := by
    have hmul := Subgroup.card_mul_index E'
    rw [hE'card] at hmul
    have hE0 : 0 < Nat.card E := Nat.card_pos
    by_contra hlt
    have hlt' : m + 1 ≤ E'.index := Nat.lt_iff_add_one_le.mp (not_le.mp hlt)
    have : Nat.card E * (m + 1) ≤ Nat.card E * E'.index := Nat.mul_le_mul_left _ hlt'
    nlinarith
  set N := E'.normalCore with hNdef
  have hNE : N ≤ E' := E'.normalCore_le
  have hNnormal : (N.subgroupOf E').Normal := Subgroup.normal_subgroupOf
  have hNeq : N = E' := by
    rcases hNnormal.eq_bot_or_eq_top with h | h
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at h
      have hN1 : N = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hx (hNE hx))
      have hdiv : N.index ∣ E'.index.factorial := E'.index_normalCore_dvd_factorial_index
      rw [hN1, Subgroup.index_bot] at hdiv
      apply hdvd
      calc Nat.card E ∣ Nat.card C := Subgroup.card_dvd_of_le hEC
        _ ∣ E'.index.factorial := hdiv
        _ ∣ m.factorial := Nat.factorial_dvd_factorial hidx
    · exact le_antisymm hNE (Subgroup.subgroupOf_eq_top.mp h)
  haveI hE'n : E'.Normal := hNeq ▸ E'.normalCore_normal
  set K' : Subgroup C := K.subgroupOf C with hK'def
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  haveI : Group.IsPerfect (K'.map (QuotientGroup.mk' E')) := Group.IsPerfect.map _
  have hpf : (Nat.card (K'.map (QuotientGroup.mk' E'))).primeFactors.card ≤ 2 := by
    have hd : Nat.card (K'.map (QuotientGroup.mk' E')) ∣ E'.index :=
      Subgroup.card_subgroup_dvd_card _
    have hpos : 0 < E'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h30 : E'.index < 30 := by omega
    have h1 : E'.index.primeFactors.card ≤ 2 := by
      interval_cases h : E'.index <;>
        exact CFSG.RankThree.PartTwo.Sec4.RonanK429H.primeFactors_card_le_two_of_twoPrimeOK
          (by decide)
    exact (Finset.card_le_card (Nat.primeFactors_mono hd (by omega))).trans h1
  haveI := CFSG.RankThree.PartTwo.Sec4.RonanK429H.subsingleton_of_isPerfect_of_card_primeFactors
    hpf
  have hbot : K'.map (QuotientGroup.mk' E') = ⊥ := Subgroup.eq_bot_of_subsingleton _
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact fun k hk => hbot (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)

theorem good425_of_pConstrained {C : Subgroup S}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3 C) : Good425 C := by
  obtain ⟨R, hRC, hn, hp, hc⟩ := h
  exact good425_of_selfCentralizing' hRC hn hp (fun x hx => hc ⟨hx.2, hx.1⟩)

theorem good425_all_of_mulEquiv {T T' : Type} [Group T] [Group T'] [Finite T] [Finite T']
    (e : T ≃* T') (h : ∀ x : T', orderOf x = 3 → Good425 (Subgroup.centralizer ({x} : Set T'))) :
    ∀ x : T, orderOf x = 3 → Good425 (Subgroup.centralizer ({x} : Set T)) :=
  fun x hx => good425_centralizer_of_mulEquiv e (h (e x) (by rwa [MulEquiv.orderOf_eq]))

end Generic

section HNGood


open CFSG.Sporadic.HNSchreier

instance finite_JH : Finite ↥JH := Finite.of_equiv _ hnEquivJ.toEquiv

theorem hn_three_class : ∀ x : JH, orderOf x = 3 ↔ IsConj (sJ 0) x ∨ IsConj (sJ 2) x :=
  ctuc_hn_intrinsic_three_class_and_alternating_localization.1

theorem card_L1J_eq : Nat.card ↥L1J = 181440 := by
  rw [Subgroup.card_map_of_injective iotaA_injective, card_alt3]

theorem isSimpleGroup_map_of_injective' {G N : Type} [Group G] [Group N] (H : Subgroup G)
    [IsSimpleGroup H] (f : G →* N) (hf : Function.Injective f) : IsSimpleGroup ↥(H.map f) :=
  (H.equivMapOfInjective f hf).symm.isSimpleGroup

theorem isSimpleGroup_L1J : IsSimpleGroup ↥L1J := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  let e1 : alternatingGroup (Fin 9) ≃* alt3 :=
    MulEquiv.ofBijective alt9Hom ⟨alt9Hom_injective, alt9Hom_surjective⟩
  haveI : IsSimpleGroup alt3 := e1.symm.isSimpleGroup
  exact isSimpleGroup_map_of_injective' alt3 iotaA iotaA_injective

theorem good425_hn_s1 : Good425 (CJ (sJ 0)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcomm⟩ :=
    ctuc_hn_three_centralizers_exact
  haveI : IsSimpleGroup ↥L1J := isSimpleGroup_L1J
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  have hKL : K ≤ L1J := by
    have h := Subgroup.commutator_mono hKC hKC
    rw [Subgroup.commutator_eq_self (H := K), hcomm] at h
    exact h
  have hLC : L1J ≤ CJ (sJ 0) := by
    rw [← hcomm]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact (CJ (sJ 0)).mul_mem ((CJ (sJ 0)).mul_mem ((CJ (sJ 0)).mul_mem hx hy)
      ((CJ (sJ 0)).inv_mem hx)) ((CJ (sJ 0)).inv_mem hy)
  have hsL : (K.subgroupOf L1J).IsSubnormal :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429H.isSubnormal_subgroupOf_of_le hLC hKL hKs
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  rcases hsL.eq_bot_or_top_of_isSimpleGroup isSimpleGroup_L1J with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    have hK0 : K = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hbot hk (hKL hk))
    exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt hK0
  · have hKeq : K = L1J := le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp htop)
    subst hKeq
    have hz : Subgroup.center ↥L1J = ⊥ :=
      CFSG.RankThree.PartTwo.Sec4.RonanK429H.center_eq_bot_of_simple_nonab
        (exists_noncomm_of_perfect (K := L1J))
    have hθ : aschbacherSolvableCore 3 ↥L1J = ⊥ :=
      le_bot_iff.mp ((aschbacherSolvableCore_le_center hKq).trans hz.le)
    have hcard : Nat.card (↥L1J ⧸ aschbacherSolvableCore 3 ↥L1J) = 181440 := by
      rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hθ).trans
        QuotientGroup.quotientBot).toEquiv, card_L1J_eq]
    have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) (M := 181440) (B := 57)
      (by norm_num) (by norm_num) hT (dvd_of_eq hcard)
    rw [hcard] at hmem
    exact absurd hmem (by decide +kernel)

theorem good425_hn_s3 : Good425 (CJ (sJ 2)) :=
  good425_of_pConstrained
    (CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_hn3bRChecks
      CFSG.HardMathSupport.Dickson.I271.hn3bR_checks)

theorem good425_hnJ (x : JH) (hx : orderOf x = 3) :
    Good425 (Subgroup.centralizer ({x} : Set JH)) := by
  rcases (hn_three_class x).1 hx with h | h
  · exact Good425.of_isConj h good425_hn_s1
  · exact Good425.of_isConj h good425_hn_s3

theorem good425_hnNative : ∀ x : Blueprint.NativeSporadic.HN, orderOf x = 3 →
    Good425 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.HN)) := by
  haveI : Finite Blueprint.NativeSporadic.HN := Finite.of_equiv _ hnEquivJ.symm.toEquiv
  exact @good425_all_of_mulEquiv Blueprint.NativeSporadic.HN ↥JH Units.instGroup _ _ _ hnEquivJ
    good425_hnJ

theorem good425_spor_HN : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → Nonempty (S ≃* Spor .HN) →
    ∀ s : S, orderOf s = 3 → Good425 (Subgroup.centralizer ({s} : Set S)) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have e0 := e.trans b.symm
  exact @good425_all_of_mulEquiv S Blueprint.NativeSporadic.HN _ Units.instGroup _ _ e0
    good425_hnNative

end HNGood

section HNRow


theorem rowOf425_hn : RowOf425 (Spor .HN) :=
  rowOf425_of_noCC fun S _ _ hs hna hX => noCC425_of_good425 (good425_spor_HN S hs hna hX)

end HNRow

section ThGood


instance finite_thJ : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J

theorem pConstrained_thU :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
      (Subgroup.centralizer ({thU} : Set ↥J)) := by
  refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_map_injective J.subtype
    J.subtype_injective ?_
  rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype']
  obtain ⟨R, hle, hnorm, hcard, hcent⟩ := CFSG.HardMathSupport.Dickson.I271.th_caseU_spec
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_normal_pgroup hle
    (CFSG.HardMathSupport.Dickson.I271.normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) hcard) hcent

theorem good425_thU : Good425 (Subgroup.centralizer ({thU} : Set ↥J)) :=
  good425_of_pConstrained pConstrained_thU

theorem good425_thZ : Good425 (Subgroup.centralizer ({thZ} : Set ↥J)) :=
  good425_of_card_dvd (M := 472392) (B := 78)
    CFSG.HardMathSupport.Dickson.I271.card_centralizer_zJ_dvd (by norm_num) (by norm_num)
    (by decide +kernel)

theorem good425_thS : Good425 (Subgroup.centralizer ({thS} : Set ↥J)) := by
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr =>
    (Census.CoverCenterThreeRest.lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨-, hsimp, -, hcard⟩ := leaf_closure_of_six thEps hε hne
  haveI := hsimp
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    CFSG.HardMathSupport.Dickson.Sec6.th3_facts.2.2.2.2.2
  have hCm : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤
      14 * Nat.card ↥(Subgroup.closure (Set.range thEps)) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEC
    rw [hcard] at hk ⊢
    rw [hk] at hC
    rw [hk]
    omega
  have hdvd : ¬ Nat.card ↥(Subgroup.closure (Set.range thEps)) ∣ Nat.factorial 14 := by
    rw [hcard]
    decide
  have hfree : typeOrders425 4245696 162 = [] := by decide +kernel
  intro K hKC hKq _ hT
  haveI : Group.IsPerfect K := hKq.1
  have hKE : K ≤ Subgroup.closure (Set.range thEps) :=
    perfect_le_of_simple_small_index hEC (m := 14) (by norm_num) hCm hdvd hKC
  have hKdvd : Nat.card K ∣ 4245696 := hcard ▸ Subgroup.card_dvd_of_le hKE
  have hdvdM : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ 4245696 :=
    (card_theta_quot_dvd K).trans hKdvd
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) (M := 4245696) (B := 162)
    (by norm_num) (by norm_num) hT hdvdM
  rw [hfree] at hmem
  exact List.not_mem_nil hmem

theorem good425_thJ (x : ↥J) (hx : orderOf x = 3) :
    Good425 (Subgroup.centralizer ({x} : Set ↥J)) := by
  obtain ⟨k, c, hc, e, he, rfl⟩ := th_census x hx
  obtain ⟨hs3, hz3, hu3⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK429H.th_reps_pow_three
  have hg : Good425 (Subgroup.centralizer ({c} : Set ↥J)) ∧ c ^ 3 = 1 := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨good425_thS, hs3⟩
    · exact ⟨good425_thZ, hz3⟩
    · exact ⟨good425_thU, hu3⟩
  have ha : Good425 (Subgroup.centralizer ({c ^ e} : Set ↥J)) := by
    rw [CFSG.RankThree.PartTwo.Sec4.RonanK429H.centralizer_pow_of_pow_three hg.2 he]
    exact hg.1
  exact Good425.of_isConj (isConj_iff.mpr ⟨k, rfl⟩) ha

theorem good425_thNative : ∀ x : Blueprint.NativeSporadic.Th, orderOf x = 3 →
    Good425 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.Th)) := by
  haveI : Finite Blueprint.NativeSporadic.Th := Finite.of_equiv _ thEquivJ.symm.toEquiv
  exact @good425_all_of_mulEquiv Blueprint.NativeSporadic.Th ↥J Units.instGroup _ _ _ thEquivJ
    good425_thJ

theorem good425_spor_Th : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → Nonempty (S ≃* Spor .Th) →
    ∀ s : S, orderOf s = 3 → Good425 (Subgroup.centralizer ({s} : Set S)) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have e0 := e.trans b.symm
  exact @good425_all_of_mulEquiv S Blueprint.NativeSporadic.Th _ Units.instGroup _ _ e0
    good425_thNative

end ThGood

section ThRow


theorem rowOf425_th : RowOf425 (Spor .Th) :=
  rowOf425_of_noCC fun S _ _ hs hna hX => noCC425_of_good425 (good425_spor_Th S hs hna hX)

end ThRow

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
