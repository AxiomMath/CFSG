module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Trans
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofJ3Assembly
import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MLayer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217SecondA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217SecondB

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section Main

set_option linter.unusedSectionVars false

theorem Cover217.not_inf_normalizer_le_zpowers {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (haA : a ∈ A) (hac : a ∉ Subgroup.zpowers c) :
    ¬ L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  intro hN
  obtain ⟨F₁, hF₁A, hF₁27, -, hcls⟩ := h.invariant_subgroups hθ hAL
  have ha3 : a ^ 3 = 1 := h.isElemAbelian_A.2 a haA
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ Subgroup.one_mem _)
  have hcard : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  have hinv : ∀ x ∈ L ⊓ Subgroup.normalizer (A : Set G),
      (Subgroup.zpowers a).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers a :=
    fun x hx => map_conj_eq_of_mem_normalizer (hN hx)
  rcases hcls _ (Subgroup.zpowers_le.2 haA) hinv with h0 | h0 | h0 | h0
  · rw [h0, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exact hac (h0 ▸ Subgroup.mem_zpowers a)
  · rw [h0, hF₁27] at hcard
    norm_num at hcard
  · rw [h0, h.card] at hcard
    norm_num at hcard

@[expose] def Item2116At217 : Prop :=
  ∀ (A E U : Subgroup G) (c : G) (L : Subgroup G), Cover217 A E U c L →
    ∀ U₀ ∈ fourGroupsMinus E, ∀ (a : G) (K : Subgroup G), a ∉ Subgroup.zpowers c →
      (a, K) ∈ lThreeStarPairs A E U₀ → ¬ IsL4L5Sp6 K

theorem item2116At217_of (h45 : Sec4.Item4_5) (h212 : Item212) : Item2116At217 (G := G) := by
  intro A E U c L h U₀ hU₀ a K hac hpair hK
  have hθ := sec217ThetaOne_holds A E U c L h
  have hAL := sec217ALe_of h45 A E U c L h
  have hp : Sec21Pair G A E U₀ a K :=
    { h.pair.toSec21Std with
      mem_E := h.pair.mem_E
      mem_U := fourGroupsMinus_subset E hU₀
      mem_pair := hpair }
  have haA : a ∈ A := h.pair.mem_E.2 (mem_lThreeStarPairs_iff.mp hpair).1.1
  exact h.not_inf_normalizer_le_zpowers hθ hAL haA hac (inf_le_right.trans (h212 G A E U₀ a K hp hK))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.K_type' {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (h211 : Item211) (h213 : Item213) (h214 : Item214Unitary)
    (h2116 : Item2116At217 (G := G))
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {a : G} {U₀ K : Subgroup G} (hU₀ : U₀ ∈ fourGroupsMinus E) (hac : a ∉ Subgroup.zpowers c)
    (hpair : (a, K) ∈ lThreeStarPairs A E U₀) (hU₀K : U₀ ≤ K) :
    (Nonempty (lBar K ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar K) NativeSporadic.J3) ∧
      Sec4.IsExtOf ↥(starOf A K) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) := by
  have hp : Sec21Pair G A E U₀ a K :=
    { h.pair.toSec21Std with
      mem_E := h.pair.mem_E
      mem_U := fourGroupsMinus_subset E hU₀
      mem_pair := hpair }
  have hcase := h211 G A E U₀ a K hp
  have hA := h.card
  have h116 := h2116 A E U c L h U₀ hU₀ a K hac hpair
  unfold Case211 at hcase
  have h34 : Nat.card A = 3 ^ 3 → False := fun hA3 => by
    rw [hA3] at hA; norm_num at hA
  rcases hcase with ⟨-, -, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ |
    ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨h10, -, -⟩ | ⟨h11, -, hext⟩ |
    ⟨-, hA3, -⟩ | ⟨h13, -, -⟩
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exfalso
    obtain ⟨n, hn, hno, ⟨e⟩⟩ := h10
    have : IsSimpleGroup (Assembly.RankThreeEven.projSU 4 2 n) :=
      isSimpleGroup_projSU le_rfl (by omega)
    have hq := h213 G A E U₀ a K hp
    have hKe : Nonempty (↥K ≃* Assembly.RankThreeEven.projSU 4 2 n) :=
      Item221Proof.nonempty_mulEquiv_of_center_eq_bot hq e fun e' =>
        Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hq.1 (by omega) e'
    exact h214 G A E U₀ a K hp ⟨n, hno, hKe⟩ ⟨U₀, hU₀, hU₀K⟩
  · exact ⟨h11, hext⟩
  · exact (h34 hA3).elim
  · exact absurd (Or.inr (Or.inr h13)) h116

theorem sec217SecondB_of' (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h211 : Item211)
    (h213 : Item213) (h214 : Item214Unitary) (h2116 : Item2116At217 (G := G))
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Sec217SecondB (G := G) := by
  intro A E U c L h a hfr U₀ hU₀ hU₀I K hK hpair
  have hθ := sec217ThetaOne_holds A E U c L h
  have hAL := sec217ALe_of h45 A E U c L h
  obtain ⟨K', hK', hIK'⟩ := h.exists_component_ge_iCore h48 hθ hAL hfr
  have hKK' : K = K' :=
    eq_of_commutator_eq_of_le hK.2 hK' (hU₀I.trans hIK') hpair.2.2.2.2.2.1
  subst hKK'
  exact ⟨(h.K_type' h211 h213 h214 h2116 hGA hU₀ hfr.not_mem hpair (hU₀I.trans hIK')).1, hIK'⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.quot_K' {A E U : Subgroup G} {c : G} {L : Subgroup G} (h : Cover217 A E U c L)
    (h211 : Item211) (h213 : Item213) (h214 : Item214Unitary) (h2116 : Item2116At217 (G := G))
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {a : G} {U₀ K : Subgroup G} (hU₀ : U₀ ∈ fourGroupsMinus E) (hac : a ∉ Subgroup.zpowers c)
    (hpair : (a, K) ∈ lThreeStarPairs A E U₀) (hU₀K : U₀ ≤ K) :
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* NativeSporadic.J3) := by
  have hp := h.sec21Pair_K hU₀ hpair
  obtain ⟨hty, -⟩ := h.K_type' h211 h213 h214 h2116 hGA hU₀ hac hpair hU₀K
  have hq := h213 G A E U₀ a K hp
  rcases hty with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · have hZ : Subgroup.center (lBar K) = ⊥ := center_eq_bot_of_equiv_J3 e
    exact nonempty_quot_center_of_lBar (S := NativeSporadic.J3) hq
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        (QuotientGroup.quotientBot.trans e))
  · exact nonempty_quot_center_of_lBar (S := NativeSporadic.J3) hq e

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.mem_K_of_notInL' {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (h211 : Item211) (h213 : Item213) (h214 : Item214Unitary)
    (h2116 : Item2116At217 (G := G))
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hN : Item217NotInL) {a : G} {U₀ K : Subgroup G} (hU₀ : U₀ ∈ fourGroupsMinus E)
    (hac : a ∉ Subgroup.zpowers c)
    (hpair : (a, K) ∈ lThreeStarPairs A E U₀) (hU₀K : U₀ ≤ K) : a ∈ K := by
  by_contra haK
  exact hN G A E U₀ a K (h.sec21Pair_K hU₀ hpair)
    (h.quot_K' h211 h213 h214 h2116 hGA hU₀ hac hpair hU₀K) haK

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.of_K' {A E U : Subgroup G} {c : G} {L : Subgroup G} (h : Cover217 A E U c L)
    (h211 : Item211) (h213 : Item213) (h214 : Item214Unitary) (h2116 : Item2116At217 (G := G))
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {a : G} (hfr : Frame217 E c L a) {U₀ K : Subgroup G} (hU₀ : U₀ ∈ fourGroupsMinus E)
    (hpair : (a, K) ∈ lThreeStarPairs A E U₀) (hU₀K : U₀ ≤ K) (haK : a ∈ K) :
    Cover217 A E U₀ a K := by
  have hp := h.sec21Pair_K hU₀ hpair
  obtain ⟨hty, hext⟩ := h.K_type' h211 h213 h214 h2116 hGA hU₀ hfr.not_mem hpair hU₀K
  have hq := h213 G A E U₀ a K hp
  have ha1 : a ≠ 1 := fun h1 => hfr.not_mem (h1 ▸ Subgroup.one_mem _)
  have ha3 : a ^ 3 = 1 := h.isElemAbelian_A.2 a (h.pair.mem_E.2 hfr.mem)
  have haord : orderOf (⟨a, haK⟩ : ↥K) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime ha3 ha1
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) :=
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.1
      (lZeroStarAt_subset A a (mem_lThreeStarPairs_iff.1 hpair).2.2.1)).1
  have htri : Sec4.IsTripleCover (lBar K) NativeSporadic.J3 := by
    rcases hty with ⟨⟨e⟩⟩ | htri
    · exfalso
      obtain ⟨hTs, hTch, hT3, -⟩ := solvable_prime_complement_core_characterization (H := K)
        Nat.prime_three
      have hcen : (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : lBar K) ∈ Subgroup.center (lBar K) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hKC k.2))
      have hZbot : Subgroup.center (lBar K) = ⊥ := center_eq_bot_of_equiv_J3 e
      rw [hZbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
      apply hT3
      have := Subgroup.orderOf_dvd_natCard _ hcen
      rw [haord] at this
      exact this
    · exact htri
  have hquot : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* NativeSporadic.J3) := by
    obtain ⟨-, ⟨e⟩⟩ := htri
    exact nonempty_quot_center_of_lBar (S := NativeSporadic.J3) hq e
  exact { pair := hp, quot := hquot, mem := haK, cover := htri, card := h.card, ext := hext }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem item217InLIrredCover_of_notInL' (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h211 : Item211) (h213 : Item213) (h214 : Item214Unitary) (h215 : Item215) (h212 : Item212)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hN : Item217NotInL) : Item217InLIrredCover := by
  intro G _ _ A E U c L hpair hq hcL hcov h81 hext
  have hC : Cover217 A E U c L := ⟨hpair, hq, hcL, hcov, h81, hext⟩
  have h2116 : Item2116At217 (G := G) := item2116At217_of h45 h212
  have hθ := sec217ThetaOne_holds A E U c L hC
  have hAL := sec217ALe_of h45 A E U c L hC
  obtain ⟨a, hfr, U₀, hU₀, hU₀I, K, hK, hKpair⟩ := sec217SecondA_of h45 h215 A E U c L hC
  obtain ⟨-, hIK⟩ := sec217SecondB_of' h45 h48 h211 h213 h214 h2116 hGA A E U c L hC a hfr U₀ hU₀
    hU₀I K hK hKpair
  have haK := hC.mem_K_of_notInL' h211 h213 h214 h2116 hGA hN hU₀ hfr.not_mem hKpair
    (hU₀I.trans hIK)
  have hKcov := hC.of_K' h211 h213 h214 h2116 hGA hfr hU₀ hKpair (hU₀I.trans hIK) haK
  have hθK := sec217ThetaOne_holds A E U₀ a K hKcov
  have hAK := sec217ALe_of h45 A E U₀ a K hKcov
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) :=
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.1
      (lZeroStarAt_subset A a (mem_lThreeStarPairs_iff.1 hKpair).2.2.1)).1
  intro B' hB'
  set S : Subgroup G := B'.map A.subtype with hS_def
  have hSA : S ≤ A := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hconj : ∀ x ∈ Subgroup.normalizer (A : Set G), S.map (MulAut.conj x).toMonoidHom = S := by
    intro x hx
    have h1 := hB' (A.normalizerMonoidHom ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
    have h2 : S.map (MulAut.conj x).toMonoidHom =
        (B'.map (A.normalizerMonoidHom ⟨x, hx⟩).toMonoidHom).map A.subtype := by
      rw [hS_def, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h2, h1]
  rcases hC.irreducible_of_K hθ hAL hfr hKcov hθK hAK hIK hKC S hSA hconj with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective B' A.subtype_injective).1 h
  · right
    apply Subgroup.map_injective A.subtype_injective
    rw [← hS_def, h, Subgroup.map_top, Subgroup.range_subtype]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem item217InLTransCover_of_notInL' (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h211 : Item211) (h213 : Item213) (h214 : Item214Unitary) (h215 : Item215) (h212 : Item212)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hN : Item217NotInL) : Item217InLTransCover := by
  intro G _ _ A E U c L hpair hq hcL hcov h81 hext
  have hC : Cover217 A E U c L := ⟨hpair, hq, hcL, hcov, h81, hext⟩
  have h2116 : Item2116At217 (G := G) := item2116At217_of h45 h212
  have hθ := sec217ThetaOne_holds A E U c L hC
  have hAL := sec217ALe_of h45 A E U c L hC
  obtain ⟨a, hfr, U₀, hU₀, hU₀I, K, hK, hKpair⟩ := sec217SecondA_of h45 h215 A E U c L hC
  obtain ⟨-, hIK⟩ := sec217SecondB_of' h45 h48 h211 h213 h214 h2116 hGA A E U c L hC a hfr U₀ hU₀
    hU₀I K hK hKpair
  have haK := hC.mem_K_of_notInL' h211 h213 h214 h2116 hGA hN hU₀ hfr.not_mem hKpair
    (hU₀I.trans hIK)
  have hKcov := hC.of_K' h211 h213 h214 h2116 hGA hfr hU₀ hKpair (hU₀I.trans hIK) haK
  have hθK := sec217ThetaOne_holds A E U₀ a K hKcov
  have hAK := sec217ALe_of h45 A E U₀ a K hKcov
  have hEA : E ≤ A := hC.pair.mem_E.2
  have hfrK := hC.frame_K hθ hAL hfr hKcov hθK hAK hIK
  exact hC.exists_transvection hθ hAL (hfr.valid hEA) hKcov hθK hAK (hfrK.valid hEA) hIK

theorem item217_of_notInL' (hMcL : KFacts.KP14.SylowTransvectionGL43) (h211 : Item211)
    (h213 : Item213) (h214 : Item214Unitary) (h215 : Item215) (h212 : Item212)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hN : Item217NotInL) : Item217 :=
  Item2113Res3Proof.item217_of_res3 hMcL h211 h45 h66
    (item217InLIrredCover_of_notInL' h45 h48 h211 h213 h214 h215 h212 hGA hN)
    (item217InLTransCover_of_notInL' h45 h48 h211 h213 h214 h215 h212 hGA hN)
    ks217J3CoverPreimage_holds ks217J3CoverNoTransvection_holds ks217J3CoverSylowFix_holds
    (fun G _ _ A E U c L hp hq hc _ _ _ => hN G A E U c L hp hq hc)

@[expose] def Sec217OutNoFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∉ L →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∀ a : G, Frame217 E c L a →
        ¬ L ⊓ Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)

@[expose] def Item2116At217Out : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∉ L →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∀ a : G, Frame217 E c L a → ∀ U₀ ∈ fourGroupsMinus E, ∀ K : Subgroup G,
        (a, K) ∈ lThreeStarPairs A E U₀ → ¬ IsL4L5Sp6 K

theorem item2116At217Out_of (h212 : Item212) (hS : Sec217OutNoFix) : Item2116At217Out := by
  intro G _ _ A E U c L hp hq hc h81 hext a hfr U₀ hU₀ K hpair hK
  have hp' : Sec21Pair G A E U₀ a K :=
    { hp.toSec21Std with
      mem_E := hp.mem_E
      mem_U := fourGroupsMinus_subset E hU₀
      mem_pair := hpair }
  exact hS G A E U c L hp hq hc h81 hext a hfr (inf_le_right.trans (h212 G A E U₀ a K hp' hK))

end Main

theorem mem_normalizer_of_forall_conj_mem {Q : Type*} [Group Q] [Finite Q] {H : Subgroup Q}
    {m : Q} (h : ∀ x ∈ H, m * x * m⁻¹ ∈ H) : m ∈ Subgroup.normalizer (H : Set Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj m).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact (Subgroup.card_map_of_injective (f := ((MulAut.conj m : MulAut Q) : Q →* Q))
    (MulAut.conj m).injective).ge

theorem mem_normalizer_zpowers_of_conj_mem {Q : Type*} [Group Q] [Finite Q] {y m : Q}
    (h : m * y * m⁻¹ ∈ Subgroup.zpowers y) :
    m ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup Q) : Set Q) := by
  refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have : m * y ^ k * m⁻¹ = (m * y * m⁻¹) ^ k := by
    simp [conj_zpow]
  rw [this]
  exact Subgroup.zpow_mem _ h k

theorem not_nonCentral_of_normalizes_sylow {Q : Type*} [Group Q] [Finite Q]
    {M : Subgroup Q} {y : Q} (hy3 : y ^ 3 = 1)
    (hM : ∀ m ∈ M, m * y * m⁻¹ ∈ Subgroup.zpowers y)
    (hcard : 3 ^ (Nat.card Q).factorization 3 ∣ Nat.card M) : ¬ NonCentral 3 y := by
  intro hnc
  have hQ : 0 < Nat.card Q := Nat.card_pos
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hv : (Nat.card M).factorization 3 = (Nat.card Q).factorization 3 := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd hMpos.ne' hQ.ne').2 (Subgroup.card_subgroup_dvd_card M) 3
    · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hMpos.ne').1 hcard
  obtain ⟨P⟩ : Nonempty (Sylow 3 M) := inferInstance
  set S : Subgroup Q := (P : Subgroup M).map M.subtype with hS
  have hScard : Nat.card S = 3 ^ (Nat.card Q).factorization 3 := by
    rw [hS, Subgroup.card_map_of_injective M.subtype_injective, P.card_eq_multiplicity, hv]
  let SS : Sylow 3 Q := Sylow.ofCard S hScard
  have hSSS : (SS : Subgroup Q) = S := rfl
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hnc SS ⟨1, Subgroup.one_mem _, rfl⟩
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcomm : ∀ s ∈ S, s * y = y * s := by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := hs
    have hsM : (s' : Q) ∈ M := s'.2
    have hnorm : (s' : Q) ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup Q) : Set Q) :=
      mem_normalizer_zpowers_of_conj_mem (hM _ hsM)
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨s', hs'⟩
    have hk1 : s' ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hk' : (s' : Q) ^ 3 ^ k = 1 := by
      rw [← Subgroup.coe_pow, hk1]
      rfl
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (Subgroup.zpowers y)).totient := by
      rw [Nat.card_zpowers, hyord, Nat.totient_prime Nat.prime_three]
      exact Nat.Coprime.pow_left _ (by norm_num)
    have hcent := CFSG.LocalAnalysis.RankThreeTheoremC.mem_centralizer_of_pow_mem_of_coprime_totient
      (Subgroup.isCyclic_zpowers y) hnorm (by rw [hk']; exact Subgroup.one_mem _) hcop
    exact (Subgroup.mem_centralizer_iff.1 hcent y (Subgroup.mem_zpowers y)).symm
  have hyN : y ∈ Subgroup.normalizer ((SS : Subgroup Q) : Set Q) := by
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    have hx' : x ∈ S := hx
    have : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [← hcomm x hx']
        _ = x := by group
    rw [this]
    exact hx
  have hyP : IsPGroup 3 (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hyord, pow_one]
  have hySS : y ∈ (SS : Subgroup Q) := by
    have h1 : y ∈ Subgroup.zpowers y ⊓ Subgroup.normalizer ((SS : Subgroup Q) : Set Q) :=
      ⟨Subgroup.mem_zpowers y, hyN⟩
    exact ((hyP.inf_normalizer_sylow SS).le h1).2
  have hcen : (⟨y, hySS⟩ : ↥(SS : Subgroup Q)) ∈ Subgroup.center ↥(SS : Subgroup Q) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm (g : Q) g.2)
  exact hnc SS ⟨⟨y, hySS⟩, hcen, rfl⟩

open CFSG.Blueprint in
theorem not_inf_normalizer_le_zpowers_of_card {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    {a : G} (haA : a ∈ A) (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (e : L ⧸ Subgroup.center L ≃* NativeSporadic.J3)
    (hproj : ∃ l : L, (∃ w ∈ Subgroup.centralizer (L : Set G), a = (l : G) * w) ∧
      NonCentral 3 (l : ↥L ⧸ Subgroup.center ↥L))
    (hZ : ∀ z ∈ Subgroup.center L, (z : G) ∈ Subgroup.normalizer (A : Set G))
    (hcard : 3 ^ 5 * Nat.card (Subgroup.center L) ∣
      Nat.card (L ⊓ Subgroup.normalizer (A : Set G) : Subgroup G)) :
    ¬ L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  intro hN
  obtain ⟨l, ⟨w, hw, hlw⟩, hnc⟩ := hproj
  set Z : Subgroup L := Subgroup.center L with hZdef
  set π : L →* L ⧸ Z := QuotientGroup.mk' Z with hπ
  set N' : Subgroup L := (L ⊓ Subgroup.normalizer (A : Set G)).subgroupOf L with hN'
  set M : Subgroup (L ⧸ Z) := N'.map π with hMdef
  have hLw : ∀ x : L, (x : G) * w = w * x := fun x => Subgroup.mem_centralizer_iff.1 hw x x.2
  have hcl : Commute (l : G) w := hLw l
  have hy3 : (π l) ^ 3 = 1 := by
    have ha3 := hA3 a haA
    rw [hlw, hcl.mul_pow] at ha3
    have hcen : (l ^ 3 : L) ∈ Z := by
      rw [hZdef, Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      have h1 : (l : G) ^ 3 = (w ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left ha3
      show (x : G) * (l : G) ^ 3 = (l : G) ^ 3 * x
      rw [h1]
      have : Commute (x : G) w := hLw x
      exact ((this.pow_right 3).inv_right).eq
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hcen
  have hM : ∀ m ∈ M, m * π l * m⁻¹ ∈ Subgroup.zpowers (π l) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxN : (x : G) ∈ L ⊓ Subgroup.normalizer (A : Set G) := Subgroup.mem_subgroupOf.1 hx
    have hxa : (x : G) * a * (x : G)⁻¹ ∈ Subgroup.zpowers a :=
      ((Subgroup.mem_normalizer_iff.1 (hN hxN) a).1 (Subgroup.mem_zpowers a))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxa
    have hxw : (x : G) * w * (x : G)⁻¹ = w := by
      rw [hLw x, mul_inv_cancel_right]
    have hkey : (x : G) * l * (x : G)⁻¹ = (l : G) ^ k * w ^ (k - 1) := by
      have h1 : (x : G) * a * (x : G)⁻¹ = ((x : G) * l * (x : G)⁻¹) * w := by
        rw [hlw]
        calc (x : G) * ((l : G) * w) * (x : G)⁻¹
            = ((x : G) * l * (x : G)⁻¹) * ((x : G) * w * (x : G)⁻¹) := by group
          _ = ((x : G) * l * (x : G)⁻¹) * w := by rw [hxw]
      have h2 : a ^ k = (l : G) ^ k * w ^ k := by rw [hlw]; exact hcl.mul_zpow k
      have h3 : ((x : G) * l * (x : G)⁻¹) * w = (l : G) ^ k * w ^ k := by
        rw [← h1, ← hk, h2]
      calc (x : G) * l * (x : G)⁻¹ = (((x : G) * l * (x : G)⁻¹) * w) * w⁻¹ := by group
        _ = ((l : G) ^ k * w ^ k) * w⁻¹ := by rw [h3]
        _ = (l : G) ^ k * w ^ (k - 1) := by rw [zpow_sub_one]; group
    have hcomm2 : (l : G) ^ k * w ^ (k - 1) = w ^ (k - 1) * (l : G) ^ k :=
      ((hcl.zpow_left k).zpow_right (k - 1)).eq
    have hcen : (x * l * x⁻¹ * l ^ (-k) : L) ∈ Z := by
      rw [hZdef, Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 : ((x * l * x⁻¹ * l ^ (-k) : L) : G) = w ^ (k - 1) := by
        have : ((x * l * x⁻¹ * l ^ (-k) : L) : G) =
            (x : G) * l * (x : G)⁻¹ * (l : G) ^ (-k) := by simp
        rw [this, hkey, hcomm2, mul_assoc, zpow_neg, mul_inv_cancel, mul_one]
      show (y : G) * ((x * l * x⁻¹ * l ^ (-k) : L) : G) = ((x * l * x⁻¹ * l ^ (-k) : L) : G) * y
      rw [h1]
      exact (((hLw y).trans rfl : (y : G) * w = w * y) |> fun h => Commute.zpow_right h (k - 1)).eq
    have hq := (QuotientGroup.eq_one_iff _).2 hcen
    have hq' : π x * π l * (π x)⁻¹ = (π l) ^ k := by
      have : π (x * l * x⁻¹ * l ^ (-k)) = 1 := hq
      rw [map_mul, map_mul, map_mul, map_inv, map_zpow, zpow_neg, mul_inv_eq_one] at this
      exact this
    show π x * π l * (π x)⁻¹ ∈ Subgroup.zpowers (π l)
    rw [hq']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hZN' : Z ≤ N' := fun z hz => Subgroup.mem_subgroupOf.2 ⟨z.2, hZ z hz⟩
  have hNcard : Nat.card N' = Nat.card (L ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  set f : N' →* L ⧸ Z := π.comp N'.subtype with hf
  have hrange : f.range = M := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = Z.subgroupOf N' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hkercard : Nat.card f.ker = Nat.card Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN').toEquiv
  have hmul : Nat.card Z * Nat.card M = Nat.card N' := by
    have := Subgroup.card_ker_mul_card_range f
    rwa [hkercard, hrange] at this
  have hJcard : Nat.card (L ⧸ Z) = 50232960 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3]
  have hfac : (Nat.card (L ⧸ Z)).factorization 3 = 5 := by
    rw [hJcard, show (50232960 : ℕ) = 3 ^ 5 * 206720 by norm_num]
    exact CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)
  have hdvd : 3 ^ 5 ∣ Nat.card M := by
    have h1 : Nat.card Z * 3 ^ 5 ∣ Nat.card Z * Nat.card M := by
      rw [hmul, hNcard, mul_comm]
      exact hcard
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
  exact not_nonCentral_of_normalizes_sylow hy3 hM (by rw [hfac]; exact hdvd) hnc

open CFSG.RankThree.PartTwo.Sec21 in
theorem three_pow_dvd_card_inf_normalizer {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {n m : ℕ}
    (hAL : 3 ^ n ∣ Nat.card (A ⊓ L : Subgroup G)) (hst : 3 ^ m ∣ Nat.card (starOf A L)) :
    3 ^ (n + m) ∣ Nat.card (L ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) := by
  set N : Subgroup G := L ⊓ Subgroup.normalizer (A : Set G) with hNdef
  have hNle : N ≤ Subgroup.normalizer (A : Set G) := inf_le_right
  set g : N →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hNle) with hg
  have hrange : g.range = starOf A L := by
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), hNle x.2⟩, Subgroup.mem_subgroupOf.2 x.2.1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), (Subgroup.mem_subgroupOf.1 hx), x.2⟩, rfl⟩
  have hAN : A ⊓ L ≤ N := fun x hx => ⟨hx.2, Subgroup.le_normalizer hx.1⟩
  have hker : (A ⊓ L).subgroupOf N ≤ g.ker := by
    intro x hx
    have hxA : (x : G) ∈ A := (Subgroup.mem_subgroupOf.1 hx).1
    rw [MonoidHom.mem_ker]
    ext y
    show (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
    rw [hA _ hxA y y.2, mul_inv_cancel_right]
  have hkcard : 3 ^ n ∣ Nat.card g.ker := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hker)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv]
    exact hAL
  have h := Subgroup.card_ker_mul_card_range g
  rw [hrange] at h
  rw [pow_add, ← Nat.card_congr (Equiv.refl N), ← h]
  exact mul_dvd_mul hkcard hst

theorem card_eq_72_of_isExtOf {X : Type*} [Group X] [Finite X]
    (h : Sec4.IsExtOf X (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))) :
    Nat.card X = 72 := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have h1 : Nat.card (Multiplicative (ZMod 8)) = 8 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 8) ≃ ZMod 8), Nat.card_zmod]
  have h2 : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 9 := by
    rw [Nat.card_congr
      (Multiplicative.toAdd : Multiplicative (ZMod 3 × ZMod 3) ≃ ZMod 3 × ZMod 3),
      Nat.card_prod, Nat.card_zmod]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, Nat.card_congr eQ.toEquiv,
    Nat.card_congr eK.toEquiv, h1, h2]

theorem sec217OutNoFix_of
    (hF27 : ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∉ L →
        Nat.card A = 3 ^ 4 →
        Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
        27 ∣ Nat.card (A ⊓ L : Subgroup G))
    (hZ1 : ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∉ L →
        Nat.card A = 3 ^ 4 →
        Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
        Subgroup.center L = ⊥) : Sec217OutNoFix := by
  intro G _ _ A E U c L hp hq hc h81 hext a hfr
  have haA : a ∈ A := hp.mem_E.2 hfr.mem
  have hab := hp.mem_S.1.1
  have hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZ := hZ1 G A E U c L hp hq hc h81 hext
  obtain ⟨e⟩ := hq
  have h72 := card_eq_72_of_isExtOf hext
  have hcard : 3 ^ 5 * Nat.card (Subgroup.center L) ∣
      Nat.card (L ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) := by
    rw [hZ, Subgroup.card_bot, mul_one]
    exact three_pow_dvd_card_inf_normalizer (n := 3) (m := 2) hA
      (by simpa using hF27 G A E U c L hp ⟨e⟩ hc h81 hext)
      (by rw [h72]; norm_num)
  exact not_inf_normalizer_le_zpowers_of_card haA (fun x hx => hab.2 x hx) e hfr.proj
    (fun z hz => by
      rw [hZ, Subgroup.mem_bot] at hz
      rw [hz]
      exact Subgroup.one_mem _) hcard

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
