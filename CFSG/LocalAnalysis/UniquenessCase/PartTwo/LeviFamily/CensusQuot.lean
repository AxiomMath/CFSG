module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Blocks
import CFSG.GroupTheory.PCore.PCoreOfNormalEq
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
import CFSG.RankThree.PartOne.S11d.LayerDecomp
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918Perm
import CFSG.GroupTheory.OddOrderClosurePerfect
import CFSG.Quasithin.EmptyFaithful.T1515gD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem pCoreOf_top_eq_bot_of_pCore_eq_bot {R : Type} [Group R]
    (hR : CFSG.pCore 2 R = ⊥) : pCoreOf 2 (⊤ : Subgroup R) = ⊥ := by
  have htop : CFSG.pCore 2 ↥(⊤ : Subgroup R) = ⊥ := by
    have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
      (Subgroup.topEquiv : ↥(⊤ : Subgroup R) ≃* R)
    rw [hR] at h
    rwa [Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective] at h
  rw [pCoreOf, htop, Subgroup.map_bot]

private theorem pCoreOf_eq_bot_of_normal_of_pCoreOf_eq_bot {R : Type} [Group R]
    {M : Subgroup R} (hM : M.Normal) (hO : pCoreOf 2 (⊤ : Subgroup R) = ⊥) :
    pCoreOf 2 M = ⊥ := by
  have hN : (M.subgroupOf ⊤).Normal := by
    rw [← Subgroup.comap_subtype (H := M) (K := ⊤)]
    exact hM.comap (⊤ : Subgroup R).subtype
  have h := CFSG.GroupTheory.pCoreOf_eq_of_le_of_normal 2 (le_top : M ≤ ⊤) hN
    (hO ▸ bot_le)
  rw [h, hO]

private theorem pCore_eq_bot_of_le_normal_of_pCoreOf_eq_bot {R : Type} [Group R]
    {M N : Subgroup R} (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal)
    (hM : pCoreOf 2 M = ⊥) : CFSG.pCore 2 ↥N = ⊥ := by
  have hpc : pCoreOf 2 N = pCoreOf 2 M :=
    CFSG.GroupTheory.pCoreOf_eq_of_le_of_normal 2 hNM hN (hM ▸ bot_le)
  have h := CFSG.openPCoreOf_subgroupOf 2 N
  rw [hpc.trans hM] at h
  simpa using h.symm

private theorem nonempty_bar2_mulEquiv_self_of_pCore_eq_bot {R : Type} [Group R]
    {N : Subgroup R} (h : CFSG.pCore 2 ↥N = ⊥) : Nonempty (Bar2 N ≃* ↥N) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

private theorem natCard_ne_one_of_isLeviBlock {X : Type} [Group X] [Finite X]
    (hX : IsLeviBlock X) : Nat.card X ≠ 1 := by
  rcases hX with h3 | h6 | ⟨-, -, h2⟩
  · obtain ⟨e⟩ := h3
    have hc : Nat.card X = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
    omega
  · obtain ⟨e⟩ := h6
    have hc : Nat.card X = 720 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
    omega
  · have hpos : 0 < Nat.card X := Nat.card_pos
    omega

private theorem mem_of_pow_two_pow_mem_of_odd_order {X : Type} [Group X] {N : Subgroup X}
    {x : X} {k : ℕ} (hx : x ^ 2 ^ k ∈ N) (hodd : Odd (orderOf x)) : x ∈ N :=
  (Subgroup.zpowers_le.mpr hx)
    (mem_zpowers_pow_iff.mpr (hodd.coprime_two_left.pow_left k).gcd_eq_one)

private theorem oUpperTwo_le_of_normal_of_not_commutator_le_bot {R : Type} [Group R]
    [Finite R] {L N : Subgroup R} (hL : IsLeviBlock ↥L) (hNL : N ≤ L)
    (hN : (N.subgroupOf L).Normal) (hc : ¬ ⁅N, L⁆ ≤ ⊥) : S17.oUpperTwo L ≤ N := by
  have hNc : ¬ (N.subgroupOf L) ≤ center ↥L := by
    intro hcent
    apply hc
    have hcomm : ⁅(N.subgroupOf L), (⊤ : Subgroup ↥L)⁆ = ⊥ :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hcent
    have hmap := Subgroup.map_commutator (N.subgroupOf L) (⊤ : Subgroup ↥L) L.subtype
    rw [hcomm, Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hNL, Subgroup.map_top,
      Subgroup.range_subtype] at hmap
    rw [← hmap]
  rw [S17.oUpperTwo_eq_closure]
  refine (Subgroup.closure_le N).mpr ?_
  rintro x ⟨hxL, hxodd⟩
  obtain ⟨k, hk⟩ := IsLeviBlock.exists_pow_two_mem hL hN hNc (⟨x, hxL⟩ : ↥L)
  refine mem_of_pow_two_pow_mem_of_odd_order (k := k) ?_ hxodd
  simpa using Subgroup.mem_subgroupOf.mp hk

private theorem isLeviFamily_of_blocks {R : Type} [Group R] [Finite R]
    (hR : CFSG.pCore 2 R = ⊥) {d : ℕ} (M : Fin d → Subgroup R)
    (hMn : ∀ i, (M i).Normal) (hMc : ∀ i j, i ≠ j → ⁅M i, M j⁆ = ⊥)
    (hMb : ∀ i, IsLeviBlock ↥(M i)) (hodd : ¬ 2 ∣ (⨆ i, M i).index) :
    IsLeviFamily (⊤ : Subgroup R) d M := by
  classical
  have hO : pCoreOf 2 (⊤ : Subgroup R) = ⊥ := pCoreOf_top_eq_bot_of_pCore_eq_bot hR
  have hOppM : ∀ i, Opp 2 (M i) = M i := fun i => by
    have h := s13_pElementSubgroup_map Nat.prime_two (M i).subtype (⊤ : Subgroup ↥(M i))
    change (Opp 2 (⊤ : Subgroup ↥(M i))).map (M i).subtype =
      Opp 2 ((⊤ : Subgroup ↥(M i)).map (M i).subtype) at h
    rw [IsLeviBlock.opp_top (hMb i), Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  have hMne : ∀ i, M i ≠ ⊥ := fun i => by
    intro hbot
    exact natCard_ne_one_of_isLeviBlock (hMb i) (by rw [hbot, Subgroup.card_bot])
  have hN0normal : (⨆ i, M i).Normal := by
    simpa using Subgroup.biSup_normal (Set.univ : Set (Fin d)) M (fun i _ => hMn i)
  have hOpp_le : Opp 2 (⊤ : Subgroup R) ≤ ⨆ i, M i := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨-, k, hk⟩
    have hidx : Odd ((⨆ i, M i).subgroupOf ⊤).index := by
      have h' : ¬ Even (⨆ i, M i).index := by rwa [even_iff_two_dvd]
      rw [CFSG.QuasithinUnique.index_subgroupOf_top]
      exact Nat.not_even_iff_odd.mp h'
    have hN0sub : ((⨆ i, M i).subgroupOf ⊤).Normal := by
      rw [← Subgroup.comap_subtype (H := ⨆ i, M i) (K := ⊤)]
      exact hN0normal.comap (⊤ : Subgroup R).subtype
    exact CFSG.RankThree.PartOne.mem_of_two_power_of_odd_index (X := ⊤)
      hN0sub hidx (Subgroup.mem_top x) ⟨k, hk⟩
  have hsup_eq : (⨆ i, M i) =
      Opp 2 (⊤ : Subgroup R) ⊔ pCoreOf 2 (⊤ : Subgroup R) := by
    rw [hO, sup_bot_eq]
    refine le_antisymm ?_ hOpp_le
    refine iSup_le fun i => ?_
    calc M i = Opp 2 (M i) := (hOppM i).symm
      _ ≤ Opp 2 (⊤ : Subgroup R) := s13_Thirteen2_pElementSubgroup_mono le_top
  refine
    { pCoreOf_le := fun i => by rw [hO]; exact bot_le
      le := fun i => le_top
      normal := fun i => by
        rw [← Subgroup.comap_subtype (H := M i) (K := ⊤)]
        exact (hMn i).comap (⊤ : Subgroup R).subtype
      eq_opp_sup := fun i => by rw [hO, sup_bot_eq]; exact (hOppM i).symm
      ne := fun i => by rw [hO]; exact hMne i
      commutator_le := fun i j hij => by rw [hMc i j hij]; exact bot_le
      iSup_eq := hsup_eq
      tits := fun i N _ hNL hN hc =>
        oUpperTwo_le_of_normal_of_not_commutator_le_bot (hMb i) hNL hN
          (by simpa [hO] using hc) }

private theorem leviAlt_of_blocks {R : Type} [Group R] [Finite R]
    (hR : CFSG.pCore 2 R = ⊥) {d : ℕ} (M : Fin d → Subgroup R)
    (hMn : ∀ i, (M i).Normal) (hMb : ∀ i, IsLeviBlock ↥(M i))
    (halt : (d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple ↥(M i)) ∨
      ∀ i, CFSG.Open.IsQuasisimple ↥(M i) → ∀ n, 3 ≤ n →
        ¬ IsL2 (↥(M i) ⧸ center ↥(M i)) n) :
    LeviAlt (⊤ : Subgroup R) d M := by
  have hO : pCoreOf 2 (⊤ : Subgroup R) = ⊥ := pCoreOf_top_eq_bot_of_pCore_eq_bot hR
  have hOiAmb : ∀ i, pCoreOf 2 (M i) = ⊥ := fun i =>
    pCoreOf_eq_bot_of_normal_of_pCoreOf_eq_bot (hMn i) hO
  have hOi : ∀ i, CFSG.pCore 2 ↥(M i) = ⊥ := fun i => by
    have h := CFSG.openPCoreOf_subgroupOf 2 (M i)
    rw [hOiAmb i] at h
    simpa using h.symm
  rcases halt with ⟨hd, hq⟩ | halt'
  · left
    refine ⟨hd, fun i => ?_⟩
    obtain ⟨e⟩ := nonempty_bar2_mulEquiv_self_of_pCore_eq_bot (hOi i)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e (hq i)
  · right
    intro i N n _ hNL hN hn hL2
    have hpcN : CFSG.pCore 2 ↥N = ⊥ :=
      pCore_eq_bot_of_le_normal_of_pCoreOf_eq_bot hNL hN (hOiAmb i)
    obtain ⟨e1⟩ := nonempty_bar2_mulEquiv_self_of_pCore_eq_bot hpcN
    refine (IsLeviBlock.not_isL2_of_normal (X := ↥(M i)) (hMb i) (halt' i) hN hn) ?_
    exact CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNL).symm
      (CFSG.Blueprint.LieModel.of_mulEquiv e1 hL2)

theorem isLeviFamily_top_leviAlt_of_blocks {R : Type} [Group R] [Finite R]
    (hR : CFSG.pCore 2 R = ⊥) {d : ℕ} (M : Fin d → Subgroup R) (hMn : ∀ i, (M i).Normal)
    (hMc : ∀ i j, i ≠ j → ⁅M i, M j⁆ = ⊥) (hMb : ∀ i, IsLeviBlock ↥(M i))
    (hodd : ¬ 2 ∣ (⨆ i, M i).index)
    (halt : (d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple ↥(M i)) ∨
      ∀ i, CFSG.Open.IsQuasisimple ↥(M i) → ∀ n, 3 ≤ n → ¬ IsL2 (↥(M i) ⧸ center ↥(M i)) n) :
    IsLeviFamily ⊤ d M ∧ LeviAlt ⊤ d M :=
  ⟨isLeviFamily_of_blocks hR M hMn hMc hMb hodd,
    leviAlt_of_blocks hR M hMn hMb halt⟩

private theorem nonempty_oUpperTwo_equiv_alternatingGroup_of_mulEquiv_perm {R : Type}
    [Group R] [Finite R] (M : Subgroup R) {k : ℕ} (e : ↥M ≃* Equiv.Perm (Fin k)) :
    Nonempty (↥(S17.oUpperTwo M) ≃* alternatingGroup (Fin k)) := by
  let N : Subgroup R := S17.oUpperTwo M
  have hNM : N ≤ M := S17.oUpperTwo_le M
  have hmapN : (S17.oUpperTwo (⊤ : Subgroup ↥M)).map M.subtype = N := by
    have h := CFSG.AGLEmbedding.SUPair.map_oUpperTwo M.subtype (⊤ : Subgroup ↥M)
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hsub : N.subgroupOf M = S17.oUpperTwo (⊤ : Subgroup ↥M) := by
    apply Subgroup.map_injective (f := M.subtype) M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hNM, hmapN]
  have hmapE : (S17.oUpperTwo (⊤ : Subgroup ↥M)).map e.toMonoidHom =
      alternatingGroup (Fin k) := by
    have h := CFSG.AGLEmbedding.SUPair.map_oUpperTwo e.toMonoidHom (⊤ : Subgroup ↥M)
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective] at h
    rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.oUpperTwo_top_perm k]
    exact h
  let e1 : ↥(S17.oUpperTwo (⊤ : Subgroup ↥M)) ≃*
      ↥((S17.oUpperTwo (⊤ : Subgroup ↥M)).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  let e2 : ↥((S17.oUpperTwo (⊤ : Subgroup ↥M)).map e.toMonoidHom) ≃*
      ↥(alternatingGroup (Fin k)) := MulEquiv.subgroupCongr hmapE
  let e3 : ↥(N.subgroupOf M) ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNM
  exact ⟨e3.symm.trans ((MulEquiv.subgroupCongr hsub).trans (e1.trans e2))⟩

private theorem isQuasisimple_alternatingGroup_six :
    CFSG.Open.IsQuasisimple (alternatingGroup (Fin 6)) :=
  ⟨Group.isPerfect_def.mp (CFSG.Quasithin.a7_isQuasisimple_alt6).1,
    (CFSG.Quasithin.a7_isQuasisimple_alt6).2.1⟩

private theorem block_facts_oUpperTwo {two : Prop} {R : Type} [Group R] [Finite R]
    (M : Subgroup R) (hpc : pCoreOf 2 M = ⊥) (hMb : IsLeviBlock ↥M)
    (h3 : CFSG.Open.IsQuasisimple ↥M → 3 ∣ Nat.card (↥M ⧸ center ↥M))
    (h2 : Nonempty (↥M ≃* Equiv.Perm (Fin 3)) → two) :
    3 ∣ Nat.card (Bar2 (S17.oUpperTwo M)) ∧
      (CFSG.Open.IsQuasisimple (Bar2 (S17.oUpperTwo M)) ∨
        (Nonempty (Bar2 (S17.oUpperTwo M) ≃* Multiplicative (ZMod 3)) ∧ two)) := by
  let N : Subgroup R := S17.oUpperTwo M
  change 3 ∣ Nat.card (Bar2 N) ∧
    (CFSG.Open.IsQuasisimple (Bar2 N) ∨
      (Nonempty (Bar2 N ≃* Multiplicative (ZMod 3)) ∧ two))
  have hNM : N ≤ M := S17.oUpperTwo_le M
  have hN : N = CFSG.GroupTheory.oddOrderClosure M := by
    change S17.oUpperTwo M = CFSG.GroupTheory.oddOrderClosure M
    rw [S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
  have hNn : (N.subgroupOf M).Normal :=
    hN ▸ CFSG.GroupTheory.normal_oddOrderClosure_subgroupOf M
  have hpcN : CFSG.pCore 2 ↥N = ⊥ :=
    pCore_eq_bot_of_le_normal_of_pCoreOf_eq_bot hNM hNn hpc
  obtain ⟨eN⟩ := nonempty_bar2_mulEquiv_self_of_pCore_eq_bot hpcN
  have hcard : Nat.card (Bar2 N) = Nat.card ↥N := Nat.card_congr eN.toEquiv
  rcases hMb with h3e | h6e | ⟨hq, -, -⟩
  · obtain ⟨e⟩ := h3e
    obtain ⟨eN3⟩ := nonempty_oUpperTwo_equiv_alternatingGroup_of_mulEquiv_perm M e
    have hcardN : Nat.card ↥N = 3 := by
      rw [Nat.card_congr eN3.toEquiv, nat_card_alternatingGroup]
      norm_num
    refine ⟨?_, Or.inr ⟨?_, h2 ⟨e⟩⟩⟩
    · simp [hcard, hcardN]
    · exact ⟨eN.trans (mulEquivOfPrimeCardEq hcardN (by simp))⟩
  · obtain ⟨e⟩ := h6e
    obtain ⟨eN6⟩ := nonempty_oUpperTwo_equiv_alternatingGroup_of_mulEquiv_perm M e
    have hcardN : Nat.card ↥N = 360 := by
      rw [Nat.card_congr eN6.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hqN : CFSG.Open.IsQuasisimple ↥N :=
      CFSG.Open.IsQuasisimple.of_mulEquiv eN6 isQuasisimple_alternatingGroup_six
    exact ⟨by rw [hcard, hcardN]; norm_num,
      Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv eN hqN)⟩
  · have hN_eq : N = M := by
      change S17.oUpperTwo M = M
      rw [S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
      have hperf : Group.IsPerfect ↥M := Group.isPerfect_def.mpr hq.1
      exact CFSG.GroupTheory.oddOrderClosure_eq_self_of_commutator_eq
        Subgroup.commutator_eq_self
    have hqN : CFSG.Open.IsQuasisimple ↥N :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hN_eq) hq
    have h3N : 3 ∣ Nat.card ↥N := by
      rw [Nat.card_congr (MulEquiv.subgroupCongr hN_eq).toEquiv]
      exact dvd_trans (h3 hq) (Subgroup.card_quotient_dvd_card (center ↥M))
    exact ⟨by rw [hcard]; exact h3N,
      Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv eN hqN)⟩

theorem leviBlk_top_of_blocks {two big : Prop} {R : Type} [Group R] [Finite R]
    (hR : CFSG.pCore 2 R = ⊥) {d : ℕ} (M : Fin d → Subgroup R) (hMn : ∀ i, (M i).Normal)
    (hMb : ∀ i, IsLeviBlock ↥(M i))
    (h3 : ∀ i, CFSG.Open.IsQuasisimple ↥(M i) → 3 ∣ Nat.card (↥(M i) ⧸ center ↥(M i)))
    (h2 : ∀ i, Nonempty (↥(M i) ≃* Equiv.Perm (Fin 3)) → two) (hd : d ≤ 2 ∨ big) :
    LeviBlk two big d M := by
  have hO : pCoreOf 2 (⊤ : Subgroup R) = ⊥ := pCoreOf_top_eq_bot_of_pCore_eq_bot hR
  have hOiAmb : ∀ i, pCoreOf 2 (M i) = ⊥ := fun i =>
    pCoreOf_eq_bot_of_normal_of_pCoreOf_eq_bot (hMn i) hO
  exact ⟨fun i => block_facts_oUpperTwo (M i) (hOiAmb i) (hMb i) (h3 i) (h2 i), hd⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
