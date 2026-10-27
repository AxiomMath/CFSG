module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFixedAxes
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoCentralizerZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.GroupTheory.PRankBound
import CFSG.RankThree.PartOne.CTP.StrongPTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFixedCentralizers
import CFSG.LocalAnalysis.GLTheoremA.S3.Basic
import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Lift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCThetaComponents
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.FivePrime
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.Theta
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.Lift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.Actor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC (Setup Standing)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.Yardstones.Mf4cdcdf2e013 (Asc83CComponent)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace SCTransitive

theorem one_le_pRank_Lf (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive (c.toCtx812EOfSubset D.sig fun _ hp => hp)) (i : Fin 3) :
    1 ≤ CFSG.Open.pRank p (t.d.Lf i) := by
  have hp2 : p ≠ 2 := (D.sig_prime p hSC.1).2
  have : Fact p.Prime := ⟨(D.sig_prime p hSC.1).1⟩
  by_contra h
  have hi : CFSG.Open.pRank p (t.d.Lf i) = 0 := by omega
  have h0 : CFSG.Open.pRank p (t.d.Lf 0) = 0 := by
    rw [← t.pRank_Lf_eq p i]
    exact hi
  have hzero : ∀ j, CFSG.Open.pRank p (t.d.Lf j) = 0 := by
    intro j
    rw [t.pRank_Lf_eq p j]
    exact h0
  have hsum := t.d.pRank_L_le_add hp2 (fun j => by rw [hzero j]; norm_num)
  rw [t.hdL] at hsum
  change CFSG.Open.pRank p c.L ≤ CFSG.Open.pRank p (t.d.Lf 0) +
    CFSG.Open.pRank p (t.d.Lf 1) + CFSG.Open.pRank p (t.d.Lf 2) at hsum
  rw [c.pRank_L_eq_three_of_isSCPrime hSC] at hsum
  have h0' := hzero 0
  have h1' := hzero 1
  have h2' := hzero 2
  omega

theorem dvd_card_inf_centralizer (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive (c.toCtx812EOfSubset D.sig fun _ hp => hp)) {i j : Fin 3}
    (hij : i ≠ j) :
    p ∣ Nat.card ↥(D.M ⊓ centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G)) := by
  have hp : p.Prime := (D.sig_prime p hSC.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hSC.1).2
  have hthird : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hthird i j hij
  obtain ⟨y, hy, hyord⟩ := SCFixedAxes.exists_prime_order_centralizing_pair t.d hp hp2
    (fun l => one_le_pRank_Lf c hSC t l) (i := k) (j := i) (k := j) hki hkj
  have hDM : D.M = t.d.M := t.hdM.symm
  have hy' : y ∈ D.M ⊓ centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G) := by
    rw [hDM]
    exact hy
  have hdvd := Subgroup.orderOf_dvd_natCard
    (D.M ⊓ centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G)) hy'
  rwa [hyord] at hdvd

theorem pairNormalizerLe_of_exists (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive (c.toCtx812EOfSubset D.sig fun _ hp => hp))
    (he : CFSG.Open.pRank p (t.d.Lf 0) ≤ 1 →
      ∃ e ∈ D.M ⊓ centralizer (t.d.AA : Set G), orderOf e = p) :
    t.PairNormalizerLe p := by
  exact t.pairNormalizerLe_of_two_le hSC.1 (c.conclusion76 hSC.1) (fun hij =>
    t.two_le_pRank_inf_centralizer_A_sup_A_of_exists hSC.1
      (one_le_pRank_Lf c hSC t 0) he hij)

theorem exists_escape (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive (c.toCtx812EOfSubset D.sig fun _ hp => hp))
    (hN : ¬ t.PairNormalizerLe p) :
    (∀ i, CFSG.Open.pRank p (t.d.Lf i) = 1) ∧
      ¬ p ∣ Nat.card ↥(D.M ⊓ centralizer (t.d.AA : Set G)) ∧
      ∃ i j : Fin 3, i ≠ j ∧ ∃ b ∈ t.d.A i ⊔ t.d.A j, b ≠ 1 ∧
        ¬ centralizer ({b} : Set G) ≤ D.M := by
  have hp : p.Prime := (D.sig_prime p hSC.1).1
  have : Fact p.Prime := ⟨hp⟩
  have h1le : ∀ i, 1 ≤ CFSG.Open.pRank p (t.d.Lf i) :=
    fun i => one_le_pRank_Lf c hSC t i
  have hr : ∀ i, CFSG.Open.pRank p (t.d.Lf i) = 1 := by
    intro i
    by_contra hne
    have h2i : 2 ≤ CFSG.Open.pRank p (t.d.Lf i) := by
      have := h1le i
      omega
    have h20 : 2 ≤ CFSG.Open.pRank p (t.d.Lf 0) := by
      rw [← t.pRank_Lf_eq p i]
      exact h2i
    exact hN (pairNormalizerLe_of_exists c hSC t (fun hle => absurd h20 (by omega)))
  refine ⟨hr, ?_, ?_⟩
  · intro hdvd
    obtain ⟨e, heord⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(D.M ⊓ centralizer (t.d.AA : Set G))) p hdvd
    have heord' : orderOf (e : G) = p := by
      rw [← Subgroup.orderOf_mk (e : G) e.2]
      simpa using heord
    exact hN (pairNormalizerLe_of_exists c hSC t (fun _ => ⟨(e : G), e.2, heord'⟩))
  · have hnotnorm : ¬ ∀ {i j : Fin 3}, i ≠ j → ∀ {Y : Subgroup G},
        Y ≤ t.d.A i ⊔ t.d.A j → Y ≠ ⊥ → normalizer (Y : Set G) ≤ D.M := by
      intro hnorm
      exact hN ⟨fun {i j} hij {Y} hY hY1 => hnorm hij hY hY1,
        fun {i j} hij => dvd_card_inf_centralizer c hSC t hij⟩
    push Not at hnotnorm
    obtain ⟨i, j, hij, Y, hY, hY1, hYnorm⟩ := hnotnorm
    obtain ⟨⟨b, hbY⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY1
    have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    refine ⟨i, j, hij, ?_⟩
    refine ⟨b, hY hbY, hb1', ?_⟩
    intro hcb
    apply hYnorm
    intro g hg
    have hCY : centralizer (Y : Set G) ≤ D.M :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbY)).trans hcb
    have hdvdY : p ∣ Nat.card ↥(D.M ⊓ centralizer (Y : Set G)) :=
      (dvd_card_inf_centralizer c hSC t hij).trans (Subgroup.card_dvd_of_le
        (inf_le_inf le_rfl (Subgroup.centralizer_le (fun x hx => hY hx))))
    have hYg : Y.map (MulAut.conj g).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hpdvd : p ∣ Nat.card ↥(D.M ⊓ centralizer
        ((Y.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) := by
      rw [hYg]
      exact hdvdY
    exact (c.isStronglyPEmbedded_of_mem_sigma hSC.1).mem_of_centralizer_le hCY hpdvd

theorem normalizer_axis_le_of_pRank_eq_one
    (hSE : Section7.StronglyEmbeddedFive) (hSAlt : Section7.StronglyEmbeddedSolvableAltTen)
    (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = D.M)
    (hinj : Function.Injective d.Lf) (hcomp : ∀ i, Asc83CComponent D.M (d.Lf i))
    (hr : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1) (i : Fin 3) :
    normalizer (d.A i : Set G) ≤ D.M := by
  have hp := (D.sig_prime p hSC.1).1
  have hp2 := (D.sig_prime p hSC.1).2
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let cE := c.toCtx812EOfSubset D.sig (fun _ hp => hp)
  let k := cE.toSec7Core4 hSC.1
  have hcal : ∀ j, d.Lf j ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC d.M := by
    intro j
    rw [hdM]
    exact ⟨(hcomp j).2.1, (hcomp j).2.2.1, (hcomp j).2.2.2.2⟩
  have hdvd : ∀ j, p ∣ Nat.card (d.Lf j) := by
    intro j
    exact CFSG.GroupTheory.dvd_card_of_one_le_pRank hp (hr j).ge
  have hZ : ∀ j, ¬ p ∣ Nat.card (Subgroup.center
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 (d.Lf j))) := by
    intro j
    have : Group.IsPerfect (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 (d.Lf j)) :=
      ⟨(hcomp j).2.2.2.2.1⟩
    have hq := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (CFSG.pCore 2 ↥(d.Lf j))
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup
        (CFSG.pCore_isPGroup (p := 2) (G := ↥(d.Lf j))) hp hp2)
    have hqr : CFSG.Open.pRank p (⊤ : Subgroup
        (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 (d.Lf j))) = 1 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, hq,
        CFSG.SectionRank.pRank_coe_eq_openPRank, hr j]
    exact Theorem82.not_dvd_card_center_of_pRank_eq_one hp2 hqr
  have hN := d.normalizer_axis_le_of_three_calC hSE hSAlt hKSM k hdM.symm
    c.rank.le (c.five_le_of_mem_sigma hSC.1) hcal hinj hdvd hZ i
  rwa [hdM] at hN

theorem normalizer_AA_le_of_isSCPrime (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hr : ∀ i, 1 ≤ CFSG.Open.pRank p (d.Lf i))
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ D.M) :
    normalizer (d.AA : Set G) ≤ D.M := by
  have hh := SCFixedAxes.normalizer_AA_le_of_axes d (D.sig_prime p hSC.1).1
    (D.sig_prime p hSC.1).2
    (hdM.symm ▸ c.isStronglyPEmbedded_of_mem_sigma hSC.1) hr
    (fun i => hdM.symm ▸ hAxis i)
  rwa [hdM] at hh

theorem normalizer_P_le_of_normalizer_AA_le {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M) : normalizer (t.P : Set G) ≤ c.S.M := by
  have hSP : t.d.S ≤ t.P := by
    rw [t.hdS]
    exact inf_le_left
  have hAAleP : t.d.AA ≤ t.P := t.d.AA_le_S.trans hSP
  intro n hn
  have hPn : t.P.map (MulAut.conj n).toMonoidHom = t.P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hAn : t.d.AA.map (MulAut.conj n).toMonoidHom = t.d.AA := by
    refine t.eq_AA_of_isElemAbelian ?_ ?_ ?_
    · calc t.d.AA.map (MulAut.conj n).toMonoidHom
          ≤ t.P.map (MulAut.conj n).toMonoidHom := Subgroup.map_mono hAAleP
        _ = t.P := hPn
    · exact CFSG.Open.IsElemAbelian.map t.d.isElemAbelian_AA (MulAut.conj n).toMonoidHom
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, t.d.card_AA]
  exact hNA (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hAn)

theorem isSylowOf_top_of_normalizer_AA_le {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M) : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤ := by
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 t.P (c.S.M ⊓ ⊤) := by
    simpa using t.hP
  have hN : Subgroup.normalizer (t.P : Set G) ⊓ ⊤ ≤ c.S.M := by
    simpa using normalizer_P_le_of_normalizer_AA_le t hNA
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hT hN

private theorem perm_factors_of_mem_M {c : Ctx812E G} (t : CaseTwoTransitive c) :
    ∀ m ∈ t.d.M, ∀ i, ∃ j,
      (t.d.Lf i).map (MulAut.conj m).toMonoidHom = t.d.Lf j := by
  intro m hm i
  exact t.hperm m (t.hdM ▸ hm) i

private theorem A_le_AA (d : SylowThreeData G) (l : Fin 3) : d.A l ≤ d.AA := by
  rw [d.AA_def]
  fin_cases l
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem inf_iInf_normalizer_Lf_eq_S {c : Ctx812E G} (t : CaseTwoTransitive c) :
    t.P ⊓ ⨅ l, normalizer (t.d.Lf l : Set G) = t.d.S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperm' := perm_factors_of_mem_M t
  have hy : ∀ i, (t.d.Lf i).map (MulAut.conj t.y).toMonoidHom ≠ t.d.Lf i := by
    intro i h
    exact (by decide : ∀ i : Fin 3, i + 1 ≠ i) i
      (t.hinj ((t.hyL i).symm.trans h))
  have hrel := (t.d.kernel_sup_zpowers_eq t.hinj hperm' (t.hdM.symm ▸ t.hP.le)
    t.hP.isPGroup t.hyP hy).1
  have hcardP : Nat.card t.P =
      3 * Nat.card ↥(t.P ⊓ (⨅ l, normalizer (t.d.Lf l : Set G))) := by
    have hmul := Subgroup.relIndex_mul_card
      (t.P ⊓ (⨅ l, normalizer (t.d.Lf l : Set G))) t.P
    rw [inf_eq_left.mpr inf_le_left, hrel] at hmul
    exact hmul.symm
  have hcardS : Nat.card t.P = 3 * Nat.card t.d.S := by
    have h := CFSG.GroupTheory.WreathThree.card_sup_zpowers t.isWreathThree t.hy3
    rw [t.base_eq, t.hPy] at h
    exact h
  have hcard : Nat.card ↥(t.P ⊓ (⨅ l, normalizer (t.d.Lf l : Set G))) =
      Nat.card t.d.S :=
    Nat.eq_of_mul_eq_mul_left (by norm_num) (hcardP.symm.trans hcardS)
  have hSK : t.d.S ≤ t.P ⊓ ⨅ l, normalizer (t.d.Lf l : Set G) := by
    refine le_inf (t.hdS.le.trans inf_le_left) ?_
    apply le_iInf
    intro l
    refine t.d.hS.le.trans ?_
    rw [t.d.hL]
    exact sup_le (sup_le (t.d.hLnorm l 0) (t.d.hLnorm l 1)) (t.d.hLnorm l 2)
  exact (Subgroup.eq_of_le_of_card_ge hSK hcard.le).symm

theorem isSylowOf_S_inf_iInf_normalizer_Lf {c : Ctx812E G} (t : CaseTwoTransitive c) :
    CFSG.ABGLocalTools.IsSylowOf 3 t.d.S (c.S.M ⊓ ⨅ l, normalizer (t.d.Lf l : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperm' := perm_factors_of_mem_M t
  let N : Subgroup G := ⨅ l, Subgroup.normalizer (t.d.Lf l : Set G)
  have hNdef : N = ⨅ l, Subgroup.normalizer (t.d.Lf l : Set G) := rfl
  have hMK : c.S.M ≤ Subgroup.normalizer (c.S.M ⊓ N : Set G) := by
    intro m hm
    have hmM : m ∈ t.d.M := t.hdM.symm ▸ hm
    have hmapM : c.S.M.map (MulAut.conj m).toMonoidHom = c.S.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
    have hmapN : N.map (MulAut.conj m).toMonoidHom = N := by
      have hle : N.map (MulAut.conj m).toMonoidHom ≤ N := by
        rw [hNdef, Subgroup.map_iInf (MulAut.conj m).toMonoidHom (MulAut.conj m).injective]
        calc (⨅ l, (Subgroup.normalizer (t.d.Lf l : Set G)).map
              (MulAut.conj m).toMonoidHom)
            ≤ ⨅ l, Subgroup.normalizer
                ((t.d.Lf l).map (MulAut.conj m).toMonoidHom : Set G) :=
              iInf_mono fun l => Subgroup.le_normalizer_map _
          _ = ⨅ l, Subgroup.normalizer
                (t.d.Lf (t.d.permHom t.hinj hperm' ⟨m, hmM⟩ l) : Set G) := by
              simp only [t.d.map_conj_Lf_eq t.hinj hperm' ⟨m, hmM⟩]
          _ = N := by
              rw [hNdef]
              exact Equiv.iInf_comp (g := fun l =>
                Subgroup.normalizer (t.d.Lf l : Set G))
                (t.d.permHom t.hinj hperm' ⟨m, hmM⟩)
      exact Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj m).injective).symm)
    change m ∈ Subgroup.normalizer ((c.S.M ⊓ N : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (c.S.M ⊓ N).map (MulAut.conj m).toMonoidHom = c.S.M ⊓ N
    rw [Subgroup.map_inf _ _ _ (MulAut.conj m).injective, hmapM, hmapN]
  have hSyl := t.hP.inf_of_le_normalizer (inf_le_left : c.S.M ⊓ N ≤ c.S.M) hMK
  have hPK : t.P ⊓ (c.S.M ⊓ N) = t.d.S := by
    rw [← inf_assoc, inf_eq_left.mpr t.hP.le, hNdef, inf_iInf_normalizer_Lf_eq_S t]
  rw [hPK] at hSyl
  simpa only [hNdef] using hSyl

theorem mem_inf_iInf_normalizer_Lf_of_le_plane {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M) {i j : Fin 3} (hij : i ≠ j) {B : Subgroup G}
    (hB : B ≤ t.d.A i ⊔ t.d.A j) (hB3 : Nat.card B = 3) {r : G}
    (hr : r ∈ normalizer (t.d.S : Set G) ⊓ centralizer (B : Set G))
    (hr3 : IsPGroup 3 (zpowers r)) :
    r ∈ c.S.M ⊓ ⨅ l, normalizer (t.d.Lf l : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperm' := perm_factors_of_mem_M t
  have hrNA : r ∈ Subgroup.normalizer (t.d.AA : Set G) :=
    SCFixedCentralizers.normalizer_S_le_normalizer_AA t.d hr.1
  have hrM : r ∈ t.d.M := t.hdM.symm ▸ hNA hrNA
  let π : Equiv.Perm (Fin 3) := t.d.permHom t.hinj hperm' ⟨r, hrM⟩
  have hπ : ∀ l, (t.d.A l).map (MulAut.conj r).toMonoidHom = t.d.A (π l) :=
    fun l => SCFixedCentralizers.map_axis_eq_of_mem_normalizer_S t.d t.hinj hperm' hrM hr.1 l
  have hAinj : Function.Injective t.d.A := by
    intro a b hab
    apply (t.d.exists_four_full_support_lines).1
    show (t.d.A a).subgroupOf t.d.AA = (t.d.A b).subgroupOf t.d.AA
    rw [hab]
  have haxis : ∀ l, B = t.d.A l → π l = l := by
    intro l hBl
    have hone : (t.d.A l).map (MulAut.conj r).toMonoidHom = t.d.A l :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer (t.d.A l : Set G) (hBl ▸ hr.2))
    exact hAinj ((hπ l).symm.trans hone)
  have hfix : ∃ k : Fin 3, π k = k := by
    by_cases hBi : B = t.d.A i
    · exact ⟨i, haxis i hBi⟩
    · by_cases hBj : B = t.d.A j
      · exact ⟨j, haxis j hBj⟩
      · obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j :=
          (by decide : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j) i j hij
        refine ⟨k, ?_⟩
        exact SCFixedCentralizers.perm_fixes_complement_of_supportTwo t.d hij hki.symm hkj.symm
          hB hB3 hBi hBj hr.2 π hπ
  obtain ⟨k, hk⟩ := hfix
  have hπ3 : π ^ 3 = 1 := t.d.permHom_pow_three_eq_one t.hinj hperm' hrM hr3
  have hπ1 : π = 1 :=
    (by decide : ∀ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, σ k = k → σ ^ 3 = 1 → σ = 1)
      π k hk hπ3
  refine ⟨hNA hrNA, Subgroup.mem_iInf.mpr fun l => ?_⟩
  exact (t.d.mem_normalizer_Lf_iff t.hinj hperm' ⟨r, hrM⟩ l).mpr (by
    show π l = l
    rw [hπ1]
    rfl)

theorem isSylowOf_S_centralizer_of_le_plane {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M) {i j : Fin 3} (hij : i ≠ j) {B : Subgroup G}
    (hB : B ≤ t.d.A i ⊔ t.d.A j) (hB3 : Nat.card B = 3) :
    CFSG.ABGLocalTools.IsSylowOf 3 t.d.S (centralizer (B : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBS : B ≤ t.d.S := (hB.trans (sup_le (A_le_AA t.d i) (A_le_AA t.d j))).trans t.d.AA_le_S
  let K : Subgroup G :=
    Subgroup.normalizer (t.d.S : Set G) ⊓ Subgroup.centralizer (B : Set G)
  have hSleK : t.d.S ≤ K := by
    refine le_inf Subgroup.le_normalizer ?_
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact t.d.S_commute b s (hBS hb) hs
  have hSp : IsPGroup 3 (t.d.S.subgroupOf K) := t.d.hS.isPGroup.comap_subtype
  obtain ⟨Q, hSQ⟩ := hSp.exists_le_sylow
  let Q' : Subgroup G := (Q : Subgroup K).map K.subtype
  have hQ'syl : CFSG.ABGLocalTools.IsSylowOf 3 Q' K := ⟨Q, rfl⟩
  have hQ'3 : IsPGroup 3 Q' := hQ'syl.isPGroup
  have hSQ' : t.d.S ≤ Q' := by
    intro s hs
    have hsK : s ∈ K := hSleK hs
    have hmem : (⟨s, hsK⟩ : K) ∈ t.d.S.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr hs
    exact Subgroup.mem_map_of_mem K.subtype (hSQ hmem)
  have hQ'le : Q' ≤ c.S.M ⊓ ⨅ l, Subgroup.normalizer (t.d.Lf l : Set G) := by
    intro q hq
    have hqK : q ∈ Subgroup.normalizer (t.d.S : Set G) ⊓
        Subgroup.centralizer (B : Set G) := hQ'syl.le hq
    exact mem_inf_iInf_normalizer_Lf_of_le_plane t hNA hij hB hB3 hqK
      (hQ'3.to_le (Subgroup.zpowers_le.mpr hq))
  have hQ'eq : Q' = t.d.S :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le
      (isSylowOf_S_inf_iInf_normalizer_Lf t) hSQ' hQ'le hQ'3
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 3 t.d.S K := hQ'eq ▸ hQ'syl
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hSylK inf_le_left


theorem zpowers_ne_A_of_not_centralizer_le {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ c.S.M) {b : G}
    (hEscape : ¬ centralizer ({b} : Set G) ≤ c.S.M) (k : Fin 3) :
    zpowers b ≠ t.d.A k := by
  intro h
  apply hEscape
  have hc : Subgroup.centralizer (t.d.A k : Set G) ≤ c.S.M :=
    (Subgroup.centralizer_le_normalizer (t.d.A k : Set G)).trans (hAxis k)
  rwa [← h, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hc

theorem not_rankThreeGamma_le_of_escape {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M)
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ c.S.M)
    (hrank : CFSG.Open.pRank 3 t.d.S ≤ 3)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    {i j : Fin 3} (hij : i ≠ j) {b : G} (hb : b ∈ t.d.A i ⊔ t.d.A j) (hb1 : b ≠ 1)
    (hK : CFSG.Open.IsKGroup ↥(centralizer ({b} : Set G)))
    (hEscape : ¬ centralizer ({b} : Set G) ≤ c.S.M) :
    ¬ CFSG.Open.rankThreeGamma 2 3 t.d.AA ≤ t.d.M := by
  intro hΓ
  let B : Subgroup G := zpowers b
  have hbAA : b ∈ t.d.AA := (sup_le (A_le_AA t.d i) (A_le_AA t.d j)) hb
  have hB : B ≤ t.d.A i ⊔ t.d.A j := zpowers_le.mpr hb
  have hBA : B ≤ t.d.AA := zpowers_le.mpr hbAA
  have hB3 : Nat.card B = 3 := by
    change Nat.card (zpowers b) = 3
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 b hbAA) hb1
  have hBi : B ≠ t.d.A i := zpowers_ne_A_of_not_centralizer_le t hAxis hEscape i
  have hBj : B ≠ t.d.A j := zpowers_ne_A_of_not_centralizer_le t hAxis hEscape j
  have hNA' : normalizer (t.d.AA : Set G) ≤ t.d.M := t.hdM.symm ▸ hNA
  have hAxis' : ∀ k, centralizer (t.d.A k : Set G) ≤ t.d.M := fun k =>
    (Subgroup.centralizer_le_normalizer (t.d.A k : Set G)).trans (t.hdM.symm ▸ hAxis k)
  have hK' : CFSG.Open.IsKGroup ↥(centralizer (B : Set G)) := by
    change CFSG.Open.IsKGroup ↥(centralizer (zpowers b : Set G))
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hK
  have hSyl := isSylowOf_S_centralizer_of_le_plane t hNA hij hB hB3
  have hfac := SCFixedCentralizers.supportTwo_centralizer_factorization_of_sylow t.d t.hinj
    (perm_factors_of_mem_M t) hrank hNA' hAxis' hK332 hij hB hB3 hBi hBj hK' hSyl
  have hle := SCFixedCentralizers.centralizer_le_of_factorization_of_gamma_two_le
    t.d hBA hfac hΓ
  change centralizer (zpowers b : Set G) ≤ t.d.M at hle
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, t.hdM] at hle
  exact hEscape hle

theorem isSylowOf_S_centralizer_singleton_of_mem_plane {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M) {k l : Fin 3} (hkl : k ≠ l) {x : G}
    (hx : x ∈ t.d.A k ⊔ t.d.A l) (hx1 : x ≠ 1) :
    CFSG.ABGLocalTools.IsSylowOf 3 t.d.S (centralizer ({x} : Set G)) := by
  have hxAA : x ∈ t.d.AA := (sup_le (A_le_AA t.d k) (A_le_AA t.d l)) hx
  have hB3 : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 x hxAA) hx1
  have h := isSylowOf_S_centralizer_of_le_plane t hNA hkl (B := zpowers x)
    (zpowers_le.mpr hx) hB3
  simpa only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using h

theorem centralizer_factorization_of_mem_plane {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M)
    (hAxis : ∀ k, normalizer (t.d.A k : Set G) ≤ c.S.M)
    (hrank : CFSG.Open.pRank 3 t.d.S ≤ 3)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    {k l : Fin 3} (hkl : k ≠ l) {x : G} (hx : x ∈ t.d.A k ⊔ t.d.A l) (hx1 : x ≠ 1)
    (hK : CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G))) :
    centralizer ({x} : Set G) = (centralizer ({x} : Set G) ⊓ t.d.M) ⊔
      (CFSG.pPrimeCore 3 ↥(centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype := by
  classical
  by_cases hax : ∃ m : Fin 3, zpowers x = t.d.A m
  · obtain ⟨m, hm⟩ := hax
    have hcx : centralizer (t.d.A m : Set G) = centralizer ({x} : Set G) := by
      rw [← hm, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hle : centralizer ({x} : Set G) ≤ t.d.M := by
      rw [← hcx]
      exact (Subgroup.centralizer_le_normalizer (t.d.A m : Set G)).trans (t.hdM.symm ▸ hAxis m)
    rw [inf_eq_left.mpr hle]
    exact (sup_eq_left.mpr (Subgroup.map_subtype_le _)).symm
  · have hxAA : x ∈ t.d.AA := (sup_le (A_le_AA t.d k) (A_le_AA t.d l)) hx
    have hB3 : Nat.card (zpowers x) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 x hxAA) hx1
    have hK' : CFSG.Open.IsKGroup ↥(centralizer (zpowers x : Set G)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hK
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 t.d.S (centralizer (zpowers x : Set G)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact isSylowOf_S_centralizer_singleton_of_mem_plane t hNA hkl hx hx1
    have hfac := SCFixedCentralizers.supportTwo_centralizer_factorization_of_sylow t.d t.hinj
      (perm_factors_of_mem_M t) hrank (t.hdM.symm ▸ hNA)
      (fun m => (Subgroup.centralizer_le_normalizer (t.d.A m : Set G)).trans
        (t.hdM.symm ▸ hAxis m)) hK332 hkl (zpowers_le.mpr hx) hB3
      (fun hh => hax ⟨k, hh⟩) (fun hh => hax ⟨l, hh⟩) hK' hSyl
    dsimp only at hfac
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hfac
    exact hfac

theorem actualData_facts {D : Data G} {c : Ctx82E3 D}
    (t : CaseTwoTransitive (c.toCtx812EOfSubset D.sig fun _ hp => hp)) :
    (∀ i, t.d.Lf i ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC t.d.M) ∧
      CFSG.Open.IsKGroup t.d.M ∧ CFSG.Open.pRank 3 t.d.M ≤ 3 := by
  refine ⟨fun i => ?_, ?_, ?_⟩ <;> rw [t.hdM]
  · exact ⟨(t.hcomp i).2.1, (t.hcomp i).2.2.1, (t.hcomp i).2.2.2.2⟩
  · exact c.kProper.isKGroup _ (Ctx82E3.M_ne_top c)
  · exact c.pRank_three_M.le

theorem centralizer_factorization_of_plane {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M)
    (hAxis : ∀ k, normalizer (t.d.A k : Set G) ≤ c.S.M)
    (hrank : CFSG.Open.pRank 3 t.d.S ≤ 3)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) :
    ∀ i j : Fin 3, i ≠ j → ∀ b ∈ t.d.A i ⊔ t.d.A j, b ≠ 1 →
      let C := centralizer ({b} : Set G)
      C = (C ⊓ t.d.M) ⊔ (CFSG.pPrimeCore 3 C).map C.subtype := by
  intro i j hij b hb hb1
  have hbAA : b ∈ t.d.AA := (sup_le (A_le_AA t.d i) (A_le_AA t.d j)) hb
  have hb3 : Nat.card (zpowers b) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 b hbAA) hb1
  have hK : CFSG.Open.IsKGroup ↥(centralizer ({b} : Set G)) := by
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen c.standing.simple
      c.standing.nonab c.standing.kProper (E := zpowers b) (by
        intro h0; rw [h0, Subgroup.card_bot] at hb3; norm_num at hb3)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  exact centralizer_factorization_of_mem_plane t hNA hAxis hrank hK332 hij hb hb1 hK

theorem le_normalizer_of_mem_thetaComponentsAt {x : G} {B : Subgroup G}
    (hBC : B ≤ centralizer ({x} : Set G))
    (hnorm : ∀ J : Subgroup (centralizer ({x} : Set G) ⧸
        CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 (centralizer ({x} : Set G))),
      CFSG.IsComponent J → ¬ 3 ∣ Nat.card J →
      (B.subgroupOf (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
            (centralizer ({x} : Set G)))) ≤
        normalizer (J : Set (centralizer ({x} : Set G) ⧸
          CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 (centralizer ({x} : Set G)))))
    {L : Subgroup G} (hL : L ∈ CFSG.RankThree.thetaComponentsAt 3 x)
    (hL3 : ¬ 3 ∣ Nat.card L) : B ≤ normalizer (L : Set G) := by
  let C := centralizer ({x} : Set G)
  let ρ := QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C)
  have hLC : L ≤ C := by
    obtain ⟨L0, hL0, he⟩ := hL
    rw [← he]
    exact Subgroup.map_subtype_le _
  have hLsub : L.subgroupOf C ∈ CFSG.RankThree.thetaComponents 3 C := by
    obtain ⟨L0, hL0, he⟩ := hL
    rw [← he, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact hL0
  have hJ : CFSG.IsComponent ((L.subgroupOf C).map ρ) :=
    CFSG.RankThree.isComponent_map_of_mem_thetaComponents Nat.prime_three hLsub
  have hJ3 : ¬ 3 ∣ Nat.card ((L.subgroupOf C).map ρ) := by
    have hcard : Nat.card ((L.subgroupOf C).map ρ) ∣ Nat.card (L.subgroupOf C) := by
      simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using
        Subgroup.card_range_dvd (ρ.comp (L.subgroupOf C).subtype)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv] at hcard
    exact fun h => hL3 (h.trans hcard)
  have hsN := ((CFSG.RankThree.theta_component_quotient_structure Nat.prime_three
    hLsub).2.2.2.2.2.2.2.2.2.2 (B.subgroupOf C)).mpr (hnorm _ hJ hJ3)
  have hg := CFSG.LocalAnalysis.GLTheoremA.I113.le_normalizer_map_subtype hBC hsN
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLC] at hg

private theorem L_le_M (d : SylowThreeData G) : d.L ≤ d.M := by
  rw [d.hL]
  exact sup_le (sup_le (d.hLM 0) (d.hLM 1)) (d.hLM 2)

private theorem not_nine_dvd_relIndex_L_M {c : Ctx812E G} (t : CaseTwoTransitive c) :
    ¬ 9 ∣ t.d.L.relIndex t.d.M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardP : Nat.card t.P = 3 * Nat.card t.d.S := by
    have h := CFSG.GroupTheory.WreathThree.card_sup_zpowers t.isWreathThree t.hy3
    rwa [t.base_eq, t.hPy] at h
  have hPM : t.P ≤ t.d.M := t.hdM.symm ▸ t.hP.le
  have hab : t.d.L.relIndex t.d.M * t.d.S.relIndex t.d.L = t.P.relIndex t.d.M * 3 := by
    have hML := Subgroup.relIndex_mul_card t.d.L t.d.M
    rw [inf_of_le_left (L_le_M t.d)] at hML
    have hLS := Subgroup.relIndex_mul_card t.d.S t.d.L
    rw [inf_of_le_left t.d.hS.le] at hLS
    have hMP := Subgroup.relIndex_mul_card t.P t.d.M
    rw [inf_of_le_left hPM] at hMP
    have hmul : t.d.L.relIndex t.d.M * (t.d.S.relIndex t.d.L * Nat.card t.d.S) =
        t.P.relIndex t.d.M * (3 * Nat.card t.d.S) := by
      rw [hLS, hML, ← hMP, hcardP]
    rw [← mul_assoc, ← mul_assoc] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hc3 : ¬ 3 ∣ t.P.relIndex t.d.M := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp t.hP).2.2
    rwa [← t.hdM] at h
  intro h9
  have h93 : 9 ∣ t.P.relIndex t.d.M * 3 := by
    rw [← hab]
    exact dvd_mul_of_dvd_left h9 _
  exact hc3 (Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) (by simpa using h93))

theorem pRank_le_one_of_isSec_M {c : Ctx812E G} (t : CaseTwoTransitive c)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (h3 : 3 ∣ Nat.card T)
    (hSec : CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec T t.d.M) : CFSG.pRank 3 T ≤ 1 := by
  have hNormal : (t.d.L.subgroupOf t.d.M).Normal :=
    SCThetaComponents.normal_L_of_permutes_factors t.d (perm_factors_of_mem_M t)
  have hSec' : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.IsSection T ↥t.d.M := hSec
  rcases @CFSG.GH74.GLS.Stage2.Signalizer.Odd87.IsSection.dichotomy T ↥t.d.M _ _ _
    (t.d.L.subgroupOf t.d.M) hNormal hSec' with hL | hQ
  · exact SCThetaComponents.pRank_le_one_of_isSec_sylowThreeData t.d h3
      (CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (L_le_M t.d)) hL)
  · have h9T : ¬ 9 ∣ Nat.card T := fun h => not_nine_dvd_relIndex_L_M t (h.trans hQ.card_dvd)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (G := T) (H := ⊤) (k := 1)
      Nat.prime_three ?_
    simpa [Subgroup.card_top] using h9T

end SCTransitive

theorem sc_transitive_full_support_theta_component_three_prime
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (t : CaseTwoTransitive
      (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig fun _ hp => hp))
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (t.d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNP : normalizer (t.P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S) :
    ∀ x ∈ t.d.AA, x ≠ 1 → (∀ k l : Fin 3, k ≠ l → x ∉ t.d.A k ⊔ t.d.A l) →
      ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x, ¬ 3 ∣ Nat.card L := by
  have hPM : t.P ≤ (PartTwo.Three.dataOfSetup hS S).M := Subgroup.le_normalizer.trans hNP
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 :=
    (CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hPG.le hPG hPM).trans c.pRank_three_M.le
  intro x hx hx1 hfull L hL
  exact SCFull.full_support_theta_component_three_prime hK326 t hPG hNA hAxis
    (fun T _ _ _ h3 hSec => SCTransitive.pRank_le_one_of_isSec_M t h3 hSec) hr hx hx1 hfull hL

theorem sc_transitive_autThetaQuot_card_ne_nine
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (t : CaseTwoTransitive
      (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig fun _ hp => hp))
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (t.d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNP : normalizer (t.P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hInner : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S) :
    ∀ x ∈ t.d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      Nat.card (CFSG.RankThree.PartTwo.Sec4.autThetaQuot t.d.AA L) ≠ 9 := by
  intro x hx hx1 L hL
  have hK : CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G)) := by
    have hc : Nat.card (zpowers x) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 x hx) hx1
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers x) (by intro h0; rw [h0, Subgroup.card_bot] at hc; norm_num at hc)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  by_cases hdiv : 3 ∣ Nat.card L
  · obtain ⟨k, l, hkl, hxkl⟩ : ∃ k l : Fin 3, k ≠ l ∧ x ∈ t.d.A k ⊔ t.d.A l := by
      by_contra hpl
      exact sc_transitive_full_support_theta_component_three_prime hS S c t hAxis hNA hNP hPG
        hK326 x hx hx1 (fun k l hkl hxkl => hpl ⟨k, l, hkl, hxkl⟩) L hL hdiv
    have hSM : t.d.S ≤ (PartTwo.Three.dataOfSetup hS S).M := by
      rw [t.hdS]
      exact inf_le_left.trans t.hP.le
    have hrank : CFSG.Open.pRank 3 t.d.S ≤ 3 :=
      (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hSM).trans c.pRank_three_M.le
    have hle :=
      SCThetaComponents.autThetaQuot_card_le_three_of_mem_thetaComponentsAt_of_simple_sections
        hInner t.d
        (SCTransitive.isSylowOf_S_centralizer_singleton_of_mem_plane t hNA hkl hxkl hx1)
        (fun T _ _ _ h3 hSec => SCTransitive.pRank_le_one_of_isSec_M t h3 hSec)
        hx hL hK hdiv
        (SCTransitive.centralizer_factorization_of_mem_plane t hNA hAxis hrank hK332
          hkl hxkl hx1 hK)
    omega
  · exact SCThetaComponents.autThetaQuot_card_ne_nine_of_mem_thetaComponentsAt_of_not_dvd hSz
      t.d hL hK hdiv

section ActualData

theorem sc_transitive_three_prime_theta_normalizes
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive
      (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig fun _ hp => hp))
    (hRank : ∀ i, CFSG.Open.pRank p (t.d.Lf i) = 1)
    (hδ : ¬ p ∣ Nat.card ↥((PartTwo.Three.dataOfSetup hS S).M ⊓ centralizer (t.d.AA : Set G)))
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (t.d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) :
    ∀ x ∈ t.d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      ¬ 3 ∣ Nat.card L → t.d.AA ≤ normalizer (L : Set G) := by
  intro x hx hx1 L hL hL3
  have hAC : t.d.AA ≤ centralizer ({x} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (t.d.S_commute a x (t.d.AA_le_S ha) (t.d.AA_le_S hx))
  refine SCTransitive.le_normalizer_of_mem_thetaComponentsAt hAC (fun J hJ hJ3 => ?_) hL hL3
  obtain ⟨hcal, hKM, hM3⟩ := SCTransitive.actualData_facts t
  have hAxisC : ∀ k, centralizer (t.d.A k : Set G) ≤ t.d.M := fun k =>
    (Subgroup.centralizer_le_normalizer (t.d.A k : Set G)).trans (t.hdM.symm ▸ hAxis k)
  have hKC : CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G)) := by
    have hc : Nat.card (zpowers x) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 x hx) hx1
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers x) (by intro h0; rw [h0, Subgroup.card_bot] at hc; norm_num at hc)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  rcases (c.five_le_of_mem_sigma hSC.1).eq_or_lt with h5 | h5
  · have hδ5 : ¬ 5 ∣ Nat.card ↥(t.d.M ⊓ centralizer (t.d.AA : Set G)) := by
      rw [h5, t.hdM]
      exact hδ
    exact SCThetaComponents.le_normalizer_component_of_five_prime_actual_data
      CFSG.RankThree.PartTwo.KFacts.kpSz t.d hcal t.hinj hM3 hKM hAxisC hx hKC hJ hJ3 hδ5
  · have hSM : t.d.S ≤ (PartTwo.Three.dataOfSetup hS S).M := by
      rw [t.hdS]
      exact inf_le_left.trans t.hP.le
    have hrank : CFSG.Open.pRank 3 t.d.S ≤ 3 :=
      (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hSM).trans c.pRank_three_M.le
    exact SCThetaComponents.le_normalizer_component_of_three_prime_of_actual_data c t.d
      hcal t.hinj hM3 hKM t.hdL ((PartTwo.Three.dataOfSetup hS S).sig_prime p hSC.1).1 h5 hRank
      hAxisC (SCTransitive.centralizer_factorization_of_plane t hNA hAxis hrank hK332) hx hJ hJ3

private theorem SCTransitive.pPrimeCore_map_le_of_five {D : Data G} {c : Ctx82E3 D}
    (t : CaseTwoTransitive (c.toCtx812EOfSubset D.sig fun _ hp => hp))
    (hδ : ¬ 5 ∣ Nat.card ↥(t.d.M ⊓ centralizer (t.d.AA : Set G)))
    {b : G} (hbAA : b ∈ t.d.AA) (hCM : centralizer (t.d.AA : Set G) ≤ t.d.M)
    (hθM : CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3)
      (centralizer ({b} : Set G)) ≤ D.M)
    (hAxis : ∀ k, centralizer (t.d.A k : Set G) ≤ t.d.M)
    (hK : CFSG.Open.IsKGroup ↥(centralizer ({b} : Set G))) :
    (CFSG.pPrimeCore 3 ↥(centralizer ({b} : Set G))).map
      (centralizer ({b} : Set G)).subtype ≤ D.M := by
  have hBC : t.d.AA ≤ centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (t.d.isElemAbelian_AA.comm hx hbAA)
  obtain ⟨hcal, hKM, hM3⟩ := SCTransitive.actualData_facts t
  exact SCZeroAlpha.pPrimeCore_map_le_of_three_dvd_components hθM
    (SCZeroAlpha.three_dvd_card_component_of_five CFSG.RankThree.PartTwo.KFacts.kpSz hBC
      t.d.isElemAbelian_AA hCM hK
      (fun J hJ hJ3 => SCThetaComponents.le_normalizer_component_of_five_prime_actual_data
        CFSG.RankThree.PartTwo.KFacts.kpSz t.d hcal t.hinj hM3 hKM hAxis hbAA hK hJ hJ3 hδ) hδ)

theorem sc_transitive_zero_alpha_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive
      (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig fun _ hp => hp))
    (hRank : ∀ i, CFSG.Open.pRank p (t.d.Lf i) = 1)
    (hδ : ¬ p ∣ Nat.card ↥((PartTwo.Three.dataOfSetup hS S).M ⊓ centralizer (t.d.AA : Set G)))
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (t.d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    {i j : Fin 3} (hij : i ≠ j) (b : G) (hb : b ∈ t.d.A i ⊔ t.d.A j) (hb1 : b ≠ 1)
    (hEscape : ¬ centralizer ({b} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hAlpha : ∀ E : Subgroup G, E ≤ t.d.AA → Nat.card E = 9 →
      CFSG.RankThree.LocalRank.thetaAlpha 3 E = ⊥) : False := by
  have hSM : t.d.S ≤ (PartTwo.Three.dataOfSetup hS S).M := by
    rw [t.hdS]
    exact inf_le_left.trans t.hP.le
  have hrank : CFSG.Open.pRank 3 t.d.S ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hSM).trans c.pRank_three_M.le
  have hbAA : b ∈ t.d.AA :=
    sup_le (SCTransitive.A_le_AA t.d i) (SCTransitive.A_le_AA t.d j) hb
  have hc : Nat.card (zpowers b) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 b hbAA) hb1
  have hK : CFSG.Open.IsKGroup ↥(centralizer ({b} : Set G)) := by
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers b) (by intro hb0; rw [hb0, Subgroup.card_bot] at hc; norm_num at hc)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  have hθM : CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3)
      (centralizer ({b} : Set G)) ≤ (PartTwo.Three.dataOfSetup hS S).M :=
    (SCZeroAlpha.inSubgroup_le_centralizer_AA_of_thetaAlpha_eq_bot t.d hij hb hb1 hAlpha).trans
      ((Subgroup.centralizer_le_normalizer (t.d.AA : Set G)).trans hNA)
  have hO : (CFSG.pPrimeCore 3 ↥(centralizer ({b} : Set G))).map
      (centralizer ({b} : Set G)).subtype ≤ (PartTwo.Three.dataOfSetup hS S).M := by
    rcases (c.five_le_of_mem_sigma hSC.1).eq_or_lt with h5 | h5
    · have hδ5 : ¬ 5 ∣ Nat.card ↥(t.d.M ⊓ centralizer (t.d.AA : Set G)) := by
        rw [t.hdM]
        exact h5.symm ▸ hδ
      exact SCTransitive.pPrimeCore_map_le_of_five t hδ5 hbAA
        ((Subgroup.centralizer_le_normalizer (t.d.AA : Set G)).trans (t.hdM.symm ▸ hNA)) hθM
        (fun k => (Subgroup.centralizer_le_normalizer (t.d.A k : Set G)).trans
          (t.hdM.symm ▸ hAxis k)) hK
    · have hp : p.Prime := ((PartTwo.Three.dataOfSetup hS S).sig_prime p hSC.1).1
      obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j :=
        (by decide : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j) i j hij
      obtain ⟨Q, hQC, hQM, hpQ, hcomm⟩ :=
        SCZeroAlpha.exists_perfect_commutator_pPrimeCore_eq_bot c t.d
          (SCTransitive.actualData_facts t).1 t.hdL hki hkj hp h5
          (hRank k) hb hK
      exact SCZeroAlpha.pPrimeCore_map_le_of_commutator_eq_bot
        (c.isStronglyPEmbedded_of_mem_sigma hSC.1) hθM hQC (hQM.trans t.hdM.le) hpQ hcomm
  refine hEscape ?_
  rw [SCTransitive.centralizer_factorization_of_mem_plane t hNA hAxis hrank hK332 hij hb hb1 hK]
  exact sup_le (inf_le_right.trans (le_of_eq t.hdM)) hO

theorem sc_transitive_theta_normalizes
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive
      (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig fun _ hp => hp))
    (hRank : ∀ i, CFSG.Open.pRank p (t.d.Lf i) = 1)
    (hδ : ¬ p ∣ Nat.card ↥((PartTwo.Three.dataOfSetup hS S).M ⊓ centralizer (t.d.AA : Set G)))
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (t.d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNP : normalizer (t.P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) :
    ∀ x ∈ t.d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      t.d.AA ≤ normalizer (L : Set G) := by
  intro x hx hx1 L hL
  by_cases hdiv : 3 ∣ Nat.card L
  · by_cases hpl : ∃ k l : Fin 3, k ≠ l ∧ x ∈ t.d.A k ⊔ t.d.A l
    · obtain ⟨k, l, hkl, hxkl⟩ := hpl
      exact SCThetaComponents.le_normalizer_theta_component_of_actual_sylow_of_dvd t.d
        (SCTransitive.isSylowOf_S_centralizer_singleton_of_mem_plane t hNA hkl hxkl hx1)
        hx hL hdiv
    · have hfull : ∀ k l : Fin 3, k ≠ l → x ∉ t.d.A k ⊔ t.d.A l := by
        intro k l hkl hxkl
        exact hpl ⟨k, l, hkl, hxkl⟩
      exact absurd hdiv
        (sc_transitive_full_support_theta_component_three_prime hS S c t hAxis hNA hNP hPG hK326
          x hx hx1 hfull L hL)
  · exact sc_transitive_three_prime_theta_normalizes hS S c hSC t hRank hδ hAxis hNA hK332 x hx
      hx1 L hL hdiv

theorem sc_transitive_full_gamma_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive
      (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig fun _ hp => hp))
    (hRank : ∀ i, CFSG.Open.pRank p (t.d.Lf i) = 1)
    (hδ : ¬ p ∣ Nat.card ↥((PartTwo.Three.dataOfSetup hS S).M ⊓ centralizer (t.d.AA : Set G)))
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (t.d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNP : normalizer (t.P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    {i j : Fin 3} (hij : i ≠ j) (b : G) (hb : b ∈ t.d.A i ⊔ t.d.A j) (hb1 : b ≠ 1)
    (hEscape : ¬ centralizer ({b} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFull : CFSG.Open.rankThreeGamma 2 3 t.d.AA = ⊤)
    (hK341 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K341)
    (hInner : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S) : False := by
  have hPM : t.P ≤ (PartTwo.Three.dataOfSetup hS S).M := Subgroup.le_normalizer.trans hNP
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 :=
    (CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hPG.le hPG hPM).trans c.pRank_three_M.le
  have hmax := SCFixedCentralizers.maximal_AA_of_pRank_top_le_three t.d hr
  have hK : ∀ x ∈ t.d.AA, x ≠ 1 → CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G)) := by
    intro x hx hx1
    have hc : Nat.card (zpowers x) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 x hx) hx1
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers x) (by intro h0; rw [h0, Subgroup.card_bot] at hc; norm_num at hc)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  have hlocal : ∀ x ∈ t.d.AA, x ≠ 1 →
      CFSG.Open.twoLocalPrimeRank 3 ↥(centralizer ({x} : Set G)) ≤ 3 :=
    fun x _ _ => SCFixedCentralizers.twoLocalPrimeRank_centralizer_le_three c x
  have hnorm := sc_transitive_theta_normalizes hS S c hSC t hRank hδ hAxis hNA hNP hPG hK326 hK332
  have hne := sc_transitive_autThetaQuot_card_ne_nine hS S c t hAxis hNA hNP hPG
    CFSG.RankThree.PartTwo.KFacts.kpSz hInner hK332 hK326
  obtain ⟨hSolv, hInd⟩ := hK341 G t.d.AA t.d.isElemAbelian_AA t.d.card_AA hmax hK hlocal hnorm
    (fun x hx hx1 L hL h9 => absurd h9 (hne x hx hx1 L hL))
  exact sc_transitive_zero_alpha_false hS S c hSC t hRank hδ hAxis hNA hij b hb hb1 hEscape hK332
    (SCFixedCentralizers.thetaAlpha_eq_bot_of_full_gamma t.d
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab hFull hSolv hInd)

theorem sc_transitive_escape_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ} (hSC : c.IsSCPrime p)
    (t : CaseTwoTransitive
      (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig fun _ hp => hp))
    (hRank : ∀ i, CFSG.Open.pRank p (t.d.Lf i) = 1)
    (hδ : ¬ p ∣ Nat.card ↥((PartTwo.Three.dataOfSetup hS S).M ⊓ centralizer (t.d.AA : Set G)))
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (t.d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNP : normalizer (t.P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    {i j : Fin 3} (hij : i ≠ j) (b : G) (hb : b ∈ t.d.A i ⊔ t.d.A j) (hb1 : b ≠ 1)
    (hEscape : ¬ centralizer ({b} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hSE : Section7.StronglyEmbeddedFive) (hSolv : Section7.StronglyEmbeddedSolvable)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hK341 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K341)
    (hInner : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S) : False := by
  have hSM : t.d.S ≤ (PartTwo.Three.dataOfSetup hS S).M := by
    rw [t.hdS]
    exact inf_le_left.trans t.hP.le
  have hrank : CFSG.Open.pRank 3 t.d.S ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hSM).trans c.pRank_three_M.le
  have hbAA : b ∈ t.d.AA := sup_le (SCTransitive.A_le_AA t.d i) (SCTransitive.A_le_AA t.d j) hb
  have hc : Nat.card (zpowers b) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (t.d.isElemAbelian_AA.2 b hbAA) hb1
  have hK : CFSG.Open.IsKGroup ↥(centralizer ({b} : Set G)) := by
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers b) (by intro hb0; rw [hb0, Subgroup.card_bot] at hc; norm_num at hc)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  have hGamma := SCTransitive.not_rankThreeGamma_le_of_escape t hNA hAxis hrank hK332
    hij hb hb1 hK hEscape
  let X : Ctx82E3.C4Data G (PartTwo.Three.dataOfSetup hS S).M :=
    ⟨S.notCatalog, S.V, S.le, S.le_normalizer, S.elemAbelian, S.not_isTI⟩
  have hFull := c.rankThreeGamma_eq_top_of_isSCPrime hSE hSolv X hSC t.d t.hdM t.hdL hGamma
  exact sc_transitive_full_gamma_false hS S c hSC t hRank hδ hAxis hNA hNP hPG hij b hb hb1 hEscape
    hFull hK341 hInner hK332 hK326

theorem sc_transitive_factors_false_of_inputs
    {G : Type} [Group G] [Finite G] (hS : Standing G) (S : Setup G)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hTrans : ¬ ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hK8 : OuterThreeSplit) (hSE : Section7.StronglyEmbeddedFive)
    (hSAlt : Section7.StronglyEmbeddedSolvableAltTen) (hSolv : Section7.StronglyEmbeddedSolvable)
    (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt) (hOut : PerfectAutInner)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S) (hK11 : K11)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hNT : CFSG.AGLEmbedding.Asc81bNineThree) (hblk : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (hKF1 : L3NotEvenClassical) (hKF2 : L3EvenParabolic)
    (hK461 : CFSG.LocalAnalysis.UniquenessCase.UCK.K461)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hK49 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K49I)
    (hST : CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainNonAbelian) (hL3 : L3Overgroup)
    (hK341 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K341)
    (hInner : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction) :
    False := by
  obtain ⟨t, rfl, rfl⟩ := (c.toCtx812EOfSubset (PartTwo.Three.dataOfSetup hS S).sig
    fun _ hp => hp).exists_caseTwoTransitive hK8 d hdM hdL hinj hcomp hperm hP hdS hTrans
  have h76 := c.conclusion76 hSC.1
  by_cases hN : t.PairNormalizerLe p
  · let X : Ctx82E3.C4Data G (PartTwo.Three.dataOfSetup hS S).M :=
      ⟨S.notCatalog, S.V, S.le, S.le_normalizer, S.elemAbelian, S.not_isTI⟩
    exact t.false_of_centralizer_Z_le_of_pairNormalizerLe hOut hSE
      (t.caseTwoResidual_of_c4Data X hK11 hK32 hGA hSp hK332 hOut hSch hNT hblk hKF1 hKF2
        hK461 hK462 hK49 (fun G _ _ hKP hsim hna K hK hM hFs R hnc _ =>
          hST G hKP hsim hna K hK hM hFs R hnc) hL3 hSE) hSC.1 h76 hN
      (t.centralizer_Z_le_of_pairNormalizerLe hK326 hSC.1 h76 hN)
  obtain ⟨hr, hδ, i, j, hij, b, hb, hb1, hEscape⟩ := SCTransitive.exists_escape c hSC t hN
  have hAxis := SCTransitive.normalizer_axis_le_of_pRank_eq_one hSE hSAlt hKSM c hSC t.d t.hdM
    t.hinj t.hcomp hr
  have hNA := SCTransitive.normalizer_AA_le_of_isSCPrime c hSC t.d t.hdM (fun l => (hr l).ge)
    hAxis
  exact sc_transitive_escape_false hS S c hSC t hr hδ hAxis hNA
    (SCTransitive.normalizer_P_le_of_normalizer_AA_le t hNA)
    (SCTransitive.isSylowOf_top_of_normalizer_AA_le t hNA) hij b hb hb1 hEscape hSE hSolv hK332
    hK341 hInner hK326

end ActualData

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
