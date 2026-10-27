module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34AlphaDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunCommute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.GroupTheory.PRankBound
import CFSG.Adapters.TauCetiExceptional.ReeCatalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL3EpsOdd17)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
  (K_FunCommute k_FunCommute_of_funHypOmega k_FunHypOmega_holds)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem exists_odd_part_of_not_isPowTwo {n : ℕ} (hn : n ≠ 0) (h : ¬ IsPowTwo n) :
    ∃ e m : ℕ, Odd m ∧ 3 ≤ m ∧ n = 2 ^ e * m := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨e, m, hm, ?_, rfl⟩
  obtain ⟨k, rfl⟩ := hm
  rcases k with _ | k
  · exact absurd ⟨e, by simp⟩ h
  · omega

theorem uc22s2112r34_exists_mem_orderOf_alpha {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {p : ℕ} (hpσ : p ∈ D.sig) {e m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hn : c.n = 2 ^ e * m) :
    ∃ b ∈ c.B0, b ∈ normalizer (D.T : Set G) ∧
      ∃ s : ℕ, s.Prime ∧ 7 ≤ s ∧ s ≠ p ∧ orderOf b = s := by
  obtain ⟨s, hs, hs7, hsd⟩ := uc22s2112r34_exists_prime_seven_le hm3 fun h => by
    subst h
    exact absurd hm (by decide)
  have hmn : 2 ^ m - 1 ∣ 2 ^ c.n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 (2 ^ e)
    rwa [one_pow, ← pow_mul, mul_comm m, ← hn] at h
  have hsB : s ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hs, hsd.trans hmn⟩
  obtain ⟨b, hbB, hbs⟩ := uc22p22i_exists_elt_of_mem_piSet hsB
  have hbα : b ∈ oPi {q | q.Prime ∧ q ∣ 2 ^ m - 1} c.B0 :=
    uc22pwtb_mem_oPi c.hB0.2.1 hbB fun q hq hqd => by
      rw [hbs] at hqd
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hs).1 hqd
      exact ⟨hq, hsd⟩
  exact ⟨b, hbB, c.hα e m hm hn hbα, s, hs, hs7,
    fun h => uc22s2112r34_not_mem_sig hσ hH c hL hsB (h ▸ hpσ), hbs⟩

section Core


theorem uc22s2112r34_exists_fixes_funSet_of_mem (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hGA : GriessAllModelsStatement) (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G}
    {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel (BarInf L) t n p f)
    (htn : FunTwoType t n ∨ ((t = .PSL ∨ t = .PSU) ∧ n = 3)) (hA1 : ¬ (t = .PSL ∧ n = 2))
    (hRee : t ≠ .twistedG2) (hpσ : p ∈ D.sig) (hMs : IsStronglyPEmbedded p D.M)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {b : G} (hbB : b ∈ c.B0)
    (hbT : b ∈ normalizer (D.T : Set G)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) (hsp : s ≠ p)
    (hbs : orderOf b = s) :
    ∃ hb : b ∈ normalizer (L : Set G), ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) ∧
      ∃ P : Sylow 2 (BarInf L),
        ∀ K ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)),
          K ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩) := by
  classical
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  have hb : b ∈ normalizer (L : Set G) := hBN hbB
  have hsg : ¬ s ∣ (genericOrders t n p f).1 := uc22s2112r34_not_dvd_genericOrders htn hs hs7
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hs (by omega)
      (uc22s2112r34_not_dvd_center hGA hTB hL hp hp2 hX hs (by omega) hsg)
  have hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1 := fun h1 => by
    have hb1 := hfaith b hbB (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 hb h1)
    rw [hb1, orderOf_one] at hbs
    omega
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (uc22s2112r34_inner_of_kFieldAutOdd hKF1 hKF7 hH c hL
    hp hp2 hadm hX hA1 hRee hpσ hMs hpN hbB hb hs (by omega) hbs hsg hsN hθ1)
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  have hxs : orderOf x = s := by
    rw [← orderOf_injective _ hinj x, hx]
    have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
    rw [Subgroup.orderOf_mk, hbs] at hd
    rcases (Nat.dvd_prime hs).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hθ1
    · exact h1
  have hZx : Nat.card (zpowers x) = s := by rw [Nat.card_zpowers, hxs]
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_barInf hL
  have hxP : x ∈ normalizer ((P : Subgroup (BarInf L)) : Set (BarInf L)) := by
    rw [hP]
    exact uc22s2112r34_mem_normalizer_map hb hbT hx.symm
  have hne : zpowers x ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hxs
    omega
  have hodd' : Odd (Nat.card (zpowers x)) := by
    rw [hZx]
    exact hs.odd_of_ne_two (by omega)
  have h3 : ¬ 3 ∣ Nat.card (zpowers x) := fun h => by
    rw [hZx] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).1 h
    omega
  have hpx : ¬ p ∣ Nat.card (zpowers x) := fun h => by
    rw [hZx] at h
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).1 h).symm
  have hperm : ((zpowers x : Subgroup (BarInf L)) : Set (BarInf L)) * (P : Set (BarInf L)) =
      (P : Set (BarInf L)) * (zpowers x : Set (BarInf L)) :=
    set_mul_normalizer_comm (zpowers x : Set (BarInf L)) (P : Subgroup (BarInf L))
      (zpowers_le.2 hxP)
  have hrank : ∀ r : ℕ, r.Prime → r ∣ Nat.card (zpowers x) →
      CFSG.pRank r (zpowers x) ≤ 2 ∧ CFSG.pRank r (⊤ : Subgroup (BarInf L)) ≤ 3 := by
    intro r hr hrd
    rw [hZx] at hrd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hs).1 hrd
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      refine (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (k := 1) hr fun h => ?_).trans
        (by norm_num)
      rw [hZx] at h
      have := (Nat.pow_dvd_pow_iff_le_right hr.one_lt).1 (by rwa [pow_one] : r ^ (1 + 1) ∣ r ^ 1)
      omega
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← pRank_eq_pRank_barInf hr hsN]
      exact (CFSG.SectionRank.pRank_mono hr.one_lt hL.1.le).trans
        (uc22s2112r34_pRank_le_three hσ hH c hL
          ⟨hr, by rw [← hbs]; exact Subgroup.orderOf_dvd_natCard _ hbB⟩ (by omega))
  refine ⟨hb, hsN, P, fun K hK => ?_⟩
  have hxK : zpowers x ⊓ K = ⊥ := by
    have hd : Nat.card ↥(zpowers x ⊓ K) ∣ s := by
      rw [← hZx]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hs).1 hd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : zpowers x ⊓ K = zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hZx])
      have hx' : x ∈ zpowers x ⊓ K := by
        rw [heq]
        exact mem_zpowers x
      obtain ⟨k, hk⟩ := uc22s2112r34_orderOf_eq_three_pow_of_mem_funSet hK (mem_inf.1 hx').2 hxP
        (by rw [hxs]; exact hs.odd_of_ne_two (by omega))
      rw [hxs] at hk
      have h3s : 3 ∣ s := by
        cases k with
        | zero =>
          rw [pow_zero] at hk
          omega
        | succ k =>
          rw [hk, pow_succ]
          exact dvd_mul_left 3 _
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).1 h3s
      omega
  have hspl := hKS (BarInf L) t n p f hp hp2 hadm hX hA1 hRee P (zpowers x) hne inferInstance
    hodd' h3 hpx hperm hrank K hK
  rw [hxK, bot_sup_eq] at hspl
  have hxC : x ∈ centralizer (K : Set (BarInf L)) := (mem_inf.1 (hspl.le (mem_zpowers x))).2
  intro y hy
  change inducedBarInfAutHom L ⟨b, hb⟩ y = y
  rw [← hx, MulAut.conj_apply, ← mem_centralizer_iff.1 hxC y hy, mul_inv_cancel_right]

theorem uc22s2112r34_exists_fixes_funSet_alpha (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hGA : GriessAllModelsStatement) (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G}
    {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D Ch) (hn0 : c.n ≠ 0) (hpow : ¬ IsPowTwo c.n) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hBN : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel (BarInf L) t n p f)
    (htn : FunTwoType t n ∨ ((t = .PSL ∨ t = .PSU) ∧ n = 3)) (hA1 : ¬ (t = .PSL ∧ n = 2))
    (hRee : t ≠ .twistedG2) (hpσ : p ∈ D.sig) (hMs : IsStronglyPEmbedded p D.M)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) :
    ∃ b ∈ c.B0, ∃ hb : b ∈ normalizer (L : Set G), (orderOf b).Prime ∧
      ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L) ∧ ∃ P : Sylow 2 (BarInf L),
        ∀ K ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)),
          K ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩) := by
  obtain ⟨e, m, hm, hm3, hn⟩ := exists_odd_part_of_not_isPowTwo hn0 hpow
  obtain ⟨b, hbB, hbT, s, hs, hs7, hsp, hbs⟩ :=
    uc22s2112r34_exists_mem_orderOf_alpha hσ hH c hL hpσ hm hm3 hn
  obtain ⟨hb, hsN, P, hPK⟩ := uc22s2112r34_exists_fixes_funSet_of_mem hKF1 hKS hGA hTB hσ hKF7
    hH c hL hBN hfaith hp hp2 hadm hX htn hA1 hRee hpσ hMs hpN hbB hbT hs hs7 hsp hbs
  exact ⟨b, hbB, hb, hbs ▸ hs, hbs ▸ hsN, P, hPK⟩

theorem uc22s2112r34_false_f2_of_alpha (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hKC : KFunCount) (hFC : K_FunCommute) (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch)
    (hn0 : c.n ≠ 0) (hpow : ¬ IsPowTwo c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (ht : FunTwoType t n) (hq7 : 7 ≤ p ^ f)
    (hX : LieModel (BarInf L) t n p f) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hMs : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  obtain ⟨b, hbB, hb, hbp, hbN, P, hPK⟩ := uc22s2112r34_exists_fixes_funSet_alpha hKF1 hKS hGA
    hTB hσ hKF7 hH c hn0 hpow hL hBN hfaith hp hp2 hadm hX (Or.inl ht) hA1 hRee hpσ hMs hpN
  obtain ⟨K₁, K₂, hne, hKeq⟩ :=
    Set.ncard_eq_two.1 ((hKC (BarInf L) t n p f hp hp2 hadm hX P).1 ht)
  have h₁ : K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert _ _
  have h₂ : K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hL3 : ¬ IsL3EpsOdd17 (BarInf L) p := by
    obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1 (fun h => hA3 ⟨h.1, h.2.1⟩)
      hRee hpN
    rcases h4 with ⟨hexc, rfl⟩ | h4
    · exact uc22s2112r34_not_isL3EpsOdd17_of_exc hp hX hexc
    · exact uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
  exact uc22s2112r34_false_of_pair hKF7 hH c hL.1.le hp hp2 hq7 hpσ hMs hbB hb hbp hbN hpN h₁.1
    h₂.1 (uc22s2112r34_funSet_commute_barInf hFC hL hp hp2 hX hno hL3 hree (by omega) P h₁ h₂ hne)
    (sup_le (hPK K₁ h₁) (hPK K₂ h₂))

end Core

section MainL3


theorem s21_12aFR34L3E_of_l3E2 (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h5 : S21_5 D Ch)
    (h82 : F08.R82 D) (h211 : S21_1 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hE2 : S21_12aFR34L3E2 D (Choice214U D)) :
    S21_12aFR34L3E D (Choice214U D) := by
  intro hH c heven L hL p hp hp2 f hf2 hm hno hfaith
  by_cases hpow : IsPowTwo c.n
  · exact hE2 hH c heven hpow L hL p hp hp2 f hf2 hm hno hfaith
  exfalso
  have hn3' : 3 ≤ c.n := hn3 hH (c.mono hCh)
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    h5 hH { c.mono hCh with B := c.B0, hB := c.hB0, hle := le_rfl } L hL
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq9 : 9 ≤ p ^ f :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  have hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f := fun f hm =>
    uc22s2112r34_ree_false hGA h82 h211 hH (c.mono hCh) hL hm
  have key : ∀ t : StatedLieTag, (t = .PSL ∨ t = .PSU) → LieModel (BarInf L) t 3 p f → False := by
    intro t ht hX
    have hRee : t ≠ .twistedG2 := by rcases ht with rfl | rfl <;> nofun
    have hA1 : ¬ (t = .PSL ∧ 3 = 2) := fun h => absurd h.2 (by norm_num)
    have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
      (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨by omega, hA1⟩))
    obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1
      (fun h => by have := h.2.2; omega) hRee hpN
    have h4' : 4 ≤ CFSG.Open.pRank p L := by rcases h4 with ⟨-, h1⟩ | h4 <;> omega
    obtain ⟨hpσ, hMs⟩ := uc22s2112r34_sig_of_le_pRank hσ hL hp hp2 h4'
    obtain ⟨b, hbB, hb, hbp, hbN, P, hPK⟩ := uc22s2112r34_exists_fixes_funSet_alpha hKF1 hKS hGA
      CFSG.TauCetiBridge.typewiseBridges hσ hKF7 hH c (by omega) hpow hL hBN hfaith hp hp2
      hX.admissible hX (Or.inr ⟨ht, rfl⟩) hA1 hRee hpσ hMs hpN
    have hL3 : ¬ IsL3EpsOdd17 (BarInf L) p :=
      uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
    obtain ⟨K, hK⟩ := uc22s2112r34_funSet_nonempty_barInf hL hp hp2 hX hno hL3 hree (by omega) P
    exact uc22s2112r34_false_of_fund hKF7 hH c hL.1.le hp hp2 hf2 hpσ hMs hbB hb hbp hbN hpN
      hK.1 (hPK K hK)
  rcases hm with h | h
  · exact key .PSL (Or.inl rfl) h
  · exact key .PSU (Or.inr rfl) h

end MainL3

section MainF2


theorem s21_12aFR34F2Even_of_f2Even2 (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount)
    (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h5 : S21_5 D Ch)
    (h82 : F08.R82 D) (h211 : S21_1 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hEv2 : S21_12aFR34F2Even2 D (Choice214U D)) : S21_12aFR34F2Even D (Choice214U D) := by
  intro hH c heven L hL p hp hp2 hpσ t n f hadm ht hq7 hcase hX hno hfaith
  by_cases hpow : IsPowTwo c.n
  · exact hEv2 hH c heven hpow L hL p hp hp2 hpσ t n f hadm ht hq7 hcase hX hno hfaith
  exfalso
  have hn3' : 3 ≤ c.n := hn3 hH (c.mono hCh)
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    h5 hH { c.mono hCh with B := c.B0, hB := c.hB0, hle := le_rfl } L hL
  have hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f := fun f hm =>
    uc22s2112r34_ree_false hGA h82 h211 hH (c.mono hCh) hL hm
  obtain ⟨hA1, -, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
    (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨by omega, hA1⟩))
  exact uc22s2112r34_false_f2_of_alpha hKF1 hKS hKC
    (k_FunCommute_of_funHypOmega k_FunHypOmega_holds) hGA CFSG.TauCetiBridge.typewiseBridges
    hσ hKF7 hH c (by omega) hpow hL hBN hfaith hp hp2 hadm ht hq7 hX hno hree hpσ hpN

end MainF2

end CFSG.LocalAnalysis.UniquenessCase.UC22
