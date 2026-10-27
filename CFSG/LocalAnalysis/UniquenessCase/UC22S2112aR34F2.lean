module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Inn
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunCommute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
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

theorem uc22s2112r34_funTwoType_ne {t : StatedLieTag} {n : ℕ} (ht : FunTwoType t n) :
    ¬ (t = .PSL ∧ n = 2) ∧ ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3) ∧ t ≠ .twistedG2 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    simp [FunTwoType] at ht
  · rintro ⟨rfl | rfl, rfl⟩ <;> simp [FunTwoType] at ht
  · rintro rfl
    simp [FunTwoType] at ht

section Cases


theorem uc22s2112r34_false_f2_of_odd (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount)
    (hFC : K_FunCommute) (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) (hodd : Odd c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
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
  obtain ⟨b, hbB, hb, hbp, hbN, P, hPK⟩ := uc22s2112r34_exists_fixes_funSet_odd hKF1 hKS hGA hTB
    hσ hKF7 hH c hn3 hodd hL hBN hfaith hp hp2 hadm hX (Or.inl ht) hA1 hRee hpσ hMs hpN
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

theorem uc22s2112r34_false_f2_of_two_le (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hKC : KFunCount) (hFC : K_FunCommute) (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M) (hBN : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f) (ht : FunTwoType t n)
    (hf2 : 2 ≤ f) (h45 : ¬ (c.n = 4 ∧ 5 ∣ (genericOrders t n p f).1))
    (hX : LieModel (BarInf L) t n p f) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hMs : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq9 : 9 ≤ p ^ f :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1 (fun h => hA3 ⟨h.1, h.2.1⟩)
    hRee hpN
  have h4' : 4 ≤ CFSG.Open.pRank p L := by rcases h4 with ⟨-, h1⟩ | h4 <;> omega
  have hL3 : ¬ IsL3EpsOdd17 (BarInf L) p :=
    uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
  obtain ⟨r, hrπ, hrp, hr5, hr7⟩ := uc22s2112r34_exists_prime_mem_piSet hσ hH c hn3 hL hpσ
  have hr : r.Prime := hrπ.1
  have hrg : ¬ r ∣ (genericOrders t n p f).1 := by
    by_cases h7 : 7 ≤ r
    · exact uc22s2112r34_not_dvd_genericOrders (Or.inl ht) hr h7
    · have hn4 : c.n = 4 := by
        by_contra hn4
        exact h7 (hr7 hn4)
      rcases (by omega : r = 5 ∨ r = 6) with rfl | rfl
      · exact fun h => h45 ⟨hn4, h⟩
      · exact absurd hr (by norm_num)
  have hrN : ¬ r ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hr (by omega)
      (uc22s2112r34_not_dvd_center hGA hTB hL hp hp2 hX hr hr5 hrg)
  obtain ⟨R, hRB, -, hrR, hRr2, hRT, hRr⟩ :=
    uc22s2112r34_exists_rSub_calB1 c.hB0 D.sylowM.isPGroup hr hrπ.2
  have hRN : R ≤ normalizer (L : Set G) := hRB.trans hBN
  obtain ⟨P, ψ, hψ, hperm⟩ := uc22s2112r34_exists_innerHom_permutes hZ hRN
    (fun x hx => uc22s2112r34_inner_of_mem hKF1 hKF7 hH c hL hp hp2 hadm hX hA1 hRee hpσ hMs hpN
      hBN hfaith hr hr5 hrg hrN hRB hRr hx)
    (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hRT
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ = 1 := by rw [← hψ x, hx, map_one]
    exact Subtype.ext (hfaith x (hRB x.2)
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 _ h1))
  have hcardB : Nat.card ψ.range = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hne : ψ.range ≠ ⊥ := fun h => by
    rw [h, card_bot] at hcardB
    rw [← hcardB] at hrR
    exact hr.one_lt.ne' (Nat.dvd_one.1 hrR)
  have : IsMulCommutative ↥c.B0 := c.hB0.2.1
  have : IsMulCommutative ↥R := isMulCommutative_anti hRB
  have hoddB : Odd (Nat.card ψ.range) := by
    rw [hcardB]
    exact (hr.odd_of_ne_two (by omega)).pow.of_dvd_nat hRr2
  have h3B : ¬ 3 ∣ Nat.card ψ.range := fun h => by
    rw [hcardB] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
      (Nat.prime_three.dvd_of_dvd_pow (h.trans hRr2))
    omega
  have hpB : ¬ p ∣ Nat.card ψ.range := fun h => by
    rw [hcardB] at h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow (h.trans hRr2))).symm
  have hrank : ∀ s : ℕ, s.Prime → s ∣ Nat.card ψ.range →
      CFSG.pRank s ψ.range ≤ 2 ∧ CFSG.pRank s (⊤ : Subgroup (BarInf L)) ≤ 3 := by
    intro s hs hsd
    rw [hcardB] at hsd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hs hr).1 (hs.dvd_of_dvd_pow (hsd.trans hRr2))
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hs fun h => ?_
      rw [hcardB] at h
      have := (Nat.pow_dvd_pow_iff_le_right hs.one_lt).1 (h.trans hRr2)
      omega
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← pRank_eq_pRank_barInf hs hrN]
      exact (CFSG.SectionRank.pRank_mono hs.one_lt hL.1.le).trans
        (uc22s2112r34_pRank_le_three hσ hH c hL hrπ (by omega))
  obtain ⟨K₁, K₂, hne12, hKeq⟩ :=
    Set.ncard_eq_two.1 ((hKC (BarInf L) t n p f hp hp2 hadm hX P).1 ht)
  have h₁ : K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert _ _
  have h₂ : K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hK12 : K₁ ≤ centralizer (K₂ : Set (BarInf L)) :=
    commutator_eq_bot_iff_le_centralizer.1
      (uc22s2112r34_funSet_commute_barInf hFC hL hp hp2 hX hno hL3 hree (by omega) P h₁ h₂ hne12)
  have key : ∀ K ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)),
      ∀ y ∈ ψ.range, y ∈ centralizer (K : Set (BarInf L)) → y ≠ 1 → False := by
    intro K hK y hy hyC hy1
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have hx1 : (x : G) ≠ 1 := fun h => hy1 (by rw [show x = 1 from Subtype.ext h, map_one])
    have hxr := hRr x x.2 hx1
    refine uc22s2112r34_false_of_fund hKF7 hH c hL.1.le hp hp2 hf2 hpσ hMs (hRB x.2) (hRN x.2)
      (by rw [hxr]; exact hr) (by rw [hxr]; exact hrN) hpN hK.1 fun k hk => ?_
    change inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ k = k
    rw [← hψ x, MulAut.conj_apply, ← mem_centralizer_iff.1 hyC k hk, mul_inv_cancel_right]
  have hspl := hKS (BarInf L) t n p f hp hp2 hadm hX hA1 hRee P ψ.range hne inferInstance hoddB
    h3B hpB hperm hrank K₁ h₁
  rcases bot_or_exists_ne_one (ψ.range ⊓ centralizer (K₁ : Set (BarInf L))) with h0 | ⟨y, hy, hy1⟩
  ·
    rw [h0, sup_bot_eq] at hspl
    rcases bot_or_exists_ne_one ψ.range with h | ⟨y, hy, hy1⟩
    · exact hne h
    · exact key K₂ h₂ y hy (hK12 (mem_inf.1 (hspl.le hy)).2) hy1
  · exact key K₁ h₁ y (mem_inf.1 hy).1 (mem_inf.1 hy).2 hy1

end Cases

section Main


theorem s21_12aFR34F2_of_cases (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount)
    (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h5 : S21_5 D Ch)
    (h82 : F08.R82 D) (h211 : S21_1 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hQ : S21_12aFR34F2Q35 D (Choice214U D)) (hSg : S21_12aFR34F2Sig D (Choice214U D))
    (hEv : S21_12aFR34F2Even D (Choice214U D)) : S21_12aFR34F2 D (Choice214U D) := by
  intro hH c L hL p hp hp2 t n f hadm ht hX hno hfaith
  by_cases hq5 : p ^ f ≤ 5
  · exact hQ hH c L hL p hp hp2 t n f hadm ht hq5 hX hno hfaith
  have hq7 : 7 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨k, hk⟩ := hodd
    omega
  by_cases hpσ : p ∉ D.sig
  · exact hSg hH c L hL p hp hp2 hpσ t n f hadm ht hq7 hX hno hfaith
  rw [not_not] at hpσ
  have hn3' : 3 ≤ c.n := hn3 hH (c.mono hCh)
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    h5 hH { c.mono hCh with B := c.B0, hB := c.hB0, hle := le_rfl } L hL
  have hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f := fun f hm =>
    uc22s2112r34_ree_false hGA h82 h211 hH (c.mono hCh) hL hm
  obtain ⟨hA1, -, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
    (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨by omega, hA1⟩))
  have hFC : K_FunCommute := k_FunCommute_of_funHypOmega k_FunHypOmega_holds
  rcases Nat.even_or_odd c.n with heven | hodd
  · by_cases hcase : f = 1 ∨ (c.n = 4 ∧ 5 ∣ (genericOrders t n p f).1)
    · exact hEv hH c heven L hL p hp hp2 hpσ t n f hadm ht hq7 hcase hX hno hfaith
    · obtain ⟨hf1, h45⟩ := not_or.1 hcase
      have hf2 : 2 ≤ f := by have := hadm.2.1; omega
      exact (uc22s2112r34_false_f2_of_two_le hKF1 hKS hKC hFC hGA
        CFSG.TauCetiBridge.typewiseBridges hσ hKF7 hH c hn3' hL hBN hfaith hp hp2 hadm ht hf2 h45
        hX hno hree hpσ hpN).elim
  · exact (uc22s2112r34_false_f2_of_odd hKF1 hKS hKC hFC hGA CFSG.TauCetiBridge.typewiseBridges
      hσ hKF7 hH c hn3' hodd hL hBN hfaith hp hp2 hadm ht hq7 hX hno hree hpσ hpN).elim

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
