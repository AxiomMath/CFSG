module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySixA2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanProductRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFourTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U7CartanRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.ConjClosureCentralProduct
public import CFSG.Timmesfeld.Orders.BangNotDvd
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21o
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sm
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l_ne_three_of_even {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h44_3 : R17_44_3AtB D V₀ V)
    (hK4 : Inputs1719.K_CartanRankLeThree)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankThreeNotU62) (he : Even n) : l ≠ 3 := by
  classical
  intro hl3
  obtain ⟨t, m, hadm, hmodel, hrank⟩ := ctx.rank
  have hB := Inputs1719.BorelChevOver.of_on hK3 hmodel
    ⟨by rw [hrank, hl3], fun ⟨_, _, hn⟩ => by obtain ⟨k, hk⟩ := he; omega⟩
  let K := Bar2 L
  let π : ↥L →* K := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  set S : Subgroup K := ((D.T ⊓ L).subgroupOf L).map π with hSdef
  have hL : L ∈ calC D.M := ctx.mem_calC
  have hq : CFSG.Open.IsQuasisimple K := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  have hmodelK : LieModel (K ⧸ Subgroup.center K) t m 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hmodel
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := isSylowTwoOf_sylowBar2 hL
  have h3dvd : 3 ∣ 2 ^ n - 1 := CFSG.Quasithin.A319.three_dvd_two_pow_sub_one he
  have hsidePSL : t = .PSL → ¬ 3 ∣ m := by
    intro ht h3m
    have hm : m = 4 := by
      rw [ht] at hrank
      simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrank
      omega
    rw [hm] at h3m
    norm_num at h3m
  have hsideE6 : t = .E6 → 3 ≠ 3 := by
    intro ht hEq
    rw [ht] at hrank
    simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrank
    omega
  have hK4app := hK4 t m n (by change CS17LieRank t m ≤ 3; rw [hrank, hl3]) K hmodelK hq hodd
    S hS 3 Nat.prime_three (by norm_num) h3dvd hsidePSL hsideE6
  have hthree : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
      (TauCeti.Subgroup.normalizerQuotient S)) := by
    have h := hK4app
    rw [hrank] at h
    rwa [hl3] at h
  have hO2 : CFSG.pCore 2 ↥L ≤ (D.T ⊓ L).subgroupOf L :=
    pCore_le_sylow_of_mem_calC hL
  have htrans : CFSG.Open.pRank 3 (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient ((D.T ⊓ L).subgroupOf L))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient
          (((D.T ⊓ L).subgroupOf L).map π))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
      (CFSG.GroupTheory.normalizerQuotient_quotientEquiv (CFSG.pCore 2 ↥L)
        ((D.T ⊓ L).subgroupOf L) hO2)
  have hbridge := pRank_normalizerQuotient_le_pRank_cartan hL ctx.cartan
    Nat.prime_three (by norm_num)
  have hDc := pRank_cartan_le_pRank_Dc (ctx := ctx) Nat.prime_three
  have h3 : 3 ≤ CFSG.Open.pRank 3 C := by
    refine hthree.trans ?_
    rw [← htrans]
    exact hbridge
  have h3Dc : 3 ≤ CFSG.Open.pRank 3 Dc := h3.trans hDc
  have h2 := (h44_3 L X p n l C Dc Gamma ctx n hB).1
  omega

theorem s17_46_not_psu_seven
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h44_3 : R17_44_3AtB D V₀ V)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankThreeNotU62) (hnOdd : Odd n)
    {t : StatedLieTag} {m : ℕ} (hadm : StatedLieAdmissible t m 2 n)
    (hmodel : LieModel (BarInf L) t m 2 n) : ¬ (t = .PSU ∧ m = 7) := by
  rintro ⟨rfl, rfl⟩
  have hB := Inputs1719.BorelChevOver.of_on hK3 hmodel ⟨by decide, by simp⟩
  have h3 : 3 ∣ 2 ^ n + 1 := by
    have hmod : (2 ^ n + 1) % 3 = 0 := by
      rw [Nat.add_mod, CFSG.two_pow_mod_three_of_odd hnOdd]
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC ctx.mem_calC
  have hmodelK : CFSG.Blueprint.LieModel
      (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSU 7 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hmodel
  have hS : IsSylowTwoOf (((D.T ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ⊤ := isSylowTwoOf_sylowBar2 ctx.mem_calC
  have hK7b' := Inputs1719.k_U7CartanRank_holds (Bar2 L) n 3 hadm hnOdd hmodelK
    ctx.mem_calC.2.2 (uc22p20p_odd_center_bar2 ↥L) Nat.prime_three (by norm_num) h3
    (((D.T ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) hS
  have hbridge := pRank_normalizerQuotient_bar2_le_pRank_cartan ctx.mem_calC ctx.cartan
    Nat.prime_three (by norm_num)
  have hK7b'' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))))) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup
      (TauCeti.Subgroup.normalizerQuotient
        (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))))]
    exact hK7b'
  have h3Dc : 3 ≤ CFSG.Open.pRank 3 Dc :=
    (hK7b''.trans hbridge).trans (pRank_cartan_le_pRank_Dc ctx Nat.prime_three)
  have h2 := (h44_3 L X p n l C Dc Gamma ctx n hB).1
  omega

theorem s17_46_core
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) (hl : l = 3)
    (h43 : R17_43At D V₀ V) (hDE : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (h638 : UC6.R6_38 D)
    (h44_1 : R17_44_1AtB D V₀ V) (h44_2 : R17_44_2AtB D V₀ V) (h44_3 : R17_44_3AtB D V₀ V)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankThreeNotU62)
    (hK4 : Inputs1719.K_CartanRankLeThree) (hK7a : K_CartanSylowAbelian)
    (hN : uc22p20rNativeGriess) :
    S17_46Core D V₀ V L X p n l C Dc Gamma := by
  classical
  obtain ⟨t, m, hadm, hmodel, hrank⟩ := ctx.rank
  have hn2 : 2 ≤ n := by
    have h43' : 2 < 2 ^ n := h43 L X p n l C Dc Gamma ctx
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num at h43'
    · exact h
  have hB : Inputs1719.BorelChevOver (BarInf L) n :=
    ctx.borelChevOver hK3 fun t m h => ⟨by rw [h, hl], fun ⟨_, _, hn⟩ => by omega⟩
  have hnOdd : Odd n := by
    rw [← Nat.not_even_iff_odd]
    exact fun he => l_ne_three_of_even ctx h44_3 hK4 hK3 he hl
  obtain ⟨r, hr, hrdvd, h2n⟩ :=
    CFSG.Timmesfeld.exists_prime_dvd_two_pow_sub_one_not_dvd_two_mul (m := n) hn2
  have hr7 : 7 ≤ r := s13_seven_le_of_dvd hnOdd hr hrdvd
  have hr2 : r ≠ 2 := by omega
  have hrn : ¬ r ∣ n := fun h => h2n (h.trans (dvd_mul_left n 2))
  rw [hl] at hrank
  have hcases : (t = .PSL ∧ m = 4) ∨ (t = .PSU ∧ (m = 6 ∨ m = 7)) ∨
      (t = .PSp ∧ m = 3) ∨ (t = .POmegaMinus ∧ m = 4) := by
    rcases t <;> simp [CS17LieRank, StatedLieAdmissible] at hadm hrank ⊢ <;> omega
  have hPSL : t = .PSL → ¬ r ∣ m := by
    rintro rfl
    rcases hcases with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · intro hd
      exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    all_goals cases h
  have hE6 : t = .E6 → r ≠ 3 := by
    intro h
    rw [h] at hrank
    simp [CS17LieRank] at hrank
  have hC3 : 3 ≤ CFSG.Open.pRank r C := by
    have h := cartanRank_le_pRank_cartan_on hK4 ctx.mem_calC ctx.cartan
      (by change CS17LieRank t m ≤ 3; rw [hrank]) hmodel hr hr2 hrdvd hPSL hE6
    rwa [hrank] at h
  have hZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    by_cases htPSL : t = .PSL
    · have hm : m = 4 := by
        rw [htPSL] at hrank
        simp [CS17LieRank] at hrank
        omega
      have hmodelPSL : CFSG.Blueprint.LieModel (BarInf L) .PSL 4 2 n := by
        simpa [htPSL, hm] using hmodel
      have hoddq : Odd (2 ^ n - 1) :=
        Nat.Even.sub_odd (Nat.one_le_two_pow)
          (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
      have hcop : Nat.Coprime 4 (2 ^ n - 1) := by
        simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hoddq)
      have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 4 2 n = (1, 1) := by
        simp [CFSG.Blueprint.Multiplier.genericOrders, hcop.gcd_eq_one]
      obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC ctx.mem_calC
      have hcb : Subgroup.center (Bar2 L) = ⊥ :=
        uc22p20v_center_eq_bot hN ctx.mem_calC.2.2 (uc22p20p_odd_center_bar2 ↥L)
          (CFSG.Blueprint.LieModel.of_mulEquiv e hmodelPSL) hg
      intro hd
      rw [hcb, Subgroup.card_bot] at hd
      exact hr.not_dvd_one hd
    · have htE6 : t ≠ .E6 := by
        intro h
        rw [h] at hrank
        simp [CS17LieRank] at hrank
      exact not_dvd_card_center_bar2 hN ctx.mem_calC hmodel htPSL htE6 hr hr2 hrdvd
  have hle3 : CFSG.Open.pRank r Dc ≤ 3 :=
    h44_1 L X p n l C Dc Gamma ctx n hB r hr hr2
  have hprod := Ctx17_42.ncard_mul_pRank_le_pRank_Dc ctx hr hr2 hZ
  have hΓ1 : Gamma.ncard ≤ 1 := by
    have h3 : Gamma.ncard * 3 ≤ 3 :=
      (Nat.mul_le_mul_left Gamma.ncard hC3).trans (hprod.trans hle3)
    omega
  have hΓpos : 0 < Gamma.ncard := by
    obtain ⟨γ, ⟨hγ, -⟩, -⟩ := ctx.reps.2 1 (Subgroup.one_mem _)
    exact (Set.ncard_pos (Set.toFinite Gamma)).2 ⟨γ, hγ⟩
  have hconj1 : (conjSetOf D.M L).ncard = 1 := by
    rw [← Ctx17_42.ncard_Gamma_eq_card_conjSet ctx]
    exact le_antisymm hΓ1 (by omega)
  have hLX : L = X := by
    rw [ctx.X_eq]
    exact (uc22s217_conjClosure_eq_of_ncard_eq_one hconj1).symm
  have hDc3 : 3 ≤ CFSG.Open.pRank r Dc := hC3.trans (pRank_cartan_le_pRank_Dc ctx hr)
  have hnotStrong : ¬ IsStronglyPEmbedded r D.M := by
    intro hsp
    have h2 := h44_2 L X p n l C Dc Gamma ctx n hB r hr (by omega) (Or.inr hsp)
    omega
  have hGne3 : CFSG.Open.evenRank G ≠ 3 := by
    intro h3
    have h2 := h44_2 L X p n l C Dc Gamma ctx n hB r hr (by omega) (Or.inl h3)
    omega
  have hG4 : 3 < CFSG.Open.evenRank G := by
    have := D.standing.rank
    omega
  have hpP : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have hM4 : 4 ≤ CFSG.Open.pRank p D.M := hDE.four_le hG4 p ctx.p_mem
  have hOp : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.OpRes p D.M = D.M :=
    h638 p hpP hp2 (Or.inl ctx.p_mem)
  have hU7 : ¬ (t = .PSU ∧ m = 7) := s17_46_not_psu_seven ctx h44_3 hK3 hnOdd hadm hmodel
  have hdisj : (t = .PSL ∧ m = 4) ∨ (t = .PSU ∧ m = 6) ∨ (t = .PSp ∧ m = 3) ∨
      (t = .POmegaMinus ∧ m = 4) := by
    rcases hcases with h | h | h | h
    · exact Or.inl h
    · obtain ⟨ht, hm⟩ := h
      rcases hm with hm | hm
      · exact Or.inr (Or.inl ⟨ht, hm⟩)
      · exact absurd ⟨ht, hm⟩ hU7
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hLM : L ≤ D.M := ctx.mem_calC.1.le
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) := by
    rw [hLX, ctx.X_eq]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hnotSig : r ∉ D.sig := fun hrs =>
    hnotStrong (hSg.sig1_sp r (by rw [← h1219]; exact hrs))
  have hrel : (L ⊔ F08.CentOverO2 D.M L).relIndex D.M ∣
      Nat.card (Outer (Bar2 L)) := relIndex_centOverO2_dvd_card_outer hLM hML
  have hOuter : ¬ r ∣ Nat.card (Outer (Bar2 L)) := by
    refine not_dvd_card_outer_bar2 ctx.mem_calC hmodel ?_ hr (by omega) hrn
    rcases hdisj with h | h | h | h
    · exact Or.inl ⟨h.1, Or.inr h.2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hout : ¬ r ∣ (L ⊔ F08.CentOverO2 D.M L).relIndex D.M := fun hdvd =>
    hOuter (hdvd.trans hrel)
  have hab : ∀ P : Sylow r (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)) := by
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC ctx.mem_calC
    have hmodelK : CFSG.Blueprint.LieModel
        (Bar2 L ⧸ Subgroup.center (Bar2 L)) t m 2 n :=
      CFSG.Blueprint.LieModel.of_mulEquiv e hmodel
    refine hK7a (Bar2 L) t m n r hadm hmodelK ctx.mem_calC.2.2
      (uc22p20p_odd_center_bar2 ↥L) ?_ hr (by omega) hrdvd
    rcases hdisj with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hn7 : ∀ E : Subgroup G, E ≤ L → IsPGroup r E →
      ∃ R : Subgroup G, IsSylowOf r R D.M ∧ E ≤ R ⊓ Subgroup.centralizer (R : Set G) :=
    fun E hEL hEr => exists_sylow_le_centralizer_of_isMulCommutative
      hr hr2 hLM hML hab hout hEL hEr
  have hcentE : ∀ E : Subgroup G, E ≤ L → IsElemAbelian r E → Nat.card E = r ^ 2 →
      CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) ≤ 1 := by
    intro E hEL hEel hEcard
    by_contra hcon
    have hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) := by omega
    obtain ⟨R, hR, hEZ⟩ := hn7 E hEL hEel.isPGroup
    exact hnotStrong (strongly_of_two_le_pRank_centralizer hSg h1219 h76 h614 ctx.p_mem
      hr hr2 hR hEel hEcard hEZ hF)
  have hcentOverO2 : CFSG.Open.pRank p (F08.CentOverO2 D.M L) ≤ 1 := by
    obtain ⟨A, hAC, hAel, hAcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt C
    obtain ⟨E, hEA, hEel, hEcard⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_card_p_sq hr hAel
        (by rw [hAcard]; exact Nat.pow_le_pow_right hr.pos (by omega))
    have hEL : E ≤ L := (hEA.trans hAC).trans ctx.cartan.1
    have hrp : r ≠ p := fun h => hnotSig (h ▸ ctx.p_mem)
    exact (pRank_centOverO2_le_pRank_inf_centralizer hLM hML hpP hp2 hr hr2 hrp hEL
      hEel.isPGroup).trans (hcentE E hEL hEel hEcard)
  have ctxX : Ctx17_42 D V₀ V X X p n l C Dc Gamma := by
    simpa [hLX] using ctx
  have hcartanCent : CFSG.Open.pRank p C ≤ 1 :=
    pRank_cartan_le_one_of_centE_of_borel ctxX
      (ctxX.borelChevOver hK3 fun t m h => ⟨by rw [h, hl], fun ⟨_, _, hn⟩ => by omega⟩)
      (r := r) hr hr2 hpP hp2 hC3
      (fun E hEX hEel hEcard => hcentE E (by rw [hLX]; exact hEX) hEel hEcard)
  refine ⟨hLX, hnOdd, ⟨t, m, hmodel, hdisj⟩, ?_, hM4, hOp, hcentOverO2, hcartanCent⟩
  exact ⟨r, hr, hr7, hrdvd, hcentE⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
