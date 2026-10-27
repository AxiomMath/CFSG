module

public import CFSG.RankThree.PartOne.KF.F128Cls
public import CFSG.RankThree.PartOne.KF.F122PSUSplit
public import CFSG.RankThree.PartOne.KF.ClsPSUBig
public import CFSG.RankThree.PartOne.KF.ClsSULift
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.KFU
  CFSG.Quasithin
open CFSG.RankThree.PartOne.K1214 (SylowShape)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem exceptionalOrders_psu {n f : ℕ} (h : (n ≠ 4 ∧ n ≠ 6) ∨ 2 ≤ f) :
    Blueprint.Multiplier.exceptionalOrders .PSU n 2 f = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem card_multiplier_psu_eq {n f : ℕ} (h : (n ≠ 4 ∧ n ≠ 6) ∨ 2 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSU n 2 f ×
      Blueprint.Multiplier.exceptional .PSU n 2 f) = Nat.gcd n (2 ^ f + 1) := by
  have hgen : Blueprint.Multiplier.genericOrders .PSU n 2 f = (Nat.gcd n (2 ^ f + 1), 1) := rfl
  have hexc := exceptionalOrders_psu h
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]

theorem two_le_orderOf_neg_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q)
    (h2 : ¬ p ∣ q + 1) : 2 ≤ orderOf (-(q : ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : -(q : ZMod p) ≠ 1 := fun h => h2 (by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast
    have : (q : ZMod p) = -1 := neg_eq_iff_eq_neg.1 h
    rw [this]; exact neg_add_cancel _)
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hpos : 0 < orderOf (-(q : ZMod p)) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, Nat.sub_pos_of_lt hp.one_lt, ZMod.pow_card_sub_one_eq_one (neg_ne_zero.2 hq0)⟩)
  by_contra hlt
  push Not at hlt
  exact hne1 (orderOf_eq_one_iff.1 (le_antisymm (Nat.le_of_lt_succ hlt) hpos))

theorem three_le_orderOf_neg_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q)
    (h1 : ¬ p ∣ q - 1) (h2 : ¬ p ∣ q + 1) (hq1 : 1 ≤ q) : 3 ≤ orderOf (-(q : ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2le := two_le_orderOf_neg_of_not_dvd hp hq h2
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hne1 : (q : ZMod p) ≠ 1 := fun h => h1 (by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h]; simp)
  by_contra hlt
  push Not at hlt
  have h2' : orderOf (-(q : ZMod p)) = 2 := le_antisymm (Nat.le_of_lt_succ hlt) h2le
  have hsq : (-(q : ZMod p)) ^ 2 = 1 := by rw [← h2']; exact pow_orderOf_eq_one _
  have : (q : ZMod p) ^ 2 = 1 := by
    calc (q : ZMod p) ^ 2 = (-(q : ZMod p)) ^ 2 := (neg_sq _).symm
      _ = 1 := hsq
  have h3 : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by ring_nf; rw [this]; ring
  have hnem1 : (q : ZMod p) ≠ -1 := fun h => h2 (by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [h]; exact neg_add_cancel _)
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact hne1 (sub_eq_zero.1 h4)
  · exact hnem1 (eq_neg_of_add_eq_zero_left h4)

open CFSG.GroupTheory.WeirSylow in
theorem sylow_cyclic_GU {K : Type} [Field K] [Finite K] {p n q : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = q ^ 2) (hpq : ¬ p ∣ q) (hn : 1 ≤ n)
    (h : n / orderOf (-(q : ZMod p)) ≤ 1) : ∀ P : Sylow p (StatedGU n q K), IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = q ^ 2 := by rw [← hK]; exact Nat.card_eq_fintype_card.symm
  intro P
  obtain ⟨e⟩ := sylow_GU (hp.odd_of_ne_two hp2) K hcard hpq hn P
  exact (MulEquiv.isCyclic e).2 (isCyclic_sigmaModel_of_div_le_one h)

theorem pRank_statedSU_le_one {K : Type} [Field K] [Finite K] {p n q : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = q ^ 2) (hpq : ¬ p ∣ q) (hn : 1 ≤ n)
    (h : n / orderOf (-(q : ZMod p)) ≤ 1) : CFSG.pRank p ↥(StatedSU n q K) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : StatedSU n q K ≤ StatedGU n q K :=
    Subgroup.closure_mono (fun A hA => hA.2)
  exact pRank_le_one_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    (sylow_cyclic_GU hp hp2 hK hpq hn h)

theorem kf128SylTag_PSU
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF128SylTag .PSU := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hkerp hLR2 n f₀ hf₀ hM α hαp hαinn hLRA hX hF hrk
  classical
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hcl : StatedClassicalModel T .PSU n 2 (p * f₀) :=
    K1214.statedClassicalModel_of_lieModel_of_tag' (Or.inl rfl) hM
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := id hcl
  have hn3 : 3 ≤ n := hadm.2.2.1
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow (f := p * f₀ * 2) (by rw [hK, ← pow_mul])
  have hU : UnitaryFieldData 2 (p * f₀) K := unitaryFieldData_two hK hf1
  have hm : Models.LieModel T .PSU n 2 (p * f₀) := ⟨hadm, Or.inl hcl⟩
  have hT0 : Subgroup.center T = ⊥ := center_eq_bot_of_cover hq.1 π hπ hcl
  have hdvd := card_ker_dvd_multiplier_cls hq π hπ hker hGA hm
  rw [card_multiplier_psu_eq (Or.inr (by omega : 2 ≤ p * f₀))] at hdvd
  have hpQ : ¬ p ∣ 2 ^ (p * f₀) := fun h => hp2
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hlr : ∀ r : ℕ, r.Prime →
      localRank r T = localRank r (StatedProj (StatedSU n (2 ^ (p * f₀)) K)) :=
    fun r hr => CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr
  have hrank1 : ¬ p ∣ 2 ^ (p * f₀) + 1 → n / orderOf (-((2 ^ (p * f₀) : ℕ) : ZMod p)) ≤ 1 →
      CFSG.pRank p T ≤ 1 := by
    intro hpq' h
    have hN : ¬ p ∣ Nat.card
        ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ (p * f₀)) K)) := by
      rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by omega)).2.2]
      exact fun hd => hpq' (hd.trans (Nat.gcd_dvd_right _ _))
    rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e]
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hN]
    exact pRank_statedSU_le_one hp hp2 hK hpQ (by omega) h
  by_cases hn7 : 7 ≤ n
  ·
    exfalso
    set π' : J →* StatedProj (StatedSU n (2 ^ (p * f₀)) K) :=
      (e : T →* StatedProj (StatedSU n (2 ^ (p * f₀)) K)).comp π with hπ'
    have hπ's : Function.Surjective π' := e.surjective.comp hπ
    have hπ'c : π'.ker ≤ Subgroup.center J := by
      intro x hx
      apply hker
      rw [MonoidHom.mem_ker] at hx ⊢
      exact (map_eq_one_iff e e.injective).1 hx
    obtain ⟨ρ, hρs, hρk⟩ := exists_cover_psu hGA hn7 hf1 hK hq.1 π' hπ's hπ'c
    obtain ⟨r, hr, hr2, hrq⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf1
    have h4 := le_localRank_of_surjective_statedSU_torus (k := 3) hU hr hrq (by omega)
      (Or.inl (by omega)) ρ hρs hρk
    have h3 := (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans he
    omega
  by_cases hn6 : n = 6
  ·
    exfalso
    subst hn6
    obtain ⟨s, hs, hs5, hsd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_prime_five_le_dvd_two_pow_add_one
        (by omega : 2 ≤ p * f₀) (by omega : p * f₀ ≠ 3)
    have hn6s : ¬ s ∣ 6 := by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases s <;> first | omega | exact absurd hs (by norm_num)
    have h4 := CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (k := 3) hU hs hsd
      (by norm_num) (Or.inr hn6s)
    have hsZ : ¬ s ∣ Nat.card π.ker := fun hd => hn6s (hd.trans (hdvd.trans (Nat.gcd_dvd_left _ _)))
    have h3 := localRank_le_three_of_cover π hπ he hs (by omega) hsZ
    rw [hlr s hs] at h3
    omega
  have hn' : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_two_pow
  by_cases hpq' : p ∣ 2 ^ (p * f₀) + 1
  ·
    have hpg : p ∣ 2 ^ f₀ + 1 := dvd_two_pow_add_one_of_mul hp hpq'
    obtain ⟨e', m, m', he2, hm', hm'p, hmm, hmp⟩ := K1214.lte_plus hp hp2 hpg
    rcases hn' with rfl | rfl | rfl
    ·
      refine ⟨e', he2, ?_, ?_⟩
      · exact K1214.sylowShape_of_psu3Model hp hp2 hp3 (by omega) hmm hmp hcl
      · have hXc : Blueprint.LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .PSU 3 2 f₀ := by
          rcases hX with hX | ⟨ht, -⟩
          · exact hX
          · exact absurd ht (by decide)
        have hclN := K1214.statedClassicalModel_of_lieModel_of_tag' (Or.inl rfl) hXc
        have hmN : Models.LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .PSU 3 2 f₀ :=
          ⟨hclN.1, Or.inl hclN⟩
        have hNZ : ¬ p ∣ Nat.card (Subgroup.center ↥(fixRes α)) := by
          intro hd
          have h2 := (hd.trans (card_center_fixRes_dvd α hGA hmN)).trans
            (card_multiplier_psu_eq (n := 3) (f := f₀) (Or.inl ⟨by norm_num, by norm_num⟩)
              ▸ Nat.gcd_dvd_left 3 (2 ^ f₀ + 1))
          exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h2)
        exact sylowShape_of_center_quotient hp hNZ
          (K1214.sylowShape_of_psu3Model hp hp2 hp3 (by omega) hm' hm'p hclN)
    ·
      exfalso
      exact false_of_row kf122Row9_holds hp hp5 hT0
        ⟨p * f₀, hf1, hpq', statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn hLRA
    ·
      exfalso
      have h3 : 3 ≤ localRank p (StatedProj (StatedSU 5 (2 ^ (p * f₀)) K)) := by
        by_cases hp5' : p = 5
        · subst hp5'
          have hp25 : 5 ^ 2 ∣ 2 ^ (5 * f₀) + 1 := by
            refine ⟨5 ^ (e' - 2) * m, ?_⟩
            rw [hmm, ← mul_assoc, ← pow_add]
            congr 2
            omega
          exact le_localRank_statedSU_lift hU hp hp2 hp25 (dvd_refl 5) (by norm_num) (by norm_num)
        · refine CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (k := 2) hU hp hpq'
            (by norm_num) (Or.inr ?_)
          exact fun hd => hp5' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hd)
      rw [← hlr p hp] at h3
      exact false_of_three_le_localRank hp hLR2 h3
  · by_cases hpq : p ∣ 2 ^ (p * f₀) - 1
    ·
      exfalso
      rcases hn' with rfl | rfl | rfl
      ·
        have hd2 := two_le_orderOf_neg_of_not_dvd hp hpQ hpq'
        have := hrank1 hpq' ((Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega))))
        omega
      · exact false_of_row kf122Row5_holds hp hp5 hT0
          ⟨p * f₀, hf1, hpq, statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn hLRA
      · exact false_of_row kf122Row6_holds hp hp5 hT0
          ⟨p * f₀, hf1, hpq, statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn hLRA
    ·
      exfalso
      have hd3 := three_le_orderOf_neg_of_not_dvd hp hpQ hpq hpq' hq1
      have := hrank1 hpq' (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
      omega

end CFSG.RankThree.PartOne
