module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKStar
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNj
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKS9Main
public import CFSG.Quasithin.Vol2.Ch8Sec2L822A

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.L829N
open scoped IsMulCommutative commutatorElement

theorem l3M22Nonsolv_noKantor (hL : NKLeaves) (hmod : StmtFSUModule) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5)
    (h331 : Stmt3_3_1) (hC58 : TheoremC58) (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (hE22 : E2.E22StatementNoN) (hD3 : StmtD3L3M22)
    (hF : StmtFelemL3M22) (hD4 : StmtD4L3M22) (hS3 : Step828Three) : L3M22Nonsolv := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hrow'
  by_contra hns
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  obtain ⟨hmin, hsq, hchar, hHMN⟩ :=
    setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hC8 := h828 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, -⟩ := hE22 G H T (H ⊓ fsuM T L) hmin hsq hns
  have hr3 : CFSG.Open.pRank 3 H ≤ 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (pRank_le_one_82 hmod (by norm_num) hyp hH hC hC5 hC8
      (hF G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' 3 (Or.inl rfl))).2
  have hr5 : CFSG.Open.pRank 5 H ≤ 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact (pRank_le_one_82 hmod (by norm_num) hyp hH hC hC5 hC8
      (hF G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' 5 (Or.inr rfl))).2
  obtain ⟨hs, hna, hsolv⟩ := star_facts_of_cases hcases hKc hHK hq
  have hT : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hTH : T ≤ H := hT.1
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hTM : T ≤ fsuM T L := by
    show T ≤ Subgroup.normalizer (fsuL0 T L : Set G)
    rw [hL0]
    exact hTL
  have hHIT : H = ch82I (fsuV T I) h ⊔ T := H_eq_ch82I_sup_T_829 hmod hyp hH hC
  obtain ⟨-, -, -, -, -, -, -, hker, -⟩ := id hC
  have hVJ : ¬ fsuV T I ≤ kerIn (H ⊓ fsuM T L) H := by
    intro hVJ'
    apply hH.2.1
    have hJN : H ≤ Subgroup.normalizer (kerIn (H ⊓ fsuM T L) H : Set G) := le_normalizer_kerIn _ _
    have hVh : B6.conjSub h (fsuV T I) ≤ kerIn (H ⊓ fsuM T L) H := by
      intro x hx
      rw [B6.mem_conjSub] at hx
      have h1 := (Subgroup.mem_normalizer_iff.mp (hJN hh) (h⁻¹ * x * h)).mp (hVJ' hx)
      simpa [mul_assoc] using h1
    calc H = ch82I (fsuV T I) h ⊔ T := hHIT
      _ ≤ kerIn (H ⊓ fsuM T L) H ⊔ T := sup_le_sup_right (sup_le hVJ' hVh) T
      _ ≤ fsuM T L := sup_le (kerIn_le.trans inf_le_right) hTM
  have hStep8 : T ≤ Subgroup.normalizer (K : Set G) → ∀ n : ℕ, 2 ≤ n →
      IsPSL 2 2 n ↥(E2.star (H ⊓ fsuM T L) H K) →
      E2.IsBorelIn (E2.star (H ⊓ fsuM T L) H K)
        (E2.star (H ⊓ fsuM T L) H ((H ⊓ fsuM T L) ⊓ K)) → False := by
    intro hTK n hn hL' hBor
    exact l2_branch_dih hT hTM hHK hTK hVT hV hVJ hHMN hh hker
      (hD3 G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow') hn hL' hBor
  have hfork : T ≤ Subgroup.normalizer (K : Set G) →
      UIn ↥(E2.star (H ⊓ fsuM T L) H K) →
      UOut ↥(E2.star (H ⊓ fsuM T L) H K)
        ((E2.star (H ⊓ fsuM T L) H ((H ⊓ fsuM T L) ⊓ K)).subgroupOf
          (E2.star (H ⊓ fsuM T L) H K)) → False := by
    intro hTK hIn hOut
    exact nk_fork_star hT hTM hHK hTK hs hna (hVT.trans hTH) hV hVJ hHMN
      (nk_star_step hmod hD4 hS3 h825 h828 hyp h731 h821 hrow hH hh hC hrow' hKc hTK hs hsolv)
      hIn hOut
  have hres := sweep_noKantor hL hcases hKc hHK hT hr3 hr5 hs hna hfork hStep8
  exact nk_step9_core hL hmod hD4 hS3 h825 h828 hyp h731 h821 hrow hH hh hC hrow' hKc hHK hq hres
    hTM hHMN hVJ

end CFSG.Quasithin.H13.L829NK
