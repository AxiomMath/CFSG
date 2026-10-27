module

public import CFSG.Quasithin.Background.PRankCommuteMod
public import CFSG.Quasithin.Vol2.Ch8Sec2L829C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H

section L829R3

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_comp {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {H X C : Subgroup G}
    {f : G} (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hHp : ∀ x ∈ H, x ^ p = 1 → x ∈ C)
    (hXC : ⁅X, C⁆ ≤ pCoreOf 2 X) (hQC : pCoreOf 2 X ≤ Subgroup.normalizer (C : Set G))
    (hfX : f ∈ X) (hfp : f ^ p = 1) (hfC : f ∉ C) (hm : CFSG.Open.pRank p (H ⊔ X) ≤ 2) :
    CFSG.Open.pRank p H ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  set Q := pCoreOf 2 X with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hQp : ¬ p ∣ Nat.card Q := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 hQ2
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h))
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    hHX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hbot : CFSG.Open.IsElemAbelian p (⊥ : Subgroup G) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  refine csSup_le ⟨0, ⊥, bot_le, hbot, by rw [Subgroup.card_bot, pow_zero]⟩ ?_
  rintro k ⟨E, hEH, hE, hEc⟩
  have hEC : E ≤ C := fun e he => hHp e (hEH he) (hE.2 e he)
  have hcomm : ⁅E, Subgroup.zpowers f⁆ ≤ Q := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hfX) hEC).trans hXC
  have hfE : f ∉ E ⊔ Q := fun hf =>
    hfC (mem_of_mem_sup_of_pow_eq_one hQC hQ2 (sup_le_sup_right hEC Q hf) hpodd hfp)
  have h1 := succ_le_pRank_of_commute_mod hQp (hEH.trans hHQ) (hXQ hfX) hE hEc hfp hcomm hfE
    (hEH.trans le_sup_left) (Subgroup.mem_sup_right hfX)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans le_sup_right)
  omega

theorem pRank_le_one_82 (hmod : StmtFSUModule) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    {H : Subgroup G} {h : G} {k : ℕ} (hH : IsHStar T (fsuM T L) H) (hC : Concl822 T L I H h k)
    (hC5 : Concl825 T L I h k) (hC8 : Concl828 T L I h)
    (hf : ∃ f ∈ ch82LU L (ch82U (fsuV T I) h), f ^ p = 1 ∧
      f ∉ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) :
    H = ch82I (fsuV T I) h ⊔ T ∧ CFSG.Open.pRank p H ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  obtain ⟨-, hhI, hIC, hZ1, -, -, hMIeq, hker, -, hcases, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, hTU, -, -, hUZ, -, hIU⟩ := hC5
  obtain ⟨hN1, hN2, -⟩ := hC8
  set U := ch82U (fsuV T I) h with hUdef
  set LU := ch82LU L U with hLUdef
  have hHIT : H = ch82I (fsuV T I) h ⊔ T :=
    eq_ch82I_sup_82 hyp.fsu.sylow hH hIC.1 hMIeq
      (not_le_normalizer_ch82I_82 hV hhI hker (nontrivial_star_82 hcases))
  refine ⟨hHIT, ?_⟩
  obtain ⟨f, hfLU, hfp, hfC⟩ := hf
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hIN : ch82I (fsuV T I) h ≤ Subgroup.normalizer (U : Set G) :=
    hIU.trans (Subgroup.centralizer_le_normalizer _)
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := by
    rw [hHIT]
    exact sup_le hIN hTU
  have hLUU : LU ≤ Subgroup.normalizer (U : Set G) := (perfectCore_le _).trans inf_le_right
  have hHp : ∀ x ∈ H, x ^ p = 1 → x ∈ Subgroup.centralizer (U : Set G) := by
    intro x hx hxp
    rw [hHIT] at hx
    exact mem_of_mem_sup_of_pow_eq_one (B6.le_normalizer_centralizer hTU) hT2
      (sup_le_sup_right hIU T hx) hpodd hxp
  have hUV : U ≤ fsuV T I := inf_le_left
  have hU2 : IsPGroup 2 U := hT2.to_le (hUV.trans (fsuV_le_T hyp.fsu hV hN))
  have hUH : U ≤ H := by
    rw [hUZ]
    exact inf_le_left.trans (le_sup_left.trans hIC.1)
  have hUO : U ≤ pCoreOf 2 (H ⊔ LU) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hUH.trans le_sup_left)
      (sup_le hHU hLUU) hU2
  have hU1 : U ≠ ⊥ := by
    rw [hUZ]
    exact hZ1
  have hm : CFSG.Open.pRank p (H ⊔ LU) ≤ 2 :=
    CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke
      (fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hUO))) hp.out hp2
  exact pRank_le_one_of_comp hp2 (hHU.trans hN1) hHp hN2
    (((CFSG.LieType.BorelTits.pCoreOf_le 2 LU).trans hLUU).trans
      (B6.le_normalizer_centralizer le_rfl)) hfLU hfp hfC hm

theorem pRank_three_le_one_82 (hmod : StmtFSUModule) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) [hc : IsMulCommutative ↥(fsuV T I)] {H : Subgroup G} {h : G}
    {k : ℕ} (hH : IsHStar T (fsuM T L) H) (hC : Concl822 T L I H h k)
    (hC5 : Concl825 T L I h k) (hC8 : Concl828 T L I h)
    (hf : ∃ f ∈ ch82LU L (ch82U (fsuV T I) h), f ^ 3 = 1 ∧
      f ∉ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) :
    H = ch82I (fsuV T I) h ⊔ T ∧ CFSG.Open.pRank 3 H ≤ 1 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  pRank_le_one_82 hmod (by norm_num) hyp hH hC hC5 hC8 hf

end L829R3

end CFSG.Quasithin.H13
