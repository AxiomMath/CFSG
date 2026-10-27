module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge
import CFSG.LocalAnalysis.StandardType.GGQTwoTransvectionFreeRules

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmCommonAux_dFun_eq_zero_iff {n : ℕ} {ρ : ZMod 3} {h v : DV n}
    (hh : dB ρ h h ≠ 0) : dFun ρ h v = 0 ↔ dB ρ h v = 0 := by
  rw [dFun_apply]
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (mul_ne_zero (by decide) hh)
    · exact h1
  · intro h0
    simp [h0]

private lemma hdRo7DSmCommonAux_fin_check :
    ∀ (ρ ρ' x a : ZMod 3), ρ ≠ 0 → ρ' ≠ 0 → x ≠ 0 → ρ ≠ ρ' →
      (ρ * x + a = 0 ↔ ρ' * x + a = 0) → a = 0 := by
  decide

private lemma hdRo7DSmCommonAux_sum_zero {n : ℕ} {H A : Subgroup (DGL n)}
    (hD : DLinData 3 n (DV n) (dStd n) H A) {ρ ρ' : ZMod 3} {r r' : DGL n} {h h' : DV n}
    (hrH : r ∈ H) (hr'H : r' ∈ H) (hρ : ρ ≠ 0) (hρ' : ρ' ≠ 0)
    (hh0 : h 0 ≠ 0) (hh'0 : h' 0 ≠ 0) (hr : DRefl ρ r h) (hr' : DRefl ρ' r' h')
    (hne : ρ ≠ ρ') :
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod 3), DSPData σ c →
      ∑ i : Fin n, h i.succ * dAct σ c h' i.succ = 0 := by
  have hTF : CFSG.StandardType.QTwoLin.TransvectionFree H := by
    intro g hg hgt
    exact hD.hNoT g (hD.hHA hg)
      (CFSG.StandardType.HdRo7SU.Small.c2Transv_of_isTransvectionLin g hgt)
  intro σ c hd
  have hhc : ∀ i, c i = 1 ∨ c i = -1 := hd.2.2.1
  have hwH : dActL σ c hhc ∈ H := hD.hPH _ (dsp_dActL hd)
  have hsH : dActL σ c hhc * r' * (dActL σ c hhc)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hwH hr'H) (H.inv_mem hwH)
  have hs : DRefl ρ' (dActL σ c hhc * r' * (dActL σ c hhc)⁻¹) (dAct σ c h') :=
    dRefl_conj_dActL hd.1 hhc hr'
  have hzp := CFSG.StandardType.QTwoLin.zero_pair_iff_of_transvectionFree (K := ZMod 3) hTF
    hrH hsH (dFun_self hr.1) (dFun_self hs.1)
    (fun v => dRefl_apply hr v) (fun v => dRefl_apply hs v)
  have hdB : dB ρ h (dAct σ c h') = 0 ↔ dB ρ' (dAct σ c h') h = 0 := by
    rw [← hdRo7DSmCommonAux_dFun_eq_zero_iff hr.1, hzp,
      hdRo7DSmCommonAux_dFun_eq_zero_iff hs.1]
  have hsymm0 : σ.symm 0 = 0 := by
    have h := Equiv.symm_apply_apply σ 0
    rwa [hd.1] at h
  have hg0 : dAct σ c h' 0 = h' 0 := by
    simp only [dAct, hsymm0, hd.2.1, one_mul]
  have hxne : h 0 * dAct σ c h' 0 ≠ 0 :=
    mul_ne_zero hh0 (by rw [hg0]; exact hh'0)
  have hxeq : ρ * (h 0 * dAct σ c h' 0) +
        (∑ i : Fin n, h i.succ * dAct σ c h' i.succ) = 0 ↔
      ρ' * (h 0 * dAct σ c h' 0) +
        (∑ i : Fin n, h i.succ * dAct σ c h' i.succ) = 0 := by
    have hda : dB ρ h (dAct σ c h')
        = ρ * (h 0 * dAct σ c h' 0) +
          ∑ i : Fin n, h i.succ * dAct σ c h' i.succ := by
      simp only [dB]
      ring
    have hdb : dB ρ' (dAct σ c h') h
        = ρ' * (h 0 * dAct σ c h' 0) +
          ∑ i : Fin n, h i.succ * dAct σ c h' i.succ := by
      simp only [dB]
      rw [show (∑ i : Fin n, dAct σ c h' i.succ * h i.succ)
            = ∑ i : Fin n, h i.succ * dAct σ c h' i.succ from
          Finset.sum_congr rfl fun i _ => mul_comm _ _]
      ring
    rw [hda, hdb] at hdB
    exact hdB
  exact hdRo7DSmCommonAux_fin_check ρ ρ' (h 0 * dAct σ c h' 0)
    (∑ i : Fin n, h i.succ * dAct σ c h' i.succ) hρ hρ' hxne hne hxeq

private lemma hdRo7DSmCommonAux_contradiction {n : ℕ} (hn : 6 ≤ n) {h h' : DV n}
    (hsh : dSupp h ≠ 0) (hsh' : dSupp h' ≠ 0)
    (hsum : ∀ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod 3), DSPData σ c →
      ∑ i : Fin n, h i.succ * dAct σ c h' i.succ = 0) : False := by
  have hsupp_h : ∃ i : Fin n, h i.succ ≠ 0 := by
    have hpos : 0 < (Finset.univ.filter fun i : Fin n => h i.succ ≠ 0).card := by
      rw [dSupp] at hsh
      exact Nat.pos_of_ne_zero hsh
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  obtain ⟨i, hi⟩ := hsupp_h
  have hsupp_h' : ∃ j : Fin n, h' j.succ ≠ 0 := by
    have hpos : 0 < (Finset.univ.filter fun j : Fin n => h' j.succ ≠ 0).card := by
      rw [dSupp] at hsh'
      exact Nat.pos_of_ne_zero hsh'
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  obtain ⟨j, hj⟩ := hsupp_h'
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.succ j.succ
  have hσ0 : σ 0 = 0 := by
    show Equiv.swap i.succ j.succ (0 : Fin (n + 1)) = 0
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  have hσsymm : σ.symm i.succ = j.succ := by
    show (Equiv.swap i.succ j.succ).symm i.succ = j.succ
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  let T : Fin n → ZMod 3 := fun k => h k.succ * h' (σ.symm k.succ)
  have hsum_d : ∀ d : Fin (n + 1) → ZMod 3, d 0 = 1 →
      (∀ m, d m = 1 ∨ d m = -1) → (∏ m, d m) = 1 →
      ∑ k : Fin n, d k.succ * T k = 0 := by
    intro d hd0 hdval hdprod
    have hdsp : DSPData σ (fun m => d (σ m)) := by
      refine ⟨hσ0, ?_, ?_, ?_⟩
      · show d (σ 0) = 1
        rw [hσ0, hd0]
      · intro m
        exact hdval (σ m)
      · show ∏ m, d (σ m) = 1
        rw [Equiv.prod_comp σ d, hdprod]
    have h0 := hsum σ (fun m => d (σ m)) hdsp
    rw [← h0]
    apply Finset.sum_congr rfl
    intro k _
    show d k.succ * T k = h k.succ * dAct σ (fun m => d (σ m)) h' k.succ
    dsimp only [T]
    simp only [dAct, Equiv.apply_symm_apply]
    ring
  have hsum1 : ∑ k : Fin n, T k = 0 := by
    have h := hsum_d (fun _ => 1) rfl (fun m => Or.inl rfl) (by simp)
    simpa using h
  have hn2 : 2 < n := lt_of_lt_of_le (by norm_num : 2 < 6) hn
  have hpair : ∀ k l : Fin n, k ≠ l → T k + T l = 0 := by
    intro k l hkl
    have hkl' : k.succ ≠ l.succ := fun hh => hkl (Fin.succ_injective n hh)
    let d : Fin (n + 1) → ZMod 3 :=
      fun m => if m = k.succ then -1 else if m = l.succ then -1 else 1
    have hd0 : d 0 = 1 := by
      dsimp only [d]
      rw [if_neg (Fin.succ_ne_zero k).symm, if_neg (Fin.succ_ne_zero l).symm]
    have hdval : ∀ m, d m = 1 ∨ d m = -1 := by
      intro m
      dsimp only [d]
      by_cases hmk : m = k.succ
      · rw [if_pos hmk]; exact Or.inr rfl
      · rw [if_neg hmk]
        by_cases hml : m = l.succ
        · rw [if_pos hml]; exact Or.inr rfl
        · rw [if_neg hml]; exact Or.inl rfl
    have hdprod : ∏ m, d m = 1 := by
      have hprod2 := Fintype.prod_eq_mul (f := d) k.succ l.succ hkl' (by
        intro m hm
        obtain ⟨hmk, hml⟩ := hm
        dsimp only [d]
        rw [if_neg hmk, if_neg hml])
      rw [hprod2]
      dsimp only [d]
      rw [if_pos rfl, if_neg hkl'.symm, if_pos rfl]
      decide
    have hE := hsum_d d hd0 hdval hdprod
    have hdiff : ∑ k : Fin n, (d k.succ - 1) * T k = 0 := by
      have hcongr : ∑ k : Fin n, (d k.succ - 1) * T k
          = ∑ k : Fin n, (d k.succ * T k - T k) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hcongr, Finset.sum_sub_distrib, hE, hsum1, sub_self]
    have hval : ∑ k : Fin n, (d k.succ - 1) * T k =
        (-2 : ZMod 3) * T k + (-2) * T l := by
      rw [Fintype.sum_eq_add (f := fun i => (d i.succ - 1) * T i) k l hkl (by
        intro i hi
        obtain ⟨hik, hil⟩ := hi
        have h1 : i.succ ≠ k.succ := fun hh => hik (Fin.succ_injective n hh)
        have h2 : i.succ ≠ l.succ := fun hh => hil (Fin.succ_injective n hh)
        dsimp only [d]
        rw [if_neg h1, if_neg h2]
        ring)]
      dsimp only [d]
      rw [if_pos rfl, if_neg hkl'.symm, if_pos rfl]
      ring
    have hzero : (-2 : ZMod 3) * T k + (-2) * T l = 0 := by
      rw [← hval, hdiff]
    have hneg2 : (-2 : ZMod 3) = 1 := by decide
    rw [hneg2] at hzero
    simpa using hzero
  obtain ⟨k, hki, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i hn2
  obtain ⟨l, hli, hlk⟩ := Fin.exists_ne_and_ne_of_two_lt i k hn2
  have hTik : T i + T k = 0 := hpair i k hki.symm
  have hTil : T i + T l = 0 := hpair i l hli.symm
  have hTkl : T k + T l = 0 := hpair k l hlk.symm
  have hTi0 : T i = 0 := by
    have h2 : (2 : ZMod 3) * T i = 0 := by
      linear_combination hTik + hTil - hTkl
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  have hTine : T i ≠ 0 := by
    dsimp only [T]
    rw [hσsymm]
    exact mul_ne_zero hi hj
  exact hTine hTi0


theorem dSmCommon_holds : DSmCommonLeaf := by
  intro n H A hD ρ ρ' r r' h h' hrH hr'H hρ hρ' hh0 hh'0 hsh hsh' hr hr'
  by_contra hne
  exact hdRo7DSmCommonAux_contradiction hD.hn hsh hsh'
    (hdRo7DSmCommonAux_sum_zero hD hrH hr'H hρ hρ' hh0 hh'0 hr hr' hne)

end CFSG.StandardType.HdRo7D.Small
