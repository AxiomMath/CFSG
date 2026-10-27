module

public import CFSG.Quasithin.AppendixH.H16.OctadZSub
public import CFSG.Quasithin.AppendixH.H16.OctadZGroup
public import CFSG.Quasithin.AppendixH.H16.MaskSup

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

theorem exists_mask (P : ℕ → Prop) (k : ℕ) :
    ∃ n < 2 ^ k, ∀ p < k, (P p ↔ n.testBit p = true) := by
  induction k with
  | zero => exact ⟨0, by norm_num, fun p hp => by omega⟩
  | succ k ih =>
    obtain ⟨n, hn, hnP⟩ := ih
    classical
    have hpow : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_succ (by norm_num : 1 < 2)
    refine ⟨if P k then n ||| 2 ^ k else n, ?_, ?_⟩
    · by_cases hP : P k
      · rw [if_pos hP]
        exact Nat.or_lt_two_pow (lt_trans hn hpow) hpow
      · rw [if_neg hP]
        exact lt_trans hn hpow
    · intro p hp
      have hp' : p < k ∨ p = k := by omega
      rcases hp' with hp | hpk
      · by_cases hP : P k
        · rw [if_pos hP, hnP p hp, Nat.testBit_lor, Nat.testBit_two_pow]
          have hne : k ≠ p := by omega
          rw [decide_eq_false_iff_not.mpr hne]
          simp
        · rw [if_neg hP]
          exact hnP p hp
      · subst p
        by_cases hP : P k
        · rw [if_pos hP]
          constructor
          · intro _
            rw [Nat.testBit_lor, Nat.testBit_two_pow, Nat.testBit_lt_two_pow hn]
            simp
          · intro _; exact hP
        · rw [if_neg hP]
          constructor
          · intro h; exact absurd h hP
          · intro h
            rw [Nat.testBit_lt_two_pow hn] at h
            exact absurd h (by simp)

private theorem xorF_two_mul (p q : ℕ) (hp : p < 8) (hq : q < 8)
    (hp' : 2 * p < 16) (hq' : 2 * q < 16) (hpq' : 2 * (p ^^^ q) < 16) :
    xorF (⟨2 * p, hp'⟩ : Fin 16) (⟨2 * q, hq'⟩ : Fin 16) =
      ⟨2 * (p ^^^ q), hpq'⟩ := by
  apply Fin.ext
  simp only [xorF, Fin.val_mk]
  interval_cases p <;> interval_cases q <;> decide

private theorem dPerm_odd_eq (p : ℕ) (hp : p < 8) (h2p : 2 * p < 16) (hodd : 2 * p + 1 < 16) :
    dPerm ⟨2 * p + 1, hodd⟩ = dPerm ⟨2 * p, h2p⟩ * dPerm 1 := by
  rw [dPerm_mul]
  congr 1
  apply Fin.ext
  simp only [xorF, Fin.val_mk]
  interval_cases p <;> decide

theorem exists_dSub_key {B : Subgroup S24} (hz : koPerm 1 ∈ B) (hB : B ≤ dGrp) :
    ∃ n ∈ dSubList, ∀ u : Fin 16, (dPerm u ∈ B ↔ dSubMem n u = true) := by
  classical
  obtain ⟨n, hn, hnP⟩ :=
    exists_mask (fun p => ∃ h : 2 * p < 16, dPerm (⟨2 * p, h⟩ : Fin 16) ∈ B) 8
  have hn256 : n < 256 := by
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num] at hn
    exact hn
  have hP0 : (∃ h : 2 * 0 < 16, dPerm (⟨2 * 0, h⟩ : Fin 16) ∈ B) := by
    refine ⟨by norm_num, ?_⟩
    simpa [dPerm_zero] using B.one_mem
  have hnodd : n % 2 = 1 :=
    Nat.mod_two_eq_one_iff_testBit_zero.mpr ((hnP 0 (by norm_num)).1 hP0)
  have hclosed : dSubClosed n = true := by
    rw [dSubClosed, List.all_eq_true]
    intro p hp
    rw [List.all_eq_true]
    intro q hq
    rw [List.mem_range] at hp hq
    by_cases hpq : (n.testBit p && n.testBit q) = true
    · rw [hpq]
      simp only [Bool.not_true, Bool.false_or]
      have hpq' := hpq
      rw [Bool.and_eq_true] at hpq'
      have hpn : n.testBit p = true := hpq'.1
      have hqn : n.testBit q = true := hpq'.2
      obtain ⟨hup, hmp⟩ := (hnP p hp).2 hpn
      obtain ⟨huq, hmq⟩ := (hnP q hq).2 hqn
      have hpq8 : p ^^^ q < 8 := by
        have hx := Nat.xor_lt_two_pow (show p < 2 ^ 3 by omega) (show q < 2 ^ 3 by omega)
        simpa using hx
      have Hpq : 2 * (p ^^^ q) < 16 := by omega
      have hmul : dPerm (xorF (⟨2 * p, hup⟩ : Fin 16) (⟨2 * q, huq⟩ : Fin 16)) ∈ B := by
        rw [← dPerm_mul]
        exact B.mul_mem hmp hmq
      have hkey' : dPerm ⟨2 * (p ^^^ q), Hpq⟩ ∈ B := by
        rw [← xorF_two_mul p q hp hq hup huq Hpq]
        exact hmul
      exact (hnP (p ^^^ q) hpq8).1 ⟨Hpq, hkey'⟩
    · have hf : (n.testBit p && n.testBit q) = false := by
        cases hh : (n.testBit p && n.testBit q)
        · rfl
        · exact absurd hh hpq
      rw [hf]
      rfl
  have hnD : n ∈ dSubList := dSub_classify n hn256 hnodd hclosed
  refine ⟨n, hnD, ?_⟩
  intro u
  have hp8 : (u : ℕ) / 2 < 8 := by omega
  have H2p : 2 * ((u : ℕ) / 2) < 16 := by omega
  have hkeyu :
      (dPerm ⟨2 * ((u : ℕ) / 2), H2p⟩ ∈ B ↔ n.testBit ((u : ℕ) / 2) = true) := by
    have hPiff :
        (∃ h : 2 * ((u : ℕ) / 2) < 16,
            dPerm (⟨2 * ((u : ℕ) / 2), h⟩ : Fin 16) ∈ B) ↔
          dPerm ⟨2 * ((u : ℕ) / 2), H2p⟩ ∈ B := by
      refine ⟨?_, fun hb => ⟨H2p, hb⟩⟩
      rintro ⟨h, hb⟩
      have he : (⟨2 * ((u : ℕ) / 2), h⟩ : Fin 16) = ⟨2 * ((u : ℕ) / 2), H2p⟩ := by
        apply Fin.ext
        rfl
      rwa [he] at hb
    exact hPiff.symm.trans (hnP ((u : ℕ) / 2) hp8)
  by_cases hu : (u : ℕ) % 2 = 0
  · have hueq : u = (⟨2 * ((u : ℕ) / 2), H2p⟩ : Fin 16) := by
      apply Fin.ext
      simp only [Fin.val_mk]
      have := Nat.div_add_mod (u : ℕ) 2
      omega
    have hdperm : dPerm u = dPerm ⟨2 * ((u : ℕ) / 2), H2p⟩ := congrArg dPerm hueq
    rw [hdperm]
    exact hkeyu
  · have hu1 : (u : ℕ) % 2 = 1 := by
      have := Nat.mod_lt (u : ℕ) (by norm_num : 0 < 2)
      omega
    have Hodd : 2 * ((u : ℕ) / 2) + 1 < 16 := by omega
    have hodd : u = (⟨2 * ((u : ℕ) / 2) + 1, Hodd⟩ : Fin 16) := by
      apply Fin.ext
      simp only [Fin.val_mk]
      have := Nat.div_add_mod (u : ℕ) 2
      omega
    have hdperm : dPerm u = dPerm ⟨2 * ((u : ℕ) / 2), H2p⟩ * dPerm 1 :=
      (congrArg dPerm hodd).trans (dPerm_odd_eq ((u : ℕ) / 2) hp8 H2p Hodd)
    rw [hdperm, Subgroup.mul_mem_cancel_right B (by rw [dPerm_one]; exact hz)]
    exact hkeyu

private theorem dSubMem_mod (n : ℕ) (u : Fin 16) :
    dSubMem (n % 256) u = dSubMem n u := by
  have hu : (u : ℕ) / 2 < 8 := by omega
  simp only [dSubMem]
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow]
  rw [decide_eq_true hu, Bool.true_and]

private theorem dSubCard_mod (n : ℕ) : dSubCard (n % 256) = dSubCard n := by
  rw [dSubCard]
  apply List.countP_congr
  intro p hp
  rw [List.mem_range] at hp
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow]
  rw [decide_eq_true hp, Bool.true_and]

private theorem card_filter_dSubMem_fin :
    ∀ n : Fin 256,
      (Finset.univ.filter fun u : Fin 16 => dSubMem n.1 u = true).card = 2 * dSubCard n.1 := by
  decide +kernel

theorem card_eq_of_dSub_key {B : Subgroup S24} (hB : B ≤ dGrp) {n : ℕ}
    (h : ∀ u : Fin 16, (dPerm u ∈ B ↔ dSubMem n u = true)) :
    Nat.card ↥B = 2 * dSubCard n := by
  have hcard1 : Nat.card ↥B = Nat.card {u : Fin 16 // dPerm u ∈ B} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun b => ⟨(mem_dGrp_iff.mp (hB b.2)).choose, by
          rw [(mem_dGrp_iff.mp (hB b.2)).choose_spec]
          exact b.2⟩
        invFun := fun u => ⟨dPerm u.1, u.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro b
      apply Subtype.ext
      exact (mem_dGrp_iff.mp (hB b.2)).choose_spec
    · intro u
      apply Subtype.ext
      exact dPerm_injective (mem_dGrp_iff.mp (hB u.2)).choose_spec
  have hcard2 : Nat.card {u : Fin 16 // dPerm u ∈ B} =
      Nat.card {u : Fin 16 // dSubMem n u = true} :=
    Nat.card_congr (Equiv.subtypeEquivRight h)
  rw [hcard1, hcard2]
  show Nat.card ↥({u : Fin 16 | dSubMem n u = true} : Set (Fin 16)) = 2 * dSubCard n
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  have hmod : (Finset.univ.filter fun u : Fin 16 => dSubMem n u = true) =
      (Finset.univ.filter fun u : Fin 16 => dSubMem (n % 256) u = true) := by
    apply Finset.filter_congr
    intro u _
    rw [dSubMem_mod n u]
  rw [hmod, card_filter_dSubMem_fin ⟨n % 256, Nat.mod_lt n (by norm_num)⟩, dSubCard_mod]

theorem fixV_eq_maskSub_of_dSub_key {B : Subgroup S24} (hB : B ≤ dGrp) {n : ℕ} (hn : n ∈ dSubList)
    (h : ∀ u : Fin 16, (dPerm u ∈ B ↔ dSubMem n u = true)) :
    fixV (rImg (rhoC11 AutPerm le_rfl) B) = maskSub 11 (dSubBasis n) := by
  ext x
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  rw [mem_fixV, toW_mem_maskSub_iff_of_lt (dSub_lt n hn) hm,
    ← dSub_fixed n hn m hm]
  constructor
  · intro hfix u hu hmem
    have hb : dPerm ⟨u, hu⟩ ∈ B := (h ⟨u, hu⟩).2 hmem
    have hX : rhoC11 AutPerm le_rfl (⟨dPerm ⟨u, hu⟩, dPerm_mem_M24g ⟨u, hu⟩⟩ : ↥AutPerm) ∈
        rImg (rhoC11 AutPerm le_rfl) B := by
      rw [rImg]
      apply Subgroup.mem_map_of_mem
      rw [Subgroup.mem_subgroupOf]
      exact hb
    have hg := hfix _ hX
    rw [rhoC11_dPerm] at hg
    exact toW_inj (actC11_lt (dArr u) m) hm hg
  · intro hfix g hg
    rw [rImg] at hg
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
    have hbB : (b : S24) ∈ B := Subgroup.mem_subgroupOf.mp hb
    obtain ⟨u, hu⟩ := mem_dGrp_iff.mp (hB hbB)
    have hb_eq : b = (⟨dPerm u, dPerm_mem_M24g u⟩ : ↥AutPerm) := Subtype.ext hu.symm
    rw [hb_eq, rhoC11_dPerm]
    rw [hfix u.1 u.2 ((h u).1 (by rw [hu]; exact hbB))]

theorem clause7_std :
    ∀ B : Subgroup S24, koPerm 1 ∈ B → B ≤ dGrp →
      rk ↥(fixV (rImg (rhoC11 AutPerm le_rfl) B)) = 8 - rk ↥B := by
  intro B hz hB
  obtain ⟨n, hn, h⟩ := exists_dSub_key hz hB
  rw [fixV_eq_maskSub_of_dSub_key hB hn h, rk_maskSub (dSub_lt n hn) (dSub_nodup n hn)]
  obtain ⟨k, hk5, hk1, hk2, hlen⟩ := dSub_rank n hn
  have hcard : Nat.card ↥B = 2 * dSubCard n := card_eq_of_dSub_key hB h
  have hBcard : Nat.card ↥B = 2 ^ k := by rw [hcard, hk2]
  have hrk : rk ↥B = k := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [rk, hBcard, padicValNat.prime_pow]
  rw [hrk]
  omega

end CFSG.ASVolI.H16