module

public import Certificates.Data.CFSGNative.ExcCensus.Core
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawInternal

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

noncomputable section

variable {m : Fin 6}

@[expose] def vec (m : Fin 6) (c : ℕ) : V m := fun k => (Chk.dig c k : ZMod 3)

@[expose] def code (m : Fin 6) (v : V m) : ℕ := ∑ k : Fin (dim m), (v k).val * 3 ^ (k : ℕ)

theorem nat_fold_add {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    Nat.fold n (fun k _ s => s + g k) 0 = ∑ k : Fin n, g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fold_succ]
    have h : Nat.fold n (fun k (_ : k < n) s => s + g k) 0 = ∑ k : Fin n, g k := ih
    rw [h, Fin.sum_univ_castSucc]
    simp

private theorem digit_sum_lt {d : ℕ} (a : Fin d → ℕ) (ha : ∀ k, a k < 3) :
    ∑ k : Fin d, a k * 3 ^ (k : ℕ) < 3 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    have ih' := ih (fun k : Fin d => a (Fin.castSucc k)) (fun k => ha _)
    calc (∑ k : Fin d, a (Fin.castSucc k) * 3 ^ ((Fin.castSucc k : ℕ))) +
          a (Fin.last d) * 3 ^ ((Fin.last d : ℕ))
        < 3 ^ d + a (Fin.last d) * 3 ^ ((Fin.last d : ℕ)) := Nat.add_lt_add_right ih' _
      _ = (a (Fin.last d) + 1) * 3 ^ d := by simp only [Fin.val_last]; ring
      _ ≤ 3 * 3 ^ d :=
          Nat.mul_le_mul_right _ (by have := ha (Fin.last d); omega)
      _ = 3 ^ (d + 1) := by ring

private theorem digit_sum_dig {d : ℕ} (a : Fin d → ℕ) (ha : ∀ k, a k < 3) {j : ℕ}
    (hj : j < d) : (∑ k : Fin d, a k * 3 ^ (k : ℕ)) / 3 ^ j % 3 = a ⟨j, hj⟩ := by
  induction d with
  | zero => omega
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases hjd : j < d
    · have ih' := ih (fun k : Fin d => a (Fin.castSucc k)) (fun k => ha _) hjd
      have hpow : 3 ^ d = 3 ^ (d - j) * 3 ^ j := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hdiv : (∑ k : Fin d, a (Fin.castSucc k) * 3 ^ (k : ℕ) +
            a (Fin.last d) * 3 ^ d) / 3 ^ j
          = (∑ k : Fin d, a (Fin.castSucc k) * 3 ^ (k : ℕ)) / 3 ^ j +
            a (Fin.last d) * 3 ^ (d - j) := by
        rw [hpow, ← mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num))]
      rw [hdiv]
      have h3 : a (Fin.last d) * 3 ^ (d - j) = 3 * (a (Fin.last d) * 3 ^ (d - j - 1)) := by
        have hdj : d - j = (d - j - 1) + 1 := by omega
        conv_lhs => rw [hdj]
        rw [Nat.pow_succ]
        ring
      rw [h3, Nat.add_mul_mod_self_left, ih']
      rfl
    · have hje : j = d := by omega
      subst hje
      rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num : 0 < 3)),
        Nat.div_eq_of_lt (digit_sum_lt (fun k : Fin j => a (Fin.castSucc k)) (fun k => ha _)),
        Nat.zero_add, Nat.mod_eq_of_lt (ha _)]
      rfl

private theorem ofDigits_eq_sum (d : ℕ) (f : ℕ → ℕ) :
    Chk.ofDigits d f = ∑ k : Fin d, (f k % 3) * 3 ^ (k : ℕ) := by
  unfold Chk.ofDigits
  rw [nat_fold_add]

private theorem dig_ofDigits (d : ℕ) (f : ℕ → ℕ) {j : ℕ} (hj : j < d) :
    Chk.dig (Chk.ofDigits d f) j = f j % 3 := by
  rw [Chk.dig, ofDigits_eq_sum]
  simpa using digit_sum_dig (d := d) (fun k : Fin d => f k % 3)
    (fun k => Nat.mod_lt _ (by norm_num)) hj

private theorem dig_code (m : Fin 6) (v : V m) {j : ℕ} (hj : j < dim m) :
    Chk.dig (code m v) j = (v ⟨j, hj⟩).val := by
  rw [Chk.dig]
  exact digit_sum_dig (fun k : Fin (dim m) => (v k).val) (fun k => ZMod.val_lt _) hj

private theorem code_vec_sum (m : Fin 6) (c : ℕ) :
    code m (vec m c) = ∑ k : Fin (dim m), Chk.dig c k * 3 ^ (k : ℕ) := by
  rw [code]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (vec m c k).val = Chk.dig c k := by
    rw [vec, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by rw [Chk.dig]; exact Nat.mod_lt _ (by norm_num))
  rw [h]

private theorem code_digits (m : Fin 6) (c : ℕ) :
    ∑ k : Fin (dim m), Chk.dig c k * 3 ^ (k : ℕ) = c % 3 ^ dim m := by
  induction dim m with
  | zero => simp [Nat.mod_one]
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hlast : Chk.dig c d * 3 ^ d = 3 ^ d * (c / 3 ^ d % 3) := by
      rw [Chk.dig, Nat.mul_comm]
    rw [hlast, ← Nat.mod_pow_succ]

theorem code_lt (m : Fin 6) (v : V m) : code m v < 3 ^ dim m := by
  simpa [code] using digit_sum_lt (fun k : Fin (dim m) => (v k).val) (fun k => ZMod.val_lt _)

theorem vec_code (m : Fin 6) (v : V m) : vec m (code m v) = v := by
  funext k
  change (Chk.dig (code m v) (k : ℕ) : ZMod 3) = v k
  rw [dig_code m v k.isLt, ZMod.natCast_zmod_val]

theorem code_vec (m : Fin 6) {c : ℕ} (hc : c < 3 ^ dim m) : code m (vec m c) = c := by
  rw [code_vec_sum, code_digits, Nat.mod_eq_of_lt hc]

theorem vec_zero (m : Fin 6) : vec m 0 = 0 := by
  funext k
  simp [vec, Chk.dig]

theorem combN_lt (m : Fin 6) (cv cy a b : ℕ) : Chk.combN (dim m) cv cy a b < 3 ^ dim m := by
  rw [Chk.combN, ofDigits_eq_sum]
  exact digit_sum_lt _ (fun k => Nat.mod_lt _ (by norm_num))

theorem vec_combN (m : Fin 6) (cv cy a b : ℕ) :
    vec m (Chk.combN (dim m) cv cy a b) = (a : ZMod 3) • vec m cv + (b : ZMod 3) • vec m cy := by
  funext k
  change (Chk.dig (Chk.combN (dim m) cv cy a b) (k : ℕ) : ZMod 3) = _
  rw [Chk.combN, dig_ofDigits _ _ k.isLt, ZMod.natCast_mod]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec]
  push_cast
  ring

@[expose] def ofMask (m : Fin 6) (n : ℕ) : Finset (Root m) :=
  Finset.univ.filter fun t => n.testBit t = true

@[simp] theorem mem_ofMask {n : ℕ} {t : Root m} : t ∈ ofMask m n ↔ n.testBit t = true := by
  simp [ofMask]

theorem mem_ofMask_land {n n' : ℕ} {t : Root m} :
    t ∈ ofMask m (n &&& n') ↔ t ∈ ofMask m n ∧ t ∈ ofMask m n' := by
  simp

private theorem card_filter_univ_fin (r : ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter (fun t : Fin r => p t = true)).card = (List.range r).countP p := by
  have hcard : ∀ n : ℕ, (Finset.univ.filter (fun t : Fin n => p t = true)).card
      = ∑ t : Fin n, (if p t then 1 else 0 : ℕ) := by
    intro n
    rw [Finset.card_filter]
  induction r with
  | zero => simp
  | succ r ih =>
    calc (Finset.univ.filter (fun t : Fin (r + 1) => p t = true)).card
        = ∑ t : Fin (r + 1), (if p t then 1 else 0 : ℕ) := hcard (r + 1)
      _ = (∑ t : Fin r, (if p t then 1 else 0 : ℕ)) + (if p r then 1 else 0 : ℕ) := by
          rw [Fin.sum_univ_castSucc]
          simp
      _ = (Finset.univ.filter (fun t : Fin r => p t = true)).card + (if p r then 1 else 0 : ℕ) := by
          rw [hcard r]
      _ = (List.range r).countP p + (if p r then 1 else 0 : ℕ) := by rw [ih]
      _ = (List.range (r + 1)).countP p := by
          rw [List.range_succ, List.countP_append, List.countP_singleton]

theorem card_ofMask (m : Fin 6) (n : ℕ) : (ofMask m n).card = Chk.cardN (nroots m) n :=
  card_filter_univ_fin (nroots m) (fun t => n.testBit t)

theorem vanish_span_pair {v y : V m} {t : Root m} :
    Vanish m (Submodule.span (ZMod 3) {v, y}) t ↔ root m t v = 0 ∧ root m t y = 0 := by
  constructor
  · intro h
    exact ⟨h v (Submodule.subset_span (by simp)), h y (Submodule.subset_span (by simp))⟩
  · rintro ⟨hv, hy⟩ u hu
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
    rw [map_add, map_smul, map_smul, hv, hy, smul_zero, smul_zero, add_zero]

theorem mem_iff_vanish_of_occurs {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)}
    (hc : occurs m U c) (hcent : cent m c = U) (t : Root m) : t ∈ c ↔ Vanish m U t :=
  ⟨hc.2.1 t, mem_of_occurs_of_cent_eq hc hcent⟩

theorem nat_all_iff {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h x _
    exact h x.val x.isLt

theorem int_emod_three_eq_zero_iff (z : ℤ) : z % 3 = 0 ↔ (z : ZMod 3) = 0 := by
  rw [← Int.dvd_iff_emod_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem maskN_testBit (r : ℕ) (p : ℕ → Bool) (j : ℕ) :
    (Chk.maskN r p).testBit j = true ↔ j < r ∧ p j = true := by
  induction r with
  | zero => simp [Chk.maskN]
  | succ r ih =>
    have hstep : Chk.maskN (r + 1) p
        = if p r then Chk.maskN r p ||| 1 <<< r else Chk.maskN r p := by
      simp only [Chk.maskN, Nat.fold_succ]
    rw [hstep]
    by_cases hp : p r = true
    · rw [if_pos hp, Nat.testBit_lor, Bool.or_eq_true, ih, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (⟨hj, hpj⟩ | hje)
        · exact ⟨by omega, hpj⟩
        · exact ⟨by omega, hje ▸ hp⟩
      · rintro ⟨hj, hpj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Or.inl ⟨h, hpj⟩
        · exact Or.inr h.symm
    · rw [if_neg hp]
      rw [ih]
      constructor
      · rintro ⟨hj, hpj⟩
        exact ⟨by omega, hpj⟩
      · rintro ⟨hj, hpj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact ⟨h, hpj⟩
        · exact absurd (h ▸ hpj) hp

variable {T : Chk.Tabs}

private theorem tabsOK_fun (hT : Chk.tabsOK m T = true) :
    (Nat.all (nroots m) fun i _ => Nat.all (dim m) fun k _ =>
        ((T.f[i]!)[k]! == Chk.fN m i k && (T.h[i]!)[k]! == Chk.hN m i k)) = true := by
  have h := hT
  simp only [Chk.tabsOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

private theorem tabsOK_pairN (hT : Chk.tabsOK m T = true) :
    (Nat.all (nroots m) fun i _ => Nat.all (nroots m) fun j _ =>
        (T.pair[i]!)[j]! == Chk.pairN m i j) = true := by
  have h := hT
  simp only [Chk.tabsOK, Bool.and_eq_true] at h
  exact h.1.1.1.2

private theorem tabsOK_adjN (hT : Chk.tabsOK m T = true) :
    (Nat.all (nroots m) fun i _ => T.adj[i]! == Chk.adjA T (nroots m) i) = true := by
  have h := hT
  simp only [Chk.tabsOK, Bool.and_eq_true] at h
  exact h.1.1.2

private theorem tabsOK_zmN (hT : Chk.tabsOK m T = true) :
    (Nat.all (3 ^ dim m) fun c _ => T.zm[c]! == Chk.zmA T (dim m) (nroots m) c) = true := by
  have h := hT
  simp only [Chk.tabsOK, Bool.and_eq_true] at h
  exact h.1.2

theorem tabsOK_rtN (hT : Chk.tabsOK m T = true) :
    (Nat.all (nroots m) fun u _ => Nat.all (nroots m) fun t _ =>
        decide ((T.rt[u]!)[t]! < nroots m) &&
          (Chk.rtEq T (dim m) ((T.rt[u]!)[t]!) u t 1 ||
            Chk.rtEq T (dim m) ((T.rt[u]!)[t]!) u t (-1))) = true := by
  have h := hT
  simp only [Chk.tabsOK, Bool.and_eq_true] at h
  exact h.2

theorem tabsOK_f (hT : Chk.tabsOK m T = true) (i : Root m) (k : Fin (dim m)) :
    (T.f[i.val]!)[k.val]! = F m i k :=
  beq_iff_eq.mp ((Bool.and_eq_true _ _).mp
    (nat_all_iff.mp (nat_all_iff.mp (tabsOK_fun hT) i.val i.isLt) k.val k.isLt)).1

theorem tabsOK_h (hT : Chk.tabsOK m T = true) (i : Root m) (k : Fin (dim m)) :
    (T.h[i.val]!)[k.val]! = H m i k :=
  beq_iff_eq.mp ((Bool.and_eq_true _ _).mp
    (nat_all_iff.mp (nat_all_iff.mp (tabsOK_fun hT) i.val i.isLt) k.val k.isLt)).2

theorem tabsOK_pair (hT : Chk.tabsOK m T = true) (i j : Root m) :
    (T.pair[i.val]!)[j.val]! = pairing m i j := by
  have h := beq_iff_eq.mp (nat_all_iff.mp (nat_all_iff.mp (tabsOK_pairN hT) i.val i.isLt)
    j.val j.isLt)
  rw [h, Chk.pairN, pairing]
  by_cases hm : m.val = 3
  · rw [if_pos hm, if_pos hm, nat_fold_add]
    exact Finset.sum_congr rfl fun k _ => rfl
  · rw [if_neg hm, if_neg hm, nat_fold_add]
    exact Finset.sum_congr rfl fun k _ => rfl

theorem tabsOK_adj (hT : Chk.tabsOK m T = true) (i : Root m) (j : ℕ) :
    (T.adj[i.val]!).testBit j = true ↔ ∃ h : j < nroots m, Adj m i ⟨j, h⟩ := by
  have hadj : T.adj[i.val]! = Chk.adjA T (nroots m) i.val :=
    beq_iff_eq.mp (nat_all_iff.mp (tabsOK_adjN hT) i.val i.isLt)
  rw [hadj, Chk.adjA, maskN_testBit, Bool.or_eq_true, bne_iff_ne, bne_iff_ne]
  constructor
  · rintro ⟨hj, hp | hp⟩
    · exact ⟨hj, Or.inl (by rwa [tabsOK_pair hT i ⟨j, hj⟩] at hp)⟩
    · exact ⟨hj, Or.inr (by rwa [tabsOK_pair hT ⟨j, hj⟩ i] at hp)⟩
  · rintro ⟨hj, hp | hp⟩
    · exact ⟨hj, Or.inl (by rwa [tabsOK_pair hT i ⟨j, hj⟩])⟩
    · exact ⟨hj, Or.inr (by rwa [tabsOK_pair hT ⟨j, hj⟩ i])⟩

theorem evA_cast (hT : Chk.tabsOK m T = true) (t : ℕ) (ht : t < nroots m) (c : ℕ) :
    ((Nat.fold (dim m) (fun k _ s => s + (T.f[t]!)[k]! * (Chk.dig c k : ℤ)) 0 : ℤ) :
        ZMod 3) = root m ⟨t, ht⟩ (vec m c) := by
  rw [nat_fold_add, root_apply]
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tabsOK_f hT ⟨t, ht⟩ k]
  simp only [vec]
  push_cast
  ring

private theorem evA_zero_iff (hT : Chk.tabsOK m T = true) (t : ℕ) (ht : t < nroots m) (c : ℕ) :
    Chk.evA T (dim m) t c = 0 ↔ root m ⟨t, ht⟩ (vec m c) = 0 := by
  rw [Chk.evA, int_emod_three_eq_zero_iff, evA_cast hT t ht c]

theorem tabsOK_zm (hT : Chk.tabsOK m T = true) {c : ℕ} (hc : c < 3 ^ dim m) (t : ℕ) :
    (T.zm[c]!).testBit t = true ↔ ∃ h : t < nroots m, root m ⟨t, h⟩ (vec m c) = 0 := by
  have hzm : T.zm[c]! = Chk.zmA T (dim m) (nroots m) c :=
    beq_iff_eq.mp (nat_all_iff.mp (tabsOK_zmN hT) c hc)
  rw [hzm, Chk.zmA, maskN_testBit, beq_iff_eq]
  exact ⟨fun ⟨ht, he⟩ => ⟨ht, (evA_zero_iff hT t ht c).mp he⟩,
    fun ⟨ht, hr⟩ => ⟨ht, (evA_zero_iff hT t ht c).mpr hr⟩⟩

theorem mem_ofMask_zm (hT : Chk.tabsOK m T = true) {c : ℕ} (hc : c < 3 ^ dim m) (t : Root m) :
    t ∈ ofMask m (T.zm[c]!) ↔ root m t (vec m c) = 0 := by
  rw [mem_ofMask, tabsOK_zm hT hc t.val]
  exact ⟨fun h => h.2, fun h => ⟨t.isLt, h⟩⟩

theorem tabsOK_rt_lt (hT : Chk.tabsOK m T = true) (u t : Root m) :
    (T.rt[u.val]!)[t.val]! < nroots m := by
  have hrt := nat_all_iff.mp (nat_all_iff.mp (tabsOK_rtN hT) u.val u.isLt) t.val t.isLt
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hrt).1


private theorem rtEq_f_zmod {T : Chk.Tabs} {d t' u t : ℕ} {ε : ℤ}
    (h : Chk.rtEq T d t' u t ε = true) {k : ℕ} (hk : k < d) :
    ((T.f[t']!)[k]! : ZMod 3) = (ε : ZMod 3) * (((T.f[t]!)[k]! : ZMod 3) -
      ((T.pair[t]!)[u]! : ZMod 3) * ((T.f[u]!)[k]! : ZMod 3)) := by
  rw [Chk.rtEq] at h
  have h1 : (((T.f[t']!)[k]! - ε * ((T.f[t]!)[k]! - ((T.pair[t]!)[u]!) * ((T.f[u]!)[k]!))) % 3
      == 0) = true := ((Bool.and_eq_true _ _).mp (nat_all_iff.mp h k hk)).1
  rw [beq_iff_eq] at h1
  have h2 := (int_emod_three_eq_zero_iff _).mp h1
  push_cast at h2
  exact sub_eq_zero.mp h2

private theorem rtEq_h_zmod {T : Chk.Tabs} {d t' u t : ℕ} {ε : ℤ}
    (h : Chk.rtEq T d t' u t ε = true) {k : ℕ} (hk : k < d) :
    ((T.h[t']!)[k]! : ZMod 3) = (ε : ZMod 3) * (((T.h[t]!)[k]! : ZMod 3) -
      ((T.pair[u]!)[t]! : ZMod 3) * ((T.h[u]!)[k]! : ZMod 3)) := by
  rw [Chk.rtEq] at h
  have h1 : (((T.h[t']!)[k]! - ε * ((T.h[t]!)[k]! - ((T.pair[u]!)[t]!) * ((T.h[u]!)[k]!))) % 3
      == 0) := ((Bool.and_eq_true _ _).mp (nat_all_iff.mp h k hk)).2
  rw [beq_iff_eq] at h1
  have h2 := (int_emod_three_eq_zero_iff _).mp h1
  push_cast at h2
  exact sub_eq_zero.mp h2

private theorem sum_eps_sub_distrib {ι : Type*} [Fintype ι] (a b v : ι → ZMod 3) (ε p : ZMod 3) :
    (∑ k, (ε * (a k - p * b k)) * v k) = ε * ((∑ k, a k * v k) - p * ∑ k, b k * v k) := by
  have h1 : (∑ k, (ε * (a k - p * b k)) * v k)
      = ∑ k, (ε * (a k * v k) - (ε * p) * (b k * v k)) :=
    Finset.sum_congr rfl fun k _ => by ring
  have h2 : (∑ k, (ε * (a k * v k) - (ε * p) * (b k * v k)))
      = ∑ k, ε * (a k * v k) - ∑ k, (ε * p) * (b k * v k) :=
    Finset.sum_sub_distrib (s := Finset.univ) _ _
  have h3 : (∑ k, ε * (a k * v k)) = ε * ∑ k, a k * v k :=
    (Finset.mul_sum (s := Finset.univ) (fun k => a k * v k) ε).symm
  have h4 : (∑ k, (ε * p) * (b k * v k)) = (ε * p) * ∑ k, b k * v k :=
    (Finset.mul_sum (s := Finset.univ) (fun k => b k * v k) (ε * p)).symm
  rw [h1, h2, h3, h4]
  ring

private theorem eps_mul_mul_self {ε x : ZMod 3} (h : ε * ε = 1) : ε * x * ε = x := by
  rw [mul_comm (ε * x) ε, ← mul_assoc, h, one_mul]

theorem root_reflection (m : Fin 6) (t u : Root m) (v : V m) :
    root m t (reflection m u v) = root m t v - (pairing m t u : ZMod 3) * root m u v := by
  rw [reflection_apply, map_sub, map_smul, pairing_eq, smul_eq_mul,
    mul_comm ((root m u) v) ((pairing m t u : ZMod 3))]
  rfl

theorem root_rt (hT : Chk.tabsOK m T = true) (u t t' : Root m) (ε : ℤ)
    (h : Chk.rtEq T (dim m) t'.val u.val t.val ε = true) (v : V m) :
    root m t' v = (ε : ZMod 3) * (root m t v - (pairing m t u : ZMod 3) * root m u v) := by
  have hF : ∀ k : Fin (dim m), (F m t' k : ZMod 3) = (ε : ZMod 3) *
      ((F m t k : ZMod 3) - (pairing m t u : ZMod 3) * (F m u k : ZMod 3)) := by
    intro k
    rw [← tabsOK_f hT t' k, ← tabsOK_f hT t k, ← tabsOK_f hT u k, ← tabsOK_pair hT t u]
    exact rtEq_f_zmod h k.isLt
  simp only [root_apply]
  rw [← sum_eps_sub_distrib (fun k : Fin (dim m) => (F m t k : ZMod 3))
    (fun k => (F m u k : ZMod 3)) v (ε : ZMod 3) (pairing m t u)]
  exact Finset.sum_congr rfl fun k _ => by rw [hF k]

theorem coroot_rt (hT : Chk.tabsOK m T = true) (u t t' : Root m) (ε : ℤ)
    (h : Chk.rtEq T (dim m) t'.val u.val t.val ε = true) (k : Fin (dim m)) :
    coroot m t' k = (ε : ZMod 3) * (coroot m t k - (pairing m u t : ZMod 3) * coroot m u k) := by
  show (H m t' k : ZMod 3) = (ε : ZMod 3) * ((H m t k : ZMod 3) -
    (pairing m u t : ZMod 3) * (H m u k : ZMod 3))
  rw [← tabsOK_h hT t' k, ← tabsOK_h hT t k, ← tabsOK_h hT u k, ← tabsOK_pair hT u t]
  exact rtEq_h_zmod h k.isLt

private theorem reflection_rt_aux (hT : Chk.tabsOK m T = true) (u t t' : Root m) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (h : Chk.rtEq T (dim m) t'.val u.val t.val ε = true) :
    reflection m t' = reflection m u * reflection m t * reflection m u := by
  have hroot : ∀ v : V m, root m t' v =
      (ε : ZMod 3) * (root m t v - (pairing m t u : ZMod 3) * root m u v) :=
    fun v => root_rt hT u t t' ε h v
  have hcoroot : coroot m t' =
      (ε : ZMod 3) • (coroot m t - (pairing m u t : ZMod 3) • coroot m u) := by
    funext k
    exact coroot_rt hT u t t' ε h k
  have hεε : (ε : ZMod 3) * (ε : ZMod 3) = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  calc reflection m t' v
      = v - root m t' v • coroot m t' := reflection_apply m t' v
    _ = v - ((ε : ZMod 3) * (root m t v - (pairing m t u : ZMod 3) * root m u v)) •
          ((ε : ZMod 3) • (coroot m t - (pairing m u t : ZMod 3) • coroot m u)) := by
          rw [hroot v, hcoroot]
    _ = v - (root m t v - (pairing m t u : ZMod 3) * root m u v) •
          (coroot m t - (pairing m u t : ZMod 3) • coroot m u) := by
          rw [smul_smul, eps_mul_mul_self hεε]
    _ = reflection m u (reflection m t (reflection m u v)) := by
          rw [reflection_apply (i := t) (v := reflection m u v), map_sub, map_smul,
            show reflection m u (reflection m u v) = v from
              Module.involutive_reflection (root_coroot m u) v,
            reflection_apply (i := u) (v := coroot m t), root_reflection, pairing_eq m u t]
          rfl

theorem reflection_rt (hT : Chk.tabsOK m T = true) (u t : Root m) :
    reflection m ⟨(T.rt[u.val]!)[t.val]!, tabsOK_rt_lt hT u t⟩ =
      reflection m u * reflection m t * reflection m u := by
  have hrt := nat_all_iff.mp (nat_all_iff.mp (tabsOK_rtN hT) u.val u.isLt) t.val t.isLt
  have h := (Bool.or_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hrt).2
  rcases h with h1 | h1
  · exact reflection_rt_aux hT u t _ 1 (Or.inl rfl) h1
  · exact reflection_rt_aux hT u t _ (-1) (Or.inr rfl) h1

end

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
