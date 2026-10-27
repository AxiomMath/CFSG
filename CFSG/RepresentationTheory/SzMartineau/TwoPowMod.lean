module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RepresentationTheory.SzMartineau

theorem two_pow_self_eq_one (f : ℕ) : (2 : ZMod (2 ^ f - 1)) ^ f = 1 := by
  change (((2 : ℕ) : ZMod (2 ^ f - 1)) ^ f) = 1
  rw [← Nat.cast_pow]
  have h : 2 ^ f = (2 ^ f - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  rw [h, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

private lemma pow_two_lt_mod {f i : ℕ} (hf : 2 ≤ f) (hi : i < f) : 2 ^ i < 2 ^ f - 1 := by
  have hmul : 2 ^ f = 2 * 2 ^ (f - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ f)]
    rw [pow_succ, mul_comm]
  have hle : 2 ^ i ≤ 2 ^ (f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hge : 2 ≤ 2 ^ (f - 1) := by
    have h := Nat.one_lt_two_pow (by omega : f - 1 ≠ 0)
    omega
  omega

private lemma pow_two_inj {f i j : ℕ} (hf : 2 ≤ f) (hi : i < f) (hj : j < f) :
    (2 : ZMod (2 ^ f - 1)) ^ i = 2 ^ j ↔ i = j := by
  constructor
  · intro h
    have hcast : ((2 ^ i : ℕ) : ZMod (2 ^ f - 1)) =
        ((2 ^ j : ℕ) : ZMod (2 ^ f - 1)) := by
      simpa using h
    have hnat : 2 ^ i = 2 ^ j := by
      have hval := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (pow_two_lt_mod hf hi),
        ZMod.val_natCast_of_lt (pow_two_lt_mod hf hj)] at hval
      exact hval
    exact Nat.pow_right_injective (by norm_num) hnat
  · rintro rfl
    rfl

theorem two_pow_eq_two_pow_iff {f u v : ℕ} (hf : 2 ≤ f) :
    (2 : ZMod (2 ^ f - 1)) ^ u = 2 ^ v ↔ u % f = v % f := by
  have hpow : (2 : ZMod (2 ^ f - 1)) ^ f = 1 := two_pow_self_eq_one f
  constructor
  · intro h
    rw [pow_eq_pow_mod u hpow, pow_eq_pow_mod v hpow] at h
    exact (pow_two_inj hf (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))).mp h
  · intro h
    rw [pow_eq_pow_mod u hpow, pow_eq_pow_mod v hpow, h]

private lemma finset_sum_two_pow_lt {f : ℕ} (hf : 2 ≤ f) {S : Finset ℕ}
    (hsub : S ⊆ Finset.range f) (hcard : S.card < f) :
    ∑ x ∈ S, (2 : ℕ) ^ x < 2 ^ f - 1 := by
  obtain ⟨d, hdmem, hdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (by simpa [Finset.card_range] using hcard : S.card < (Finset.range f).card)
  have hpos : 0 < ∑ x ∈ Finset.range f \ S, (2 : ℕ) ^ x := by
    refine Finset.sum_pos (fun i _ => Nat.two_pow_pos i) ⟨d, ?_⟩
    exact Finset.mem_sdiff.mpr ⟨hdmem, hdnot⟩
  have hsplit := Finset.sum_sdiff hsub (f := fun x => (2 : ℕ) ^ x)
  have htotal : ∑ i ∈ Finset.range f, (2 : ℕ) ^ i = 2 ^ f - 1 := by
    rw [Nat.geomSum_eq (by omega : 2 ≤ 2)]
    simp
  omega

private lemma two_pow_add_two_pow_lt {f a b : ℕ} (hf : 3 ≤ f) (ha : a < f) (hb : b < f)
    (hab : a ≠ b) : 2 ^ a + 2 ^ b < 2 ^ f - 1 := by
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.range f := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [ha, hb]
  have hcard : ({a, b} : Finset ℕ).card < f := by
    rw [Finset.card_pair hab]
    omega
  have hsum : (∑ x ∈ ({a, b} : Finset ℕ), (2 : ℕ) ^ x) = 2 ^ a + 2 ^ b := by
    rw [Finset.sum_pair hab]
  have hlt := finset_sum_two_pow_lt (by omega : 2 ≤ f) hsub hcard
  rwa [hsum] at hlt

private lemma bitIndices_two_pow_add_two_pow {a b : ℕ} (hab : a ≠ b) :
    Nat.bitIndices (2 ^ a + 2 ^ b) = [min a b, max a b] := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    have hs : List.SortedLT [a, b] := by
      rw [List.sortedLT_iff_pairwise]
      simp [hlt]
    have h := Nat.bitIndices_sum_map_two_pow (L := [a, b]) hs
    simpa using h
  · rw [min_eq_right hlt.le, max_eq_left hlt.le]
    have hs : List.SortedLT [b, a] := by
      rw [List.sortedLT_iff_pairwise]
      simp [hlt]
    have h := Nat.bitIndices_sum_map_two_pow (L := [b, a]) hs
    simpa [add_comm] using h

private lemma nat_two_pow_add_two_pow_eq_two_pow {a b c : ℕ} (hab : a ≠ b)
    (h : 2 ^ a + 2 ^ b = 2 ^ c) : False := by
  have hbits := bitIndices_two_pow_add_two_pow hab
  rw [h, Nat.bitIndices_two_pow] at hbits
  have hlen := congrArg List.length hbits
  simp at hlen

private lemma nat_two_pow_add_two_pow_eq_of_ne {a b c d : ℕ} (hab : a ≠ b) (hcd : c ≠ d)
    (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hl := bitIndices_two_pow_add_two_pow hab
  have hr := bitIndices_two_pow_add_two_pow hcd
  rw [h, hr] at hl
  have hcons := List.cons.inj hl
  have hmin : min c d = min a b := hcons.1
  have hmax : max c d = max a b := by simpa using hcons.2
  rcases le_total a b with hab' | hab'
  · have hmina : min a b = a := min_eq_left hab'
    have hmaxa : max a b = b := max_eq_right hab'
    rw [hmina] at hmin
    rw [hmaxa] at hmax
    rcases le_total c d with hcd' | hcd'
    · have hminc : min c d = c := min_eq_left hcd'
      have hmaxc : max c d = d := max_eq_right hcd'
      rw [hminc] at hmin
      rw [hmaxc] at hmax
      exact Or.inl ⟨hmin.symm, hmax.symm⟩
    · have hminc : min c d = d := min_eq_right hcd'
      have hmaxc : max c d = c := max_eq_left hcd'
      rw [hminc] at hmin
      rw [hmaxc] at hmax
      exact Or.inr ⟨hmin.symm, hmax.symm⟩
  · have hmina : min a b = b := min_eq_right hab'
    have hmaxa : max a b = a := max_eq_left hab'
    rw [hmina] at hmin
    rw [hmaxa] at hmax
    rcases le_total c d with hcd' | hcd'
    · have hminc : min c d = c := min_eq_left hcd'
      have hmaxc : max c d = d := max_eq_right hcd'
      rw [hminc] at hmin
      rw [hmaxc] at hmax
      exact Or.inr ⟨hmax.symm, hmin.symm⟩
    · have hminc : min c d = d := min_eq_right hcd'
      have hmaxc : max c d = c := max_eq_left hcd'
      rw [hminc] at hmin
      rw [hmaxc] at hmax
      exact Or.inl ⟨hmax.symm, hmin.symm⟩

private lemma natCast_list_sum_map_two_pow {f : ℕ} (l : List ℕ) :
    (((l.map fun x => 2 ^ x).sum : ℕ) : ZMod (2 ^ f - 1)) =
      (l.map fun x => (2 : ZMod (2 ^ f - 1)) ^ x).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

private lemma multiset_sum_two_pow_ne_zero_of_nodup {f : ℕ} (hf : 2 ≤ f) {M : Multiset ℕ}
    (hnodup : M.Nodup) (hlt : ∀ x ∈ M, x < f) (hne : M ≠ 0) (hcardf : M.card < f) :
    (M.map fun u => (2 : ZMod (2 ^ f - 1)) ^ u).sum ≠ 0 := by
  have hLnodup : M.toList.Nodup := by
    rw [← Multiset.coe_nodup, Multiset.coe_toList]
    exact hnodup
  have hLne : M.toList ≠ [] := by
    intro hnil
    exact hne (Multiset.toList_eq_nil.mp hnil)
  have hsub : M.toList.toFinset ⊆ Finset.range f := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.mpr (hlt x (by simpa using hx))
  have hScard : M.toList.toFinset.card < f := by
    rw [List.toFinset_card_of_nodup hLnodup, Multiset.length_toList]
    exact hcardf
  have hbound : (∑ x ∈ M.toList.toFinset, (2 : ℕ) ^ x) < 2 ^ f - 1 :=
    finset_sum_two_pow_lt hf hsub hScard
  have hNat_eq : (M.toList.map fun x => (2 : ℕ) ^ x).sum =
      ∑ x ∈ M.toList.toFinset, (2 : ℕ) ^ x :=
    (List.sum_toFinset (fun x => (2 : ℕ) ^ x) hLnodup).symm
  have hNat_pos : 0 < (M.toList.map fun x => (2 : ℕ) ^ x).sum := by
    refine List.sum_pos _ (fun y hy => ?_) ?_
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact Nat.two_pow_pos x
    · simpa using hLne
  have hNat_lt : (M.toList.map fun x => (2 : ℕ) ^ x).sum < 2 ^ f - 1 := by
    rw [hNat_eq]
    exact hbound
  have hcast : (((M.toList.map fun x => (2 : ℕ) ^ x).sum : ℕ) : ZMod (2 ^ f - 1)) =
      (M.map fun x => (2 : ZMod (2 ^ f - 1)) ^ x).sum := by
    rw [← Multiset.sum_map_toList M (fun x => (2 : ZMod (2 ^ f - 1)) ^ x)]
    exact natCast_list_sum_map_two_pow M.toList
  intro hsum
  have hzero : (((M.toList.map fun x => (2 : ℕ) ^ x).sum : ℕ) :
      ZMod (2 ^ f - 1)) = 0 := by
    rw [hcast, hsum]
  have hdvd : (2 ^ f - 1) ∣ (M.toList.map fun x => (2 : ℕ) ^ x).sum :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact Nat.not_dvd_of_pos_of_lt hNat_pos hNat_lt hdvd

private lemma multiset_sum_two_pow_ne_zero {f : ℕ} (hf : 2 ≤ f) (n : ℕ) :
    ∀ M : Multiset ℕ, M.card = n → (∀ x ∈ M, x < f) → M ≠ 0 → M.card < f →
      (M.map fun u => (2 : ZMod (2 ^ f - 1)) ^ u).sum ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hcard hlt hne hcardf
    by_cases hnodup : M.Nodup
    · exact multiset_sum_two_pow_ne_zero_of_nodup hf hnodup hlt hne hcardf
    · have hex : ∃ a, 1 < M.count a := by
        by_contra h
        push Not at h
        exact hnodup (Multiset.nodup_iff_count_le_one.mpr h)
      obtain ⟨a, ha⟩ := hex
      have haM : a ∈ M := Multiset.count_pos.mp (by omega)
      have haM1 : a ∈ M.erase a := by
        rw [← Multiset.count_pos, Multiset.count_erase_self]
        omega
      have hM1 : a ::ₘ M.erase a = M := Multiset.cons_erase haM
      have hM2 : a ::ₘ (M.erase a).erase a = M.erase a := Multiset.cons_erase haM1
      have hM : a ::ₘ a ::ₘ (M.erase a).erase a = M := by
        rw [hM2, hM1]
      let M' : Multiset ℕ := ((a + 1) % f) ::ₘ (M.erase a).erase a
      have hM'card : M'.card < M.card := by
        have hMc : M.card = ((M.erase a).erase a).card + 2 := by
          rw [← hM]
          simp
        rw [hMc]
        simp only [M', Multiset.card_cons]
        omega
      have hM'lt : ∀ x ∈ M', x < f := by
        intro x hx
        simp only [M', Multiset.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Nat.mod_lt _ (by omega)
        · exact hlt x (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx))
      have hM'ne : M' ≠ 0 := by
        intro h0
        have hc := congrArg Multiset.card h0
        simp only [M', Multiset.card_cons, Multiset.card_zero] at hc
        omega
      have hsum_eq : (M'.map fun x => (2 : ZMod (2 ^ f - 1)) ^ x).sum =
          (M.map fun x => (2 : ZMod (2 ^ f - 1)) ^ x).sum := by
        rw [← hM]
        simp only [M', Multiset.map_cons, Multiset.sum_cons]
        have hb : (2 : ZMod (2 ^ f - 1)) ^ ((a + 1) % f) =
            (2 : ZMod (2 ^ f - 1)) ^ a + 2 ^ a := by
          rw [← pow_eq_pow_mod (a + 1) (two_pow_self_eq_one f), pow_succ]
          ring
        rw [hb]
        ring
      have hrec := ih M'.card (by omega) M' rfl hM'lt hM'ne (by omega)
      intro hsum
      exact hrec (by rw [hsum_eq]; exact hsum)

theorem sum_two_pow_ne_zero {f : ℕ} {l : List ℕ} (hl : l ≠ []) (hlf : l.length < f) :
    (l.map fun u => (2 : ZMod (2 ^ f - 1)) ^ u).sum ≠ 0 := by
  have hf : 2 ≤ f := by
    have hpos := List.length_pos_iff.mpr hl
    omega
  have hsum_eq : (l.map fun u => (2 : ZMod (2 ^ f - 1)) ^ u).sum =
      ((l.map (· % f)).map fun u => (2 : ZMod (2 ^ f - 1)) ^ u).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left (fun u _ => pow_eq_pow_mod u (two_pow_self_eq_one f))
  rw [hsum_eq]
  refine multiset_sum_two_pow_ne_zero hf l.length (l.map (· % f)) ?_ ?_ ?_ ?_
  · simp
  · intro u hu
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
    exact Nat.mod_lt _ (by omega)
  · simpa
  · simpa using hlf

theorem two_pow_add_two_pow_eq_two_pow {f u v w : ℕ} (hf : 3 ≤ f)
    (h : (2 : ZMod (2 ^ f - 1)) ^ u + 2 ^ v = 2 ^ w) :
    u % f = v % f ∧ w % f = (u + 1) % f := by
  have hf2 : 2 ≤ f := by omega
  have hpow : (2 : ZMod (2 ^ f - 1)) ^ f = 1 := two_pow_self_eq_one f
  rw [pow_eq_pow_mod u hpow, pow_eq_pow_mod v hpow, pow_eq_pow_mod w hpow] at h
  have hu : u % f < f := Nat.mod_lt _ (by omega)
  have hv : v % f < f := Nat.mod_lt _ (by omega)
  have hw : w % f < f := Nat.mod_lt _ (by omega)
  by_cases huv : u % f = v % f
  · have hsingle : (2 : ZMod (2 ^ f - 1)) ^ (u % f + 1) =
        (2 : ZMod (2 ^ f - 1)) ^ (w % f) := by
      calc (2 : ZMod (2 ^ f - 1)) ^ (u % f + 1)
          = (2 : ZMod (2 ^ f - 1)) ^ (u % f) + 2 ^ (u % f) := by
            rw [pow_succ]
            ring
        _ = (2 : ZMod (2 ^ f - 1)) ^ (w % f) := by
            rw [← huv] at h
            exact h
    have hsingle' : (2 : ZMod (2 ^ f - 1)) ^ ((u % f + 1) % f) =
        (2 : ZMod (2 ^ f - 1)) ^ (w % f) := by
      rw [← pow_eq_pow_mod (u % f + 1) hpow]
      exact hsingle
    have hmod : (u % f + 1) % f = w % f :=
      (pow_two_inj hf2 (Nat.mod_lt _ (by omega)) hw).mp hsingle'
    refine ⟨huv, ?_⟩
    rw [← hmod]
    rw [Nat.add_mod u 1 f, Nat.mod_eq_of_lt (by omega : 1 < f)]
  · have hlt : 2 ^ (u % f) + 2 ^ (v % f) < 2 ^ f - 1 :=
      two_pow_add_two_pow_lt hf hu hv huv
    have hlw : 2 ^ (w % f) < 2 ^ f - 1 := pow_two_lt_mod hf2 hw
    have hnat : 2 ^ (u % f) + 2 ^ (v % f) = 2 ^ (w % f) := by
      have hcast : (((2 ^ (u % f) + 2 ^ (v % f) : ℕ)) : ZMod (2 ^ f - 1)) =
          ((2 ^ (w % f) : ℕ) : ZMod (2 ^ f - 1)) := by
        simpa [Nat.cast_add, Nat.cast_pow] using h
      have hval := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt hlw] at hval
    exact False.elim (nat_two_pow_add_two_pow_eq_two_pow huv hnat)

theorem two_pow_add_two_pow_eq_two_pow_add_two_pow {f u v x y : ℕ} (hf : 3 ≤ f)
    (h : (2 : ZMod (2 ^ f - 1)) ^ u + 2 ^ v = 2 ^ x + 2 ^ y) :
    (u % f = x % f ∧ v % f = y % f) ∨ (u % f = y % f ∧ v % f = x % f) := by
  have hf2 : 2 ≤ f := by omega
  have hpow : (2 : ZMod (2 ^ f - 1)) ^ f = 1 := two_pow_self_eq_one f
  rw [pow_eq_pow_mod u hpow, pow_eq_pow_mod v hpow, pow_eq_pow_mod x hpow,
    pow_eq_pow_mod y hpow] at h
  have hu : u % f < f := Nat.mod_lt _ (by omega)
  have hv : v % f < f := Nat.mod_lt _ (by omega)
  have hx : x % f < f := Nat.mod_lt _ (by omega)
  have hy : y % f < f := Nat.mod_lt _ (by omega)
  by_cases huv : u % f = v % f
  · have hsingle : (2 : ZMod (2 ^ f - 1)) ^ (u % f + 1) =
        (2 : ZMod (2 ^ f - 1)) ^ (x % f) + 2 ^ (y % f) := by
      calc (2 : ZMod (2 ^ f - 1)) ^ (u % f + 1)
          = (2 : ZMod (2 ^ f - 1)) ^ (u % f) + 2 ^ (u % f) := by
            rw [pow_succ]
            ring
        _ = (2 : ZMod (2 ^ f - 1)) ^ (x % f) + 2 ^ (y % f) := by
            rw [← huv] at h
            exact h
    have hs := two_pow_add_two_pow_eq_two_pow hf hsingle.symm
    have hxy : x % f = y % f := by simpa using hs.1
    have hcong : (u % f + 1) % f = (x % f + 1) % f := by simpa using hs.2
    have hux : u % f = x % f :=
      Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' 1 hcong) hu hx
    exact Or.inl ⟨hux, huv.symm.trans (hux.trans hxy)⟩
  · by_cases hxy : x % f = y % f
    · have hsingle : (2 : ZMod (2 ^ f - 1)) ^ (u % f) + 2 ^ (v % f) =
          (2 : ZMod (2 ^ f - 1)) ^ (x % f + 1) := by
        calc (2 : ZMod (2 ^ f - 1)) ^ (u % f) + 2 ^ (v % f)
            = (2 : ZMod (2 ^ f - 1)) ^ (x % f) + 2 ^ (y % f) := h
          _ = (2 : ZMod (2 ^ f - 1)) ^ (x % f) + 2 ^ (x % f) := by rw [hxy]
          _ = (2 : ZMod (2 ^ f - 1)) ^ (x % f + 1) := by
              rw [pow_succ]
              ring
      have hvu : u % f = v % f := by
        simpa using (two_pow_add_two_pow_eq_two_pow hf hsingle).1
      exact False.elim (huv hvu)
    · have hlt : 2 ^ (u % f) + 2 ^ (v % f) < 2 ^ f - 1 :=
        two_pow_add_two_pow_lt hf hu hv huv
      have hlt' : 2 ^ (x % f) + 2 ^ (y % f) < 2 ^ f - 1 :=
        two_pow_add_two_pow_lt hf hx hy hxy
      have hnat : 2 ^ (u % f) + 2 ^ (v % f) = 2 ^ (x % f) + 2 ^ (y % f) := by
        have hcast : (((2 ^ (u % f) + 2 ^ (v % f) : ℕ)) : ZMod (2 ^ f - 1)) =
            (((2 ^ (x % f) + 2 ^ (y % f) : ℕ)) : ZMod (2 ^ f - 1)) := by
          simpa [Nat.cast_add, Nat.cast_pow] using h
        have hval := congrArg ZMod.val hcast
        rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt hlt'] at hval
      exact nat_two_pow_add_two_pow_eq_of_ne huv hxy hnat

end CFSG.RepresentationTheory.SzMartineau
