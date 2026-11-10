module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGDepASmallNat
public import Certificates.Data.TwoDepSmall

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggTWPosNat : GGTWPos → ℕ
  | .ends => 0
  | .adj => 1

abbrev ggTWNToZ (p N : ℕ) (l : List ℕ) : GGTWE p N := ggDepANToZ p (N - 1) l

@[simp] private lemma l05nE1_getD_map_range {N : ℕ} (F : ℕ → ℕ) (j : ℕ) (hj : j < N) :
    (((List.range N).map F).getD j 0) = F j := by
  simp [List.getD_eq_getElem?_getD, hj]

private lemma l05nE1_natCast_psub {p k : ℕ} (hk : k ≤ p) :
    ((p - k : ℕ) : ZMod p) = -((k : ℕ) : ZMod p) := by
  have h : ((p - k : ℕ) : ZMod p) + (k : ZMod p) = 0 := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hk, ZMod.natCast_self]
  exact eq_neg_of_add_eq_zero_left h

private lemma l05nE1_psub_mod {p k : ℕ} (hp : 0 < p) :
    (((p - k % p) % p : ℕ) : ZMod p) = -((k : ℕ) : ZMod p) := by
  have h1 := ZMod.natCast_mod (p - k % p) p
  rw [h1]
  have h2 : ((p - k % p : ℕ) : ZMod p) = (p : ZMod p) - ((k % p : ℕ) : ZMod p) :=
    Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt k hp))
  rw [h2, ZMod.natCast_self, ZMod.natCast_mod]
  ring

private lemma l05nE1_natCast_mod_pred {p : ℕ} (hp : 0 < p) :
    (((p - 1) % p : ℕ) : ZMod p) = -1 := by
  rw [ZMod.natCast_mod, l05nE1_natCast_psub (Nat.succ_le_of_lt hp)]
  norm_num

private lemma l05nE1_toZ_cons {p n : ℕ} (a : ℕ) (l : List ℕ) :
    ggDepANToZ p (n + 1) (a :: l) =
      Fin.cons ((a : ℕ) : ZMod p) (ggDepANToZ p n l) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [ggDepANToZ]
  · intro k
    simp [ggDepANToZ]

private lemma l05nE1_decode_succ (p n k : ℕ) :
    ggTWNDecode p (n + 1) k = (k % p) :: ggTWNDecode p n (k / p) := by
  simp [ggTWNDecode]

theorem ggTWNX_length (N : ℕ) : (ggTWNX N).length = N - 1 := by
  simp [ggTWNX]

theorem ggTWNH_length (p N i : ℕ) : (ggTWNH p N i).length = N - 1 := by
  simp [ggTWNH]

theorem ggTWNA_length (p N i : ℕ) : (ggTWNA p N i).length = N - 1 := by
  simp [ggTWNA]

theorem ggTWNZ_length (p N pos : ℕ) : (ggTWNZ p N pos).length = N - 1 := by
  simp [ggTWNZ]

theorem ggTWNX_toZ {p N : ℕ} : ggTWNToZ p N (ggTWNX N) = ggTWx p N := by
  funext j
  simp only [ggTWNToZ, ggDepANToZ, ggTWNX, ggTWx]
  rw [l05nE1_getD_map_range _ j.val j.isLt]
  by_cases h : j.val + 2 = N <;> simp [h]

theorem ggTWNH_toZ {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggTWNToZ p N (ggTWNH p N i.val) = ggTWh p N i := by
  funext j
  simp only [ggTWNToZ, ggDepANToZ, ggTWNH, ggTWh]
  rw [l05nE1_getD_map_range _ j.val j.isLt]
  push_cast
  split_ifs with h2 hi hji
  · rfl
  · rw [l05nE1_psub_mod (Fact.out : p.Prime).pos]
    push_cast
    ring
  · rfl
  · rfl

theorem ggTWNA_toZ {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggTWNToZ p N (ggTWNA p N i.val) = ggTWα p N i := by
  funext j
  simp only [ggTWNToZ, ggDepANToZ, ggTWNA, ggTWα]
  rw [l05nE1_getD_map_range _ j.val j.isLt]
  simp only [Bool.or_eq_true, decide_eq_true_iff]
  push_cast
  split_ifs with h2 h1 h3
  · rfl
  · rw [ZMod.natCast_mod]; norm_num
  · exact l05nE1_natCast_mod_pred (Fact.out : p.Prime).pos
  · rfl

theorem ggTWNZ_toZ {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) :
    ggTWNToZ p N (ggTWNZ p N (ggTWPosNat pos)) = ggTWz p N pos := by
  cases pos with
  | ends =>
    funext j
    simp only [ggTWNToZ, ggDepANToZ, ggTWNZ, ggTWz, ggTWPosNat]
    rw [l05nE1_getD_map_range _ j.val j.isLt]
    push_cast
    split_ifs with h2
    · rfl
    · rw [ZMod.natCast_mod]; push_cast; ring
  | adj =>
    funext j
    simp only [ggTWNToZ, ggDepANToZ, ggTWNZ, ggTWz, ggTWPosNat]
    rw [l05nE1_getD_map_range _ j.val j.isLt]
    by_cases h3 : j.val + 3 = N <;> simp [h3]

theorem ggTWNInJ_iff {N : ℕ} (pos : GGTWPos) (c : ℕ) :
    ggTWNInJ N (ggTWPosNat pos) c = true ↔ ggTWInJ N pos c := by
  cases pos <;>
    simp [ggTWNInJ, ggTWInJ, ggTWPosNat, Bool.and_eq_true, decide_eq_true_iff]

theorem ggTWNPlace_eq {N : ℕ} (pos : GGTWPos) (c : ℕ) :
    ggTWNPlace (ggTWPosNat pos) c = ggTWPlace pos c := by
  cases pos <;> simp [ggTWNPlace, ggTWPlace, ggTWPosNat]

theorem ggTWPat1_mn {N c0 : ℕ} {pos : GGTWPos} {m n : ℤ} (h : GGTWPat1 N pos c0 m n) :
    (m = -1 ∨ m = -2) ∧ (n = -1 ∨ n = -2) := by
  unfold GGTWPat1 at h
  rcases h with ⟨_, h | h | h⟩
  · rcases h with ⟨_, h | h | h⟩
    · exact ⟨Or.inl h.1, Or.inl h.2⟩
    · exact ⟨Or.inl h.1, Or.inr h.2⟩
    · exact ⟨Or.inr h.1, Or.inl h.2⟩
  · rcases h with ⟨_, _, hm, hn⟩
    exact ⟨Or.inl hm, Or.inl hn⟩
  · rcases h with ⟨_, _, _, hm, hn⟩
    exact ⟨Or.inl hm, Or.inl hn⟩

theorem ggTWNPat1B_iff {N : ℕ} (pos : GGTWPos) (c0 mi ni : ℕ) (hmi : mi = 1 ∨ mi = 2)
    (hni : ni = 1 ∨ ni = 2) :
    ggTWNPat1B N (ggTWPosNat pos) c0 mi ni = true ↔
      GGTWPat1 N pos c0 (-(mi : ℤ)) (-(ni : ℤ)) := by
  cases pos <;>
    rcases hmi with rfl | rfl <;> rcases hni with rfl | rfl <;>
    simp [ggTWNPat1B, GGTWPat1, ggTWNInJ, ggTWInJ, ggTWNPlace, ggTWPlace, ggTWPosNat,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff] <;>
    tauto

theorem ggTWNPat2B_iff {N : ℕ} (pos : GGTWPos) (c : ℕ) (c2 : Option ℕ) :
    ggTWNPat2B N (ggTWPosNat pos) c c2 = true ↔ GGTWPat2 N pos c c2 := by
  cases pos <;> cases c2 <;>
    simp [ggTWNPat2B, GGTWPat2, ggTWNInJ, ggTWInJ, ggTWNPlace, ggTWPlace, ggTWPosNat,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff] <;>
    tauto

theorem ggTWNDecode_length (p n k : ℕ) : (ggTWNDecode p n k).length = n := by
  induction n generalizing k with
  | zero => simp [ggTWNDecode]
  | succ n ih => simp [l05nE1_decode_succ, ih]

theorem ggTWNDecode_surj {p : ℕ} [Fact p.Prime] (n : ℕ) (v : Fin n → ZMod p) :
    ∃ k < p ^ n, ggDepANToZ p n (ggTWNDecode p n k) = v := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction n with
  | zero =>
    exact ⟨0, by simp, by funext j; exact Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨k', hk'lt, hk'eq⟩ := ih (fun j : Fin n => v j.succ)
    refine ⟨(v 0).val + p * k', ?_, ?_⟩
    · calc (v 0).val + p * k' < p + p * k' := Nat.add_lt_add_right (ZMod.val_lt (v 0)) _
        _ = p * (k' + 1) := by ring
        _ ≤ p * p ^ n := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hk'lt)
        _ = p ^ (n + 1) := (pow_succ' p n).symm
    · have hmod : ((v 0).val + p * k') % p = (v 0).val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt (v 0))]
      have hdiv : ((v 0).val + p * k') / p = k' := by
        rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (ZMod.val_lt (v 0)), zero_add]
      rw [l05nE1_decode_succ, hmod, hdiv, l05nE1_toZ_cons, hk'eq]
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [ZMod.natCast_zmod_val]
      · intro i
        simp

end CFSG.StandardType
