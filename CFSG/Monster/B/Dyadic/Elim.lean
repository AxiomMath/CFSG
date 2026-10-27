module

public import Certificates.Data.CFSGNative.MonsterB.DyadicElim
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native

theorem ba_size_set! (v : ByteArray) (i : ℕ) (x : UInt8) : (v.set! i x).size = v.size := by
  cases v with
  | mk bs => simp [ByteArray.set!, ByteArray.size]

theorem ba_get!_set! (v : ByteArray) (i k : ℕ) (x : UInt8) (hk : k < v.size) :
    (v.set! i x).get! k = if i = k then x else v.get! k := by
  cases v with
  | mk bs =>
    simp only [ByteArray.set!, ByteArray.get!, ByteArray.size] at hk ⊢
    by_cases h : i = k
    · subst h
      simp [Array.set!, hk]
    · rw [ite_eq_right h, Array.set!]
      rw [getElem!_pos (bs.setIfInBounds i x) k (by simpa using hk), getElem!_pos bs k hk,
        Array.getElem_setIfInBounds_ne _ h]

theorem zeroBytes_size (n : ℕ) : (zeroBytes n).size = n := by
  simp [zeroBytes, ByteArray.size]

theorem zeroBytes_get (n k : ℕ) : (zeroBytes n).get! k = 0 := by
  simp only [zeroBytes, ByteArray.get!]
  by_cases hk : k < n
  · rw [getElem!_pos (Array.replicate n (0 : UInt8)) k (by simpa using hk)]
    simp
  · rw [getElem!_neg (Array.replicate n (0 : UInt8)) k (by simpa using hk)]
    rfl

theorem subRow_size (mask q : UInt8) (row : ByteArray) (n : ℕ) :
    ∀ k v, (subRow mask q row n k v).size = v.size := by
  intro k v
  induction h : n - k generalizing k v with
  | zero =>
    rw [subRow, ite_eq_right (by omega)]
  | succ d ih =>
    rw [subRow, ite_eq_left (by omega), ih (k + 1) _ (by omega), ba_size_set!]

theorem subRow_get (mask q : UInt8) (row : ByteArray) (n : ℕ) :
    ∀ k₀ v, ∀ k < v.size, (subRow mask q row n k₀ v).get! k =
      if k₀ ≤ k ∧ k < n then (v.get! k - q * row.get! k) &&& mask else v.get! k := by
  intro k₀ v
  induction h : n - k₀ generalizing k₀ v with
  | zero =>
    intro k hk
    rw [subRow, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ d ih =>
    intro k hk
    rw [subRow, ite_eq_left (by omega)]
    have hk' : k < (v.set! k₀ ((v.get! k₀ - q * row.get! k₀) &&& mask)).size := by
      rw [ba_size_set!]; exact hk
    rw [ih (k₀ + 1) _ (by omega) k hk', ba_get!_set! _ _ _ _ hk]
    by_cases hkk : k₀ = k
    · subst hkk
      simp
      omega
    · rw [ite_eq_right hkk]
      by_cases h1 : k₀ + 1 ≤ k ∧ k < n
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem toNat_sub_cast (a b : UInt8) : ((a - b).toNat : ZMod 256) = a.toNat - b.toNat := by
  rw [UInt8.toNat_sub, ZMod.natCast_mod]
  have hb : b.toNat ≤ 256 := by have := b.toNat_lt; omega
  rw [Nat.cast_add, Nat.cast_sub hb]
  have : ((256 : ℕ) : ZMod 256) = 0 := by decide
  rw [this]
  ring

theorem toNat_mul_cast (a b : UInt8) : ((a * b).toNat : ZMod 256) = a.toNat * b.toNat := by
  rw [UInt8.toNat_mul, ZMod.natCast_mod, Nat.cast_mul]

structure GoodMask (M : ℕ) (mask : UInt8) : Prop where
  dvd : M ∣ 256
  and_eq : ∀ a : UInt8, (((a &&& mask).toNat : ℕ) : ZMod M) = (a.toNat : ZMod M)

theorem goodMask255 : GoodMask 256 255 := ⟨dvd_rfl, fun a => by
  congr 1
  rw [UInt8.toNat_and]
  have h : (255 : UInt8).toNat = 2 ^ 8 - 1 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt a.toNat_lt⟩

theorem goodMask127 : GoodMask 128 127 := ⟨⟨2, rfl⟩, fun a => by
  rw [UInt8.toNat_and]
  have h : (127 : UInt8).toNat = 2 ^ 7 - 1 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod, ZMod.natCast_mod]⟩

theorem sub_mask_cast {M : ℕ} {mask : UInt8} (hm : GoodMask M mask) (a q b : UInt8) :
    ((((a - q * b) &&& mask).toNat : ℕ) : ZMod M) = (a.toNat : ZMod M) - q.toNat * b.toNat := by
  rw [hm.and_eq, ← ZMod.cast_natCast hm.dvd, toNat_sub_cast, toNat_mul_cast,
    ZMod.cast_sub hm.dvd, ZMod.cast_mul hm.dvd, ZMod.cast_natCast hm.dvd,
    ZMod.cast_natCast hm.dvd, ZMod.cast_natCast hm.dvd]

@[expose] def bz (M : ℕ) (v : ByteArray) (k : ℕ) : ZMod M := ((v.get! k).toNat : ZMod M)

theorem bz_eq_zero {M : ℕ} {r : ByteArray} {j : ℕ} (h : r.get! j = 0) : bz M r j = 0 := by
  unfold bz; rw [h]; simp

theorem subRow_bz {M : ℕ} {mask : UInt8} (hm : GoodMask M mask) (q : UInt8) (row : ByteArray)
    (n j : ℕ) (hrow : ∀ k < j, row.get! k = 0) (v : ByteArray) (hv : v.size = n) (k : ℕ)
    (hk : k < n) :
    bz M (subRow mask q row n j v) k = bz M v k - (q.toNat : ZMod M) * bz M row k := by
  unfold bz
  rw [subRow_get mask q row n j v k (by omega)]
  by_cases hjk : j ≤ k
  · rw [ite_eq_left ⟨hjk, hk⟩, sub_mask_cast hm]
  · rw [ite_eq_right (by omega), hrow k (by omega)]
    simp

theorem elimGo_spec {M : ℕ} {mask : UInt8} (hm : GoodMask M mask) (rows : Array ByteArray)
    (pexp : Array ℕ) (n : ℕ) (hup : ∀ t < n, ∀ k < t, rows[t]!.get! k = 0) :
    ∀ j (v qs : ByteArray), v.size = n → qs.size = n → (∀ t, j ≤ t → t < n → qs.get! t = 0) →
      (elimGo mask rows pexp n j v qs).1.size = n ∧ (elimGo mask rows pexp n j v qs).2.size = n ∧
      (∀ t < j, (elimGo mask rows pexp n j v qs).2.get! t = qs.get! t) ∧
      ∀ k < n, bz M (elimGo mask rows pexp n j v qs).1 k =
        bz M v k - ∑ t ∈ Finset.Ico j n,
          bz M (elimGo mask rows pexp n j v qs).2 t * bz M rows[t]! k := by
  intro j
  induction h : n - j generalizing j with
  | zero =>
    intro v qs hv hqs _
    rw [elimGo, ite_eq_right (by omega)]
    refine ⟨hv, hqs, fun _ _ => rfl, fun k _ => ?_⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, sub_zero]
  | succ d ih =>
    intro v qs hv hqs hz
    have hj : j < n := by omega
    rw [elimGo, ite_eq_left hj]
    by_cases hx : v.get! j == 0
    · rw [ite_eq_left hx]
      obtain ⟨h1, h2, h3, h4⟩ := ih (j + 1) (by omega) v qs hv hqs
        (fun t ht ht' => hz t (by omega) ht')
      refine ⟨h1, h2, fun t ht => h3 t (by omega), fun k hk => ?_⟩
      rw [h4 k hk, Finset.sum_eq_sum_Ico_succ_bot hj,
        bz_eq_zero ((h3 j (by omega)).trans (hz j le_rfl hj))]
      ring
    · rw [ite_eq_right hx]
      simp only
      set q := UInt8.ofNat ((v.get! j).toNat >>> pexp[j]!)
      set v' := subRow mask q rows[j]! n j v
      have hv' : v'.size = n := by rw [subRow_size]; exact hv
      have hqs' : (qs.set! j q).size = n := by rw [ba_size_set!]; exact hqs
      obtain ⟨h1, h2, h3, h4⟩ := ih (j + 1) (by omega) v' (qs.set! j q) hv' hqs'
        (fun t ht ht' => by
          rw [ba_get!_set! _ _ _ _ (by omega), ite_eq_right (by omega)]
          exact hz t (by omega) ht')
      refine ⟨h1, h2, fun t ht => ?_, fun k hk => ?_⟩
      · rw [h3 t (by omega), ba_get!_set! _ _ _ _ (by omega), ite_eq_right (by omega)]
      · have hq : (elimGo mask rows pexp n (j + 1) v' (qs.set! j q)).2.get! j = q := by
          rw [h3 j (by omega), ba_get!_set! _ _ _ _ (by omega), ite_eq_left rfl]
        rw [h4 k hk, Finset.sum_eq_sum_Ico_succ_bot hj,
          subRow_bz hm q rows[j]! n j (hup j hj) v hv k hk]
        have : bz M (elimGo mask rows pexp n (j + 1) v' (qs.set! j q)).2 j =
            (q.toNat : ZMod M) := by
          unfold bz; rw [hq]
        rw [this]
        ring

theorem allLt_iff {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem allLt_spec {n : ℕ} {p : ℕ → Bool} (h : allLt n p = true) {i : ℕ} (hi : i < n) :
    p i = true :=
  allLt_iff.1 h i hi

theorem parLt_spec {n chunks : ℕ} {p : ℕ → Bool} (hc : 0 < chunks)
    (h : parLt n chunks p = true) : ∀ i < n, p i = true := by
  intro i hi
  unfold parLt at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  set sz := n / chunks + 1 with hsz
  have hsz0 : 0 < sz := Nat.succ_pos _
  have hj : i / sz < chunks := by
    rw [Nat.div_lt_iff_lt_mul hsz0]
    have h1 := Nat.div_add_mod n chunks
    have h2 := Nat.mod_lt n hc
    have : chunks * sz = chunks * (n / chunks) + chunks := by rw [hsz]; ring
    rw [this]
    generalize chunks * (n / chunks) = A at h1 ⊢
    omega
  have hstep := h (i / sz) hj
  change allLt sz (fun k => !(decide (i / sz * sz + k < n)) || p (i / sz * sz + k)) = true
    at hstep
  have := allLt_spec hstep (Nat.mod_lt i hsz0)
  have e : i / sz * sz + i % sz = i := by
    rw [mul_comm]
    exact Nat.div_add_mod i sz
  rw [e] at this
  simpa [hi] using this

theorem allZero_spec {M : ℕ} {n : ℕ} {v : ByteArray} (h : allZero n v = true) {k : ℕ}
    (hk : k < n) : bz M v k = 0 := by
  have := allLt_spec h hk
  rw [beq_iff_eq] at this
  exact bz_eq_zero this

@[expose] def byteVec (n : ℕ) (r : ByteArray) : Fin n → ℤ := fun k => ((r.get! k).toNat : ℤ)

@[expose] def sing (n : ℕ) (c : ℤ) (i : ℕ) : Fin n → ℤ := fun l => if (l : ℕ) = i then c else 0

theorem sing_mem_of_elim {n : ℕ} (rows : Array ByteArray) (pexp : Array ℕ)
    (L : Submodule ℤ (Fin n → ℤ)) (hrow : ∀ t < n, byteVec n rows[t]! ∈ L)
    (hup : ∀ t < n, ∀ k < t, rows[t]!.get! k = 0)
    (s : ℕ → ℤ) (hdiag : ∀ i < n, s i * ((rows[i]!.get! i).toNat : ℤ) = 128)
    (v : ℕ → ByteArray) (hv : ∀ i < n, (v i).size = n)
    (hvz : ∀ i < n, ∀ k < n, bz 128 (v i) k = ((s i * (rows[i]!.get! k).toNat : ℤ) : ZMod 128))
    (hcheck : ∀ i < n, allZero n (elimGo 127 rows pexp n (i + 1) (v i) (zeroBytes n)).1 = true) :
    ∀ i < n, sing n 128 i ∈ L := by
  intro i
  induction h : n - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
  intro hi
  obtain ⟨-, -, -, hspec⟩ := elimGo_spec goodMask127 rows pexp n hup (i + 1) (v i) (zeroBytes n)
    (hv i hi) (zeroBytes_size n) (fun t _ _ => zeroBytes_get n t)
  set r := elimGo 127 rows pexp n (i + 1) (v i) (zeroBytes n) with hr
  set B : ℕ → ℕ → ℤ := fun t k => ((rows[t]!.get! k).toNat : ℤ) with hB
  set uN : ℕ → ℤ := fun k =>
    s i * B i k - ∑ t ∈ Finset.Ico (i + 1) n, ((r.2.get! t).toNat : ℤ) * B t k with huN
  have hdvd : ∀ k < n, (128 : ℤ) ∣ uN k := by
    intro k hk
    have h1 := hspec k hk
    rw [allZero_spec (hcheck i hi) hk, hvz i hi k hk] at h1
    unfold bz at h1
    have h2 : ((uN k : ℤ) : ZMod 128) = 0 := by
      simp only [huN, hB]
      push_cast [Int.cast_sum] at h1 ⊢
      exact h1.symm
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 128).1 h2
  have hlow : ∀ k < i, uN k = 0 := by
    intro k hk
    simp only [huN, hB]
    rw [hup i hi k hk, Finset.sum_eq_zero fun t ht => by
      rw [hup t (Finset.mem_Ico.1 ht).2 k (by have := (Finset.mem_Ico.1 ht).1; omega)]; simp]
    simp
  have hdi : uN i = 128 := by
    simp only [huN, hB]
    rw [Finset.sum_eq_zero fun t ht => by
      rw [hup t (Finset.mem_Ico.1 ht).2 i (by have := (Finset.mem_Ico.1 ht).1; omega)]; simp]
    rw [hdiag i hi, sub_zero]
  have hmem : (fun l : Fin n => uN l) ∈ L := by
    have h1 := L.smul_mem (s i) (hrow i hi)
    have h2 : ∑ t ∈ Finset.Ico (i + 1) n, ((r.2.get! t).toNat : ℤ) • byteVec n rows[t]! ∈ L :=
      L.sum_mem fun t ht => L.smul_mem _ (hrow t (Finset.mem_Ico.1 ht).2)
    convert L.sub_mem h1 h2 using 1
    funext l
    simp only [huN, hB, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, byteVec]
  have heq : sing n 128 i = (fun l : Fin n => uN l) -
      ∑ k ∈ Finset.Ico (i + 1) n, (uN k / 128) • sing n 128 k := by
    funext l
    simp only [sing, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
      mul_zero]
    rw [Finset.sum_ite_eq]
    rcases lt_trichotomy (l : ℕ) i with hl | hl | hl
    · rw [ite_eq_right (by omega), hlow l hl, ite_eq_right (by simp; omega)]
      simp
    · rw [ite_eq_left hl, hl, hdi, ite_eq_right (by simp)]
      simp
    · rw [ite_eq_right (by omega), ite_eq_left (by simp; omega)]
      rw [Int.ediv_mul_cancel (hdvd l l.2), sub_self]
  rw [heq]
  exact L.sub_mem hmem (L.sum_mem fun k hk => L.smul_mem _
    (ih (n - k) (by have := Finset.mem_Ico.1 hk; omega) k rfl (Finset.mem_Ico.1 hk).2))

theorem smul_mem_of_sing {n : ℕ} {L : Submodule ℤ (Fin n → ℤ)} {c : ℤ}
    (h : ∀ i < n, sing n c i ∈ L) (v : Fin n → ℤ) : c • v ∈ L := by
  have : c • v = ∑ i : Fin n, v i • sing n c i := by
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, sing, mul_ite, mul_zero, Fin.val_inj]
    rw [Finset.sum_ite_eq]
    simp [mul_comm]
  rw [this]
  exact L.sum_mem fun i _ => L.smul_mem _ (h i i.2)

end CFSG.Monster.B.Dyadic
