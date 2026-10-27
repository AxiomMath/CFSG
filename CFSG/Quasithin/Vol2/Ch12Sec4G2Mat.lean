module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Open

@[expose] def encodeZ (x : quasithinZorn (ZMod 2)) : ℕ :=
  x.1.val + 2 * (x.2.1 0).val + 4 * (x.2.1 1).val + 8 * (x.2.1 2).val + 16 * (x.2.2.1 0).val +
    32 * (x.2.2.1 1).val + 64 * (x.2.2.1 2).val + 128 * x.2.2.2.val

theorem encodeZ_decodeZ : ∀ c < 256, encodeZ (decodeZ c) = c := by
  decide +kernel

theorem decodeZ_encodeZ (x : quasithinZorn (ZMod 2)) : decodeZ (encodeZ x) = x := by
  obtain ⟨c, hc, rfl⟩ := decodeZ_surjective x
  rw [encodeZ_decodeZ c hc]

theorem encodeZ_lt (x : quasithinZorn (ZMod 2)) : encodeZ x < 256 := by
  obtain ⟨c, hc, rfl⟩ := decodeZ_surjective x
  rw [encodeZ_decodeZ c hc]
  exact hc

theorem bitZ_xor (a b k : ℕ) : bitZ (a ^^^ b) k = bitZ a k + bitZ b k := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> decide

theorem decodeZ_xor (a b : ℕ) : decodeZ (a ^^^ b) = decodeZ a + decodeZ b := by
  apply zorn_ext <;> (try intro i) <;> simp [decodeZ, bitZ_xor]

theorem decodeZ_zero : decodeZ 0 = 0 := by
  decide

theorem decodeZ_eq_sum : ∀ c < 256, decodeZ c =
    ∑ k ∈ Finset.range 8, (if c.testBit k then decodeZ (2 ^ k) else 0) := by
  decide +kernel

@[expose] def mactN (m : List ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => mactN m c n ^^^ (if c.testBit n then m.getD n 0 else 0)

@[expose] def mact (m : List ℕ) (c : ℕ) : ℕ := mactN m c 8

@[expose] def mmul (m n : List ℕ) : List ℕ := n.map (mact m)

@[expose] def matCode (g : quasithinZorn (ZMod 2) → quasithinZorn (ZMod 2)) : List ℕ :=
  (List.range 8).map fun k => encodeZ (g (decodeZ (2 ^ k)))

@[expose] def idMat : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128]

theorem decodeZ_mactN (m : List ℕ) (c n : ℕ) :
    decodeZ (mactN m c n) =
      ∑ k ∈ Finset.range n, (if c.testBit k then decodeZ (m.getD k 0) else 0) := by
  induction n with
  | zero => simp [mactN, decodeZ_zero]
  | succ n ih =>
    rw [mactN, decodeZ_xor, ih, Finset.sum_range_succ]
    congr 1
    split_ifs <;> simp [decodeZ_zero]

theorem matCode_getD (g : quasithinZorn (ZMod 2) → quasithinZorn (ZMod 2)) {k : ℕ} (hk : k < 8) :
    (matCode g).getD k 0 = encodeZ (g (decodeZ (2 ^ k))) := by
  simp [matCode, hk]

theorem matCode_getD_lt (g : quasithinZorn (ZMod 2) → quasithinZorn (ZMod 2)) {k : ℕ}
    (hk : k < 8) : (matCode g).getD k 0 < 256 := by
  rw [matCode_getD g hk]
  exact encodeZ_lt _

theorem mact_lt {m : List ℕ} (hm : ∀ k < 8, m.getD k 0 < 256) (c : ℕ) : mact m c < 256 := by
  have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
  have key : ∀ n ≤ 8, mactN m c n < 2 ^ 8 := by
    intro n hn
    induction n with
    | zero => simp [mactN]
    | succ n ih =>
      rw [mactN]
      refine Nat.xor_lt_two_pow (ih (by omega)) ?_
      split_ifs
      · rw [← h256]
        exact hm n (by omega)
      · positivity
  rw [h256]
  exact key 8 le_rfl

theorem decodeZ_mact (g : quasithinZorn (ZMod 2) →ₗ[ZMod 2] quasithinZorn (ZMod 2)) {c : ℕ}
    (hc : c < 256) : decodeZ (mact (matCode g) c) = g (decodeZ c) := by
  rw [mact, decodeZ_mactN, decodeZ_eq_sum c hc, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [matCode_getD g (Finset.mem_range.1 hk), decodeZ_encodeZ]
  split_ifs <;> simp

theorem matCode_comp (g h : quasithinZorn (ZMod 2) →ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    matCode (g ∘ h) = mmul (matCode g) (matCode h) := by
  simp only [matCode, mmul, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  refine decodeZ_injective (encodeZ_lt _) (mact_lt (fun _ hj => matCode_getD_lt g hj) _) ?_
  rw [decodeZ_encodeZ, Function.comp_apply, Function.comp_apply,
    show (List.range 8).map (fun k => encodeZ (g (decodeZ (2 ^ k)))) = matCode g from rfl,
    decodeZ_mact g (encodeZ_lt _), decodeZ_encodeZ]

theorem matCode_injective {g h : quasithinZorn (ZMod 2) →ₗ[ZMod 2] quasithinZorn (ZMod 2)}
    (hgh : matCode g = matCode h) : g = h := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨c, hc, rfl⟩ := decodeZ_surjective x
  rw [← decodeZ_mact g hc, ← decodeZ_mact h hc, hgh]

theorem matCode_id : matCode id = idMat := by
  decide +kernel

theorem matCode_mul (g h : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    matCode ⇑(g * h) = mmul (matCode ⇑g) (matCode ⇑h) :=
  matCode_comp g.toLinearMap h.toLinearMap

theorem matCode_one : matCode ((1 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    quasithinZorn (ZMod 2) → quasithinZorn (ZMod 2)) = idMat :=
  matCode_id

theorem decodeZ_mact' (g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) {c : ℕ}
    (hc : c < 256) : decodeZ (mact (matCode g) c) = g (decodeZ c) :=
  decodeZ_mact g.toLinearMap hc

theorem mact_lt' (g : quasithinZorn (ZMod 2) → quasithinZorn (ZMod 2)) (c : ℕ) :
    mact (matCode g) c < 256 :=
  mact_lt (fun _ hk => matCode_getD_lt g hk) c

theorem linearEquiv_eq_of_matCode {g h : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)}
    (hgh : matCode g = matCode h) : g = h :=
  LinearEquiv.toLinearMap_injective (matCode_injective (g := g.toLinearMap) hgh)

end CFSG.Quasithin.H13.Orbit
