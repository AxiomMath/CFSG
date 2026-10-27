module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModE

public section

namespace CFSG.Quasithin.H13.S127.Mod

theorem decomp_bits : ∀ c < 64, c = bitV c 0 1 ^^^ bitV c 1 2 ^^^ bitV c 2 4 ^^^ bitV c 3 8 ^^^
    bitV c 4 16 ^^^ bitV c 5 32 := by decide

theorem xor_lt_64' {a b : ℕ} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  (Nat.xor_lt_two_pow (n := 6) ha hb : _)

theorem bitV_pow_lt (c i : ℕ) {x : ℕ} (hx : x < 64) : bitV c i x < 64 := B6.bitV_lt hx

theorem B6.eq_app_of_additive (f : ℕ → ℕ)
    (hf : ∀ c < 64, ∀ d < 64, f (c ^^^ d) = f c ^^^ f d) {c : ℕ} (hc : c < 64) :
    f c = (B6.mk (f 1) (f 2) (f 4) (f 8) (f 16) (f 32)).app c := by
  have h0 : f 0 = 0 := by
    have h := hf 0 (by norm_num) 0 (by norm_num)
    rw [Nat.xor_self] at h
    rw [Nat.xor_self] at h
    exact h
  have hb : ∀ i x, f (bitV c i x) = bitV c i (f x) := by
    intro i x
    unfold bitV
    split_ifs
    · rfl
    · exact h0
  have l1 := bitV_pow_lt c 0 (x := 1) (by norm_num)
  have l2 := bitV_pow_lt c 1 (x := 2) (by norm_num)
  have l3 := bitV_pow_lt c 2 (x := 4) (by norm_num)
  have l4 := bitV_pow_lt c 3 (x := 8) (by norm_num)
  have l5 := bitV_pow_lt c 4 (x := 16) (by norm_num)
  have l6 := bitV_pow_lt c 5 (x := 32) (by norm_num)
  conv_lhs => rw [decomp_bits c hc]
  rw [hf _ (xor_lt_64' (xor_lt_64' (xor_lt_64' (xor_lt_64' l1 l2) l3) l4) l5) _ l6,
    hf _ (xor_lt_64' (xor_lt_64' (xor_lt_64' l1 l2) l3) l4) _ l5,
    hf _ (xor_lt_64' (xor_lt_64' l1 l2) l3) _ l4, hf _ (xor_lt_64' l1 l2) _ l3, hf _ l1 _ l2,
    hb, hb, hb, hb, hb, hb]
  rfl

structure Coding (V : Type) [CommGroup V] where
  cd : V → ℕ
  dc : ℕ → V
  cd_lt : ∀ v, cd v < 64
  dc_cd : ∀ v, dc (cd v) = v
  cd_dc : ∀ c, c < 64 → cd (dc c) = c
  cd_mul : ∀ u v, cd (u * v) = cd u ^^^ cd v

namespace Coding

variable {V : Type} [CommGroup V] (C : Coding V)

theorem cd_injective : Function.Injective C.cd := fun u v h => by
  rw [← C.dc_cd u, h, C.dc_cd]

theorem cd_one : C.cd 1 = 0 := by
  have h := C.cd_mul 1 1
  rw [mul_one] at h
  have h2 : C.cd 1 ^^^ C.cd 1 = 0 := Nat.xor_self _
  rw [← h] at h2
  exact h2

theorem cd_eq_zero {v : V} : C.cd v = 0 ↔ v = 1 := by
  constructor
  · intro h
    apply C.cd_injective
    rw [h, C.cd_one]
  · rintro rfl
    exact C.cd_one

theorem dc_zero : C.dc 0 = 1 := by
  rw [← C.cd_one, C.dc_cd]

theorem dc_xor {c d : ℕ} (hc : c < 64) (hd : d < 64) : C.dc (c ^^^ d) = C.dc c * C.dc d := by
  apply C.cd_injective
  rw [C.cd_dc _ (xor_lt_64' hc hd), C.cd_mul, C.cd_dc _ hc, C.cd_dc _ hd]

theorem cd_inv (v : V) : C.cd v⁻¹ = C.cd v := by
  have h := C.cd_mul v v⁻¹
  rw [mul_inv_cancel, C.cd_one] at h
  have := congrArg (fun x => C.cd v ^^^ x) h
  simp only [Nat.xor_zero] at this
  rw [this, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

@[expose] def cB (a : MulAut V) : B6 :=
  ⟨C.cd (a (C.dc 1)), C.cd (a (C.dc 2)), C.cd (a (C.dc 4)), C.cd (a (C.dc 8)),
    C.cd (a (C.dc 16)), C.cd (a (C.dc 32))⟩

theorem cB_valid (a : MulAut V) : (C.cB a).Valid :=
  ⟨C.cd_lt _, C.cd_lt _, C.cd_lt _, C.cd_lt _, C.cd_lt _, C.cd_lt _⟩

theorem cd_apply (a : MulAut V) (v : V) : C.cd (a v) = (C.cB a).app (C.cd v) := by
  have key := B6.eq_app_of_additive (fun c => C.cd (a (C.dc c))) (fun c hc d hd => by
    show C.cd (a (C.dc (c ^^^ d))) = C.cd (a (C.dc c)) ^^^ C.cd (a (C.dc d))
    rw [C.dc_xor hc hd, map_mul, C.cd_mul]) (C.cd_lt v)
  simp only [C.dc_cd] at key
  exact key

theorem cB_mul (a b : MulAut V) : C.cB (a * b) = (C.cB a).comp (C.cB b) := by
  show B6.mk (C.cd (a (b (C.dc 1)))) (C.cd (a (b (C.dc 2)))) (C.cd (a (b (C.dc 4))))
    (C.cd (a (b (C.dc 8)))) (C.cd (a (b (C.dc 16)))) (C.cd (a (b (C.dc 32)))) = _
  simp only [C.cd_apply a]
  rfl

theorem cB_one : C.cB 1 = B6.id := by
  simp only [cB, MulAut.one_apply]
  rw [C.cd_dc _ (by norm_num), C.cd_dc _ (by norm_num), C.cd_dc _ (by norm_num),
    C.cd_dc _ (by norm_num), C.cd_dc _ (by norm_num), C.cd_dc _ (by norm_num)]
  rfl

theorem cB_injective : Function.Injective C.cB := by
  intro a b h
  ext v
  apply C.cd_injective
  rw [C.cd_apply, C.cd_apply, h]

theorem cB_pow (a : MulAut V) : ∀ n : ℕ, C.cB (a ^ n) = (C.cB a).pow n
  | 0 => by rw [pow_zero, cB_one]; rfl
  | n + 1 => by rw [pow_succ', cB_mul, cB_pow a n]; rfl

theorem cB_eq_one {a : MulAut V} : C.cB a = B6.id ↔ a = 1 := by
  constructor
  · intro h
    apply C.cB_injective
    rw [h, C.cB_one]
  · rintro rfl
    exact C.cB_one

theorem apply_eq_self_iff (a : MulAut V) (v : V) : a v = v ↔ (C.cB a).app (C.cd v) = C.cd v := by
  rw [← C.cd_apply]
  exact C.cd_injective.eq_iff.symm

theorem pow_eq_one_iff (a : MulAut V) (n : ℕ) : a ^ n = 1 ↔ (C.cB a).pow n = B6.id := by
  rw [← C.cB_pow, C.cB_eq_one]

theorem card_of_codes (S : Set V) (l : List ℕ) (hl : l.Nodup) (hlt : ∀ c ∈ l, c < 64)
    (hS : ∀ v, v ∈ S ↔ C.cd v ∈ l) : Nat.card S = l.length := by
  classical
  have e : S ≃ {c : ℕ // c ∈ l} :=
    { toFun := fun v => ⟨C.cd v, (hS v).1 v.2⟩
      invFun := fun c => ⟨C.dc c, (hS _).2 (by rw [C.cd_dc _ (hlt _ c.2)]; exact c.2)⟩
      left_inv := fun v => Subtype.ext (C.dc_cd v)
      right_inv := fun c => Subtype.ext (C.cd_dc _ (hlt _ c.2)) }
  rw [Nat.card_congr e]
  have e2 : {c : ℕ // c ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hl]

end Coding

end CFSG.Quasithin.H13.S127.Mod

end
