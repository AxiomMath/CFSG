module

public import CFSG.RankThree.PartOne.KF.D8Mod

public section

namespace CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K]

theorem dihedral_four_cases (w : DihedralGroup 4) :
    w = .r 0 ∨ w = .r 1 ∨ w = .r 2 ∨ w = .r 3 ∨
      w = .sr 0 ∨ w = .sr 1 ∨ w = .sr 2 ∨ w = .sr 3 := by
  revert w
  decide

theorem eq_one_of_sq_eq_one_of_odd (hp : Odd p) {x : rootsOfUnity p K} (hx : x ^ 2 = 1) :
    x = 1 := by
  have hxp : x ^ p = 1 := Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp x.2)
  obtain ⟨k, rfl⟩ := hp
  have : x ^ (2 * k + 1) = (x ^ 2) ^ k * x := by rw [pow_succ, pow_mul]
  rw [this, hx, one_pow, one_mul] at hxp
  exact hxp

theorem d8Act_injective (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Function.Injective (d8Act : DihedralGroup 4 →* MulAut (D8Mod p K)) := by
  rw [injective_iff_map_eq_one]
  obtain ⟨ζ, hζ⟩ := hζ
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ.pow_eq_one⟩ with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    have h0 : ζ = 1 := congrArg Subtype.val h
    rw [h0] at hζ
    have := hζ.eq_orderOf
    rw [orderOf_one] at this
    exact hp.ne_one this
  have hz2 : z⁻¹ ≠ z := by
    intro h
    apply hz1
    apply eq_one_of_sq_eq_one_of_odd hpodd
    rw [pow_two]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel z
  intro w hw
  have h1 : ∀ v : D8Mod p K, d8Act w v = v := fun v => by
    have := congrArg (fun φ : MulAut (D8Mod p K) => φ v) hw
    simpa using this
  rcases dihedral_four_cases w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · have := h1 (z, 1)
    rw [d8Act_r_one] at this
    exact absurd (congrArg Prod.fst this).symm hz1
  · have := h1 (z, 1)
    rw [d8Act_r_two] at this
    exact absurd (congrArg Prod.fst this) hz2
  · have := h1 (z, 1)
    rw [d8Act_r_three] at this
    exact absurd (congrArg Prod.fst this).symm hz1
  · have := h1 (z, 1)
    rw [d8Act_sr_zero] at this
    exact absurd (congrArg Prod.fst this) hz2
  · have := h1 (z, 1)
    rw [d8Act_sr_one] at this
    exact absurd (congrArg Prod.fst this).symm hz1
  · have := h1 (1, z)
    rw [d8Act_sr_two] at this
    exact absurd (congrArg Prod.snd this) hz2
  · have := h1 (z, 1)
    rw [d8Act_sr_three] at this
    exact absurd (congrArg Prod.fst this).symm hz1


section Moved

variable {V : Type*} [CommGroup V]

@[expose] def movedV {V : Type*} [Group V] (φ : MulAut V) : Subgroup V :=
  Subgroup.closure (Set.range fun v : V => φ v * v⁻¹)

@[expose] def movedHom (φ : MulAut V) : V →* V where
  toFun v := φ v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem movedV_eq_range (φ : MulAut V) : movedV φ = (movedHom φ).range := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_
  · rintro _ ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨v, rfl⟩

theorem mem_ker_movedHom (φ : MulAut V) (v : V) : v ∈ (movedHom φ).ker ↔ φ v = v := by
  rw [MonoidHom.mem_ker]
  show φ v * v⁻¹ = 1 ↔ _
  exact mul_inv_eq_one

theorem card_movedV_mul_card_fixed (φ : MulAut V) :
    Nat.card (movedV φ) * Nat.card (movedHom φ).ker = Nat.card V := by
  rw [movedV_eq_range, mul_comm]
  exact Subgroup.card_ker_mul_card_range (movedHom φ)

end Moved

section D8

theorem card_rootsOfUnity_eq' (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (rootsOfUnity p K) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

theorem card_D8Mod (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (D8Mod p K) = p ^ 2 := by
  rw [Nat.card_prod, card_rootsOfUnity_eq' hp hζ, sq]

theorem card_movedV_eq_of_fixed (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (w : DihedralGroup 4) (ι : rootsOfUnity p K →* D8Mod p K) (hι : Function.Injective ι)
    (hfix : ∀ v : D8Mod p K, d8Act w v = v ↔ ∃ x, ι x = v) :
    Nat.card (movedV (d8Act (p := p) (K := K) w)) = p := by
  have h1 := card_movedV_mul_card_fixed (d8Act (p := p) (K := K) w)
  have hker : (movedHom (d8Act (p := p) (K := K) w)).ker = ι.range := by
    ext v
    rw [mem_ker_movedHom, hfix, MonoidHom.mem_range]
  have hμ : Nat.card (rootsOfUnity p K) = p := card_rootsOfUnity_eq' hp hζ
  have hV : Nat.card (D8Mod p K) = p ^ 2 := card_D8Mod hp hζ
  rw [hker, Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm, hμ, hV] at h1
  exact Nat.eq_of_mul_eq_mul_right hp (h1.trans (sq p))

theorem card_movedV_eq_of_fixed_trivial (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (w : DihedralGroup 4) (hfix : ∀ v : D8Mod p K, d8Act w v = v → v = 1) :
    Nat.card (movedV (d8Act (p := p) (K := K) w)) = p ^ 2 := by
  have h1 := card_movedV_mul_card_fixed (d8Act (p := p) (K := K) w)
  have hker : (movedHom (d8Act (p := p) (K := K) w)).ker = ⊥ := by
    ext v
    rw [mem_ker_movedHom, Subgroup.mem_bot]
    exact ⟨hfix v, fun h => by rw [h, map_one]⟩
  have hV : Nat.card (D8Mod p K) = p ^ 2 := card_D8Mod hp hζ
  rw [hker, Subgroup.card_bot, mul_one, hV] at h1
  exact h1


theorem eq_one_of_inv_eq_self (hp : Odd p) {x : rootsOfUnity p K} (h : x⁻¹ = x) : x = 1 :=
  eq_one_of_sq_eq_one_of_odd hp (by rw [pow_two]; nth_rewrite 1 [← h]; exact inv_mul_cancel x)

theorem card_movedV_sr_zero (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (d8Act (p := p) (K := K) (DihedralGroup.sr 0))) = p := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine card_movedV_eq_of_fixed hp.pos hζ _ (MonoidHom.inr _ _)
    (fun a b h => congrArg Prod.snd h) ?_
  intro v
  rw [d8Act_sr_zero]
  constructor
  · intro h
    have h1 : v.1 = 1 := eq_one_of_inv_eq_self hpodd (congrArg Prod.fst h)
    exact ⟨v.2, Prod.ext h1.symm rfl⟩
  · rintro ⟨x, rfl⟩
    simp

theorem card_movedV_sr_one (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (d8Act (p := p) (K := K) (DihedralGroup.sr 1))) = p := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine card_movedV_eq_of_fixed hp.pos hζ _ ((MonoidHom.id _).prod invMonoidHom)
    (fun a b h => congrArg Prod.fst h) ?_
  intro v
  rw [d8Act_sr_one]
  constructor
  · intro h
    refine ⟨v.1, Prod.ext rfl ?_⟩
    have h2 : v.2⁻¹ = v.1 := congrArg Prod.fst h
    simp only [MonoidHom.prod_apply, MonoidHom.id_apply, invMonoidHom_apply]
    rw [← h2, inv_inv]
  · rintro ⟨x, rfl⟩
    simp

theorem card_movedV_sr_two (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (d8Act (p := p) (K := K) (DihedralGroup.sr 2))) = p := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine card_movedV_eq_of_fixed hp.pos hζ _ (MonoidHom.inl _ _)
    (fun a b h => congrArg Prod.fst h) ?_
  intro v
  rw [d8Act_sr_two]
  constructor
  · intro h
    have h1 : v.2 = 1 := eq_one_of_inv_eq_self hpodd (congrArg Prod.snd h)
    exact ⟨v.1, Prod.ext rfl h1.symm⟩
  · rintro ⟨x, rfl⟩
    simp

theorem card_movedV_sr_three (hp : p.Prime) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (d8Act (p := p) (K := K) (DihedralGroup.sr 3))) = p := by
  refine card_movedV_eq_of_fixed hp.pos hζ _ ((MonoidHom.id _).prod (MonoidHom.id _))
    (fun a b h => congrArg Prod.fst h) ?_
  intro v
  rw [d8Act_sr_three]
  constructor
  · intro h
    exact ⟨v.1, Prod.ext rfl (congrArg Prod.fst h).symm⟩
  · rintro ⟨x, rfl⟩
    simp

theorem card_movedV_r_two (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card (movedV (d8Act (p := p) (K := K) (DihedralGroup.r 2))) = p ^ 2 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine card_movedV_eq_of_fixed_trivial hp.pos hζ _ ?_
  intro v h
  rw [d8Act_r_two] at h
  exact Prod.ext (eq_one_of_inv_eq_self hpodd (congrArg Prod.fst h))
    (eq_one_of_inv_eq_self hpodd (congrArg Prod.snd h))

theorem exists_sr_of_card_moved (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {w : DihedralGroup 4} (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hc : Nat.card (movedV (d8Act (p := p) (K := K) w)) = p) : ∃ i, w = DihedralGroup.sr i := by
  rcases dihedral_four_cases w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hw1
  · exact absurd hw2 (by decide)
  · rw [card_movedV_r_two hp hp2 hζ] at hc
    have : p * 1 = p * p := by rw [mul_one, ← sq]; exact hc.symm
    have := Nat.eq_of_mul_eq_mul_left hp.pos this
    exact absurd this.symm hp.ne_one
  · exact absurd hw2 (by decide)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

end D8

end CFSG.RankThree.PartOne.KFU
