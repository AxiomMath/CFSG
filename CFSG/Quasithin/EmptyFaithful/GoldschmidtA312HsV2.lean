module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.Quasithin

@[expose] def hsV2Coord (i : ℕ) : Fin 3 → ZMod 4 :=
  ![((i / 16 : ℕ) : ZMod 4), ((i / 4 % 4 : ℕ) : ZMod 4), ((i % 4 : ℕ) : ZMod 4)]

theorem hsV2Mul_coord : ∀ i < 64, ∀ k < 64, hsV2Mul i k < 64 ∧
    hsV2Coord (hsV2Mul i k) = hsV2Coord i + hsV2Coord k := by
  decide +kernel

theorem hsV2Coord_inj : ∀ i < 64, ∀ k < 64, hsV2Coord i = hsV2Coord k → i = k := by
  decide +kernel

theorem isZ4Cubed_of_idx {G : Type} [Group G] (idx : Fin 64 ≃ G)
    (hm : ∀ (i k : Fin 64) (hik : hsV2Mul i k < 64), idx ⟨hsV2Mul i k, hik⟩ = idx i * idx k) :
    IsZ4Cubed G := by
  have h00 : idx 0 = 1 := by
    have h := hm 0 0 (by decide)
    have e : hsV2Mul 0 0 = 0 := by decide
    have h' : idx 0 = idx 0 * idx 0 := by
      convert h using 2
      exact Fin.ext e.symm
    exact (mul_eq_left.mp h'.symm)
  let φ : G →* Multiplicative (Fin 3 → ZMod 4) :=
    { toFun := fun g => Multiplicative.ofAdd (hsV2Coord (idx.symm g).1)
      map_one' := by
        have : idx.symm 1 = 0 := by rw [← h00]; exact idx.symm_apply_apply 0
        simp only [this]
        rw [show hsV2Coord ((0 : Fin 64) : ℕ) = 0 from by decide +kernel]
        rfl
      map_mul' := by
        intro g h
        obtain ⟨i, rfl⟩ := idx.surjective g
        obtain ⟨k, rfl⟩ := idx.surjective h
        obtain ⟨hlt, hco⟩ := hsV2Mul_coord i i.2 k k.2
        have hij : idx i * idx k = idx ⟨hsV2Mul i k, hlt⟩ := (hm i k hlt).symm
        simp only [hij, Equiv.symm_apply_apply]
        rw [hco]
        rfl }
  have hinj : Function.Injective φ := by
    intro g h hgh
    obtain ⟨i, rfl⟩ := idx.surjective g
    obtain ⟨k, rfl⟩ := idx.surjective h
    have h1 : hsV2Coord i = hsV2Coord k := by
      have := congrArg Multiplicative.toAdd hgh
      simpa [φ] using this
    exact congrArg idx (Fin.ext (hsV2Coord_inj i i.2 k k.2 h1))
  have hcard : Nat.card (Multiplicative (Fin 3 → ZMod 4)) ≤ Nat.card G := by
    have h1 : Nat.card G = 64 := by
      rw [← Nat.card_congr idx, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h2 : Nat.card (Multiplicative (Fin 3 → ZMod 4)) = 64 := by
      show Nat.card (Fin 3 → ZMod 4) = 64
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    omega
  exact ⟨MulEquiv.ofBijective φ (hinj.bijective_of_nat_card_le hcard)⟩

end CFSG.Quasithin.A312Hs
