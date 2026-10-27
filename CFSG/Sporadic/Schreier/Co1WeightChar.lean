module

public import CFSG.Sporadic.Schreier.Co1ElemThreeGroup

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

abbrev F4 : Type := GaloisField 2 2

theorem card_F4 : Nat.card F4 = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

instance : Finite F4 := Nat.finite_of_card_ne_zero (by rw [card_F4]; norm_num)

theorem card_F4_units : Nat.card F4ˣ = 3 := by
  classical
  have := Fintype.ofFinite F4
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, card_F4]

theorem exists_ne_one_F4 : ∃ w : F4ˣ, w ≠ 1 := by
  have : Nontrivial F4ˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_F4_units]
    norm_num
  exact exists_ne 1

@[expose] noncomputable def ω : F4ˣ := Classical.choose exists_ne_one_F4

theorem ω_ne_one : ω ≠ 1 := Classical.choose_spec exists_ne_one_F4

theorem ω_cube : ω ^ 3 = 1 := by
  rw [← card_F4_units]
  exact pow_card_eq_one'

theorem orderOf_ω : orderOf ω = 3 := orderOf_eq_prime ω_cube ω_ne_one

theorem ω_pow_val_inj {m n : ZMod 3} (h : ω ^ m.val = ω ^ n.val) : m = n := by
  have := pow_injOn_Iio_orderOf (x := ω)
  rw [orderOf_ω] at this
  exact ZMod.val_injective _ (this (Set.mem_Iio.mpr (ZMod.val_lt m))
    (Set.mem_Iio.mpr (ZMod.val_lt n)) h)

@[expose] noncomputable def eExp
    (x : E) : Fin 6 → ZMod 3 := Multiplicative.toAdd (eEquiv.symm x)

theorem eExp_mul
    (x y : E) : eExp (x * y) = eExp x + eExp y := by
  unfold eExp
  rw [map_mul, toAdd_mul]

theorem eExp_one :
    eExp 1 = 0 := by
  unfold eExp
  rw [map_one, toAdd_one]

theorem eProd_eExp
    (x : E) : eProd (eExp x) = x := by
  have := eEquiv_apply (eExp x)
  unfold eExp at this
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem eExp_eProd
    (b : Fin 6 → ZMod 3) : eExp ⟨eProd b, eProd_mem b⟩ = b := by
  have h : (⟨eProd b, eProd_mem b⟩ : E) = eEquiv (Multiplicative.ofAdd b) :=
    Subtype.ext (eEquiv_apply b).symm
  unfold eExp
  rw [h, MulEquiv.symm_apply_apply, toAdd_ofAdd]

@[expose] noncomputable def charE
    (f : Fin 6 → ZMod 3) : E →* F4ˣ where
  toFun x := ω ^ (f ⬝ᵥ eExp x).val
  map_one' := by rw [eExp_one, dotProduct_zero, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rw [eExp_mul, dotProduct_add, pow_val_add_of_pow_three ω_cube]

theorem charE_eProd
    (f b : Fin 6 → ZMod 3) :
    charE f ⟨eProd b, eProd_mem b⟩ = ω ^ (∑ i, f i * b i).val := by
  change ω ^ (f ⬝ᵥ eExp ⟨eProd b, eProd_mem b⟩).val = _
  rw [eExp_eProd]
  rfl

open Classical in
@[expose] noncomputable def charV
    (f : Fin 6 → ZMod 3) (x : GL24) : F4ˣ :=
  if hx : x ∈ E then charE f ⟨x, hx⟩ else 1

theorem charV_of_mem
    (f : Fin 6 → ZMod 3) {x : GL24} (hx : x ∈ E) :
    charV f x = charE f ⟨x, hx⟩ := by
  unfold charV
  simp only [hx, ↓reduceDIte]

end CFSG.Sporadic.Co1Schreier
