module

public import CFSG.Quasithin.Background.Harris.Interfaces
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoprimeCentralizer

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

lemma eq_one_of_mem_A_centralizes_L [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : OneCompSetting Γ A L m) {a : GLV V} (ha : a ∈ A) (hc : ∀ l ∈ L, a * l = l * a) :
    a = 1 := by
  have hA2 : IsPGroup 2 ↥A := isPGroup_two_of_isElemAbelian h.A_elem
  have hmem : a ∈ A ⊓ (Γ ⊓ Subgroup.centralizer (L : Set (GLV V))) :=
    ⟨ha, h.A_le ha, Subgroup.mem_centralizer_iff.mpr (fun l hl => (hc l hl).symm)⟩
  rw [inf_centralizer_eq_bot_of_two_group h.L_irr Γ hA2, Subgroup.mem_bot] at hmem
  exact hmem

@[expose] def oneCompConjL {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : OneCompSetting Γ A L m)
    (γ : GLV V) (hγ : γ ∈ Γ) : ↥L ≃* ↥L where
  toFun l := ⟨γ * l * γ⁻¹, h.L_normal γ hγ l l.2⟩
  invFun l := ⟨γ⁻¹ * l * γ, by
    have := h.L_normal γ⁻¹ (Subgroup.inv_mem _ hγ) l l.2
    simpa using this⟩
  left_inv l := Subtype.ext (by dsimp only; group)
  right_inv l := Subtype.ext (by dsimp only; group)
  map_mul' x y := Subtype.ext (by dsimp only [Subgroup.coe_mul]; group)

@[expose] def oneCompConjHom {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : OneCompSetting Γ A L m) :
    ↥A →* MulAut ↥L where
  toFun a := oneCompConjL h a.1 (h.A_le a.2)
  map_one' := MulEquiv.ext fun l => Subtype.ext (by simp [oneCompConjL])
  map_mul' a b := MulEquiv.ext fun l => Subtype.ext (by
    simp only [oneCompConjL, MulAut.mul_apply, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_mul]
    group)

lemma oneCompConjHom_injective [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : OneCompSetting Γ A L m) : Function.Injective (oneCompConjHom h) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply Subtype.ext
  show (a : GLV V) = 1
  apply eq_one_of_mem_A_centralizes_L h a.2
  intro l hl
  have h1 : oneCompConjL h a.1 (h.A_le a.2) ⟨l, hl⟩ = ⟨l, hl⟩ := by
    have := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) ha
    simpa [oneCompConjHom] using this
  have h2 : (a : GLV V) * l * (a : GLV V)⁻¹ = l := congrArg Subtype.val h1
  exact mul_inv_eq_iff_eq_mul.mp h2

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
