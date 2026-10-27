module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

@[expose] def coordAct (j n : ℕ) (P : GL (Fin n) (ZMod 2)) :
    (Fin j → Fin n → ZMod 2) ≃+ (Fin j → Fin n → ZMod 2) where
  toFun t := fun i => (P : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (t i)
  invFun t := fun i => ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (t i)
  left_inv t := by
    funext i
    simp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv t := by
    funext i
    simp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' t t' := by
    funext i
    simp [Matrix.mulVec_add]

theorem coordAct_apply (j n : ℕ) (P : GL (Fin n) (ZMod 2)) (t : Fin j → Fin n → ZMod 2)
    (i : Fin j) :
    coordAct j n P t i = (P : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (t i) := rfl

theorem transport_coordinates {G : Type} [Group G] {K U : Subgroup G} {n j : ℕ}
    (α : ↥K →* GL (Fin n) (ZMod 2)) (β : ↥U →* Multiplicative (Fin j → Fin n → ZMod 2))
    (hsurj : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) (hbij : Function.Bijective β)
    (hequi : ∀ (x : ↥K) (u v : ↥U), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
      Multiplicative.toAdd (β v) i =
        ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u) i))
    (P : GL (Fin n) (ZMod 2)) :
    ∃ (α' : ↥K →* GL (Fin n) (ZMod 2)) (β' : ↥U →* Multiplicative (Fin j → Fin n → ZMod 2)),
      Function.Surjective α' ∧ α'.ker = CFSG.pCore 2 ↥K ∧ Function.Bijective β' ∧
      (∀ (x : ↥K) (u v : ↥U), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
        Multiplicative.toAdd (β' v) i =
          ((α' x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
            (Multiplicative.toAdd (β' u) i)) ∧
      (∀ (u : ↥U) (i : Fin j), Multiplicative.toAdd (β' u) i =
        (P : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (β u) i)) := by
  let c : GL (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) := MulAut.conj P
  let e : Multiplicative (Fin j → Fin n → ZMod 2) ≃* Multiplicative (Fin j → Fin n → ZMod 2) :=
    (coordAct j n P).toMultiplicative
  refine ⟨c.toMonoidHom.comp α, e.toMonoidHom.comp β, ?_, ?_, ?_, ?_, ?_⟩
  · exact c.surjective.comp hsurj
  · rw [MonoidHom.ker_comp_of_injective α _ c.injective, hker]
  · exact e.bijective.comp hbij
  · intro x u v huv i
    have h := hequi x u v huv i
    show (coordAct j n P (Multiplicative.toAdd (β v))) i =
      ((P * α x * P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        ((coordAct j n P (Multiplicative.toAdd (β u))) i)
    rw [coordAct_apply, coordAct_apply, h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  · intro u i
    rfl

end CFSG.Quasithin.H13.Ch4.NSB
