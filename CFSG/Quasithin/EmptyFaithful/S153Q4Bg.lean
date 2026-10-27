module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Be
public import CFSG.Quasithin.EmptyFaithful.S153Q4Bf

public section

namespace CFSG.Quasithin

namespace S153Q

theorem hat_core_B {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w * w = 1)
    (hWc : Nat.card W = 2 ^ 6) {Γ Ah X : Subgroup (MulAut W)} {z : MulAut W} (hG : HatGrp Γ Ah z)
    (hfpf : ∀ w : W, z w = w → w = 1) {lab : Fin 6 → Subgroup W} (hO : OvalData Ah z lab)
    (hAX : Ah ≤ X) (V V₁ V₂ : Subgroup W) (hVij : V = lab 4 ⊔ lab 5)
    (hV : V₁ ⊔ V₂ = V) (hI : V₁ ⊓ V₂ = ⊥) (h1 : Nat.card ↥V₁ = 4) (h2 : Nat.card ↥V₂ = 4)
    (hX' : ∀ x ∈ X, (∀ v ∈ V, x v ∈ V) → (∀ v ∈ V₁, x v ∈ V₁) ∨ (∀ v ∈ V₁, x v ∈ V₂)) :
    ¬ Group.IsSolvable ↥(X ⊓ stab V₁) := by
  subst hVij
  have C : Q4B.Ctx W Ah z lab :=
    { sq := hW2, cube := hG.z_cube, fpf := hfpf, card := hWc, zA := hG.z_mem,
      zc := hG.z_central, O := hO }
  rcases C.key hAX hV hI h1 h2 hX' with h | h
  · rw [h]; exact Q4B.conclusion C.toZCtx hO.toOvalData0 hAX 4
  · rw [h]; exact Q4B.conclusion C.toZCtx hO.toOvalData0 hAX 5

end S153Q

end CFSG.Quasithin
