module

public import CFSG.SignalizerFunctorTheorem.McBride.Defs

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

@[expose] def SigClass : Type (u + 1) :=
  ∀ (H : Type u) [Group H] [Finite H], Subgroup H → Subgroup H → Prop

structure IsSigClass (p : ℕ) (Cl : SigClass.{u}) : Prop where
  mono : ∀ (H : Type u) [Group H] [Finite H] {A X Y : Subgroup H}, Y ≤ X →
    A ≤ Subgroup.normalizer (Y : Set H) → Cl H A X → Cl H A Y
  map_iff : ∀ (H K : Type u) [Group H] [Finite H] [Group K] [Finite K] (f : H →* K),
    Function.Injective f → ∀ A X : Subgroup H, Cl H A X ↔ Cl K (A.map f) (X.map f)
  quotient : ∀ (H : Type u) [Group H] [Finite H] {A X N : Subgroup H} [N.Normal],
    IsElemAbelian p A → A ≤ Subgroup.normalizer (X : Set H) → Nat.Coprime p (Nat.card X) →
      Cl H A X → Cl (H ⧸ N) (A.map (QuotientGroup.mk' N)) (X.map (QuotientGroup.mk' N))
  extension : ∀ (H : Type u) [Group H] [Finite H] {A X N : Subgroup H} [N.Normal],
    IsElemAbelian p A → A ≤ Subgroup.normalizer (X : Set H) → N ≤ X →
      Nat.Coprime p (Nat.card N) → Cl H A N →
      Cl (H ⧸ N) (A.map (QuotientGroup.mk' N)) (X.map (QuotientGroup.mk' N)) → Cl H A X

theorem IsSigClass.map_conj {p : ℕ} {Cl : SigClass.{u}} (hCl : IsSigClass p Cl) {H : Type u}
    [Group H] [Finite H] {A X : Subgroup H} {g : H} (hg : g ∈ A) (h : Cl H A X) :
    Cl H A (X.map (MulAut.conj g).toMonoidHom) := by
  have h1 := (hCl.map_iff H H (MulAut.conj g).toMonoidHom (MulAut.conj g).injective A X).mp h
  have hA : A.map (MulAut.conj g).toMonoidHom = A := by
    refine le_antisymm ?_ fun x hx => ⟨g⁻¹ * x * g, A.mul_mem (A.mul_mem (A.inv_mem hg) hx) hg, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact A.mul_mem (A.mul_mem hg hy) (A.inv_mem hg)
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
  rwa [hA] at h1

@[expose] def CompleteBelow (p : ℕ) (Cl : SigClass.{u}) (n m : ℕ) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], Nat.card H < n → ∀ (A : Subgroup H) (θ : H → Subgroup H),
    IsElemAbelian p A → Nat.card A = m → IsFunctor p A θ →
    (∀ a ∈ A, a ≠ 1 → Cl H A (θ a)) → IsCompleteIn (signalizers p A θ (Cl H A))

end CFSG.SignalizerFunctorTheorem.McBride
