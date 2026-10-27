module

public import CFSG.Quasithin.EmptyFaithful.S1565B

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153L

@[expose] def KsCover (L : Type) [Group L] : Prop :=
  ∃ (Y : Type) (_ : Group Y) (Ks : Subgroup Y) (n : ℕ) (σ : L →* ↥Ks),
    3 ≤ n ∧ Odd n ∧ Shape15365 n Ks ∧ Function.Surjective σ ∧ σ.ker ≤ Subgroup.center L

theorem KsCover.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L') (h : KsCover L) :
    KsCover L' := by
  obtain ⟨Y, _, Ks, n, σ, h3, hodd, hKs, hs, hz⟩ := h
  refine ⟨Y, inferInstance, Ks, n, σ.comp e.symm.toMonoidHom, h3, hodd, hKs,
    hs.comp e.symm.surjective, ?_⟩
  intro x hx
  have hx' : e.symm x ∈ σ.ker := hx
  have := hz hx'
  rw [Subgroup.mem_center_iff] at this ⊢
  intro g
  have h1 := this (e.symm g)
  have h2 := congrArg e h1
  simpa using h2

@[expose] def TypesFourShapeNatWSec {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (V : Subgroup W) :
    Prop :=
  (∃ n', 2 ≤ n' ∧ BinaryNaturalSL L V (V ⊓ fixV L) 2 n') ∨
    (∃ f, BinaryNaturalSz L V (V ⊓ fixV L) f) ∨ (∃ a, BinaryNaturalSU3 L V (V ⊓ fixV L) a) ∨
    (∃ n', 2 ≤ n' ∧ BinaryNaturalSL L V (V ⊓ fixV L) 3 n') ∨
    (∃ n', 2 ≤ n' ∧ BinaryNaturalSp4 L V (V ⊓ fixV L) n')

end S153L

end CFSG.Quasithin
