module

public import CFSG.Quasithin.Background.JonesParshallSL5Wedge
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace S125

variable {G : Type} [Group G]

@[expose] def coordSub (S : Finset (Fin 10)) : Subgroup (Multiplicative (Fin 10 → ZMod 2)) where
  carrier := {x | ∀ k, k ∉ S → Multiplicative.toAdd x k = 0}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {x y} hx hy k hk => by
    change Multiplicative.toAdd (x * y) k = 0
    rw [toAdd_mul, Pi.add_apply, hx k hk, hy k hk, add_zero]
  inv_mem' := fun {x} hx k hk => by
    change Multiplicative.toAdd x⁻¹ k = 0
    rw [toAdd_inv, Pi.neg_apply, hx k hk, neg_zero]

@[expose] def IsUpperTri (u : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Prop :=
  ∀ i j : Fin 5, j < i → (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0

@[expose] def StabGam (k : ℕ) (g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Prop :=
  ∀ i j : Fin 5, j.val < k → k ≤ i.val → (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0

structure Frame125 (T L V : Subgroup G) where
  e : ↥V ≃* Multiplicative (Fin 10 → ZMod 2)
  γ : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
  wedge : ∀ (h : ↥(autOn L V)) (v : ↥V), e ((h : MulAut ↥V) v) =
    Multiplicative.ofAdd (JonesParshall.wedgeRep (γ h) (Multiplicative.toAdd (e v)))
  borel : ∀ t ∈ T, ∃ u : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2), IsUpperTri u ∧
    ∀ v w : ↥V, (w : G) = t * v * t⁻¹ →
      e w = Multiplicative.ofAdd (JonesParshall.wedgeRep u (Multiplicative.toAdd (e v)))

namespace Frame125

variable {T L V : Subgroup G} (F : Frame125 T L V)

@[expose] def sub (S : Finset (Fin 10)) : Subgroup G :=
  ((coordSub S).comap F.e.toMonoidHom).map V.subtype

@[expose] def V1 : Subgroup G := F.sub {0}

@[expose] def V3 : Subgroup G := F.sub {0, 1, 4}

@[expose] def V4 : Subgroup G := F.sub {0, 1, 2, 3}

@[expose] def V6 : Subgroup G := F.sub {0, 1, 2, 4, 5, 7}

@[expose] def V7 : Subgroup G := F.sub {0, 1, 2, 3, 4, 5, 6}

@[expose] def w1' : ↥V :=
  F.e.symm (Multiplicative.ofAdd (Pi.single 2 1 + Pi.single 4 1))

@[expose] def v1' : G := (F.w1' : G)

end Frame125

@[expose] def mi (T L W : Subgroup G) : Subgroup G := (L ⊔ T) ⊓ Subgroup.normalizer (W : Set G)

@[expose] def li (L W : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup CFSG.perfectResidual (L ⊓ Subgroup.normalizer (W : Set G))

@[expose] def ri (T L W : Subgroup G) : Subgroup G := pCoreOf 2 (li L W ⊔ T)

@[expose] def Frame125.P {T L V : Subgroup G} (F : Frame125 T L V) : Subgroup G :=
  mi T L F.V1 ⊓ Subgroup.normalizer (F.V3 : Set G) ⊓ Subgroup.normalizer (F.V6 : Set G)

@[expose] def Frame125.IsStab {T L V : Subgroup G} (F : Frame125 T L V) (X : Subgroup G)
    (k : ℕ) : Prop :=
  autOn X V ≤ autOn L V ∧
    ∀ h : ↥(autOn L V), (h : MulAut ↥V) ∈ autOn X V ↔ StabGam k (F.γ h)

@[expose] def QuotSL (X Y V : Subgroup G) (d : ℕ) : Prop :=
  ∃ _ : ((autOn Y V).subgroupOf (autOn X V)).Normal,
    Nonempty (↥(autOn X V) ⧸ (autOn Y V).subgroupOf (autOn X V) ≃*
      Matrix.SpecialLinearGroup (Fin d) (ZMod 2))

@[expose] def IrrSection (X A B : Subgroup G) : Prop :=
  A < B ∧ X ≤ Subgroup.normalizer (A : Set G) ∧ X ≤ Subgroup.normalizer (B : Set G) ∧
    ∀ W : Subgroup G, A ≤ W → W ≤ B → X ≤ Subgroup.normalizer (W : Set G) → W = A ∨ W = B

end S125

end CFSG.Quasithin.H13
