module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ZLab

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]

@[expose] def IsZ2Pair (lam a β δ δ' : V) (k : ℕ) : Prop :=
  Γ.dist lam a = k ∧ Γ.Adj a β ∧ Γ.dist lam β + 1 = Γ.dist lam a ∧
    Γ.dist a δ = 2 ∧ Γ.dist a δ' = 2 ∧ Γ.dist lam δ = k + 2 ∧ Γ.dist lam δ' = k + 2 ∧
    ¬ ∃ g ∈ Gcirc Γ G a β, g • δ = δ'

@[expose] def pathSet (u v : V) : Set V := {w | Γ.dist u w + Γ.dist w v = Γ.dist u v}

variable {Γ G}

structure D10Set (L : ZLab Γ G) (α : V) where
  P : Fin 5 → Arc Γ 4
  val : valence Γ α = 5
  start : ∀ i, (P i).vert 0 = α
  inj : Function.Injective fun i => L.z ((P i).vert 4)
  dih : Nonempty (↥(Subgroup.closure (Set.range fun i => L.z ((P i).vert 4))) ≃*
    DihedralGroup 5)
  conj : ∀ i : Fin 5, (L.z ((P 2).vert 4) * L.z ((P 0).vert 4))⁻¹ * L.z ((P i).vert 4) *
    (L.z ((P 2).vert 4) * L.z ((P 0).vert 4)) = L.z ((P (i + 1)).vert 4)

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

@[expose] def beta (i : Fin 5) : V := (D.P i).vert 1

@[expose] def alpha (i : Fin 5) : V := (D.P i).vert 2

@[expose] def xi (i : Fin 5) : V := (D.P i).vert 3

@[expose] def delta (i : Fin 5) : V := (D.P i).vert 4

@[expose] def x : G := L.z (D.delta 2) * L.z (D.delta 0)

@[expose] def Delta4 : Set V := {v | ∃ i m, m ≤ 4 ∧ v = (D.P i).vert m}

@[expose] def calpha : Subgroup G := nbrStab Γ G α ⊓ Subgroup.centralizer ({D.x} : Set G)

@[expose] def IsYPair (δ' : V) : Prop :=
  IsZ2Pair Γ G α (D.alpha 0) (D.beta 0) (D.delta 0) δ' 2

@[expose] def y (δ' : V) (i : Fin 5) : G :=
  (D.x ^ (i : ℕ))⁻¹ * (L.z (D.delta 0) * L.z δ') * D.x ^ (i : ℕ)

end D10Set

end CFSG.Quasithin.Fan86
