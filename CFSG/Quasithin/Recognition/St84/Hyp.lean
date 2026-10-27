module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*}

@[expose] noncomputable def nOf (Γ : SimpleGraph V) (v : V) : ℕ :=
  Nat.log 2 (Nat.card (Γ.neighborSet v) - 1)

variable (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]

structure IsLocL2 (v : V) (n : ℕ) (N : Subgroup G) : Prop where
  le : N ≤ MulAction.stabilizer G v
  normal : (N.subgroupOf (MulAction.stabilizer G v)).Normal
  oTwo_le : pCoreOf 2 (MulAction.stabilizer G v) ≤ N
  quot : Nonempty (↥N ⧸ CFSG.pCore 2 ↥N ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
  trans : ∀ a b : V, Γ.Adj v a → Γ.Adj v b → ∃ g ∈ N, g • a = b

structure Hyp30 : Prop where
  isTree : Γ.IsTree
  adj_smul : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v
  faithful : ∀ g : G, (∀ v : V, g • v = v) → g = 1
  edgeTrans : EdgeTransitive Γ (⊤ : Subgroup G)
  minimal : ∀ N : Subgroup G, N.Normal → EdgeTransitive Γ N → N = ⊤
  finite_stab : ∀ v : V, Finite (MulAction.stabilizer G v)
  valency : ∀ v : V, 1 ≤ nOf Γ v ∧ Nat.card (Γ.neighborSet v) = 2 ^ nOf Γ v + 1
  locL2 : ∀ v : V, ∃ N : Subgroup G, IsLocL2 Γ G v (nOf Γ v) N

@[expose] def PreservesParts : Prop :=
  ∀ (g : G) (v : V), Even (Γ.dist v (g • v))

@[expose] def CharTwoStab : Prop :=
  ∀ v : V, CharTwo (MulAction.stabilizer G v)

@[expose] def Regular {k : ℕ} (P : Arc Γ k) : Prop :=
  LeftTransitive Γ G P.vert 0 k ∧ RightTransitive Γ G P.vert 0 k

@[expose] def IsSingularity (s : ℕ) : Prop :=
  1 ≤ s ∧ (∀ k : ℕ, 1 ≤ k → k < s → ∀ P : Arc Γ k, Regular Γ G P) ∧
    ∃ P : Arc Γ s, ¬ Regular Γ G P

structure KTrack extends Track Γ G where
  K : Subgroup G
  K_fix : ∀ k ∈ K, ∀ i : ℤ, k • line.vert i = line.vert i
  τ_norm : τ ∈ Subgroup.normalizer (K : Set G)

structure Setup extends KTrack Γ G where
  hyp : Hyp30 Γ G
  K_inf : K ⊓ pCoreOf 2 (MulAction.stabilizer G (line.vert 0) ⊓
    MulAction.stabilizer G (line.vert 1)) = ⊥
  K_sup : K ⊔ pCoreOf 2 (MulAction.stabilizer G (line.vert 0) ⊓
    MulAction.stabilizer G (line.vert 1)) =
      MulAction.stabilizer G (line.vert 0) ⊓ MulAction.stabilizer G (line.vert 1)

namespace Setup

variable {Γ G} (X : Setup Γ G)

abbrev vert (i : ℤ) : V := X.line.vert i

abbrev Gi (i : ℤ) : Subgroup G := MulAction.stabilizer G (X.vert i)

abbrev Q (i : ℤ) : Subgroup G := pCoreOf 2 (X.Gi i)

abbrev L (i : ℤ) : Subgroup G := oTwoPrime (X.Gi i)

@[expose] def Z (i : ℤ) : Subgroup G :=
  ⨆ (P : Subgroup G) (_ : IsSylowTwoOf P (X.Gi i)), centerOf P ⊓ X.Q i

abbrev Ki (i : ℤ) : Subgroup G := X.K ⊓ X.L i

noncomputable abbrev n (i : ℤ) : ℕ := nOf Γ (X.vert i)

abbrev S : Subgroup G := pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1)

@[expose] def arcStab (m r : ℤ) : Subgroup G := fixSet G (X.vert '' Set.Icc m r)

@[expose] def GT : Subgroup G := fixSet G (Set.range X.vert)

end Setup

end CFSG.Quasithin.St84
