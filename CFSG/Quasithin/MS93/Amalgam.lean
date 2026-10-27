module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAct

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

structure Hyp20 : Prop where
  finite_edge : Finite C
  nontrivial_edge : Nontrivial C
  isPGroup_edge : IsPGroup 2 C
  normal_edgeB : X.edgeB.Normal
  faithful : X.IsFaithful

@[expose] def IsMVtx (δ : Vtx X) : Prop := δ.isLeft = true

@[expose] def stab (δ : Vtx X) : Subgroup X.Universal := MulAction.stabilizer X.Universal δ

@[expose] def kerAt (δ : Vtx X) (i : ℕ) : Subgroup X.Universal :=
  ⨅ ρ ∈ {ρ : Vtx X | X.treeGraph.dist δ ρ ≤ i}, stab X ρ

@[expose] def Qv (δ : Vtx X) : Subgroup X.Universal := kerAt X δ 1

@[expose] def ZH (β : Vtx X) : Subgroup X.Universal := omegaOneCenterOf (Qv X β)

@[expose] def ZM (α : Vtx X) : Subgroup X.Universal :=
  ⨆ ρ ∈ X.treeGraph.neighborSet α, ZH X ρ

@[expose] def Zv (δ : Vtx X) : Subgroup X.Universal := if δ.isLeft then ZM X δ else ZH X δ

@[expose] def CM (α : Vtx X) : Subgroup X.Universal :=
  stab X α ⊓ Subgroup.centralizer (ZM X α : Set X.Universal)

@[expose] def Vi (δ : Vtx X) (i : ℕ) : Subgroup X.Universal :=
  ⨆ ρ ∈ {ρ : Vtx X | X.treeGraph.dist δ ρ ≤ i}, Zv X ρ

abbrev Vv (δ : Vtx X) : Subgroup X.Universal := Vi X δ 2

@[expose] def XM (α : Vtx X) : Subgroup X.Universal := omegaOneCenterOf (Qv X α)

@[expose] noncomputable def critDist : ℕ :=
  sInf {n | ∃ α α' : Vtx X, IsMVtx X α ∧ X.treeGraph.dist α α' = n ∧ ¬ ZM X α ≤ Qv X α'}

@[expose] def IsCritical (α α' : Vtx X) : Prop :=
  IsMVtx X α ∧ X.treeGraph.dist α α' = critDist X ∧ ¬ ZM X α ≤ Qv X α'

theorem zv_of_isMVtx {δ : Vtx X} (h : IsMVtx X δ) : Zv X δ = ZM X δ := by
  simp [Zv, show δ.isLeft = true from h]

theorem zv_of_not_isMVtx {δ : Vtx X} (h : ¬ IsMVtx X δ) : Zv X δ = ZH X δ := by
  have h' : δ.isLeft = false := by simpa [IsMVtx] using h
  simp [Zv, h']

end CFSG.Quasithin.MS93
