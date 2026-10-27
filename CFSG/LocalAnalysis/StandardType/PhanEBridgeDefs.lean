module

public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Phan.TitsChamber CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary

section Family

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)}
  {G : Type} [Group G]

@[expose] noncomputable def PhanFamilyE.nodeTor (S : PhanFamilyE K 2 f M G) (i : Fin n) :
    normOne (unitaryInvolution K 2 f) →* G :=
  (S.ι i).comp (torusTwo (unitaryInvolution K 2 f))

@[expose] noncomputable def PhanFamilyE.torus (S : PhanFamilyE K 2 f M G) : Subgroup G :=
  ⨆ i, (S.nodeTor i).range

@[expose] noncomputable def PhanFamilyE.parab (S : PhanFamilyE K 2 f M G) (J : Set (Fin n)) :
    Subgroup G :=
  S.torus ⊔ ⨆ j ∈ J, (S.ι j).range

structure PhanFamilyE.Good (S : PhanFamilyE K 2 f M G) : Prop where
  simplyLaced : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3
  inj : ∀ i, Function.Injective (S.ι i)
  disj : ∀ i j, i ≠ j → (S.ι i).range ⊓ (S.ι j).range = ⊥
  θ_inj : ∀ i j : Fin n, i < j → M i j = 3 → Function.Injective (S.θ i j)
  indep : iSupIndep fun i => (S.nodeTor i).range
  torus_inf : ∀ J : Set (Fin n), J.encard ≤ 2 →
    (⨆ j ∈ J, (S.ι j).range) ⊓ S.torus = ⨆ j ∈ J, (S.nodeTor j).range

theorem PhanFamilyE.torus_le_parab (S : PhanFamilyE K 2 f M G) (J : Set (Fin n)) :
    S.torus ≤ S.parab J :=
  le_sup_left

@[expose] noncomputable def phanSystemE (S : PhanFamilyE K 2 f M G) :
    ChamberSystem (Fin n) (G ⧸ S.torus) :=
  cosetSystem S.torus (fun i => S.parab {i}) (fun i => S.torus_le_parab {i})

theorem phanSystemE_adj_mk (S : PhanFamilyE K 2 f M G) {i : Fin n} {a b : G} :
    (phanSystemE S).adj i (a : G ⧸ S.torus) b ↔ a⁻¹ * b ∈ S.parab {i} :=
  cosetSystem_adj_mk _

end Family

end CFSG.ClassicalInvolution.Phan.PhanE
