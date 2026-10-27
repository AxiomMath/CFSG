module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.Monster.B.Geometry.Coxeter
public import CFSG.RankThree.E6.RootLatticeTools

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6

@[expose] def e6JAdj (J : Set (Fin Tag.E6.rank)) (i j : Fin Tag.E6.rank) : Prop :=
  i ∈ J ∧ j ∈ J ∧ i ≠ j ∧ Tag.E6.cartan i j ≠ 0

@[expose] def e6JComponent (J : Set (Fin Tag.E6.rank)) (i : Fin Tag.E6.rank) :
    Set (Fin Tag.E6.rank) :=
  {j | Relation.ReflTransGen (e6JAdj J) i j}

@[expose] def e6Longest (J : Set (Fin Tag.E6.rank)) : WeylGroup Tag.E6 :=
  CFSG.Monster.B.Geometry.longest (coxeterSystem Tag.E6) J

@[expose] def e6Delta (J : Set (Fin Tag.E6.rank)) (x : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  -(e6Longest J • permLattice e6Rho x)

@[expose] def e6W0 : WeylGroup Tag.E6 := e6Longest Set.univ

@[expose] def e6Xi (J : Set (Fin Tag.E6.rank)) (i : Fin Tag.E6.rank) :
    Set (Fin Tag.E6.rank → ℤ) :=
  ⋃ k : ℕ, (e6Delta J)^[k] '' parabolicRoots Tag.E6 (e6JComponent J i)

structure E6EvenFixedRootDatum (Ω : Type) [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] where
  isAlgebraic : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω
  f : ℕ
  two_le_f : 2 ≤ f
  J : Set (Fin Tag.E6.rank)
  J_ne_univ : J ≠ Set.univ
  J_stable : ∀ i, i ∈ J ↔ e6Rho i ∈ J
  i₀ : Fin Tag.E6.rank
  i₀_mem : i₀ ∈ J
  orthogonal : ∀ α ∈ e6Xi J i₀, ∀ k : ℕ, (e6Delta J)^[k] α ≠ α →
    iform α ((e6Delta J)^[k] α) = 0

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

@[expose] def q : ℕ := 2 ^ D.f

@[expose] def wJ : WeylGroup Tag.E6 := e6Longest D.J

@[expose] def δ : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ := e6Delta D.J

@[expose] def Ξ : Set (Fin Tag.E6.rank → ℤ) := e6Xi D.J D.i₀

@[expose] def psiRep : ModGL Tag.E6 Ω :=
  canonicalRep (coxeterSystem Tag.E6) Ω D.wJ * canonicalRep (coxeterSystem Tag.E6) Ω e6W0

@[expose] def frob : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  Units.map (entrywiseHom (iterateFrobenius Ω 2 D.f))

@[expose] def psi : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj D.psiRep).toMonoidHom.comp D.frob

@[expose] def rootGroup : Subgroup (ModGL Tag.E6 Ω) := rootSpan Tag.E6 Ω D.Ξ

@[expose] def torus : Subgroup (ModGL Tag.E6 Ω) := D.rootGroup ⊓ torusGroup Tag.E6 Ω

@[expose] def fixedGroup : Subgroup (ModGL Tag.E6 Ω) :=
  D.rootGroup ⊓ D.psi.eqLocus (MonoidHom.id _)

@[expose] def posRoots : Set (Fin Tag.E6.rank → ℤ) := D.Ξ ∩ {α | 0 < height α}

@[expose] def unipotent : Subgroup (ModGL Tag.E6 Ω) := rootSpan Tag.E6 Ω D.posRoots

@[expose] def fixedUnipotent : Subgroup (ModGL Tag.E6 Ω) :=
  D.unipotent ⊓ D.psi.eqLocus (MonoidHom.id _)

@[expose] def simpleOrbit (j : Fin Tag.E6.rank) : Set (Fin Tag.E6.rank → ℤ) :=
  {β | ∃ k : ℕ, β = D.δ^[k] (Pi.single j 1)}

@[expose] def orbits : Set (Set (Fin Tag.E6.rank → ℤ)) :=
  {O | ∃ j : Fin Tag.E6.rank, Pi.single j 1 ∈ D.Ξ ∧ O = D.simpleOrbit j}

open _root_.Classical in
@[expose] def orbitIndex (O : Set (Fin Tag.E6.rank → ℤ)) : Fin Tag.E6.rank :=
  if h : ∃ j : Fin Tag.E6.rank, Pi.single j 1 ∈ O then
    (Finset.univ.filter fun j : Fin Tag.E6.rank => Pi.single j 1 ∈ O).min'
      (by obtain ⟨j, hj⟩ := h; exact ⟨j, by simpa using hj⟩)
  else ⟨0, by decide⟩

@[expose] def orbitRoot (O : Set (Fin Tag.E6.rank → ℤ)) : Fin Tag.E6.rank → ℤ :=
  Pi.single (orbitIndex O) 1

@[expose] def orbitCard (O : Set (Fin Tag.E6.rank → ℤ)) : ℕ := O.ncard

@[expose] def orbitField (O : Set (Fin Tag.E6.rank → ℤ)) : Subfield Ω :=
  frobeniusFixedField Ω 2 (D.f * orbitCard O)

@[expose] def orbitMap (O : Set (Fin Tag.E6.rank → ℤ)) (A : SL2 (D.orbitField O)) :
    ModGL Tag.E6 Ω :=
  ((List.range (orbitCard O)).map fun j => rootSL2 Tag.E6 Ω (D.δ^[j] (orbitRoot O))
    (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 (D.f * j))
      (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A))).prod

@[expose] def orbitX (O : Set (Fin Tag.E6.rank → ℤ)) (a : D.orbitField O) : ModGL Tag.E6 Ω :=
  D.orbitMap O (uSL a)

@[expose] def orbitY (O : Set (Fin Tag.E6.rank → ℤ)) (a : D.orbitField O) : ModGL Tag.E6 Ω :=
  D.orbitMap O (vSL a)

theorem neg_one_eq_one_orbitField (O : Set (Fin Tag.E6.rank → ℤ)) :
    (-1 : D.orbitField O) = 1 :=
  Subtype.ext (by rw [Subfield.coe_neg, Subfield.coe_one]; exact CharTwo.neg_eq 1)

@[expose] def orbitSwap (O : Set (Fin Tag.E6.rank → ℤ)) : SL2 (D.orbitField O) :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp only [mul_zero, mul_one, zero_sub]
    exact D.neg_one_eq_one_orbitField O⟩

@[expose] def orbitN (O : Set (Fin Tag.E6.rank → ℤ)) : ModGL Tag.E6 Ω :=
  D.orbitMap O (D.orbitSwap O)

@[expose] def orbitGroup : Subgroup (ModGL Tag.E6 Ω) :=
  Subgroup.closure {g | ∃ O ∈ D.orbits, ∃ a : D.orbitField O, g = D.orbitX O a ∨ g = D.orbitY O a}

@[expose] def orbitTorus : Subgroup (ModGL Tag.E6 Ω) := D.orbitGroup ⊓ D.torus

@[expose] def orbitBorel : Set (ModGL Tag.E6 Ω) :=
  {g | ∃ t ∈ D.orbitTorus, ∃ u ∈ D.fixedUnipotent, g = t * u}

@[expose] def orbitReflection (O : Set (Fin Tag.E6.rank → ℤ)) : WeylGroup Tag.E6 :=
  setReflection O

@[expose] def relWeyl : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure (orbitReflection '' D.orbits)

@[expose] def relLength (w : WeylGroup Tag.E6) : ℕ :=
  sInf {m | ∃ l : List (WeylGroup Tag.E6), l.length = m ∧
    (∀ x ∈ l, x ∈ orbitReflection '' D.orbits) ∧ l.prod = w}

theorem psi_apply (g : ModGL Tag.E6 Ω) :
    D.psi g = D.psiRep * D.frob g * D.psiRep⁻¹ :=
  rfl

theorem mem_fixedGroup {g : ModGL Tag.E6 Ω} : g ∈ D.fixedGroup ↔ g ∈ D.rootGroup ∧ D.psi g = g :=
  Iff.rfl

theorem mem_fixedUnipotent {g : ModGL Tag.E6 Ω} :
    g ∈ D.fixedUnipotent ↔ g ∈ D.unipotent ∧ D.psi g = g :=
  Iff.rfl

theorem fixedGroup_le_rootGroup : D.fixedGroup ≤ D.rootGroup := inf_le_left

theorem fixedUnipotent_le_unipotent : D.fixedUnipotent ≤ D.unipotent := inf_le_left

theorem orbitTorus_le_orbitGroup : D.orbitTorus ≤ D.orbitGroup := inf_le_left

theorem orbitTorus_le_torus : D.orbitTorus ≤ D.torus := inf_le_right

theorem mem_orbitField {O : Set (Fin Tag.E6.rank → ℤ)} {a : Ω} :
    a ∈ D.orbitField O ↔ a ^ D.q ^ orbitCard O = a := by
  rw [orbitField, mem_frobeniusFixedField, q, ← pow_mul]

theorem orbitX_mem_orbitGroup {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    (a : D.orbitField O) : D.orbitX O a ∈ D.orbitGroup :=
  Subgroup.subset_closure ⟨O, hO, a, Or.inl rfl⟩

theorem orbitY_mem_orbitGroup {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    (a : D.orbitField O) : D.orbitY O a ∈ D.orbitGroup :=
  Subgroup.subset_closure ⟨O, hO, a, Or.inr rfl⟩

end E6EvenFixedRootDatum

end CFSG.RankThree.Lattice
