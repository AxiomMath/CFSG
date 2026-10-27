module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin.F6
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

@[expose] def normIn (H X : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  H ⊓ Subgroup.normalizer (X : Set (MulAut W))

@[expose] def Pset (Y : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {A | IsFFStarOffender Y A}

@[expose] def IsPStar (Y : Subgroup (MulAut W)) (A : Subgroup (MulAut W)) : Prop :=
  A ∈ Pset Y ∧
    ∀ B ∈ Pset Y, B ≤ A →
      Nat.card A * Nat.card (fixV A) = Nat.card B * Nat.card (fixV B) → B = A

@[expose] def PstarSet (Y : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {A | IsPStar Y A}

@[expose] def Wk (k : ℕ) (X : Subgroup (MulAut W)) (Ω : Set (Subgroup (MulAut W))) :
    Subgroup (MulAut W) :=
  ⨆ (U : Subgroup (MulAut W)) (_ : U ≤ X)
    (_ : ∃ V ∈ Ω, U ≤ V ∧ E3.mQuot V U = k), U

@[expose] def O2Trivial (Y : Subgroup (MulAut W)) : Prop :=
  ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥

@[expose] def IsL3OddOver (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ q = p ^ f ∧ LieModel X .PSL 3 p f

@[expose] def IsU3OddOver (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ q = p ^ f ∧ LieModel X .PSU 3 p f

@[expose] def IsCoverL3OddOver (X : Type) [Group X] (q : ℕ) : Prop :=
  IsQuasisimple X ∧ IsL3OddOver (X ⧸ Subgroup.center X) q

@[expose] def IsCoverU3OddOver (X : Type) [Group X] (q : ℕ) : Prop :=
  IsQuasisimple X ∧ IsU3OddOver (X ⧸ Subgroup.center X) q

@[expose] def IsAutOf (X : Type) [Group X] (L : Type) [Group L] : Prop :=
  Nonempty (X ≃* MulAut L)

section ACandidate

abbrev fstarTop (H : Type) [Group H] : Subgroup H :=
  Fstar (⊤ : Subgroup H)

abbrev fstarSubOf (Y : Subgroup (MulAut W)) : Subgroup ↥Y :=
  (Fstar Y).subgroupOf Y

abbrev quotBy {A : Type} [Group A] (N : Subgroup A) (hN : N.Normal) : Type :=
  letI := hN
  A ⧸ N

@[expose] noncomputable def quotCenterAut (H : Type) [Group H] :
    MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun a := QuotientGroup.congr _ _ a (Subgroup.map_center_eq a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

@[expose] noncomputable def conjImgTop (H : Type) [Group H] (hL : (fstarTop H).Normal) :
    Subgroup (MulAut (↥(fstarTop H) ⧸ Subgroup.center ↥(fstarTop H))) :=
  letI := hL
  ((quotCenterAut ↥(fstarTop H)).comp
    (MulAut.conjNormal (G := H) (H := fstarTop H))).range

@[expose] noncomputable def conjImgSub (Y : Subgroup (MulAut W)) (hL : (fstarSubOf Y).Normal) :
    Subgroup (MulAut (↥(fstarSubOf Y) ⧸ Subgroup.center ↥(fstarSubOf Y))) :=
  letI := hL
  ((quotCenterAut ↥(fstarSubOf Y)).comp
    (MulAut.conjNormal (G := ↥Y) (H := fstarSubOf Y))).range

structure ACandidate (H : Type) [Group H] [Finite H] (n : ℕ) where
  W : Type
  [commGroup : CommGroup W]
  [finiteW : Finite W]
  expTwo : ∀ w : W, w ^ 2 = 1
  Y : Subgroup (MulAut W)
  hLn : (fstarTop H).Normal
  hLgn : (fstarSubOf Y).Normal
  hLq : IsQuasisimple ↥(fstarTop H)
  hLgq : IsQuasisimple ↥(fstarSubOf Y)
  central_factor : ∃ (Z₀ : Subgroup ↥(fstarTop H)) (hZ₀ : Z₀.Normal),
    Z₀ ≤ Subgroup.center ↥(fstarTop H) ∧
      Nonempty (↥(fstarSubOf Y) ≃* quotBy Z₀ hZ₀)
  φ : (↥(fstarTop H) ⧸ Subgroup.center ↥(fstarTop H)) ≃*
    (↥(fstarSubOf Y) ⧸ Subgroup.center ↥(fstarSubOf Y))
  img_contains : (conjImgTop H hLn).map (MulAut.congr φ).toMonoidHom ≤ conjImgSub Y hLgn
  eq_n : n = E3.aParam Y

end ACandidate

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
