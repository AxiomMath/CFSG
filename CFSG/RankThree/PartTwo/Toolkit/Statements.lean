module

public import CFSG.RankThree.PartTwo.Sec5.Hyp
public import CFSG.RankThree.SubgroupLists.CliffordPrime
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.Asc83Table.Automizer

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Subgroup CFSG.RankThree.SubgroupLists
open scoped Matrix

universe u v

section Clause2

@[expose] def linePermuting (L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    Subgroup (GL (Fin 3) (ZMod 3)) where
  carrier := {g | ∀ i, (∃ j, translate g (L i) = L j) ∧ ∃ j, translate g⁻¹ (L i) = L j}
  mul_mem' {g h} hg hh i := by
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hj⟩ := (hh i).1
      obtain ⟨k, hk⟩ := (hg j).1
      exact ⟨k, by rw [translate_mul, hj, hk]⟩
    · obtain ⟨j, hj⟩ := (hg i).2
      obtain ⟨k, hk⟩ := (hh j).2
      exact ⟨k, by rw [_root_.mul_inv_rev, translate_mul, hj, hk]⟩
  one_mem' i := ⟨⟨i, translate_one _⟩, ⟨i, by rw [inv_one, translate_one]⟩⟩
  inv_mem' {g} hg i := ⟨(hg i).2, by rw [inv_inv]; exact (hg i).1⟩

@[expose] def monomialDetOne (L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    Subgroup (GL (Fin 3) (ZMod 3)) :=
  linePermuting L ⊓ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3)

@[expose] def IsSemilinearNormalizer (F : Subgroup (GL (Fin 3) (ZMod 3))) : Prop :=
  ∃ (e : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] GaloisField 3 3)
    (μ : (GaloisField 3 3)ˣ →* GL (Fin 3) (ZMod 3)) (τ : GL (Fin 3) (ZMod 3)),
    Function.Injective μ ∧
    (∀ (c : (GaloisField 3 3)ˣ) (x : Fin 3 → ZMod 3),
      e ((μ c : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x) = (c : GaloisField 3 3) * e x) ∧
    (∀ x : Fin 3 → ZMod 3, e ((τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x) = e x ^ 3) ∧
    IsCyclic μ.range ∧ Nat.card μ.range = 26 ∧ orderOf τ = 3 ∧
    (∀ c : (GaloisField 3 3)ˣ, τ * μ c * τ⁻¹ = μ (c ^ 3)) ∧
    F ≤ μ.range ∧ μ.range ≤ normalizer (F : Set (GL (Fin 3) (ZMod 3))) ∧
    (μ.range.subgroupOf (normalizer (F : Set (GL (Fin 3) (ZMod 3))))).Normal ∧
    μ.range ⊓ zpowers τ = ⊥ ∧
    μ.range ⊔ zpowers τ = normalizer (F : Set (GL (Fin 3) (ZMod 3)))

@[expose] def BloomCaseA (G : Subgroup (GL (Fin 3) (ZMod 3))) : Prop :=
  ∃ F : Subgroup (GL (Fin 3) (ZMod 3)), F ≤ G ∧ (F.subgroupOf G).Normal ∧ Nat.card F = 13 ∧
    G ≤ normalizer (F : Set (GL (Fin 3) (ZMod 3))) ∧ IsSemilinearNormalizer F

@[expose] def BloomCaseB (G : Subgroup (GL (Fin 3) (ZMod 3))) : Prop :=
  G = CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ∨ G = ⊤

@[expose] def BloomCaseC (G : Subgroup (GL (Fin 3) (ZMod 3))) : Prop :=
  ∃ L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3), DirectSum.IsInternal L ∧
    (∀ i, Module.finrank (ZMod 3) (L i) = 1) ∧
    (∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) ∧ (∀ i j, ∃ g ∈ G, translate g (L i) = L j) ∧
    Nonempty (monomialDetOne L ≃* Equiv.Perm (Fin 4)) ∧
    monomialDetOne L ⊓ zpowers (-1) = ⊥ ∧
    ∃ G₀ : Subgroup (GL (Fin 3) (ZMod 3)), G₀ ≤ monomialDetOne L ∧
      (G₀.subgroupOf (monomialDetOne L)).index = 2 ∧ Nonempty (G₀ ≃* alternatingGroup (Fin 4)) ∧
      G₀ ≤ G ∧ G ≤ monomialDetOne L ⊔ zpowers (-1)

@[expose] def BloomIrreducibleGL33 : Prop :=
  ∀ G : Subgroup (GL (Fin 3) (ZMod 3)), IsIrreducibleOn G →
    (BloomCaseA G ∨ BloomCaseB G ∨ BloomCaseC G) ∧ ¬ (BloomCaseA G ∧ BloomCaseB G) ∧
      ¬ (BloomCaseA G ∧ BloomCaseC G) ∧ ¬ (BloomCaseB G ∧ BloomCaseC G)

end Clause2

section Clause3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {Y : Type u} [Group Y]

@[expose] noncomputable def natRepVia (φ : Y →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
    Representation (ZMod 3) Y (Fin 3 → ZMod 3) where
  toFun y := Matrix.toLin' (φ y : Matrix (Fin 3) (Fin 3) (ZMod 3))
  map_one' := by
    rw [map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  map_mul' y z := by
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl

@[expose] noncomputable def dualRepVia (φ : Y →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
    Representation (ZMod 3) Y (Fin 3 → ZMod 3) where
  toFun y := Matrix.toLin' ((φ y⁻¹ : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ)
  map_one' := by
    rw [inv_one, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one,
      Matrix.toLin'_one]
    rfl
  map_mul' y z := by
    rw [_root_.mul_inv_rev, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
      Matrix.toLin'_mul]
    rfl

@[expose] def H1Vanishing : Prop :=
  ∀ (Y : Type) [Group Y] (φ : Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)),
    Subsingleton (groupCohomology.H1 (@Rep.of (ZMod 3) Y _ _ (Fin 3 → ZMod 3) _
        (Pi.Function.module _ _ _) (natRepVia φ.toMonoidHom))) ∧
      Subsingleton (groupCohomology.H1 (@Rep.of (ZMod 3) Y _ _ (Fin 3 → ZMod 3) _
        (Pi.Function.module _ _ _) (dualRepVia φ.toMonoidHom)))

variable {D : Type v} [AddCommGroup D] [Module (ZMod 3) D]

@[expose] def IsYSubmodule (ρ : Representation (ZMod 3) Y D) (W : Submodule (ZMod 3) D) :
    Prop :=
  ∀ y : Y, ∀ w ∈ W, ρ y w ∈ W

@[expose] def SubmoduleIso (ρ : Representation (ZMod 3) Y D) (W : Submodule (ZMod 3) D)
    (σ : Representation (ZMod 3) Y (Fin 3 → ZMod 3)) : Prop :=
  ∃ f : (Fin 3 → ZMod 3) →ₗ[ZMod 3] D, Function.Injective f ∧ LinearMap.range f = W ∧
    ∀ (y : Y) (x : Fin 3 → ZMod 3), f (σ y x) = ρ y (f x)

@[expose] def QuotientIso (ρ : Representation (ZMod 3) Y D) (W : Submodule (ZMod 3) D)
    (σ : Representation (ZMod 3) Y (Fin 3 → ZMod 3)) : Prop :=
  ∃ q : D →ₗ[ZMod 3] (Fin 3 → ZMod 3), Function.Surjective q ∧ LinearMap.ker q = W ∧
    ∀ (y : Y) (d : D), q (ρ y d) = σ y (q d)

@[expose] def SL33Splitting : Prop :=
  ∀ (Y : Type u) [Group Y] (φ : Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))
    (D : Type v) [AddCommGroup D] [Module (ZMod 3) D] (ρ : Representation (ZMod 3) Y D)
    (W : Submodule (ZMod 3) D), IsYSubmodule ρ W →
    (((SubmoduleIso ρ W (natRepVia φ.toMonoidHom) ∨
          SubmoduleIso ρ W (dualRepVia φ.toMonoidHom)) ∧
        Module.finrank (ZMod 3) (D ⧸ W) = 1 ∧ ∀ (y : Y) (d : D), ρ y d - d ∈ W) ∨
      (Module.finrank (ZMod 3) W = 1 ∧ (∀ y : Y, ∀ w ∈ W, ρ y w = w) ∧
        (QuotientIso ρ W (natRepVia φ.toMonoidHom) ∨
          QuotientIso ρ W (dualRepVia φ.toMonoidHom)))) →
    ∃ W' : Submodule (ZMod 3) D, IsYSubmodule ρ W' ∧ IsCompl W W'

end Clause3

@[expose] def YoshidaTransfer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ P : Sylow p G,
    (∀ (N : Subgroup (P : Subgroup G)) [N.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ N) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) →
    ((P : Subgroup G) ⊓ commutator G =
        (P : Subgroup G) ⊓
          (commutator (normalizer (P : Set G))).map (normalizer (P : Set G)).subtype) ∧
      ((∀ (N : Subgroup G) [N.Normal], IsPGroup p (G ⧸ N) → N = ⊤) →
        (P : Subgroup G) = ⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆)

section Clause5

open CFSG.RankThree.Asc83Table

@[expose] def M12SylowData {G : Type u} [Group G] (P : Subgroup G) : Prop :=
  IsExtraspecialPGroup 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3 ∧
    IsElementaryAbelian 2 (normalizer (P : Set G) ⧸ P.subgroupOf (normalizer (P : Set G))) ∧
    Nat.card (normalizer (P : Set G) ⧸ P.subgroupOf (normalizer (P : Set G))) = 4 ∧
    {B : Subgroup G | B ≤ P ∧ Nat.card B = 9}.ncard = 4 ∧
    (∀ B : Subgroup G, B ≤ P → Nat.card B = 9 →
      IsElementaryAbelian 3 B ∧ (center P).map P.subtype ≤ B) ∧
    ∃ E F A A' : Subgroup G, {B : Subgroup G | B ≤ P ∧ Nat.card B = 9} = {E, F, A, A'} ∧
      normalizer (P : Set G) ≤ normalizer (E : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (F : Set G) ∧
      ¬ normalizer (P : Set G) ≤ normalizer (A : Set G) ∧
      ¬ normalizer (P : Set G) ≤ normalizer (A' : Set G) ∧
      (∃ g ∈ normalizer (P : Set G), A.map (MulAut.conj g).toMonoidHom = A') ∧
      Nonempty (Automizer E ≃* GL (Fin 2) (ZMod 3)) ∧
      Nonempty (Automizer F ≃* GL (Fin 2) (ZMod 3)) ∧
      centralizer (E : Set G) = E ∧ centralizer (F : Set G) = F ∧
      Nonempty (Automizer A ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Automizer A' ≃* Equiv.Perm (Fin 3)) ∧
      (∀ a ∈ A, a ∉ (center P).map P.subtype →
        Nonempty (normalizer (zpowers a : Set G) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))) ∧
      (∀ a ∈ A', a ∉ (center P).map P.subtype →
        Nonempty (normalizer (zpowers a : Set G) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)))

@[expose] def M12ThreeLocalData (G : Type u) [Group G] : Prop :=
  ∀ P : Sylow 3 G, M12SylowData (P : Subgroup G)

@[expose] def M12J1ThreeLocal : Prop :=
  (∀ (G : Type u) [Group G], Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.M12) →
      M12ThreeLocalData G) ∧
    ∀ (G : Type u) [Group G], Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J1) →
      Nat.card G = 175560 ∧ pRank 3 G = 1

end Clause5

@[expose] def KnownGroupToolkit : Prop :=
  CFSG.RankThree.PartTwo.Item37.{u} ∧ BloomIrreducibleGL33 ∧
    (H1Vanishing ∧ SL33Splitting.{u, u}) ∧ M12J1ThreeLocal.{u} ∧ YoshidaTransfer.{u}

end CFSG.RankThree.PartTwo.Toolkit
