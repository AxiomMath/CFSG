module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.Quasithin

namespace B42SL3

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X7Sec CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Rep

variable {F : Type} [Field F] {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W]

@[expose] noncomputable def repOf (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    (φ : SL(3, F) →* ↥L) : Representation (ZMod 2) SL(3, F) W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((binPsi θ).toMonoidHom.comp (L.subtype.comp φ))

theorem repOf_apply (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} (φ : SL(3, F) →* ↥L)
    (x : SL(3, F)) (w : W) : repOf θ φ x w = binPsi θ ((φ x : ↥L) : MulAut V) w := rfl

theorem repOf_toAdd (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} (φ : SL(3, F) →* ↥L)
    (x : SL(3, F)) (v : V) :
    repOf θ φ x (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ (((φ x : ↥L) : MulAut V) v)) := by
  rw [repOf_apply, B42L2.toAdd_binPsi]

theorem repOf_ker (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} {φ : SL(3, F) →* ↥L}
    (hφ : Cover φ) : ∀ x : SL(3, F), repOf θ φ x = 1 → x ∈ scalars 3 F := by
  intro x hx
  refine hφ.ker_le x ?_
  have h1 : binPsi θ ((φ x : ↥L) : MulAut V) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    have := LinearMap.congr_fun hx w
    rw [repOf_apply] at this
    exact this
  have h2 : ((φ x : ↥L) : MulAut V) = 1 := (binPsi θ).injective (h1.trans (map_one _).symm)
  exact Subtype.ext h2

theorem repOf_irreducible (θ : V ≃* Multiplicative W) [Nontrivial W] {L : Subgroup (MulAut V)}
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {φ : SL(3, F) →* ↥L} (hφ : Function.Surjective φ) : (repOf θ φ).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨inferInstance, fun U hU => B42L2.irr_map θ hirr U ?_⟩
  rintro _ ⟨l, hl, rfl⟩ u hu
  obtain ⟨x, hx⟩ := hφ ⟨l, hl⟩
  have h1 := hU x u hu
  rw [repOf_apply, hx] at h1
  exact h1

theorem intertwines_map (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    {φ : SL(3, F) →* ↥L} (hφ : Function.Surjective φ) {Q : Subgroup (MulAut V)}
    (hQ : Q ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ∀ a ∈ Q.map (binPsi θ).toMonoidHom, ∀ x : SL(3, F), ∃ y : SL(3, F),
      Intertwines (repOf θ φ) a x y := by
  rintro _ ⟨g, hg, rfl⟩ x
  have hmem : g * ((φ x : ↥L) : MulAut V) * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hQ hg) _).mp (φ x).2
  obtain ⟨y, hy⟩ := hφ ⟨_, hmem⟩
  refine ⟨y, fun u => ?_⟩
  show binPsi θ g (repOf θ φ x u) = repOf θ φ y (binPsi θ g u)
  rw [repOf_apply, repOf_apply, hy, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply,
    ← map_mul, ← map_mul]
  congr 2
  group

theorem card_fix_map (θ : V ≃* Multiplicative W) (Q : Subgroup (MulAut V)) :
    Nat.card {u : W // ∀ a ∈ Q.map (binPsi θ).toMonoidHom, a u = u} = Nat.card ↥(fixV Q) :=
  natCard_fixGL_map θ Q

theorem card_le_map [Finite V] (θ : V ≃* Multiplicative W) {G Q : Subgroup (MulAut V)}
    (hQ : IsFFStarOffender G Q) :
    Nat.card W ≤ Nat.card ↥(Q.map (binPsi θ).toMonoidHom) *
      Nat.card {u : W // ∀ a ∈ Q.map (binPsi θ).toMonoidHom, a u = u} := by
  rw [card_fix_map, Subgroup.card_map_of_injective (binPsi θ).injective, ← natCard_eq θ]
  exact B42L2.card_le_of_offender hQ

theorem quad_map (θ : V ≃* Multiplicative W) {Q : Subgroup (MulAut V)} (hQ : IsQuadratic Q) :
    ∀ a ∈ Q.map (binPsi θ).toMonoidHom, ∀ b ∈ Q.map (binPsi θ).toMonoidHom, ∀ w : W,
      b (a w - w) = a w - w :=
  B42L2.quad_map θ hQ

end Rep

section Cover

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_cover_core
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4HypCore G L) {f : ℕ} (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) :
    Odd (Nat.card (Subgroup.center ↥L)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL(3, F) →* ↥L),
        Nat.card F = 2 ^ f ∧ Cover φ := by
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  have hirr := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    Setup.Family.odd_card_center_of_irreducible hV' hirr
  exact ⟨hodd, exists_cover_of_model hHyp.2.1.1 hodd hf hmodel⟩

theorem exists_cover
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) {f : ℕ} (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) :
    Odd (Nat.card (Subgroup.center ↥L)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL(3, F) →* ↥L),
        Nat.card F = 2 ^ f ∧ Cover φ :=
  exists_cover_core hV hHyp.core hf hmodel

end Cover

end B42SL3

end CFSG.Quasithin
