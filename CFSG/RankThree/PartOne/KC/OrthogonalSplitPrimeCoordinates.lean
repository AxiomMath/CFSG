module

public import CFSG.RankThree.PartOne.KC.OrthogonalAdaptedPairs
public import CFSG.RankThree.PartOne.KC.OrthogonalHypCoordinates

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.RankThree.Classical
open scoped IsMulCommutative

@[expose] def charToMultiplicative {G : Type*} [Group G] {p : ℕ} (χ : Additive G →+ ZMod p) :
    G →* Multiplicative (ZMod p) where
  toFun g := Multiplicative.ofAdd (χ (Additive.ofMul g))
  map_one' := by simp
  map_mul' a b := by simp [ofMul_mul]

theorem charToMultiplicative_apply {G : Type*} [Group G] {p : ℕ} (χ : Additive G →+ ZMod p)
    (g : G) : (charToMultiplicative χ g).toAdd = χ (Additive.ofMul g) :=
  rfl

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_split_coordinates (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (G : Subgroup (V ≃ₗ[K] V)) [Finite G]
    [IsMulCommutative G] (hGQ : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGexp : ∀ g ∈ G, g ^ p = 1) (hGcard : (Nat.card G : K) ≠ 0) :
    ∃ (r : ℕ) (U : Submodule K V) (φ : V ≃ₗ[K] (Fin r ⊕ Fin r → K) × ↥U)
      (χ : Fin r → (G →* Multiplicative (ZMod p))),
      (∀ v, quadTail r (Q.comp U.subtype) (φ v) = Q v) ∧
      (∀ x ∈ U, Q x = 0 → x = 0) ∧
      (PolarNondegOn Q U) ∧
      (∀ (g : G) (i : Fin r),
        LinearEquiv.autCongr φ (g : V ≃ₗ[K] V) (hypVec K ↥U (Sum.inl i)) =
            ζ ^ (χ i g).toAdd.val • hypVec K ↥U (Sum.inl i) ∧
          LinearEquiv.autCongr φ (g : V ≃ₗ[K] V) (hypVec K ↥U (Sum.inr i)) =
            (ζ ^ (χ i g).toAdd.val)⁻¹ • hypVec K ↥U (Sum.inr i)) ∧
      (∀ (g : G) (u : ↥U),
        LinearEquiv.autCongr φ (g : V ≃ₗ[K] V) ((0 : Fin r ⊕ Fin r → K), u) = (0, u)) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (Additive G →+ ZMod p) := by
    have : Finite (Additive G →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
    exact Fintype.ofFinite _
  set ρ : G →* Module.End K V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp G.subtype with hρ
  have hρapp : ∀ (g : G) (v : V), ρ g v = (g : V ≃ₗ[K] V) v := fun g v => rfl
  have hρQ : ∀ g v, Q (ρ g v) = Q v := fun g v => by
    rw [hρapp]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hGQ g.2) v
  have hexp : ∀ g : G, g ^ p = 1 := fun g => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hGexp g g.2)
  have hΓ : (Fintype.card G : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact hGcard
  obtain ⟨r, P, χ, h1, h2, h3, h4, h5⟩ :=
    exists_adapted_hypPairs (ρ := ρ) hp hp2 hζ hexp hΓ hρQ ⊤ (fun _ _ _ => trivial)
      (polarNondegOn_top hQ)
  have hU : PolarNondegOn Q (pairsPerp P) := polarNondegOn_pairsPerp h2 hQ
  have hφe : ∀ i, (hypCoordEquiv h2).symm (hypVec K ↥(pairsPerp P) (Sum.inl i)) = (P i).e :=
    fun i => by
      rw [LinearEquiv.symm_apply_eq, hypCoordEquiv_e]
  have hφf : ∀ i, (hypCoordEquiv h2).symm (hypVec K ↥(pairsPerp P) (Sum.inr i)) = (P i).f :=
    fun i => by
      rw [LinearEquiv.symm_apply_eq, hypCoordEquiv_f]
  refine ⟨r, pairsPerp P, hypCoordEquiv h2, fun i => charToMultiplicative (χ i),
    quadTail_hypCoordEquiv h2, fun x hx hQx => h4 x trivial hx hQx, hU, ?_, ?_⟩
  · intro g i
    refine ⟨?_, ?_⟩
    · rw [LinearEquiv.autCongr_apply_apply, hφe, ← hρapp, (mem_charSpace.mp (h3 i).1) g,
        map_smul, hypCoordEquiv_e]
      rfl
    · rw [LinearEquiv.autCongr_apply_apply, hφf, ← hρapp, (mem_charSpace.mp (h3 i).2) g,
        map_smul, hypCoordEquiv_f]
      have hneg : ζ ^ ((-χ i) (Additive.ofMul g)).val = (ζ ^ (χ i (Additive.ofMul g)).val)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [AddMonoidHom.neg_apply]
        exact root_pow_val_neg_mul hζ.pow_eq_one _
      rw [hneg]
      rfl
  · intro g u
    rw [LinearEquiv.autCongr_apply_apply]
    have hu : (hypCoordEquiv h2).symm ((0 : Fin r ⊕ Fin r → K), u) = (u : V) :=
      (LinearEquiv.symm_apply_eq _).mpr (hypCoordEquiv_of_mem h2 u.2).symm
    rw [hu, ← hρapp, h5 g u trivial u.2, hypCoordEquiv_of_mem h2 u.2]

end CFSG.RankThree.PartOne.KCOrthogonal
