module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.B4ModelsLie

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Assembly.LowTwoRank

@[expose] def pr4 : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

section Minors4

variable {K : Type*} [Field K]

@[expose] def minorAlt4 (i j : Fin 4) : (Fin 4 → K) [⋀^Fin 2]→ₗ[K] K :=
  (Matrix.detRowAlternating : (Fin 2 → K) [⋀^Fin 2]→ₗ[K] K).compLinearMap
    (LinearMap.pi ![LinearMap.proj i, LinearMap.proj j])

theorem minorAlt4_apply (i j : Fin 4) (v : Fin 2 → Fin 4 → K) :
    minorAlt4 i j v = v 0 i * v 1 j - v 0 j * v 1 i := by
  change Matrix.det (Matrix.of fun a => (LinearMap.pi ![LinearMap.proj i, LinearMap.proj j] :
    (Fin 4 → K) →ₗ[K] (Fin 2 → K)) (v a)) = _
  rw [det_fin_two]
  simp

@[expose] def wedgeCoord4 : ⋀[K]^2 (Fin 4 → K) →ₗ[K] (Fin 6 → K) :=
  LinearMap.pi fun k => exteriorPower.alternatingMapLinearEquiv (minorAlt4 (pr4 k).1 (pr4 k).2)

theorem wedgeCoord4_ιMulti (v : Fin 2 → Fin 4 → K) (k : Fin 6) :
    wedgeCoord4 (exteriorPower.ιMulti K 2 v) k =
      v 0 (pr4 k).1 * v 1 (pr4 k).2 - v 0 (pr4 k).2 * v 1 (pr4 k).1 := by
  rw [wedgeCoord4, LinearMap.pi_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    minorAlt4_apply]

@[expose] def wedgeMat4 (g : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun k l => g (pr4 k).1 (pr4 l).1 * g (pr4 k).2 (pr4 l).2 -
    g (pr4 k).1 (pr4 l).2 * g (pr4 k).2 (pr4 l).1

theorem wedgeCoord_map4 (g : Matrix (Fin 4) (Fin 4) K) (x : ⋀[K]^2 (Fin 4 → K)) :
    wedgeCoord4 (exteriorPower.map 2 (Matrix.toLin' g) x) = wedgeMat4 g *ᵥ wedgeCoord4 x := by
  have h : wedgeCoord4 ∘ₗ exteriorPower.map 2 (Matrix.toLin' g) =
      (wedgeMat4 g).mulVecLin ∘ₗ wedgeCoord4 := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    funext k
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, Matrix.mulVecLin_apply]
    rw [wedgeCoord4_ιMulti]
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, wedgeCoord4_ιMulti,
      Function.comp_apply, Matrix.toLin'_apply]
    fin_cases k <;> simp [wedgeMat4, pr4] <;> ring
  exact LinearMap.congr_fun h x

@[expose] def wedgeBasis4 (k : Fin 6) : ⋀[K]^2 (Fin 4 → K) :=
  exteriorPower.ιMulti K 2 ![Pi.single (pr4 k).1 1, Pi.single (pr4 k).2 1]

theorem wedgeCoord4_basis (k : Fin 6) :
    wedgeCoord4 (wedgeBasis4 k : ⋀[K]^2 (Fin 4 → K)) = Pi.single k 1 := by
  funext l
  rw [wedgeBasis4, wedgeCoord4_ιMulti]
  fin_cases k <;> fin_cases l <;> simp [pr4]

theorem wedgeCoord4_surjective : Function.Surjective (wedgeCoord4 (K := K)) := by
  intro c
  refine ⟨∑ k, c k • wedgeBasis4 k, ?_⟩
  rw [map_sum]
  simp only [map_smul, wedgeCoord4_basis]
  funext l
  simp [Finset.sum_apply, Pi.single_apply]

theorem finrank_wedge4 : Module.finrank K (⋀[K]^2 (Fin 4 → K)) = 6 := by
  rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
  rfl

theorem wedgeCoord4_bijective : Function.Bijective (wedgeCoord4 (K := K)) := by
  have h : Module.finrank K (⋀[K]^2 (Fin 4 → K)) = Module.finrank K (Fin 6 → K) := by
    rw [finrank_wedge4, Module.finrank_fin_fun]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mpr wedgeCoord4_surjective,
    wedgeCoord4_surjective⟩

variable (K) in
@[expose] def wedgeEquiv4 : ⋀[K]^2 (Fin 4 → K) ≃ₗ[K] (Fin 6 → K) :=
  LinearEquiv.ofBijective wedgeCoord4 wedgeCoord4_bijective

theorem wedgeEquiv4_apply (x : ⋀[K]^2 (Fin 4 → K)) : wedgeEquiv4 K x = wedgeCoord4 x :=
  rfl

theorem wedgeMat4_mul (g h : Matrix (Fin 4) (Fin 4) K) :
    wedgeMat4 (g * h) = wedgeMat4 g * wedgeMat4 h := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [wedgeMat4, pr4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six] <;> ring

theorem wedgeMat4_one : wedgeMat4 (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [wedgeMat4, pr4, Matrix.one_apply]

end Minors4

@[expose] def wedgeRep4 : Representation (ZMod 2) ↥(StatedSL 4 (ZMod 2)) (Fin 6 → ZMod 2) where
  toFun γ := (wedgeMat4 (((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))).mulVecLin
  map_one' := by
    simp only [Subgroup.coe_one, Units.val_one, wedgeMat4_one, Matrix.mulVecLin_one]
    rfl
  map_mul' γ δ := by
    simp only [Subgroup.coe_mul, Units.val_mul, wedgeMat4_mul, Matrix.mulVecLin_mul]
    rfl

theorem wedgeRep4_apply (γ : ↥(StatedSL 4 (ZMod 2))) (x : Fin 6 → ZMod 2) :
    wedgeRep4 γ x =
      wedgeMat4 (((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) *ᵥ x :=
  rfl

theorem sl4ExteriorTwo_coord {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : SLExteriorTwo H U Z 4) :
    ∃ (π : ↥(StatedSL 4 (ZMod 2)) →* ↥H) (β : ↥U →* Multiplicative (Fin 6 → ZMod 2)),
      Function.Surjective π ∧ Z ≤ U ∧ (∀ g : ↥H, ∀ u ∈ U, (g : MulAut V) u ∈ U) ∧
      Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd (wedgeRep4 γ (Multiplicative.toAdd (β u))) := by
  obtain ⟨π, hπ⟩ := h
  have hπ' := hπ
  obtain ⟨hπs, hZU, -, hUinv, -, -, -, -⟩ := hπ'
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.extSq (ZMod 2) 4) rfl rfl hπ
  let Φ : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) ≃* Multiplicative (Fin 6 → ZMod 2) :=
    AddEquiv.toMultiplicative (wedgeEquiv4 (ZMod 2)).toAddEquiv
  refine ⟨π, Φ.toMonoidHom.comp β, hπs, hZU, hUinv, Φ.surjective.comp hβs, fun u => ?_,
    fun γ u hu => ?_⟩
  · rw [← hβk u]
    exact map_eq_one_iff Φ Φ.injective
  · have h1 := hβe γ u hu
    change Φ (β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩) = _
    rw [h1]
    change Multiplicative.ofAdd (wedgeCoord4 (exteriorPower.map 2 (Matrix.toLin'
      (((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))) _)) = _
    rw [wedgeCoord_map4]
    rfl

end CFSG.Quasithin.JonesParshall
