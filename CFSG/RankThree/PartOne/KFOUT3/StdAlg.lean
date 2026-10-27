module

public import CFSG.RankThree.PartOne.KFOUT3.Cocycle

public section

namespace CFSG.RankThree.PartOne.KFOUT3

variable {K : Type} [Field K]

@[expose] noncomputable def glMap (σ : K ≃+* K) : GL (Fin 3) K →* GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.map σ.toRingHom

theorem coe_glMap (σ : K ≃+* K) (g : GL (Fin 3) K) :
    ((glMap σ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K).map σ := rfl

theorem coe_glMap_inv (σ : K ≃+* K) (g : GL (Fin 3) K) :
    (((glMap σ g)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ := by
  rw [← map_inv]
  rfl

theorem stdHom_stdHom (G G' : GL (Fin 3) K) (σ σ' : K ≃+* K) (x : SL3 K) :
    stdHom G σ (stdHom G' σ' x) = stdHom (G * glMap σ G') (σ * σ') x := by
  apply Subtype.ext
  rw [coe_stdHom, coe_stdHom, coe_stdHom]
  simp only [Matrix.map_mul, Units.val_mul, mul_inv_rev, Matrix.mul_assoc, coe_glMap_inv,
    coe_glMap]
  rw [Matrix.map_map]
  rfl

theorem stdHom_cube (G : GL (Fin 3) K) (σ : K ≃+* K) (x : SL3 K) :
    stdHom G σ (stdHom G σ (stdHom G σ x)) =
      stdHom (G * glMap σ G * glMap (σ * σ) G) (σ * σ * σ) x := by
  rw [stdHom_stdHom G G σ σ, stdHom_stdHom (G * glMap σ G) G (σ * σ) σ]

section Unique

variable [CharP K 2]

theorem std_unique {G : GL (Fin 3) K} {σ : K ≃+* K}
    (h : ∀ x : SL3 K, (QuotientGroup.mk (stdHom G σ x) : PSL3 K) = QuotientGroup.mk x) :
    σ = 1 ∧ ∃ c : K, c ≠ 0 ∧ (G : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  have hGG : (G : Matrix (Fin 3) (Fin 3) K) *
      ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGG' : ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (G : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrt : ∀ {i j : Fin 3} (hij : i ≠ j) (s : K), stdHom G σ (rt hij s) = rt hij s := by
    intro i j hij s
    exact eq_of_mk_eq_of_involution (by rw [← map_mul, rt_mul_self, map_one])
      (rt_mul_self hij s) (h _)
  have hmat : ∀ {i j : Fin 3} (_ : i ≠ j) (s : K),
      (G : Matrix (Fin 3) (Fin 3) K) * Matrix.single i j (σ s) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.single i j s := by
    intro i j hij s
    have h1 := congrArg (fun y : SL3 K => (y : Matrix (Fin 3) (Fin 3) K)) (hrt hij s)
    simp only [coe_stdHom, Matrix.SpecialLinearGroup.transvection_coe] at h1
    have e1 : ((1 : Matrix (Fin 3) (Fin 3) K) + Matrix.single i j s).map σ =
        1 + Matrix.single i j (σ s) := by
      show σ.toRingHom.mapMatrix ((1 : Matrix (Fin 3) (Fin 3) K) + Matrix.single i j s) = _
      rw [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_single]
      rfl
    rw [e1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hGG] at h1
    exact add_left_cancel h1
  have hcomm : ∀ {i j : Fin 3} (hij : i ≠ j),
      Commute (Matrix.single i j (1 : K)) (G : Matrix (Fin 3) (Fin 3) K) := by
    intro i j hij
    have h1 := hmat hij 1
    rw [map_one] at h1
    show Matrix.single i j (1 : K) * (G : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) * Matrix.single i j (1 : K)
    calc Matrix.single i j (1 : K) * (G : Matrix (Fin 3) (Fin 3) K)
        = ((G : Matrix (Fin 3) (Fin 3) K) * Matrix.single i j 1 *
            ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            (G : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
      _ = (G : Matrix (Fin 3) (Fin 3) K) * Matrix.single i j 1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hGG', Matrix.mul_one]
  have hσ : ∀ {i j : Fin 3} (hij : i ≠ j) (s : K), σ s = s := by
    intro i j hij s
    have h1 := hmat hij s
    have hc := (hcomm hij).eq
    have e : Matrix.single i j (σ s) = σ s • Matrix.single i j (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    have h2 : (G : Matrix (Fin 3) (Fin 3) K) * Matrix.single i j (σ s) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.single i j (σ s) := by
      rw [e, Matrix.mul_smul, Matrix.smul_mul, ← hc, Matrix.mul_assoc, hGG, Matrix.mul_one]
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 i) j
    simpa [Matrix.single_apply] using h3
  refine ⟨?_, ?_⟩
  · ext s
    exact hσ (show (0 : Fin 3) ≠ 1 by decide) s
  · have hs : (G : Matrix (Fin 3) (Fin 3) K) ∈ Set.range (Matrix.scalar (Fin 3)) :=
      Matrix.mem_range_scalar_of_commute_single fun i j hij => hcomm hij
    obtain ⟨c, hc⟩ := hs
    refine ⟨c, ?_, hc.symm⟩
    intro hc0
    have hdet := (Matrix.isUnit_iff_isUnit_det _).1 G.isUnit
    rw [← hc, hc0] at hdet
    simp at hdet

end Unique

end CFSG.RankThree.PartOne.KFOUT3
