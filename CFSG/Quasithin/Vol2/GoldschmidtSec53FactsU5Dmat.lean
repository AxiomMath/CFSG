module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Field

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.BA

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] noncomputable def dEnt (δ : Kˣ) : HypIndex 2 1 → K :=
  torusEntries hK (1 : Fin 2 → Kˣ) (fun _ : Fin 1 => δ)

theorem dEnt_mul (δ δ' : Kˣ) (x : HypIndex 2 1) :
    dEnt hK δ x * dEnt hK δ' x = dEnt hK (δ * δ') x := by
  rcases x with i | k | i <;> simp [dEnt, torusEntries]

theorem dEnt_one (x : HypIndex 2 1) : dEnt hK 1 x = 1 := by
  rcases x with i | k | i <;> simp [dEnt, torusEntries]

@[expose] noncomputable def dGL (δ : Kˣ) : GL (HypIndex 2 1) K :=
  ⟨diagonal (dEnt hK δ), diagonal (dEnt hK δ⁻¹),
    by rw [diagonal_mul_diagonal, ← diagonal_one]
       congr 1
       funext x
       rw [dEnt_mul, mul_inv_cancel, dEnt_one],
    by rw [diagonal_mul_diagonal, ← diagonal_one]
       congr 1
       funext x
       rw [dEnt_mul, inv_mul_cancel, dEnt_one]⟩

theorem mat_dGL (δ : Kˣ) :
    ((dGL hK δ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      diagonal (dEnt hK δ) := rfl

theorem dGL_mul (δ δ' : Kˣ) : dGL hK (δ * δ') = dGL hK δ * dGL hK δ' := by
  refine Units.ext ?_
  rw [Units.val_mul, mat_dGL, mat_dGL, mat_dGL, diagonal_mul_diagonal]
  congr 1
  funext x
  rw [dEnt_mul]

theorem dGL_one : dGL hK 1 = 1 := by
  refine Units.ext ?_
  rw [mat_dGL, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  rw [dEnt_one]

theorem dGL_inv (δ : Kˣ) : (dGL hK δ)⁻¹ = dGL hK δ⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← dGL_mul, inv_mul_cancel, dGL_one]

theorem det_dGL (δ : Kˣ) :
    ((dGL hK δ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det = δ := by
  rw [mat_dGL, dEnt, det_diagonal_torusEntries]
  simp [torusRatio]

theorem dGL_mem_hypUnitary {δ : Kˣ} (hδ : hK.norm (δ : K) = 1) :
    dGL hK δ ∈ hypUnitary hK 2 1 := by
  rw [mem_hypUnitary, mat_dGL]
  exact diagonal_torusEntries_isometry hK (1 : Fin 2 → Kˣ) (d := fun _ : Fin 1 => δ)
    (fun _ => hδ)

theorem glAut_dGL (σ : K ≃+* K) (δ : Kˣ) :
    glAut σ (dGL hK δ) = dGL hK (Units.map (σ : K →* K) δ) := by
  refine Units.ext ?_
  rw [coe_glAut, mat_dGL, mat_dGL, diagonal_map (map_zero σ)]
  congr 1
  funext x
  rcases x with i | k | i <;> simp [dEnt, torusEntries]

theorem dGL_mem_sim {δ : Kˣ} (hδ : hK.norm (δ : K) = 1) :
    (SemidirectProduct.inl (dGL hK δ) : SemiGL (HypIndex 2 1) K) ∈
      semilinearSimilitudes hK 2 1 :=
  ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact mem_hypUnitary.1 (dGL_mem_hypUnitary hK hδ)⟩

@[expose] noncomputable def dGam (δ : Kˣ) (hδ : hK.norm (δ : K) = 1) : Gam hK :=
  ⟨SemidirectProduct.inl (dGL hK δ), dGL_mem_sim hK hδ⟩

noncomputable abbrev normOne : Subgroup Kˣ := (Units.map hK.normHom).ker

theorem mem_normOne {δ : Kˣ} : δ ∈ normOne hK ↔ hK.norm (δ : K) = 1 :=
  UnitaryFieldData.mem_ker_normUnits hK

@[expose] noncomputable def dHom : normOne hK →* MulAut (hypPSU hK 2 1) where
  toFun δ := Phi hK (dGam hK δ.1 ((mem_normOne hK).1 δ.2))
  map_one' := by
    rw [show dGam hK ((1 : normOne hK) : Kˣ) ((mem_normOne hK).1 (1 : normOne hK).2) = 1 from
      Subtype.ext (by
        change SemidirectProduct.inl (dGL hK 1) = _
        rw [dGL_one, map_one]; rfl), map_one]
  map_mul' δ δ' := by
    rw [← map_mul]
    refine congrArg (Phi hK) (Subtype.ext ?_)
    change SemidirectProduct.inl (dGL hK (δ.1 * δ'.1)) =
      SemidirectProduct.inl (dGL hK δ.1) * SemidirectProduct.inl (dGL hK δ'.1)
    rw [dGL_mul, map_mul]

theorem conj_dGL_apply (δ : Kˣ) (g : GL (HypIndex 2 1) K) (i j : HypIndex 2 1) :
    ((dGL hK δ * g * (dGL hK δ)⁻¹ : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j =
      dEnt hK δ i * ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j *
        dEnt hK δ⁻¹ j := by
  rw [dGL_inv, Units.val_mul, Units.val_mul, mat_dGL, mat_dGL, mul_diagonal, diagonal_mul]

theorem dEnt_mul_inv (δ : Kˣ) (i : HypIndex 2 1) : dEnt hK δ i * dEnt hK δ⁻¹ i = 1 := by
  rw [dEnt_mul, mul_inv_cancel, dEnt_one]

theorem phi_dGam_apply (δ : Kˣ) (hδ : hK.norm (δ : K) = 1) (g : hypSU hK 2 1) :
    ((act hK (dGam hK δ hδ) g : hypSU hK 2 1) : GL (HypIndex 2 1) K) =
      dGL hK δ * (g : GL (HypIndex 2 1) K) * (dGL hK δ)⁻¹ := by
  change (dGam hK δ hδ).1.left * glAut (dGam hK δ hδ).1.right (g : GL (HypIndex 2 1) K) *
    (dGam hK δ hδ).1.left⁻¹ = _
  simp [dGam]

theorem act_dGam_mem_U (δ : Kˣ) (hδ : hK.norm (δ : K) = 1) {g : hypSU hK 2 1}
    (hg : g ∈ hypUnitriangular hK 2 1) : act hK (dGam hK δ hδ) g ∈ hypUnitriangular hK 2 1 := by
  obtain ⟨hb, hd⟩ := mem_hypUnitriangular.1 hg
  refine mem_hypUnitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [phi_dGam_apply, conj_dGL_apply, hb hij]
    simp
  · rw [phi_dGam_apply, conj_dGL_apply, hd i, mul_one, dEnt_mul_inv]

theorem inv_mul_conj_mem (δ : Kˣ) (hδ : hK.norm (δ : K) = 1) {g : hypSU hK 2 1}
    (hg : g ∈ hypBorel hK 2 1) :
    g⁻¹ * act hK (dGam hK δ hδ) g ∈ hypUnitriangular hK 2 1 := by
  have hT := blockTriangular_of_mem_hypBorel hK (r := 2) (ε := 1) le_rfl hg
  have hTi := blockTriangular_inv_fullPos hT
  set G : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hG
  set Gi : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    (((g : GL (HypIndex 2 1) K)⁻¹ : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hGi
  have hM : (((dGL hK δ * (g : GL (HypIndex 2 1) K) * (dGL hK δ)⁻¹ : GL (HypIndex 2 1) K)) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K).BlockTriangular fullPos := fun i j hij => by
    rw [conj_dGL_apply]
    have h0 : ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j = 0 :=
      hT hij
    rw [h0]
    simp
  have hmat : (((g⁻¹ * act hK (dGam hK δ hδ) g : hypSU hK 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      Gi * (((dGL hK δ * (g : GL (HypIndex 2 1) K) * (dGL hK δ)⁻¹ : GL (HypIndex 2 1) K)) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) := by
    rw [Subgroup.coe_mul, phi_dGam_apply, Units.val_mul, Subgroup.coe_inv]
  have h1 : (Gi * G) = 1 := by
    rw [hGi, hG, ← Units.val_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  refine mem_hypUnitriangular.2 ⟨?_, fun a => ?_⟩
  · rw [hmat]
    exact hTi.mul hM
  · rw [hmat]
    have h2 := mul_apply_self_of_blockTriangular fullPos_injective hTi hM a
    have h3 := mul_apply_self_of_blockTriangular fullPos_injective hTi hT a
    rw [h1, one_apply_eq] at h3
    rw [h2, conj_dGL_apply]
    have h4 : dEnt hK δ a * G a a * dEnt hK δ⁻¹ a = G a a := by
      rw [mul_comm (dEnt hK δ a), mul_assoc, dEnt_mul_inv, mul_one]
    rw [h4]
    exact h3.symm

theorem normOne_map (σ : K ≃+* K) (δ : normOne hK) :
    Units.map (σ : K →* K) δ.1 ∈ normOne hK := by
  rw [mem_normOne]
  have h := (mem_normOne hK).1 δ.2
  simp only [UnitaryFieldData.norm, Units.coe_map, MonoidHom.coe_ofClass] at h ⊢
  rw [← map_bar_comm hK σ, ← map_mul, h, map_one]

theorem fieldP_conj_dHom (σ : K ≃+* K) (δ : normOne hK) :
    fieldP hK σ * dHom hK δ * (fieldP hK σ)⁻¹ = dHom hK ⟨_, normOne_map hK σ δ⟩ := by
  change Phi hK (inrGam hK σ) * Phi hK (dGam hK δ.1 _) * (Phi hK (inrGam hK σ))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  refine congrArg (Phi hK) (Subtype.ext ?_)
  change SemidirectProduct.inr σ * SemidirectProduct.inl (dGL hK δ.1) *
    (SemidirectProduct.inr σ)⁻¹ = SemidirectProduct.inl (dGL hK (Units.map (σ : K →* K) δ.1))
  rw [← glAut_dGL, (map_inv SemidirectProduct.inr σ).symm, ← SemidirectProduct.inl_aut]

end CFSG.Quasithin.H13.Sec53F.Unit
