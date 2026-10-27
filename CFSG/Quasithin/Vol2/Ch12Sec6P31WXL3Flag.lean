module

public import CFSG.Milestones.ASVolI.F411.aSwL3BTri
public import CFSG.Milestones.ASVolI.F411.aSwL3Aut

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI

theorem l3_zeta_mul_self {K : Type} [Field K] :
    CFSG.ASVolI.burnsideF411a_L3zeta K (RingEquiv.refl K) *
      CFSG.ASVolI.burnsideF411a_L3zeta K (RingEquiv.refl K) = 1 := by
  obtain ⟨-, -, -, -, h5, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  have hf : fieldAut 3 K (RingEquiv.refl K) = 1 := map_one (fieldAut 3 K)
  have hd := h5 (burnsideF411a_w0 K)
  rw [burnsideF411a_inverseTranspose_w0] at hd
  rw [burnsideF411a_L3zeta, hf, mul_one]
  calc conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K *
        (conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K)
      = conjAut 3 K (burnsideF411a_w0 K) *
          (dualAut 3 K * conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K) := by
        simp only [mul_assoc]
    _ = conjAut 3 K (burnsideF411a_w0 K) * conjAut 3 K (burnsideF411a_w0 K) := by rw [hd]
    _ = conjAut 3 K (burnsideF411a_w0 K * burnsideF411a_w0 K) := by rw [map_mul]
    _ = 1 := by rw [burnsideF411a_w0_mul_self, map_one]

theorem l3b_inv_of_le {K : Type} [Field K] {W : Submodule K (Fin 3 → K)}
    (h : projUnitriangular 3 K ≤ projStabilizer W) :
    ∀ u ∈ unitriangular 3 K, ∀ v ∈ W, Matrix.mulVec (u : Matrix (Fin 3) (Fin 3) K) v ∈ W := by
  intro u hu v hv
  obtain ⟨s, hs, hsu⟩ := h (Subgroup.mem_map_of_mem _ hu)
  have hz : s⁻¹ * u ∈ scalars 3 K := proj_eq_proj_iff.mp hsu
  have hu' : u ∈ stabilizer W := by
    have hsplit : u = s * (s⁻¹ * u) := by group
    rw [hsplit]
    exact (stabilizer W).mul_mem hs (scalars_le_stabilizer W hz)
  have h3 : Matrix.mulVec (u : Matrix (Fin 3) (Fin 3) K) v ∈
      W.map (Matrix.mulVecLin (u : Matrix (Fin 3) (Fin 3) K)) := ⟨v, hv, rfl⟩
  rwa [mem_stabilizer.1 hu'] at h3

theorem l3b_flag_of_borel_le {K : Type} [Field K] {W : Submodule K (Fin 3 → K)}
    (h0 : ⊥ < W) (ht : W < ⊤) (hB : projUpperTriangular 3 K ≤ projStabilizer W) :
    W = flagSpace 3 K 1 ∨ W = flagSpace 3 K 2 := by
  have hU : projUnitriangular 3 K ≤ projStabilizer W :=
    le_trans (Subgroup.map_mono (unitriangular_le_upperTriangular (n := 3) (K := K))) hB
  obtain ⟨m, hm, rfl⟩ := eq_flagSpace_of_invariant (l3b_inv_of_le hU)
  interval_cases m
  · rw [flagSpace_zero] at h0
    exact absurd h0 (lt_irrefl _)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    have hfin : Module.finrank K (flagSpace 3 K 3) = Module.finrank K (Fin 3 → K) := by
      rw [finrank_flagSpace (K := K) (le_refl 3), Module.finrank_fin_fun]
    exact ht.ne (Submodule.eq_top_of_finrank_eq hfin)

theorem l3b_flag_of_image {K : Type} [Field K] {β : MulAut (projectiveSL 3 K)}
    {W W' : Submodule K (Fin 3 → K)}
    (hB : (projUpperTriangular 3 K).map β.toMonoidHom = projUpperTriangular 3 K)
    (hBW : projUpperTriangular 3 K ≤ projStabilizer W)
    (hW' : (projStabilizer W).map β.toMonoidHom = projStabilizer W')
    (h0 : ⊥ < W') (ht : W' < ⊤) :
    W' = flagSpace 3 K 1 ∨ W' = flagSpace 3 K 2 := by
  apply l3b_flag_of_borel_le h0 ht
  calc projUpperTriangular 3 K = (projUpperTriangular 3 K).map β.toMonoidHom := hB.symm
    _ ≤ (projStabilizer W).map β.toMonoidHom := Subgroup.map_mono hBW
    _ = projStabilizer W' := hW'

theorem l3b_borel_fix {K : Type} [Field K] [Finite K] [CharP K 2] (β : MulAut (projectiveSL 3 K))
    (hβ : (projUnitriangular 3 K).map β.toMonoidHom = projUnitriangular 3 K) :
    (projUpperTriangular 3 K).map β.toMonoidHom = projUpperTriangular 3 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← normalizer_projUnitriangular (K := K) (n := 3) 2,
    Subgroup.map_normalizer_eq_of_bijective (projUnitriangular 3 K) β.bijective, hβ]

theorem l3b_image_one {K : Type} [Field K] [Finite K] (β : MulAut (projectiveSL 3 K))
    (hB : (projUpperTriangular 3 K).map β.toMonoidHom = projUpperTriangular 3 K) :
    (projStabilizer (flagSpace 3 K 1)).map β.toMonoidHom = projStabilizer (flagSpace 3 K 1) ∨
      (projStabilizer (flagSpace 3 K 1)).map β.toMonoidHom = projStabilizer (flagSpace 3 K 2) := by
  obtain ⟨v0F1, -, v1nF1, -, v0nO1, -, v1O1, -, -⟩ := burnsideF411a_L3_vectors (K := K)
  have hne : ∀ i : Fin 3, (Pi.single i 1 : Fin 3 → K) ≠ 0 := fun i h0 => by
    have := congrFun h0 i
    simp at this
  have hBW : projUpperTriangular 3 K ≤ projStabilizer (flagSpace 3 K 1) :=
    projUpperTriangular_le_projStabilizer (n := 3) (K := K) 1
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) (by norm_num)).2 β
  interval_cases ε
  · have hW' := (burnsideF411a_L3_map_projStab A σ (flagSpace 3 K 1)).1
    have hpr := burnsideF411a_L3_proper A σ v0F1 (hne 0) v1nF1
    rw [burnsideF411a_L3_coordImage_flag] at hW' hpr
    rw [pow_zero, mul_one] at hB ⊢
    rcases l3b_flag_of_image hB hBW hW' hpr.1 hpr.2 with h | h
    · exact Or.inl (by rw [hW', h])
    · exact Or.inr (by rw [hW', h])
  · have hW' := (burnsideF411a_L3_map_projStab A σ (flagSpace 3 K 1)).2
    have hpr := burnsideF411a_L3_proper A σ v1O1 (hne 1) v0nO1
    rw [pow_one] at hB ⊢
    rcases l3b_flag_of_image hB hBW hW' hpr.1 hpr.2 with h | h
    · exact Or.inl (by rw [hW', h])
    · exact Or.inr (by rw [hW', h])

theorem l3b_image_two {K : Type} [Field K] [Finite K] (β : MulAut (projectiveSL 3 K))
    (hB : (projUpperTriangular 3 K).map β.toMonoidHom = projUpperTriangular 3 K) :
    (projStabilizer (flagSpace 3 K 2)).map β.toMonoidHom = projStabilizer (flagSpace 3 K 1) ∨
      (projStabilizer (flagSpace 3 K 2)).map β.toMonoidHom = projStabilizer (flagSpace 3 K 2) := by
  obtain ⟨-, v1F2, -, v2nF2, -, v0nO2, -, v2O2, -⟩ := burnsideF411a_L3_vectors (K := K)
  have hne : ∀ i : Fin 3, (Pi.single i 1 : Fin 3 → K) ≠ 0 := fun i h0 => by
    have := congrFun h0 i
    simp at this
  have hBW : projUpperTriangular 3 K ≤ projStabilizer (flagSpace 3 K 2) :=
    projUpperTriangular_le_projStabilizer (n := 3) (K := K) 2
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) (by norm_num)).2 β
  interval_cases ε
  · have hW' := (burnsideF411a_L3_map_projStab A σ (flagSpace 3 K 2)).1
    have hpr := burnsideF411a_L3_proper A σ v1F2 (hne 1) v2nF2
    rw [burnsideF411a_L3_coordImage_flag] at hW' hpr
    rw [pow_zero, mul_one] at hB ⊢
    rcases l3b_flag_of_image hB hBW hW' hpr.1 hpr.2 with h | h
    · exact Or.inl (by rw [hW', h])
    · exact Or.inr (by rw [hW', h])
  · have hW' := (burnsideF411a_L3_map_projStab A σ (flagSpace 3 K 2)).2
    have hpr := burnsideF411a_L3_proper A σ v2O2 (hne 2) v0nO2
    rw [pow_one] at hB ⊢
    rcases l3b_flag_of_image hB hBW hW' hpr.1 hpr.2 with h | h
    · exact Or.inl (by rw [hW', h])
    · exact Or.inr (by rw [hW', h])

theorem l3b_borel_main {K : Type} [Field K] [Finite K] [CharP K 2]
    (α ζ : MulAut (projectiveSL 3 K)) (hζ : ζ * ζ = 1)
    (hζ1 : (projStabilizer (flagSpace 3 K 1)).map ζ.toMonoidHom = projStabilizer (flagSpace 3 K 2))
    (hζ2 : (projStabilizer (flagSpace 3 K 2)).map ζ.toMonoidHom = projStabilizer (flagSpace 3 K 1))
    (hα : (projUnitriangular 3 K).map α.toMonoidHom = projUnitriangular 3 K) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (η : ℕ), η ≤ 1 ∧
      (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
      α = conjAut 3 K A * fieldAut 3 K σ * ζ ^ η := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hinj, -⟩ := maximal_parabolics (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨v0F1, v1F2, v1nF1, v2nF2, -⟩ := burnsideF411a_L3_vectors (K := K)
  have hne : ∀ i : Fin 3, (Pi.single i 1 : Fin 3 → K) ≠ 0 := fun i h0 => by
    have := congrFun h0 i
    simp at this
  have hF1 : flagSpace 3 K 1 ∈ {W : Submodule K (Fin 3 → K) | ⊥ < W ∧ W < ⊤} :=
    ⟨bot_lt_iff_ne_bot.mpr fun h => hne 0 (by rw [h] at v0F1; exact (Submodule.mem_bot K).mp v0F1),
      lt_top_iff_ne_top.mpr fun h => v1nF1 (h ▸ Submodule.mem_top)⟩
  have hF2 : flagSpace 3 K 2 ∈ {W : Submodule K (Fin 3 → K) | ⊥ < W ∧ W < ⊤} :=
    ⟨bot_lt_iff_ne_bot.mpr fun h => hne 1 (by rw [h] at v1F2; exact (Submodule.mem_bot K).mp v1F2),
      lt_top_iff_ne_top.mpr fun h => v2nF2 (h ▸ Submodule.mem_top)⟩
  have hPne : projStabilizer (flagSpace 3 K 1) ≠ projStabilizer (flagSpace 3 K 2) := fun h => by
    have hFF := hinj hF1 hF2 h
    exact v1nF1 (by rw [hFF]; exact v1F2)
  have hne12 : (projStabilizer (flagSpace 3 K 1)).map α.toMonoidHom ≠
      (projStabilizer (flagSpace 3 K 2)).map α.toMonoidHom := fun h =>
    hPne (Subgroup.map_injective (f := α.toMonoidHom) α.injective h)
  have hB := l3b_borel_fix α hα
  rcases l3b_image_one α hB with h1 | h1
  · have h2 : (projStabilizer (flagSpace 3 K 2)).map α.toMonoidHom =
        projStabilizer (flagSpace 3 K 2) := by
      rcases l3b_image_two α hB with h2 | h2
      · exact absurd (h1.trans h2.symm) hne12
      · exact h2
    obtain ⟨A, σ, hA, hα'⟩ := burnsideF411a_borel_aut α h1 h2
    exact ⟨A, σ, 0, Nat.zero_le _, hA, by rw [pow_zero, mul_one]; exact hα'⟩
  · have h2 : (projStabilizer (flagSpace 3 K 2)).map α.toMonoidHom =
        projStabilizer (flagSpace 3 K 1) := by
      rcases l3b_image_two α hB with h2 | h2
      · exact h2
      · exact absurd (h1.trans h2.symm) hne12
    have hc : ∀ x : MulAut (projectiveSL 3 K),
        (x * ζ).toMonoidHom = x.toMonoidHom.comp ζ.toMonoidHom :=
      fun x => MonoidHom.ext fun _ => rfl
    have hγ1 : (projStabilizer (flagSpace 3 K 1)).map (α * ζ).toMonoidHom =
        projStabilizer (flagSpace 3 K 1) := by
      rw [hc, ← Subgroup.map_map, hζ1, h2]
    have hγ2 : (projStabilizer (flagSpace 3 K 2)).map (α * ζ).toMonoidHom =
        projStabilizer (flagSpace 3 K 2) := by
      rw [hc, ← Subgroup.map_map, hζ2, h1]
    obtain ⟨A, σ, hA, hγ⟩ := burnsideF411a_borel_aut (α * ζ) hγ1 hγ2
    refine ⟨A, σ, 1, le_rfl, hA, ?_⟩
    calc α = α * (ζ * ζ) := by rw [hζ, mul_one]
      _ = α * ζ * ζ := by rw [mul_assoc]
      _ = conjAut 3 K A * fieldAut 3 K σ * ζ := by rw [hγ]
      _ = conjAut 3 K A * fieldAut 3 K σ * ζ ^ 1 := by rw [pow_one]

theorem l3_borel_aut {K : Type} [Field K] [Finite K] [CharP K 2] (α : MulAut (projectiveSL 3 K))
    (hα : (projUnitriangular 3 K).map α.toMonoidHom = projUnitriangular 3 K) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (η : ℕ), η ≤ 1 ∧
      (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
      α = conjAut 3 K A * fieldAut 3 K σ *
        CFSG.ASVolI.burnsideF411a_L3zeta K (RingEquiv.refl K) ^ η :=
  l3b_borel_main α (CFSG.ASVolI.burnsideF411a_L3zeta K (RingEquiv.refl K))
    (l3_zeta_mul_self (K := K))
    (burnsideF411a_L3zeta_map_flag_one (K := K) (RingEquiv.refl K))
    (burnsideF411a_L3zeta_map_flag_two (K := K) (RingEquiv.refl K)) hα

end CFSG.Quasithin.H13.P31X
