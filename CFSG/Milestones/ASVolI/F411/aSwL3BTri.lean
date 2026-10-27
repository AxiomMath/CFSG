module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public noncomputable section

namespace CFSG.ASVolI

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem burnsideF411a_L3_map_projStab (A : GL (Fin 3) K) (σ : K ≃+* K)
    (W : Submodule K (Fin 3 → K)) :
    (projStabilizer W).map (conjAut 3 K A * fieldAut 3 K σ).toMonoidHom =
        projStabilizer ((coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) ∧
      (projStabilizer W).map (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K).toMonoidHom =
        projStabilizer ((coordImage σ (dotOrth W)).map
          (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) := by
  obtain ⟨-, -, -, -, -, -, hA, hσ, hδ, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  constructor
  · rw [show (conjAut 3 K A * fieldAut 3 K σ).toMonoidHom =
      (conjAut 3 K A).toMonoidHom.comp (fieldAut 3 K σ).toMonoidHom from rfl, ← Subgroup.map_map]
    rw [show (fieldAut 3 K σ).toMonoidHom =
      ((fieldAut 3 K σ : projectiveSL 3 K →* projectiveSL 3 K)) from rfl, hσ,
      show (conjAut 3 K A).toMonoidHom =
        ((conjAut 3 K A : projectiveSL 3 K →* projectiveSL 3 K)) from rfl, hA]
  · rw [show (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K).toMonoidHom =
      (conjAut 3 K A).toMonoidHom.comp ((fieldAut 3 K σ).toMonoidHom.comp
        (dualAut 3 K).toMonoidHom) from rfl, ← Subgroup.map_map, ← Subgroup.map_map]
    rw [show (dualAut 3 K).toMonoidHom =
      ((dualAut 3 K : projectiveSL 3 K →* projectiveSL 3 K)) from rfl, hδ,
      show (fieldAut 3 K σ).toMonoidHom =
        ((fieldAut 3 K σ : projectiveSL 3 K →* projectiveSL 3 K)) from rfl, hσ,
      show (conjAut 3 K A).toMonoidHom =
        ((conjAut 3 K A : projectiveSL 3 K →* projectiveSL 3 K)) from rfl, hA]

theorem burnsideF411a_L3_proper (A : GL (Fin 3) K) (σ : K ≃+* K)
    {W : Submodule K (Fin 3 → K)} {w v : Fin 3 → K} (hw : w ∈ W) (hw0 : w ≠ 0) (hv : v ∉ W) :
    ⊥ < (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) ∧
      (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) < ⊤ := by
  have hAinv : ∀ x, ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨bot_lt_iff_ne_bot.mpr fun hbot => ?_, lt_top_iff_ne_top.mpr fun htop => ?_⟩
  · have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun i => σ (w i)) ∈
        (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) :=
      ⟨_, coord_mem_coordImage hw, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply hw0
    have h1 := hAinv (fun i => σ (w i))
    rw [hmem, Matrix.mulVec_zero] at h1
    funext i
    have := congrFun h1 i
    simpa using this.symm
  · have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun i => σ (v i)) ∈
        (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨x, hx, hxe⟩ := hmem
    have hx' : x = fun i => σ (v i) := by
      have := congrArg (fun y => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) hxe
      simp only [mulVecLin_apply] at this
      rwa [hAinv, hAinv] at this
    have hx2 : (fun i => σ (v i)) ∈ coordImage σ W := hx' ▸ hx
    rw [mem_coordImage] at hx2
    apply hv
    simpa using hx2

theorem burnsideF411a_L3_coordImage_flag (σ : K ≃+* K) (i : ℕ) :
    coordImage σ (flagSpace 3 K i) = flagSpace 3 K i := by
  ext v
  rw [mem_coordImage, mem_flagSpace, mem_flagSpace]
  simp

theorem burnsideF411a_L3_vectors :
    (Pi.single 0 1 : Fin 3 → K) ∈ flagSpace 3 K 1 ∧ (Pi.single 1 1 : Fin 3 → K) ∈ flagSpace 3 K 2 ∧
      (Pi.single 1 1 : Fin 3 → K) ∉ flagSpace 3 K 1 ∧
      (Pi.single 2 1 : Fin 3 → K) ∉ flagSpace 3 K 2 ∧
      (Pi.single 0 1 : Fin 3 → K) ∉ dotOrth (flagSpace 3 K 1) ∧
      (Pi.single 0 1 : Fin 3 → K) ∉ dotOrth (flagSpace 3 K 2) ∧
      (Pi.single 1 1 : Fin 3 → K) ∈ dotOrth (flagSpace 3 K 1) ∧
      (Pi.single 2 1 : Fin 3 → K) ∈ dotOrth (flagSpace 3 K 2) ∧
      flagSpace 3 K 1 ≤ flagSpace 3 K 2 := by
  have e0F1 : (Pi.single 0 1 : Fin 3 → K) ∈ flagSpace 3 K 1 := by
    rw [mem_flagSpace]
    intro j hj
    fin_cases j <;> simp_all
  have e0F2 : (Pi.single 0 1 : Fin 3 → K) ∈ flagSpace 3 K 2 := by
    rw [mem_flagSpace]
    intro j hj
    fin_cases j <;> simp_all
  refine ⟨e0F1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_flagSpace]
    intro j hj
    fin_cases j <;> simp_all
  · rw [mem_flagSpace]
    intro h
    have := h 1 le_rfl
    simp at this
  · rw [mem_flagSpace]
    intro h
    have := h 2 le_rfl
    simp at this
  · rw [mem_dotOrth]
    intro h
    have := h _ e0F1
    simp at this
  · rw [mem_dotOrth]
    intro h
    have := h _ e0F2
    simp at this
  · rw [mem_dotOrth]
    intro w hw
    have h1 := (mem_flagSpace.mp hw) 1 le_rfl
    have h2 := (mem_flagSpace.mp hw) 2 (by decide)
    simp [dotProduct, Fin.sum_univ_three, h1, h2]
  · rw [mem_dotOrth]
    intro w hw
    have h2 := (mem_flagSpace.mp hw) 2 le_rfl
    simp [dotProduct, Fin.sum_univ_three, h2]
  · intro v hv
    rw [mem_flagSpace] at hv ⊢
    intro j hj
    exact hv j (by omega)

theorem burnsideF411a_borel_aut [Finite K] (β : MulAut (projectiveSL 3 K))
    (h1 : (projStabilizer (flagSpace 3 K 1)).map β.toMonoidHom =
      projStabilizer (flagSpace 3 K 1))
    (h2 : (projStabilizer (flagSpace 3 K 2)).map β.toMonoidHom =
      projStabilizer (flagSpace 3 K 2)) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K),
      (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
        β = conjAut 3 K A * fieldAut 3 K σ := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, hinj, -⟩ := maximal_parabolics (K := K) p (n := 3) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) (by norm_num)).2 β
  obtain ⟨v0F1, v1F2, v1nF1, hF2nt, v0nO1, v0nO2, v1O1, v2O2, hF12⟩ :=
    burnsideF411a_L3_vectors (K := K)
  have hne : ∀ i : Fin 3, (Pi.single i 1 : Fin 3 → K) ≠ 0 := fun i h0 => by
    have := congrFun h0 i
    simp at this
  have hF1 : flagSpace 3 K 1 ∈ {W : Submodule K (Fin 3 → K) | ⊥ < W ∧ W < ⊤} :=
    ⟨bot_lt_iff_ne_bot.mpr fun h => hne 0 (by rw [h] at v0F1; exact (Submodule.mem_bot K).mp v0F1),
      lt_top_iff_ne_top.mpr fun h => v1nF1 (h ▸ Submodule.mem_top)⟩
  have hF2 : flagSpace 3 K 2 ∈ {W : Submodule K (Fin 3 → K) | ⊥ < W ∧ W < ⊤} :=
    ⟨bot_lt_iff_ne_bot.mpr fun h => hne 1 (by rw [h] at v1F2; exact (Submodule.mem_bot K).mp v1F2),
      lt_top_iff_ne_top.mpr fun h => hF2nt (h ▸ Submodule.mem_top)⟩
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at h1 h2 ⊢
    refine ⟨A, σ, ?_, rfl⟩
    set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
    have hA1 : (flagSpace 3 K 1).map (mulVecLin M) = flagSpace 3 K 1 := by
      rw [(burnsideF411a_L3_map_projStab A σ _).1] at h1
      have hpr := burnsideF411a_L3_proper A σ v0F1 (hne 0) v1nF1
      rw [burnsideF411a_L3_coordImage_flag] at hpr h1
      exact hinj hpr hF1 h1
    have hA2 : (flagSpace 3 K 2).map (mulVecLin M) = flagSpace 3 K 2 := by
      rw [(burnsideF411a_L3_map_projStab A σ _).1] at h2
      have hpr := burnsideF411a_L3_proper A σ v1F2 (hne 1) hF2nt
      rw [burnsideF411a_L3_coordImage_flag] at hpr h2
      exact hinj hpr hF2 h2
    have hAe0 : M *ᵥ (Pi.single 0 1 : Fin 3 → K) ∈ flagSpace 3 K 1 := by
      rw [← hA1]
      exact ⟨_, v0F1, rfl⟩
    have hAe1 : M *ᵥ (Pi.single 1 1 : Fin 3 → K) ∈ flagSpace 3 K 2 := by
      rw [← hA2]
      exact ⟨_, v1F2, rfl⟩
    have c10 := (mem_flagSpace.mp hAe0) 1 le_rfl
    have c20 := (mem_flagSpace.mp hAe0) 2 (by decide)
    have c21 := (mem_flagSpace.mp hAe1) 2 le_rfl
    rw [Matrix.mulVec_single_one] at c10 c20 c21
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | simpa using c10
      | simpa using c20
      | simpa using c21
  ·
    exfalso
    rw [pow_one] at h1 h2
    rw [(burnsideF411a_L3_map_projStab A σ _).2] at h1 h2
    have hW1 := hinj (burnsideF411a_L3_proper A σ v1O1 (hne 1) v0nO1) hF1 h1
    have hW2 := hinj (burnsideF411a_L3_proper A σ v2O2 (hne 2) v0nO2) hF2 h2
    have hle : dotOrth (flagSpace 3 K 2) ≤ dotOrth (flagSpace 3 K 1) := fun v hv =>
      mem_dotOrth.mpr fun w hw => mem_dotOrth.mp hv w (hF12 hw)
    have hle' : (coordImage σ (dotOrth (flagSpace 3 K 2))).map
        (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) ≤
        (coordImage σ (dotOrth (flagSpace 3 K 1))).map
          (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) :=
      Submodule.map_mono fun v hv => mem_coordImage.mpr (hle (mem_coordImage.mp hv))
    rw [hW1, hW2] at hle'
    exact v1nF1 (hle' v1F2)

end CFSG.ASVolI
