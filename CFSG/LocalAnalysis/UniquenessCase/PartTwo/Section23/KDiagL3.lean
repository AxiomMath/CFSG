module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix Module Subgroup

namespace KDiagL3

variable {K : Type} [Field K]

theorem flagStabilizer_one_two : flagStabilizer 3 K ({1, 2} : Set ℕ) = upperTriangular 3 K := by
  refine le_antisymm ?_ (upperTriangular_le_flagStabilizer _)
  intro g hg
  rw [mem_flagStabilizer] at hg
  rw [mem_upperTriangular]
  intro i j hji
  have hi3 : (i : ℕ) < 3 := i.isLt
  have hj3 : (j : ℕ) < 3 := j.isLt
  have hji' : (j : ℕ) < (i : ℕ) := Fin.lt_def.mp hji
  have key : ∀ c ∈ ({1, 2} : Set ℕ), (j : ℕ) < c → c ≤ (i : ℕ) →
      (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro c hc hjc hci
    have hmem := hg c hc
    rw [mem_stabilizer] at hmem
    have hv : (Pi.single j (1 : K) : Fin 3 → K) ∈ flagSpace 3 K c :=
      Submodule.subset_span ⟨j, hjc, rfl⟩
    have hm : (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) (Pi.single j (1 : K)) ∈
        flagSpace 3 K c := by
      have hv' := Submodule.mem_map_of_mem (p := flagSpace 3 K c)
        (f := Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) hv
      rwa [hmem] at hv'
    have hz := (mem_flagSpace (n := 3) (K := K) (i := c)).mp hm i hci
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at hz
    simpa using hz
  rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with h0 | h1
  · exact key 1 (by simp) (by omega) (by omega)
  · exact key 2 (by simp) (by omega) (by omega)

theorem overgroups_projUpperTriangular {P : Subgroup (projectiveSL 3 K)}
    (hP : projUpperTriangular 3 K ≤ P) :
    P = projUpperTriangular 3 K ∨ P = projStabilizer (flagSpace 3 K 1) ∨
      P = projStabilizer (flagSpace 3 K 2) ∨ P = ⊤ := by
  classical
  set A := P.comap (proj 3 K) with hA
  have hMA : A.map (proj 3 K) = P :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 K) P
  have hBA : upperTriangular 3 K ≤ A := by
    rw [hA, ← Subgroup.map_le_iff_le_comap]
    exact hP
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA
  set I := borelOvergroupCuts A with hI
  have hsub : I ⊆ {1, 2} := by
    rintro i ⟨hi, hin, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · left
    have hI12 : I = {1, 2} := Set.Subset.antisymm hsub (by
      intro i hi
      rcases hi with rfl | rfl
      · exact h1
      · exact h2)
    rw [← hMA, hAI, hI12, flagStabilizer_one_two]
    rfl
  · right; left
    have hI1 : I = {1} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · rfl
      · exact absurd hi h2) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h1)
    rw [← hMA, hAI, hI1, flagStabilizer_singleton]
    rfl
  · right; right; left
    have hI2 : I = {2} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · exact absurd hi h1
      · rfl) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h2)
    rw [← hMA, hAI, hI2, flagStabilizer_singleton]
    rfl
  · right; right; right
    have hI0 : I = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun i hi => by
      rcases hsub hi with rfl | rfl
      · exact h1 hi
      · exact h2 hi)
    rw [← hMA, hAI, hI0, flagStabilizer_empty, Subgroup.map_top_of_surjective _
      (proj_surjective 3 K)]

theorem finrank_eq_of_natCard_eq [Finite K] {W W' : Submodule K (Fin 3 → K)}
    (h : Nat.card W = Nat.card W') : finrank K W = finrank K W' := by
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := ↥W)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := ↥W')
  rw [h1, h2] at h
  exact Nat.pow_right_injective (Finite.one_lt_card (α := K)) h

theorem finrank_map_mulVecLin_gl [Finite K] (A : GL (Fin 3) K)
    (W : Submodule K (Fin 3 → K)) :
    finrank K (W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) = finrank K W := by
  refine finrank_eq_of_natCard_eq ?_
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := fun v w h => by
    have h1 := congrArg (fun u => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) h
    simpa [mulVec_mulVec] using h1
  have e : Nat.card ↥(W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) =
      Nat.card ↑((mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) '' (W : Set (Fin 3 → K))) := by
    rw [← Submodule.map_coe]
    rfl
  rw [e, Nat.card_image_of_injective hinj]
  rfl

theorem finrank_map_mulVecLin_sl [Finite K] (g : SpecialLinearGroup (Fin 3) K)
    (W : Submodule K (Fin 3 → K)) :
    finrank K (W.map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) = finrank K W := by
  refine finrank_eq_of_natCard_eq ?_
  have hinj : Function.Injective (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) := by
    intro v w h
    have h2 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (g : Matrix (Fin 3) (Fin 3) K) = 1 := coe_inv_mul_coe g
    have hmv : ∀ u : Fin 3 → K,
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u) = u := by
      intro u
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have h1 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
      simpa [Matrix.mulVecLin_apply] using congrArg (fun u =>
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) h
    rwa [hmv v, hmv w] at h1
  have e : Nat.card ↥(W.map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) =
      Nat.card ↑((mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) '' (W : Set (Fin 3 → K))) := by
    rw [← Submodule.map_coe]
    rfl
  rw [e, Nat.card_image_of_injective hinj]
  rfl

theorem finrank_coordImage [Finite K] (σ : K ≃+* K) (W : Submodule K (Fin 3 → K)) :
    finrank K (coordImage σ W) = finrank K W := by
  refine finrank_eq_of_natCard_eq (Nat.card_congr
    { toFun := fun v => ⟨fun i => σ.symm ((v : Fin 3 → K) i), v.2⟩
      invFun := fun w => ⟨fun i => σ ((w : Fin 3 → K) i), coord_mem_coordImage w.2⟩
      left_inv := fun v => Subtype.ext (by funext i; simp)
      right_inv := fun w => Subtype.ext (by funext i; simp) })

theorem eq_of_projStabilizer_eq [Finite K] [CharP K 2] {W W' : Submodule K (Fin 3 → K)}
    (hW : 1 ≤ finrank K W ∧ finrank K W < 3)
    (hW' : 1 ≤ finrank K W' ∧ finrank K W' < 3)
    (h : projStabilizer W = projStabilizer W') : W = W' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (maximal_parabolics (K := K) (n := 3) 2 (by norm_num)).2.1
    (bot_lt_and_lt_top_of_finrank hW.1 hW.2)
    (bot_lt_and_lt_top_of_finrank hW'.1 hW'.2) h

theorem eq_flagSpace_of_le_projUpperTriangular [Finite K] [CharP K 2]
    {W : Submodule K (Fin 3 → K)} (h0 : ⊥ < W) (htop : W < ⊤)
    (h : projUpperTriangular 3 K ≤ projStabilizer W) :
    W = flagSpace 3 K 1 ∨ W = flagSpace 3 K 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he1, he3, heq⟩ :=
    eq_projStabilizer_of_isCoatom (isCoatom_projStabilizer h0 htop) h
  have hdimF : 1 ≤ finrank K (flagSpace 3 K e) ∧ finrank K (flagSpace 3 K e) < 3 := by
    rw [finrank_flagSpace (show e ≤ 3 by omega)]
    exact ⟨he1, he3⟩
  have hWe : W = flagSpace 3 K e :=
    eq_of_projStabilizer_eq (one_le_finrank_and_lt h0 htop) hdimF heq
  rcases (by omega : e = 1 ∨ e = 2) with rfl | rfl
  · exact Or.inl hWe
  · exact Or.inr hWe

theorem kDiag_projectiveSL [Finite K] [CharP K 2] :
    ∀ (θ : MulAut (projectiveSL 3 K)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (projectiveSL 3 K),
      (∀ x ∈ (S : Subgroup (projectiveSL 3 K)), θ x ∈ (S : Subgroup (projectiveSL 3 K))) →
    ∀ P : Subgroup (projectiveSL 3 K), IsParabolicTwo (projectiveSL 3 K) P →
      (S : Subgroup (projectiveSL 3 K)) ≤
        Subgroup.normalizer (P : Set (projectiveSL 3 K)) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hθ S hSθ P hP hSP x hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP' : (S : Subgroup (projectiveSL 3 K)) ≤ P :=
    IsParabolicTwo.le_of_le_normalizer hP S.isPGroup' hSP
  have hNS : Subgroup.normalizer (S : Set (projectiveSL 3 K)) ≤ P :=
    hP.normalizer_le S hSP'
  have hSmap : Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K)
      (S : Subgroup (projectiveSL 3 K)) = (S : Subgroup (projectiveSL 3 K)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  have hNfix : Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K)
      (Subgroup.normalizer (S : Set (projectiveSL 3 K))) =
      Subgroup.normalizer (S : Set (projectiveSL 3 K)) := by
    refine (Subgroup.map_equiv_normalizer_eq (S : Subgroup (projectiveSL 3 K)) θ).trans ?_
    exact congrArg (fun H : Subgroup (projectiveSL 3 K) =>
      Subgroup.normalizer (H : Set (projectiveSL 3 K)))
      (show Subgroup.map (MulEquiv.toMonoidHom θ) (S : Subgroup (projectiveSL 3 K)) =
        (S : Subgroup (projectiveSL 3 K)) from hSmap)
  have hmem : Subgroup.normalizer (S : Set (projectiveSL 3 K)) ∈
      sylowNormalizers (projectiveSL 3 K) 2 := ⟨S, rfl⟩
  rw [sylowNormalizers_eq (K := K) (n := 3) 2 (by norm_num)] at hmem
  obtain ⟨x₀, hx₀⟩ := hmem
  obtain ⟨g, hg⟩ := proj_surjective 3 K x₀
  obtain ⟨A, σ, hθeq⟩ : ∃ (A : GL (Fin 3) K) (σ : K ≃+* K),
      θ = conjAut 3 K A * fieldAut 3 K σ := by
    have hE : θ ∈ semilinearAutGroup 3 K :=
      mem_semilinearAutGroup_of_pow_odd (K := K) (n := 3) (α := θ) (m := orderOf θ)
        (by norm_num) hθ (pow_orderOf_eq_one θ)
    exact mem_semilinearAutGroup_iff.mp hE
  have hmapConj : ∀ (B : GL (Fin 3) K) (W : Submodule K (Fin 3 → K)),
      Subgroup.map (conjAut 3 K B : projectiveSL 3 K →* projectiveSL 3 K) (projStabilizer W) =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 3) (Fin 3) K))) :=
    fun B W => (standard_automorphism_transport (n := 3) (K := K)).2.2.2.2.2.2.1 B W
  have hmapField : ∀ (τ : K ≃+* K) (W : Submodule K (Fin 3 → K)),
      Subgroup.map (fieldAut 3 K τ : projectiveSL 3 K →* projectiveSL 3 K) (projStabilizer W) =
        projStabilizer (coordImage τ W) :=
    fun τ W => (standard_automorphism_transport (n := 3) (K := K)).2.2.2.2.2.2.2.1 τ W
  have hmapmul : ∀ (X : Subgroup (projectiveSL 3 K)) (e f : MulAut (projectiveSL 3 K)),
      Subgroup.map ((e * f : MulAut (projectiveSL 3 K)) : projectiveSL 3 K →* projectiveSL 3 K) X =
        Subgroup.map (e : projectiveSL 3 K →* projectiveSL 3 K)
          (Subgroup.map (f : projectiveSL 3 K →* projectiveSL 3 K) X) := by
    intro X e f
    rw [Subgroup.map_map]
    rfl
  have himg : ∀ (W : Submodule K (Fin 3 → K)),
      Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K) (projStabilizer W) =
        projStabilizer ((coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) := by
    intro W
    rw [hθeq, hmapmul, hmapField σ W, hmapConj A (coordImage σ W)]
  have hcomp : ((MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K)).comp
      (MulAut.conj x₀ : projectiveSL 3 K →* projectiveSL 3 K) = MonoidHom.id _ := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : ((MulAut.conj x₀ : projectiveSL 3 K →* projectiveSL 3 K)).comp
      (MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K) = MonoidHom.id _ := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hNmap : Subgroup.map (MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K)
      (Subgroup.normalizer (S : Set (projectiveSL 3 K))) = projUpperTriangular 3 K := by
    rw [hx₀]
    show ((projUpperTriangular 3 K).map
      (MulAut.conj x₀ : projectiveSL 3 K →* projectiveSL 3 K)).map
      (MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K) = projUpperTriangular 3 K
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  set P' : Subgroup (projectiveSL 3 K) :=
    Subgroup.map (MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K) P with hP'def
  have hP'B : projUpperTriangular 3 K ≤ P' := by
    rw [hP'def, ← hNmap]
    exact Subgroup.map_mono hNS
  have hPP' : Subgroup.map (MulAut.conj x₀ : projectiveSL 3 K →* projectiveSL 3 K) P' = P := by
    rw [hP'def]
    show ((P).map (MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K)).map
      (MulAut.conj x₀ : projectiveSL 3 K →* projectiveSL 3 K) = P
    rw [Subgroup.map_map, hcomp', Subgroup.map_id]
  have key : ∀ (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d < 3) (W' : Submodule K (Fin 3 → K)),
      finrank K W' = d →
      (Subgroup.normalizer (S : Set (projectiveSL 3 K)) ≤
        projStabilizer ((flagSpace 3 K d).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))) →
      (Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K)
          (projStabilizer ((flagSpace 3 K d).map
            (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))) = projStabilizer W') →
      projStabilizer W' = projStabilizer ((flagSpace 3 K d).map
        (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
    intro d hd1 hd2 W' hdimW' hWN hθP
    set W : Submodule K (Fin 3 → K) :=
      (flagSpace 3 K d).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) with hWdef
    set W'' : Submodule K (Fin 3 → K) := W'.map
      (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      with hW''def
    have hW''eq : Subgroup.map (MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K)
        (projStabilizer W') = projStabilizer W'' := by
      rw [hW''def, show x₀⁻¹ = proj 3 K g⁻¹ from by rw [← hg, map_inv]]
      exact projStabilizer_map_conj (g := g⁻¹) (W := W')
    have hB : projUpperTriangular 3 K ≤ projStabilizer W'' := by
      have h1 : Subgroup.normalizer (S : Set (projectiveSL 3 K)) ≤ projStabilizer W' := by
        rw [← hθP, ← hNfix]
        exact Subgroup.map_mono hWN
      have h2 := Subgroup.map_mono (f := (MulAut.conj (x₀⁻¹) : projectiveSL 3 K →* projectiveSL 3 K)) h1
      rwa [hNmap, hW''eq] at h2
    have hdimW'' : finrank K W'' = d := by
      rw [hW''def, finrank_map_mulVecLin_sl, hdimW']
    have hproper : ⊥ < W'' ∧ W'' < ⊤ := bot_lt_and_lt_top_of_finrank (by omega) (by omega)
    have hP'eq : Subgroup.map (MulAut.conj x₀ : projectiveSL 3 K →* projectiveSL 3 K)
        (projStabilizer W'') = projStabilizer W' := by
      rw [← hW''eq, Subgroup.map_map, hcomp', Subgroup.map_id]
    obtain hW1 | hW2 := eq_flagSpace_of_le_projUpperTriangular hproper.1 hproper.2 hB
    · have hd : d = 1 := by
        rw [← hdimW'', hW1, finrank_flagSpace (by norm_num)]
      have hW1' : W = (flagSpace 3 K 1).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) := by
        rw [hWdef, hd]
      rw [hW1', ← hP'eq, hW1, ← hg, projStabilizer_map_conj]
    · have hd : d = 2 := by
        rw [← hdimW'', hW2, finrank_flagSpace (by norm_num)]
      have hW2' : W = (flagSpace 3 K 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) := by
        rw [hWdef, hd]
      rw [hW2', ← hP'eq, hW2, ← hg, projStabilizer_map_conj]
  rcases overgroups_projUpperTriangular (P := P') hP'B with hB | hF1 | hF2 | htop
  ·
    have hPNS : P = Subgroup.normalizer (S : Set (projectiveSL 3 K)) := by
      rw [← hPP', hB, hx₀]
    rw [hPNS] at hx ⊢
    rw [← hNfix]
    exact Subgroup.mem_map_of_mem (θ : projectiveSL 3 K →* projectiveSL 3 K) hx
  ·
    have hPform : P = projStabilizer ((flagSpace 3 K 1).map
        (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
      rw [← hPP', hF1, ← hg, projStabilizer_map_conj]
    have hWN : Subgroup.normalizer (S : Set (projectiveSL 3 K)) ≤
        projStabilizer ((flagSpace 3 K 1).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
      rw [← hPform]
      exact hNS
    set W' : Submodule K (Fin 3 → K) :=
      (coordImage σ ((flagSpace 3 K 1).map
        (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))).map
        (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) with hW'def
    have hdimW' : finrank K W' = 1 := by
      rw [hW'def, finrank_map_mulVecLin_gl, finrank_coordImage, finrank_map_mulVecLin_sl,
        finrank_flagSpace (by norm_num)]
    have hθP : Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K)
        (projStabilizer ((flagSpace 3 K 1).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))) = projStabilizer W' := by
      rw [himg]
    have hfix := key 1 (by norm_num) (by norm_num) W' hdimW' hWN hθP
    have hmapfix : Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K)
        (projStabilizer ((flagSpace 3 K 1).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))) =
        projStabilizer ((flagSpace 3 K 1).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
      rw [hθP, hfix]
    rw [hPform] at hx ⊢
    rw [← hmapfix]
    exact Subgroup.mem_map_of_mem (θ : projectiveSL 3 K →* projectiveSL 3 K) hx
  ·
    have hPform : P = projStabilizer ((flagSpace 3 K 2).map
        (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
      rw [← hPP', hF2, ← hg, projStabilizer_map_conj]
    have hWN : Subgroup.normalizer (S : Set (projectiveSL 3 K)) ≤
        projStabilizer ((flagSpace 3 K 2).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
      rw [← hPform]
      exact hNS
    set W' : Submodule K (Fin 3 → K) :=
      (coordImage σ ((flagSpace 3 K 2).map
        (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))).map
        (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) with hW'def
    have hdimW' : finrank K W' = 2 := by
      rw [hW'def, finrank_map_mulVecLin_gl, finrank_coordImage, finrank_map_mulVecLin_sl,
        finrank_flagSpace (by norm_num)]
    have hθP : Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K)
        (projStabilizer ((flagSpace 3 K 2).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))) = projStabilizer W' := by
      rw [himg]
    have hfix := key 2 (by norm_num) (by norm_num) W' hdimW' hWN hθP
    have hmapfix : Subgroup.map (θ : projectiveSL 3 K →* projectiveSL 3 K)
        (projStabilizer ((flagSpace 3 K 2).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)))) =
        projStabilizer ((flagSpace 3 K 2).map
          (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
      rw [hθP, hfix]
    rw [hPform] at hx ⊢
    rw [← hmapfix]
    exact Subgroup.mem_map_of_mem (θ : projectiveSL 3 K →* projectiveSL 3 K) hx
  ·
    have hPtop : P = ⊤ := by
      rw [← hPP', htop]
      exact Subgroup.map_top_of_surjective _
        (MulAut.conj x₀).surjective
    rw [hPtop]
    exact Subgroup.mem_top _


end KDiagL3

theorem kDiag_of_isL3 {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsL3 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have hX' : CFSG.Blueprint.LieModel X .PSL 3 2 n := hX
  have ht : (CFSG.Open.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSL 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX' ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨e₀⟩⟩ := hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedLieAdmissible] at hadm
  have hn1 : 1 ≤ n := hadm.2.1
  have hEven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr hEven
  haveI : CharP K 2 := ringChar.of_eq hchar
  exact kDiag_transport
    (e := e₀.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          3 K)))
    (KDiagL3.kDiag_projectiveSL (K := K))



end CFSG.LocalAnalysis.UniquenessCase.UC22

end
