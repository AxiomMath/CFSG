module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix Module Subgroup

namespace KDiagPSL4

variable {K : Type} [Field K] {m : ℕ}

theorem finrank_eq_of_natCard_eq [Finite K] {W W' : Submodule K (Fin m → K)}
    (h : Nat.card W = Nat.card W') : finrank K W = finrank K W' := by
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := ↥W)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := ↥W')
  rw [h1, h2] at h
  exact Nat.pow_right_injective (Finite.one_lt_card (α := K)) h

theorem finrank_map_mulVecLin_gl [Finite K] (A : GL (Fin m) K)
    (W : Submodule K (Fin m → K)) :
    finrank K (W.map (mulVecLin (A : Matrix (Fin m) (Fin m) K))) = finrank K W := by
  refine finrank_eq_of_natCard_eq ?_
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin m) (Fin m) K)) := fun v w h => by
    have h1 := congrArg (fun u => ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ u) h
    simpa [mulVec_mulVec] using h1
  have e : Nat.card ↥(W.map (mulVecLin (A : Matrix (Fin m) (Fin m) K))) =
      Nat.card ↑((mulVecLin (A : Matrix (Fin m) (Fin m) K)) '' (W : Set (Fin m → K))) := by
    rw [← Submodule.map_coe]
    rfl
  rw [e, Nat.card_image_of_injective hinj]
  rfl

theorem finrank_map_mulVecLin_sl [Finite K] (g : SpecialLinearGroup (Fin m) K)
    (W : Submodule K (Fin m → K)) :
    finrank K (W.map (mulVecLin (g : Matrix (Fin m) (Fin m) K))) = finrank K W := by
  refine finrank_eq_of_natCard_eq ?_
  have hinj : Function.Injective (mulVecLin (g : Matrix (Fin m) (Fin m) K)) := by
    intro v w h
    have h2 : ((g⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        (g : Matrix (Fin m) (Fin m) K) = 1 := coe_inv_mul_coe g
    have hmv : ∀ u : Fin m → K,
        ((g⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
          ((g : Matrix (Fin m) (Fin m) K) *ᵥ u) = u := by
      intro u
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have h1 : ((g⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
        ((g : Matrix (Fin m) (Fin m) K) *ᵥ v) =
        ((g⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
          ((g : Matrix (Fin m) (Fin m) K) *ᵥ w) := by
      simpa [Matrix.mulVecLin_apply] using congrArg (fun u =>
        ((g⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ u) h
    rwa [hmv v, hmv w] at h1
  have e : Nat.card ↥(W.map (mulVecLin (g : Matrix (Fin m) (Fin m) K))) =
      Nat.card ↑((mulVecLin (g : Matrix (Fin m) (Fin m) K)) '' (W : Set (Fin m → K))) := by
    rw [← Submodule.map_coe]
    rfl
  rw [e, Nat.card_image_of_injective hinj]
  rfl

theorem finrank_coordImage [Finite K] (σ : K ≃+* K) (W : Submodule K (Fin m → K)) :
    finrank K (coordImage σ W) = finrank K W := by
  refine finrank_eq_of_natCard_eq (Nat.card_congr
    { toFun := fun v => ⟨fun i => σ.symm ((v : Fin m → K) i), v.2⟩
      invFun := fun w => ⟨fun i => σ ((w : Fin m → K) i), coord_mem_coordImage w.2⟩
      left_inv := fun v => Subtype.ext (by funext i; simp)
      right_inv := fun w => Subtype.ext (by funext i; simp) })

theorem eq_of_projStabilizer_eq [Finite K] [CharP K 2] {W W' : Submodule K (Fin m → K)}
    (hW : 1 ≤ finrank K W ∧ finrank K W < m)
    (hW' : 1 ≤ finrank K W' ∧ finrank K W' < m)
    (h : projStabilizer W = projStabilizer W') : W = W' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (maximal_parabolics (K := K) (n := m) 2 (by omega)).2.1
    (bot_lt_and_lt_top_of_finrank hW.1 hW.2)
    (bot_lt_and_lt_top_of_finrank hW'.1 hW'.2) h

theorem map_flagStabilizer_eq_iInf {I : Set ℕ} (hI : I.Nonempty) :
    (flagStabilizer m K I).map (proj m K) =
      ⨅ i ∈ I, projStabilizer (flagSpace m K i) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [Subgroup.mem_iInf]
    intro i
    rw [Subgroup.mem_iInf]
    intro hi
    exact Subgroup.map_mono (fun g hg => mem_flagStabilizer.mp hg i hi) hy
  · intro y hy
    obtain ⟨i0, hi0⟩ := hI
    have hy0 : y ∈ projStabilizer (flagSpace m K i0) := by
      rw [Subgroup.mem_iInf] at hy
      exact (Subgroup.mem_iInf.mp (hy i0)) hi0
    obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hy0
    rw [Subgroup.mem_map]
    refine ⟨g, ?_, rfl⟩
    refine mem_flagStabilizer.mpr fun i hi => ?_
    have hyi : proj m K g ∈ projStabilizer (flagSpace m K i) := by
      rw [Subgroup.mem_iInf] at hy
      exact (Subgroup.mem_iInf.mp (hy i)) hi
    obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp hyi
    have hker : g * h⁻¹ ∈ scalars m K := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
    have hg' : g = (g * h⁻¹) * h := by group
    rw [hg']
    exact (stabilizer (flagSpace m K i)).mul_mem (scalars_le_stabilizer _ hker) hh

theorem kDiag_projectiveSL_four [Finite K] [CharP K 2] :
    ∀ (θ : MulAut (projectiveSL 4 K)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (projectiveSL 4 K),
      (∀ x ∈ (S : Subgroup (projectiveSL 4 K)), θ x ∈ (S : Subgroup (projectiveSL 4 K))) →
    ∀ P : Subgroup (projectiveSL 4 K), IsParabolicTwo (projectiveSL 4 K) P →
      (S : Subgroup (projectiveSL 4 K)) ≤
        Subgroup.normalizer (P : Set (projectiveSL 4 K)) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hθ S hSθ P hP hSP x hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP' : (S : Subgroup (projectiveSL 4 K)) ≤ P :=
    IsParabolicTwo.le_of_le_normalizer hP S.isPGroup' hSP
  have hNS : Subgroup.normalizer (S : Set (projectiveSL 4 K)) ≤ P :=
    hP.normalizer_le S hSP'
  have hSmap : Subgroup.map (θ : projectiveSL 4 K →* projectiveSL 4 K)
      (S : Subgroup (projectiveSL 4 K)) = (S : Subgroup (projectiveSL 4 K)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  have hNfix : Subgroup.map (θ : projectiveSL 4 K →* projectiveSL 4 K)
      (Subgroup.normalizer (S : Set (projectiveSL 4 K))) =
      Subgroup.normalizer (S : Set (projectiveSL 4 K)) := by
    refine (Subgroup.map_equiv_normalizer_eq (S : Subgroup (projectiveSL 4 K)) θ).trans ?_
    exact congrArg (fun H : Subgroup (projectiveSL 4 K) =>
      Subgroup.normalizer (H : Set (projectiveSL 4 K)))
      (show Subgroup.map (MulEquiv.toMonoidHom θ) (S : Subgroup (projectiveSL 4 K)) =
        (S : Subgroup (projectiveSL 4 K)) from hSmap)
  have hmem : Subgroup.normalizer (S : Set (projectiveSL 4 K)) ∈
      sylowNormalizers (projectiveSL 4 K) 2 := ⟨S, rfl⟩
  rw [sylowNormalizers_eq (K := K) (n := 4) 2 (by norm_num)] at hmem
  obtain ⟨x₀, hx₀⟩ := hmem
  obtain ⟨g, hg⟩ := proj_surjective 4 K x₀
  obtain ⟨A, σ, hθeq⟩ : ∃ (A : GL (Fin 4) K) (σ : K ≃+* K),
      θ = conjAut 4 K A * fieldAut 4 K σ := by
    have hE : θ ∈ semilinearAutGroup 4 K :=
      mem_semilinearAutGroup_of_pow_odd (K := K) (n := 4) (α := θ) (m := orderOf θ)
        (by norm_num) hθ (pow_orderOf_eq_one θ)
    exact mem_semilinearAutGroup_iff.mp hE
  have hmapConj : ∀ (B : GL (Fin 4) K) (W : Submodule K (Fin 4 → K)),
      Subgroup.map (conjAut 4 K B : projectiveSL 4 K →* projectiveSL 4 K) (projStabilizer W) =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 4) (Fin 4) K))) :=
    fun B W => (standard_automorphism_transport (n := 4) (K := K)).2.2.2.2.2.2.1 B W
  have hmapField : ∀ (τ : K ≃+* K) (W : Submodule K (Fin 4 → K)),
      Subgroup.map (fieldAut 4 K τ : projectiveSL 4 K →* projectiveSL 4 K) (projStabilizer W) =
        projStabilizer (coordImage τ W) :=
    fun τ W => (standard_automorphism_transport (n := 4) (K := K)).2.2.2.2.2.2.2.1 τ W
  have hmapmul : ∀ (X : Subgroup (projectiveSL 4 K)) (e f : MulAut (projectiveSL 4 K)),
      Subgroup.map ((e * f : MulAut (projectiveSL 4 K)) : projectiveSL 4 K →* projectiveSL 4 K) X =
        Subgroup.map (e : projectiveSL 4 K →* projectiveSL 4 K)
          (Subgroup.map (f : projectiveSL 4 K →* projectiveSL 4 K) X) := by
    intro X e f
    rw [Subgroup.map_map]
    rfl
  have himg : ∀ (W : Submodule K (Fin 4 → K)),
      Subgroup.map (θ : projectiveSL 4 K →* projectiveSL 4 K) (projStabilizer W) =
        projStabilizer ((coordImage σ W).map (mulVecLin (A : Matrix (Fin 4) (Fin 4) K))) := by
    intro W
    rw [hθeq, hmapmul, hmapField σ W, hmapConj A (coordImage σ W)]
  have hcomp : ((MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K)).comp
      (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) = MonoidHom.id _ := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : ((MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K)).comp
      (MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K) = MonoidHom.id _ := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hNmap : Subgroup.map (MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K)
      (Subgroup.normalizer (S : Set (projectiveSL 4 K))) = projUpperTriangular 4 K := by
    rw [hx₀]
    show ((projUpperTriangular 4 K).map
      (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K)).map
      (MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K) = projUpperTriangular 4 K
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  set P' : Subgroup (projectiveSL 4 K) :=
    Subgroup.map (MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K) P with hP'def
  have hP'B : projUpperTriangular 4 K ≤ P' := by
    rw [hP'def, ← hNmap]
    exact Subgroup.map_mono hNS
  have hPP' : Subgroup.map (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) P' = P := by
    rw [hP'def]
    show ((P).map (MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K)).map
      (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) = P
    rw [Subgroup.map_map, hcomp', Subgroup.map_id]
  set Apre : Subgroup (SpecialLinearGroup (Fin 4) K) := P'.comap (proj 4 K) with hApre
  have hMA : Subgroup.map (proj 4 K) Apre = P' :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 4 K) P'
  have hBA : upperTriangular 4 K ≤ Apre := by
    rw [hApre, ← Subgroup.map_le_iff_le_comap]
    exact hP'B
  obtain ⟨hAI, -⟩ := borel_overgroups Apre hBA
  set I : Set ℕ := borelOvergroupCuts Apre with hI
  have hcut : ∀ i ∈ I, 1 ≤ i ∧ i < 4 := fun i hi => ⟨hi.1, hi.2.1⟩
  have hP'I : P' = (flagStabilizer 4 K I).map (proj 4 K) := by
    rw [← hMA, hAI]
  have key : ∀ (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d < 4) (W' : Submodule K (Fin 4 → K)),
      finrank K W' = d →
      (Subgroup.normalizer (S : Set (projectiveSL 4 K)) ≤
        projStabilizer ((flagSpace 4 K d).map
          (mulVecLin (g : Matrix (Fin 4) (Fin 4) K)))) →
      (Subgroup.map (θ : projectiveSL 4 K →* projectiveSL 4 K)
          (projStabilizer ((flagSpace 4 K d).map
            (mulVecLin (g : Matrix (Fin 4) (Fin 4) K)))) = projStabilizer W') →
      projStabilizer W' = projStabilizer ((flagSpace 4 K d).map
        (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) := by
    intro d hd1 hd4 W' hdimW' hWN hθP
    set W : Submodule K (Fin 4 → K) :=
      (flagSpace 4 K d).map (mulVecLin (g : Matrix (Fin 4) (Fin 4) K)) with hWdef
    set W'' : Submodule K (Fin 4 → K) := W'.map
      (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      with hW''def
    have hW''eq : Subgroup.map (MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K)
        (projStabilizer W') = projStabilizer W'' := by
      rw [hW''def, show x₀⁻¹ = proj 4 K g⁻¹ from by rw [← hg, map_inv]]
      exact projStabilizer_map_conj (g := g⁻¹) (W := W')
    have hB : projUpperTriangular 4 K ≤ projStabilizer W'' := by
      have h1 : Subgroup.normalizer (S : Set (projectiveSL 4 K)) ≤ projStabilizer W' := by
        rw [← hθP, ← hNfix]
        exact Subgroup.map_mono hWN
      have h2 := Subgroup.map_mono
        (f := (MulAut.conj (x₀⁻¹) : projectiveSL 4 K →* projectiveSL 4 K)) h1
      rwa [hNmap, hW''eq] at h2
    have hdimW'' : finrank K W'' = d := by
      rw [hW''def, finrank_map_mulVecLin_sl, hdimW']
    have hproper : ⊥ < W'' ∧ W'' < ⊤ := bot_lt_and_lt_top_of_finrank (by omega) (by omega)
    have hP'eq : Subgroup.map (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K)
        (projStabilizer W'') = projStabilizer W' := by
      rw [← hW''eq, Subgroup.map_map, hcomp', Subgroup.map_id]
    obtain ⟨e, he1, he4, heq⟩ :=
      eq_projStabilizer_of_isCoatom (isCoatom_projStabilizer hproper.1 hproper.2) hB
    have hWe : W'' = flagSpace 4 K e :=
      eq_of_projStabilizer_eq (one_le_finrank_and_lt hproper.1 hproper.2)
        (by rw [finrank_flagSpace (by omega)]; exact ⟨he1, he4⟩) heq
    have hde : d = e := by
      rw [← hdimW'', hWe, finrank_flagSpace (by omega)]
    have hW1' : W = (flagSpace 4 K e).map (mulVecLin (g : Matrix (Fin 4) (Fin 4) K)) := by
      rw [hWdef, hde]
    rw [hW1', ← hP'eq, hWe, ← hg, projStabilizer_map_conj]
  by_cases hIne : I.Nonempty
  ·
    have hQ : ∀ i ∈ I, P ≤ projStabilizer ((flagSpace 4 K i).map
        (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) := by
      intro i hi
      have h1 : P' ≤ projStabilizer (flagSpace 4 K i) := by
        rw [hP'I]
        exact Subgroup.map_mono (fun y hy => mem_flagStabilizer.mp hy i hi)
      have h2 := Subgroup.map_mono
        (f := (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K)) h1
      rwa [hPP', show (projStabilizer (flagSpace 4 K i)).map
          (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) =
          projStabilizer ((flagSpace 4 K i).map
            (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) from by
        rw [← hg]
        exact projStabilizer_map_conj (K := K) (n := 4) (g := g)
          (W := flagSpace 4 K i)] at h2
    have hfix : ∀ i ∈ I, Subgroup.map (θ : projectiveSL 4 K →* projectiveSL 4 K)
        (projStabilizer ((flagSpace 4 K i).map
          (mulVecLin (g : Matrix (Fin 4) (Fin 4) K)))) =
        projStabilizer ((flagSpace 4 K i).map
          (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) := by
      intro i hi
      obtain ⟨hi1, hi4⟩ := hcut i hi
      have hWN : Subgroup.normalizer (S : Set (projectiveSL 4 K)) ≤
          projStabilizer ((flagSpace 4 K i).map
            (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) := by
        have h := Subgroup.map_mono
          (f := (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K))
          (projUpperTriangular_le_projStabilizer (n := 4) (K := K) i)
        rwa [← hx₀, show (projStabilizer (flagSpace 4 K i)).map
            (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) =
            projStabilizer ((flagSpace 4 K i).map
              (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) from by
          rw [← hg]
          exact projStabilizer_map_conj (K := K) (n := 4) (g := g)
            (W := flagSpace 4 K i)] at h
      set W' : Submodule K (Fin 4 → K) :=
        (coordImage σ ((flagSpace 4 K i).map
          (mulVecLin (g : Matrix (Fin 4) (Fin 4) K)))).map
          (mulVecLin (A : Matrix (Fin 4) (Fin 4) K)) with hW'def
      have hdimW' : finrank K W' = i := by
        rw [hW'def, finrank_map_mulVecLin_gl, finrank_coordImage, finrank_map_mulVecLin_sl,
          finrank_flagSpace (le_of_lt hi4)]
      have hθP : Subgroup.map (θ : projectiveSL 4 K →* projectiveSL 4 K)
          (projStabilizer ((flagSpace 4 K i).map
            (mulVecLin (g : Matrix (Fin 4) (Fin 4) K)))) = projStabilizer W' := by
        rw [himg]
      rw [hθP, key i hi1 hi4 W' hdimW' hWN hθP]
    have hstep : ∀ i ∈ I,
        (MulAut.conj (x₀⁻¹)) (θ x) ∈ projStabilizer (flagSpace 4 K i) := by
      intro i hi
      have h1 : θ x ∈ projStabilizer ((flagSpace 4 K i).map
          (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) := by
        rw [← hfix i hi]
        exact Subgroup.mem_map_of_mem (θ : projectiveSL 4 K →* projectiveSL 4 K) (hQ i hi hx)
      have h2 : projStabilizer ((flagSpace 4 K i).map
          (mulVecLin (g : Matrix (Fin 4) (Fin 4) K))) =
          (projStabilizer (flagSpace 4 K i)).map
            (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) := by
        rw [← hg, projStabilizer_map_conj]
      rw [h2] at h1
      have hw : (MulAut.conj x₀) ((MulAut.conj (x₀⁻¹)) (θ x)) = θ x := by
        simp [MulAut.conj_apply, mul_assoc]
      have h3 : (MulAut.conj x₀) ((MulAut.conj (x₀⁻¹)) (θ x)) ∈
          (projStabilizer (flagSpace 4 K i)).map
            (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) := by
        rw [hw]
        exact h1
      exact (Subgroup.mem_map_iff_mem
        (f := (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K))
        (MulAut.conj x₀).injective).mp h3
    have hwP' : (MulAut.conj (x₀⁻¹)) (θ x) ∈ P' := by
      rw [hP'I, map_flagStabilizer_eq_iInf (m := 4) (K := K) hIne]
      rw [Subgroup.mem_iInf]
      intro i
      rw [Subgroup.mem_iInf]
      intro hi
      exact hstep i hi
    have hθxP : θ x ∈ P := by
      rw [← hPP']
      rw [show θ x = (MulAut.conj x₀) ((MulAut.conj (x₀⁻¹)) (θ x)) from by
        simp [MulAut.conj_apply, mul_assoc]]
      exact Subgroup.mem_map_of_mem
        (MulAut.conj x₀ : projectiveSL 4 K →* projectiveSL 4 K) hwP'
    exact hθxP
  ·
    have hIempty : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hIne
    have hP'top : P' = ⊤ := by
      rw [hP'I, hIempty, flagStabilizer_empty,
        Subgroup.map_top_of_surjective _ (proj_surjective 4 K)]
    have hPtop : P = ⊤ := by
      rw [← hPP', hP'top]
      exact Subgroup.map_top_of_surjective _ (MulAut.conj x₀).surjective
    rw [hPtop]
    exact Subgroup.mem_top _

end KDiagPSL4

theorem kDiag_of_lieModel_psl4 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSL 4 2 n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have ht : (CFSG.Open.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSL 4 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX ht
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
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          4 K)))
    (KDiagPSL4.kDiag_projectiveSL_four (K := K))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
