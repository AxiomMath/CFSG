module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaCore
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaAnisoInner
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaLin
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaMix
import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
import CFSG.Timmesfeld.Transvection.QuadFormBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix QuadraticMap CFSG.Open CFSG.LieType.SeitzGeneration
  CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
private lemma span_singleton_singular {v : Fin d → K} (hv : Q v = 0) :
    ∀ x ∈ Submodule.span K ({v} : Set (Fin d → K)), Q x = 0 := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp [QuadraticMap.map_smul, hv]

omit [Finite K] in
private lemma span_singleton_stable {T : (Fin d → K) →ₗ[K] (Fin d → K)} {v : Fin d → K}
    (hv : T v ∈ Submodule.span K ({v} : Set (Fin d → K))) :
    ∀ x ∈ Submodule.span K ({v} : Set (Fin d → K)),
      T x ∈ Submodule.span K ({v} : Set (Fin d → K)) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul]
  exact Submodule.smul_mem _ _ hv

omit [Finite K] in
private lemma span_pair_singular {v w : Fin d → K} (hv : Q v = 0) (hw : Q w = 0)
    (hp : polar Q v w = 0) :
    ∀ x ∈ Submodule.span K ({v, w} : Set (Fin d → K)), Q x = 0 := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [CFSG.Timmesfeld.Transvection.QuadForm.apply_smul_add_smul, hv, hw, hp]
  ring

omit [Finite K] in
private lemma span_pair_stable {T : (Fin d → K) →ₗ[K] (Fin d → K)} {v w : Fin d → K}
    (hv : T v ∈ Submodule.span K ({v, w} : Set (Fin d → K)))
    (hw : T w ∈ Submodule.span K ({v, w} : Set (Fin d → K))) :
    ∀ x ∈ Submodule.span K ({v, w} : Set (Fin d → K)),
      T x ∈ Submodule.span K ({v, w} : Set (Fin d → K)) := by
  intro x hx
  refine Submodule.span_induction
    (p := fun y _ => T y ∈ Submodule.span K ({v, w} : Set (Fin d → K))) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hv
    · exact hw
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ ihy ihz; rw [map_add]; exact Submodule.add_mem _ ihy ihz
  · intro c y _ ihy; rw [map_smul]; exact Submodule.smul_mem _ _ ihy

omit [Finite K] in
private lemma Q_map_of_selfAdjoint_sq {T : (Fin d → K) →ₗ[K] (Fin d → K)} {β : K}
    (h2 : (2 : K) ≠ 0) (hsa : ∀ u w, polar Q (T u) w = polar Q u (T w))
    (hT2 : ∀ v, T (T v) = β • v) (v : Fin d → K) :
    Q (T v) = β * Q v := by
  have h1 : polar Q (T v) (T v) = polar Q v (T (T v)) := hsa v (T v)
  rw [hT2 v, polar_smul_right_eq, polar_self_eq_two_mul, polar_self_eq_two_mul] at h1
  have hc : (2 : K) * Q (T v) = (2 : K) * (β * Q v) := by
    rw [h1]; ring
  exact mul_left_cancel₀ h2 hc

theorem seitzFourOOuterAniso_holds : SeitzFourOOuterAniso := by
  intro K hK hFin d Q h2 hd7 hd8 hnd hS3 hEQ hAP E hE h4 hEim hout hlin hno
  classical
  have hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a :=
    fun g => (CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff
      Q hnd hS3 hAP g).1
  have hder : elementaryGroup Q = orthDerived Q := hEQ.symm
  obtain ⟨ga, gb, hκga, hκgb, hκga1, hκgb1, hκne, hgen, hgra, hgrb,
    cA, cB, cAB, hA2σ, hB2σ, hABσ⟩ := exists_generator_lifts hker hE h4 hEim hlin
  have hα0 : (cA : K) ≠ 0 := Units.ne_zero cA
  have hβ0 : (cB : K) ≠ 0 := Units.ne_zero cB
  let A : (Fin d → K) →ₗ[K] (Fin d → K) := (matrixLinearEquiv ga.val.left).toLinearMap
  let B : (Fin d → K) →ₗ[K] (Fin d → K) := (matrixLinearEquiv gb.val.left).toLinearMap
  have hA_coe : ∀ v, A v = coordinateSemilinearMap ga.val v := by
    intro v
    change matrixLinearEquiv ga.val.left v = coordinateSemilinearMap ga.val v
    rw [coordinateSemilinearMap_apply, hgra, matrixLinearEquiv_apply]
    simp
  have hB_coe : ∀ v, B v = coordinateSemilinearMap gb.val v := by
    intro v
    change matrixLinearEquiv gb.val.left v = coordinateSemilinearMap gb.val v
    rw [coordinateSemilinearMap_apply, hgrb, matrixLinearEquiv_apply]
    simp
  have hA2 : ∀ v, A (A v) = (cA : K) • v := fun v => by
    simpa [hA_coe] using hA2σ v
  have hB2 : ∀ v, B (B v) = (cB : K) • v := fun v => by
    simpa [hB_coe] using hB2σ v
  have hABε : ∀ v, A (B v) = (cAB : K) • B (A v) := fun v => by
    simpa [hA_coe, hB_coe] using hABσ v
  have hnoAB : ∀ W : Submodule K (Fin d → K), (∀ x ∈ W, Q x = 0) →
      (∀ x ∈ W, A x ∈ W) → (∀ x ∈ W, B x ∈ W) → W = ⊥ := by
    intro W hsing hsta hstb
    apply hno W hsing
    intro g hg w hw
    refine stable_of_generators hker (ga := ga) (gb := gb)
      (a := matrixProjectiveConjugationHom Q ga) (b := matrixProjectiveConjugationHom Q gb)
      rfl rfl hgen ?_ ?_ g hg w hw
    · intro y hy
      rw [← hA_coe]
      exact hsta y hy
    · intro y hy
      rw [← hB_coe]
      exact hstb y hy
  have hlin3 : (∀ u w, polar Q (A u) w = polar Q u (A w)) ∧
      (∀ u w, polar Q (B u) w = polar Q u (B w)) ∧ ∀ v, A (B v) = B (A v) := by
    by_contra hcon
    have hμA : ∀ v, Q (A v) = (multiplier Q ga : K) * Q v := by
      intro v
      have h := multiplier_spec Q ga v
      rw [coordinateSemilinearMap_right_one_eq_linear ga.val hgra] at h
      rw [hgra] at h
      simpa [A] using h
    have hμB : ∀ v, Q (B v) = (multiplier Q gb : K) * Q v := by
      intro v
      have h := multiplier_spec Q gb v
      rw [coordinateSemilinearMap_right_one_eq_linear gb.val hgrb] at h
      rw [hgrb] at h
      simpa [B] using h
    have hdim : 9 ≤ Module.finrank K (Fin d → K) ∨ (7 ≤ Module.finrank K (Fin d → K) ∧
        ¬ ((∀ u w, polar Q (A u) w = polar Q u (A w)) ∧
          (∀ u w, polar Q (B u) w = polar Q u (B w)) ∧ ∀ v, A (B v) = B (A v))) := by
      refine Or.inr ⟨?_, hcon⟩
      rwa [Module.finrank_fin_fun]
    obtain ⟨W, hW0, hWsing, hWA, hWB⟩ :=
      exists_stable_singular_of_similitudes (K := K) (V := Fin d → K) h2 hnd
        (A := A) (B := B) (μA := (multiplier Q ga : K)) (μB := (multiplier Q gb : K))
        (α := (cA : K)) (β := (cB : K)) (ε := (cAB : K))
        hμA hμB hA2 hB2 (Units.ne_zero cA) (Units.ne_zero cB) hABε hdim
    exact hW0 (hnoAB W hWsing hWA hWB)
  obtain ⟨hsaA, hsaB, hcomm⟩ := hlin3
  have hcommσ : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val v) =
      coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val v) :=
    fun v => by simpa [hA_coe, hB_coe] using hcomm v
  have hAsaσ : ∀ u w, polar Q (coordinateSemilinearMap ga.val u) w =
      polar Q u (coordinateSemilinearMap ga.val w) :=
    fun u w => by simpa [hA_coe] using hsaA u w
  have hBsaσ : ∀ u w, polar Q (coordinateSemilinearMap gb.val u) w =
      polar Q u (coordinateSemilinearMap gb.val w) :=
    fun u w => by simpa [hB_coe] using hsaB u w
  by_cases hα : IsSquare (cA : K)
  · by_cases hβ : IsSquare (cB : K)
    ·
      obtain ⟨a, ha⟩ := hα
      obtain ⟨b, hb⟩ := hβ
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hα0 (by rw [ha]; simp)
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact hβ0 (by rw [hb]; simp)
      have haA2 : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v) =
          (a * a) • v := fun v => by rw [hA2σ v, ha]
      have hbB2 : ∀ v, coordinateSemilinearMap gb.val (coordinateSemilinearMap gb.val v) =
          (b * b) • v := fun v => by rw [hB2σ v, hb]
      have hanisA : ∀ v, (coordinateSemilinearMap ga.val v = a • v ∨
          coordinateSemilinearMap ga.val v = -(a • v)) →
          (coordinateSemilinearMap gb.val v = b • v ∨
            coordinateSemilinearMap gb.val v = -(b • v)) → Q v = 0 → v = 0 := by
        intro v hv1 hv2 hQv
        have hW : Submodule.span K ({v} : Set (Fin d → K)) = ⊥ := by
          refine hnoAB _ (span_singleton_singular hQv) ?_ ?_
          · refine span_singleton_stable ?_
            rcases hv1 with h | h
            · rw [hA_coe, h]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
            · rw [hA_coe, h]
              exact Submodule.neg_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          · refine span_singleton_stable ?_
            rcases hv2 with h | h
            · rw [hB_coe, h]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
            · rw [hB_coe, h]
              exact Submodule.neg_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have hv : v ∈ Submodule.span K ({v} : Set (Fin d → K)) :=
          Submodule.subset_span (by simp)
        rw [hW] at hv
        simpa using hv
      have hanisB : ∀ v, (coordinateSemilinearMap gb.val v = b • v ∨
          coordinateSemilinearMap gb.val v = -(b • v)) →
          (coordinateSemilinearMap ga.val v = a • v ∨
            coordinateSemilinearMap ga.val v = -(a • v)) → Q v = 0 → v = 0 :=
        fun v h1 h2 h3 => hanisA v h2 h1 h3
      have hmem1 := mem_conj_range_of_isometric_lifts (Q := Q) h2 hd7 hd8 ga gb hgra hgrb
        ha0 hb0 haA2 hbB2 hAsaσ hBsaσ hcommσ hanisA
      have hmem2 := mem_conj_range_of_isometric_lifts (Q := Q) h2 hd7 hd8 gb ga hgrb hgra
        hb0 ha0 hbB2 haA2 hBsaσ hAsaσ (fun v => (hcommσ v).symm) hanisB
      have hle : Subgroup.closure {matrixProjectiveConjugationHom Q ga,
          matrixProjectiveConjugationHom Q gb} ≤
          (MulAut.conj : matrixProjectiveDerived Q →*
            MulAut (matrixProjectiveDerived Q)).range := by
        refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hmem1
        · exact hmem2
      exact False.elim (hout (hgen ▸ hle))
    ·
      obtain ⟨a, ha⟩ := hα
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hα0 (by rw [ha]; simp)
      have hβnsq : ∀ s : K, s * s ≠ (cB : K) := by
        intro s hs
        exact hβ (hs ▸ IsSquare.mul_self s)
      have haA2 : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v) =
          (a * a) • v := fun v => by rw [hA2σ v, ha]
      have hanisMix : ∀ v, (coordinateSemilinearMap ga.val v = a • v ∨
          coordinateSemilinearMap ga.val v = -(a • v)) → Q v = 0 →
          polar Q v (coordinateSemilinearMap gb.val v) = 0 → v = 0 := by
        intro v hv1 hQv hpv
        have hv1A : A v = a • v ∨ A v = -(a • v) := by
          rcases hv1 with h | h
          · exact Or.inl (by rw [hA_coe]; exact h)
          · exact Or.inr (by rw [hA_coe]; exact h)
        have hQbv : Q (B v) = 0 := by
          rw [Q_map_of_selfAdjoint_sq h2 hsaB hB2 v, hQv, mul_zero]
        have hW : Submodule.span K ({v, B v} : Set (Fin d → K)) = ⊥ := by
          refine hnoAB _ (span_pair_singular hQv hQbv ?_) ?_ ?_
          · rwa [hB_coe]
          · refine span_pair_stable ?_ ?_
            · rcases hv1A with h | h
              · rw [h]
                exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
              · rw [h]
                exact Submodule.neg_mem _
                  (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            · rw [hcomm v]
              rcases hv1A with h | h
              · rw [h, map_smul]
                exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
              · rw [h, map_neg, map_smul]
                exact Submodule.neg_mem _
                  (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          · refine span_pair_stable ?_ ?_
            · exact Submodule.subset_span (by simp)
            · rw [hB2]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        have hv : v ∈ Submodule.span K ({v, B v} : Set (Fin d → K)) :=
          Submodule.subset_span (by simp)
        rw [hW] at hv
        simpa using hv
      exact planeGen_of_mixed_lifts (Q := Q) h2 hnd hd7 hder ga gb hκga hκgb hκga1 hκgb1
        hgra hgrb ha0 hβnsq haA2 hB2σ hAsaσ hBsaσ hcommσ hanisMix
  · by_cases hβ : IsSquare (cB : K)
    ·
      obtain ⟨b, hb⟩ := hβ
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact hβ0 (by rw [hb]; simp)
      have hαnsq : ∀ s : K, s * s ≠ (cA : K) := by
        intro s hs
        exact hα (hs ▸ IsSquare.mul_self s)
      have hbB2 : ∀ v, coordinateSemilinearMap gb.val (coordinateSemilinearMap gb.val v) =
          (b * b) • v := fun v => by rw [hB2σ v, hb]
      have hanisMix : ∀ v, (coordinateSemilinearMap gb.val v = b • v ∨
          coordinateSemilinearMap gb.val v = -(b • v)) → Q v = 0 →
          polar Q v (coordinateSemilinearMap ga.val v) = 0 → v = 0 := by
        intro v hv1 hQv hpv
        have hv1B : B v = b • v ∨ B v = -(b • v) := by
          rcases hv1 with h | h
          · exact Or.inl (by rw [hB_coe]; exact h)
          · exact Or.inr (by rw [hB_coe]; exact h)
        have hQav : Q (A v) = 0 := by
          rw [Q_map_of_selfAdjoint_sq h2 hsaA hA2 v, hQv, mul_zero]
        have hW : Submodule.span K ({v, A v} : Set (Fin d → K)) = ⊥ := by
          refine hnoAB _ (span_pair_singular hQv hQav ?_) ?_ ?_
          · rwa [hA_coe]
          · refine span_pair_stable ?_ ?_
            · exact Submodule.subset_span (by simp)
            · rw [hA2]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
          · refine span_pair_stable ?_ ?_
            · rcases hv1B with h | h
              · rw [h]
                exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
              · rw [h]
                exact Submodule.neg_mem _
                  (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            · rw [← hcomm v]
              rcases hv1B with h | h
              · rw [h, map_smul]
                exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
              · rw [h, map_neg, map_smul]
                exact Submodule.neg_mem _
                  (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have hv : v ∈ Submodule.span K ({v, A v} : Set (Fin d → K)) :=
          Submodule.subset_span (by simp)
        rw [hW] at hv
        simpa using hv
      exact planeGen_of_mixed_lifts (Q := Q) h2 hnd hd7 hder gb ga hκgb hκga hκgb1 hκga1
        hgrb hgra hb0 hαnsq hbB2 hA2σ hBsaσ hAsaσ (fun v => (hcommσ v).symm) hanisMix
    ·
      let : Fintype K := Fintype.ofFinite K
      have hα1 : quadraticChar K (cA : K) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hα
      have hβ1 : quadraticChar K (cB : K) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hβ
      have hsqprod : IsSquare ((cA : K) * (cB : K)) := by
        rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hα0 hβ0)]
        rw [map_mul, hα1, hβ1]
        norm_num
      obtain ⟨s, hs⟩ := hsqprod
      have hs0 : s ≠ 0 := by
        rintro rfl
        refine mul_ne_zero hα0 hβ0 ?_
        rw [hs]; simp
      let gab : similarityPairs Q := ga * gb
      have hσab : ∀ v, coordinateSemilinearMap gab.val v = A (B v) := by
        intro v
        have h : coordinateSemilinearMap gab.val v =
            coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val v) := by
          rw [show gab.val = ga.val * gb.val from rfl, coordinateSemilinearMap_mul]
        simpa [hA_coe, hB_coe] using h
      have hga' : matrixProjectiveConjugationHom Q gab ∈ E := by
        rw [show matrixProjectiveConjugationHom Q gab = matrixProjectiveConjugationHom Q ga *
          matrixProjectiveConjugationHom Q gb from map_mul (matrixProjectiveConjugationHom Q) ga gb]
        exact Subgroup.mul_mem _ hκga hκgb
      have hgb2 : matrixProjectiveConjugationHom Q gb * matrixProjectiveConjugationHom Q gb =
          1 := by
        have h := hE.2 (matrixProjectiveConjugationHom Q gb) hκgb
        simpa [pow_two] using h
      have hga1' : matrixProjectiveConjugationHom Q gab ≠ 1 := by
        intro h
        have h1 : matrixProjectiveConjugationHom Q ga * matrixProjectiveConjugationHom Q gb =
            1 := by
          rw [← map_mul (matrixProjectiveConjugationHom Q) ga gb]
          exact h
        have h2 : matrixProjectiveConjugationHom Q ga = matrixProjectiveConjugationHom Q gb := by
          calc matrixProjectiveConjugationHom Q ga
              = matrixProjectiveConjugationHom Q ga * 1 := (mul_one _).symm
            _ = matrixProjectiveConjugationHom Q ga *
                (matrixProjectiveConjugationHom Q gb * matrixProjectiveConjugationHom Q gb) := by
                rw [hgb2]
            _ = (matrixProjectiveConjugationHom Q ga * matrixProjectiveConjugationHom Q gb) *
                matrixProjectiveConjugationHom Q gb := by rw [mul_assoc]
            _ = 1 * matrixProjectiveConjugationHom Q gb := by rw [h1]
            _ = matrixProjectiveConjugationHom Q gb := one_mul _
        exact hκne h2
      have hgra' : gab.val.right = 1 := by
        rw [show gab.val.right = ga.val.right * gb.val.right from rfl, hgra, hgrb, mul_one]
      have hAB2 : ∀ v, A (B (A (B v))) = ((cA : K) * (cB : K)) • v := by
        intro v
        calc A (B (A (B v))) = A (A (B (B v))) := by rw [← hcomm (B v)]
          _ = (cA : K) • B (B v) := by rw [hA2]
          _ = (cA : K) • ((cB : K) • v) := by rw [hB2]
          _ = ((cA : K) * (cB : K)) • v := by rw [smul_smul]
      have hA2'' : ∀ v, coordinateSemilinearMap gab.val (coordinateSemilinearMap gab.val v) =
          (s * s) • v := by
        intro v
        rw [hσab, hσab, hAB2, hs]
      have hAsa'' : ∀ u w, polar Q (coordinateSemilinearMap gab.val u) w =
          polar Q u (coordinateSemilinearMap gab.val w) := by
        intro u w
        rw [hσab, hσab, hsaA (B u) w, hsaB u (A w), hcomm w]
      have hAB'' : ∀ v, coordinateSemilinearMap gab.val (coordinateSemilinearMap gb.val v) =
          coordinateSemilinearMap gb.val (coordinateSemilinearMap gab.val v) := by
        intro v
        rw [hσab, hσab]
        simpa [hB_coe] using hcomm (B v)
      have hanis'' : ∀ v, (coordinateSemilinearMap gab.val v = s • v ∨
          coordinateSemilinearMap gab.val v = -(s • v)) → Q v = 0 →
          polar Q v (coordinateSemilinearMap gb.val v) = 0 → v = 0 := by
        intro v hv1 hQv hpv
        have hv1AB : A (B v) = s • v ∨ A (B v) = -(s • v) := by
          rcases hv1 with h | h
          · exact Or.inl (by rwa [hσab] at h)
          · exact Or.inr (by rwa [hσab] at h)
        have hQbv : Q (B v) = 0 := by
          rw [Q_map_of_selfAdjoint_sq h2 hsaB hB2 v, hQv, mul_zero]
        have hWBW : ∀ x ∈ Submodule.span K ({v, B v} : Set (Fin d → K)),
            B x ∈ Submodule.span K ({v, B v} : Set (Fin d → K)) := by
          refine span_pair_stable ?_ ?_
          · exact Submodule.subset_span (by simp)
          · rw [hB2]
            exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        have hABW : ∀ x ∈ Submodule.span K ({v, B v} : Set (Fin d → K)),
            A (B x) ∈ Submodule.span K ({v, B v} : Set (Fin d → K)) := by
          refine span_pair_stable (T := A.comp B) ?_ ?_
          · change A (B v) ∈ Submodule.span K ({v, B v} : Set (Fin d → K))
            rcases hv1AB with h | h
            · rw [h]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
            · rw [h]
              exact Submodule.neg_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          · change A (B (B v)) ∈ Submodule.span K ({v, B v} : Set (Fin d → K))
            rw [hcomm (B v)]
            rcases hv1AB with h | h
            · rw [h, map_smul]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
            · rw [h, map_neg, map_smul]
              exact Submodule.neg_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have hWAW : ∀ x ∈ Submodule.span K ({v, B v} : Set (Fin d → K)),
            A x ∈ Submodule.span K ({v, B v} : Set (Fin d → K)) := by
          intro x hx
          have hAeq : A x = (cB : K)⁻¹ • A (B (B x)) := by
            rw [hB2 x, map_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
          rw [hAeq]
          exact Submodule.smul_mem _ _ (hABW (B x) (hWBW x hx))
        have hW : Submodule.span K ({v, B v} : Set (Fin d → K)) = ⊥ :=
          hnoAB _ (span_pair_singular hQv hQbv (by rwa [hB_coe])) hWAW hWBW
        have hv : v ∈ Submodule.span K ({v, B v} : Set (Fin d → K)) :=
          Submodule.subset_span (by simp)
        rw [hW] at hv
        simpa using hv
      have hβnsq : ∀ t : K, t * t ≠ (cB : K) := by
        intro t ht
        exact hβ (ht ▸ IsSquare.mul_self t)
      exact planeGen_of_mixed_lifts (Q := Q) h2 hnd hd7 hder gab gb hga' hκgb hga1' hκgb1
        hgra' hgrb hs0 hβnsq hA2'' hB2σ hAsa'' hBsaσ hAB'' hanis''

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
