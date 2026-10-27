module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusForm
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace SpNS

section Scale

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {ι κ : Type}

@[expose] noncomputable def scaleEquiv (t : ι → L) (ht : ∀ i, t i ≠ 0) :
    ((ι → L) × (κ → K)) ≃ₗ[K] ((ι → L) × (κ → K)) where
  toFun x := (fun i => t i * x.1 i, x.2)
  invFun x := (fun i => (t i)⁻¹ * x.1 i, x.2)
  map_add' x y := Prod.ext (funext fun i => mul_add _ _ _) rfl
  map_smul' c x := Prod.ext (funext fun i => by simp [Algebra.smul_def, mul_left_comm]) rfl
  left_inv x := Prod.ext (funext fun i => by simp [inv_mul_cancel_left₀ (ht i)]) rfl
  right_inv x := Prod.ext (funext fun i => by simp [mul_inv_cancel_left₀ (ht i)]) rfl

theorem scaleEquiv_apply (t : ι → L) (ht : ∀ i, t i ≠ 0) (d : ι → L) (w : κ → K) :
    scaleEquiv (κ := κ) (K := K) t ht (d, w) = (fun i => t i * d i, w) := rfl

end Scale

section NFrame

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

theorem exists_nframe (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hdeg : (CoordSL.rootPB g).dim = 2)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hAlt : B.IsAlt)
    (hnd : B.Nondegenerate) (S : Set (Module.End K V)) (hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x')
    (hSp : ∀ x ∈ S, x ^ p = 1) (hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w) :
    ∃ (s : ℕ) (κ : Type) (_ : Fintype κ) (Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] V)
      (β : LinearMap.BilinForm K (AdjoinRoot g)), β.IsAlt ∧
      (∀ x ∈ S, ∃ k : Fin s → ℕ, ∀ d w,
        x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)) ∧
      ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
        ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')) := by
  classical
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  set ζ := AdjoinRoot.root g with hζdef
  set c := LinearMap.mulLeft K ζ with hc
  have hck : ∀ (m : ℕ) (u : AdjoinRoot g), (c ^ m) u = ζ ^ m * u := fun m u => by
    rw [hc, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
  obtain ⟨ι, κ, _, _, Φ₀, hΦS, hΦB⟩ := exists_spFrame
    (spBlockExists_selfDual hp hp2 hpK hgd hσ) hp.one_lt.le B S hAlt hnd hSc hSp hSB
  have hrefl : B.IsRefl := hAlt.isRefl
  have hζ1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hp.one_lt)
  have hc1 : ∀ u : AdjoinRoot g, ∃ u₀, c u₀ - u₀ = u := fun u =>
    ⟨(ζ - 1)⁻¹ * u, by
      rw [hc, LinearMap.mulLeft_apply, ← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ hζ1,
        one_mul]⟩
  have hdec := frame_bilin_eq hrefl hc1 hΦB
  set b : Basis (Fin 2) K (AdjoinRoot g) := (CoordSL.rootPB g).basis.reindex (finCongr hdeg)
    with hb
  have hblockAlt : ∀ i, (frameBlockForm B Φ₀ i).IsAlt := fun i u => hAlt _
  have hblockNd : ∀ i u, (∀ v, frameBlockForm B Φ₀ i u v = 0) → u = 0 := by
    intro i u hu
    have h1 : ∀ y : V, B (Φ₀ (Pi.single i u, 0)) y = 0 := by
      intro y
      obtain ⟨⟨d', w'⟩, rfl⟩ := Φ₀.surjective y
      rw [hdec, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, hu, zero_add, Prod.mk_zero_zero, LinearEquiv.map_zero,
          LinearMap.map_zero₂]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, LinearMap.map_zero₂]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have h2 := hnd.1 _ h1
    have h3 : ((Pi.single i u : ι → AdjoinRoot g), (0 : κ → K)) = 0 :=
      Φ₀.injective (h2.trans (map_zero Φ₀).symm)
    have h4 := congrArg (fun x : (ι → AdjoinRoot g) × (κ → K) => x.1 i) h3
    simpa using h4
  have ha : ∀ i, frameBlockForm B Φ₀ i (b 0) (b 1) ≠ 0 := fun i =>
    alt_two_ne_zero b (hblockAlt i) (hblockNd i)
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have ht : ∀ i, ∃ t : AdjoinRoot g, Algebra.norm K t = (frameBlockForm B Φ₀ i (b 0) (b 1))⁻¹ :=
    fun i => FiniteField.norm_surjective K (AdjoinRoot g) _
  choose t ht using ht
  have ht0 : ∀ i, t i ≠ 0 := fun i h0 => by
    have := ht i
    rw [h0, Algebra.norm_zero] at this
    exact inv_ne_zero (ha i) this.symm
  set Φ₁ := (scaleEquiv (κ := κ) (K := K) t ht0).trans Φ₀ with hΦ₁
  have hΦ₁a : ∀ d w, Φ₁ (d, w) = Φ₀ (fun i => t i * d i, w) := fun d w => rfl
  have hform : ∀ i, frameBlockForm B Φ₁ i =
      (Algebra.norm K (t i)) • frameBlockForm B Φ₀ i := by
    intro i
    refine LinearMap.ext₂ fun u v => ?_
    rw [frameBlockForm_apply, hΦ₁a, hΦ₁a, LinearMap.smul_apply, LinearMap.smul_apply,
      smul_eq_mul]
    have e : ∀ x : AdjoinRoot g, (fun j => t j * (Pi.single i x : ι → AdjoinRoot g) j) =
        Pi.single i (t i * x) := fun x => by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    rw [e, e, Algebra.norm_apply]
    exact bilin_apply_det b (hblockAlt i) (Algebra.lmul K (AdjoinRoot g) (t i)) u v
  have hform1 : ∀ i, frameBlockForm B Φ₁ i (b 0) (b 1) = 1 := fun i => by
    rw [hform, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, ht i,
      inv_mul_cancel₀ (ha i)]
  have hAlt₁ : ∀ i, (frameBlockForm B Φ₁ i).IsAlt := fun i u => hAlt _
  have heq : ∀ i j, frameBlockForm B Φ₁ i = frameBlockForm B Φ₁ j := fun i j => by
    rw [alt_two_eq_smul b (hAlt₁ i) (hAlt₁ j) (by rw [hform1]; exact one_ne_zero), hform1,
      hform1, div_one, one_smul]
  have hΦ₁B : ∀ (k : ι → ℕ) (d d' : ι → AdjoinRoot g) (w w' : κ → K),
      B (Φ₁ (fun i => (c ^ k i) (d i), w)) (Φ₁ (fun i => (c ^ k i) (d' i), w')) =
        B (Φ₁ (d, w)) (Φ₁ (d', w')) := by
    intro k d d' w w'
    rw [hΦ₁a, hΦ₁a, hΦ₁a, hΦ₁a]
    have e : ∀ x : ι → AdjoinRoot g, (fun i => t i * (c ^ k i) (x i)) =
        fun i => (c ^ k i) (t i * x i) := fun x => by
      funext i
      rw [hck, hck, mul_left_comm]
    rw [e, e]
    exact hΦB k _ _ w w'
  have hdec₁ := frame_bilin_eq hrefl hc1 hΦ₁B
  have hact₁ : ∀ x ∈ S, ∃ k : ι → ℕ, ∀ d w,
      x (Φ₁ (d, w)) = Φ₁ (fun i => ζ ^ k i * d i, w) := by
    intro x hx
    obtain ⟨k, hk⟩ := hΦS x hx
    refine ⟨k, fun d w => ?_⟩
    rw [hΦ₁a, hΦ₁a, hk]
    congr 2
    funext i
    rw [hck, mul_left_comm]
  set e := Fintype.equivFin ι with he
  set Φ := ((LinearEquiv.funCongrLeft K (AdjoinRoot g) e).prodCongr
    (LinearEquiv.refl K (κ → K))).trans Φ₁ with hΦ
  have hΦa : ∀ d w, Φ (d, w) = Φ₁ (d ∘ e, w) := fun d w => rfl
  obtain ⟨β, hβalt, hβ⟩ : ∃ β : LinearMap.BilinForm K (AdjoinRoot g), β.IsAlt ∧
      ∀ i, frameBlockForm B Φ₁ i = β := by
    by_cases hι : Nonempty ι
    · obtain ⟨i₀⟩ := hι
      exact ⟨frameBlockForm B Φ₁ i₀, hAlt₁ i₀, fun i => heq i i₀⟩
    · exact ⟨0, fun _ => rfl, fun i => absurd ⟨i⟩ hι⟩
  refine ⟨Fintype.card ι, κ, inferInstance, Φ, β, hβalt, fun x hx => ?_, fun d d' w w' => ?_⟩
  · obtain ⟨k, hk⟩ := hact₁ x hx
    refine ⟨k ∘ e.symm, fun d w => ?_⟩
    rw [hΦa, hΦa, hk]
    congr 2
    funext i
    simp
  · rw [hΦa, hΦa, hdec₁, hΦa, hΦa]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ]
    simp

end NFrame

end SpNS

end CFSG.StandardType
