module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsTorus
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusForm

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace CoordSpNs

section Trans

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D]

@[expose] def FormTransitive (K : Type) [Field K] (D : Type) [AddCommGroup D] [Module K D]
    (c : D ≃ₗ[K] D) : Prop :=
  ∀ β β' : LinearMap.BilinForm K D, β.IsAlt → β'.IsAlt → β.Nondegenerate → β'.Nondegenerate →
    (∀ x y, β (c x) (c y) = β x y) → (∀ x y, β' (c x) (c y) = β' x y) →
    ∃ T : D ≃ₗ[K] D, (∀ x, T (c x) = c (T x)) ∧ ∀ x y, β' (T x) (T y) = β x y

theorem symm_of_isAlt [CharP K 2] {β : LinearMap.BilinForm K D} (hβ : β.IsAlt) (x y : D) :
    β x y = β y x := by
  rw [← hβ.neg_eq x y, CharTwo.neg_eq]

theorem apply_c_left {β : LinearMap.BilinForm K D} {c : D ≃ₗ[K] D}
    (hβc : ∀ x y, β (c x) (c y) = β x y) (x y : D) : β (c x) y = β x (c.symm y) := by
  conv_lhs => rw [← c.apply_symm_apply y]
  exact hβc x (c.symm y)

theorem end_add_self [CharP K 2] (T : Module.End K D) : T + T = 0 := by
  rw [← two_smul K T, CharTwo.two_eq_zero, zero_smul]

theorem formTransitive_of_comm [Finite K] [CharP K 2] [FiniteDimensional K D] {c : D ≃ₗ[K] D}
    (hcomm : ∀ T T' : Module.End K D, (∀ x, T (c x) = c (T x)) → (∀ x, T' (c x) = c (T' x)) →
      T * T' = T' * T)
    (hred : ∀ T : Module.End K D, (∀ x, T (c x) = c (T x)) → T * T = 0 → T = 0) :
    FormTransitive K D c := by
  intro β β' hβa hβ'a hβnd hβ'nd hβc hβ'c
  classical
  set e' := β'.toDual hβ'nd with he'
  set T : Module.End K D := e'.symm.toLinearMap ∘ₗ β with hTdef
  have hT : ∀ x y, β' (T x) y = β x y := fun x y => by
    rw [← LinearMap.BilinForm.toDual_def hβ'nd]
    change (e' (e'.symm (β x))) y = β x y
    rw [LinearEquiv.apply_symm_apply]
  have hsep : ∀ v w : D, (∀ y, β' v y = β' w y) → v = w := fun v w h => by
    have := hβ'nd.1 (v - w) fun y => by rw [LinearMap.map_sub₂, h y, sub_self]
    exact sub_eq_zero.mp this
  have hTc : ∀ x, T (c x) = c (T x) := fun x => hsep _ _ fun y => by
    rw [hT, apply_c_left hβc, ← hT, ← hβ'c (T x) (c.symm y), LinearEquiv.apply_symm_apply]
  have hTsa : ∀ x y, β' (T x) y = β' x (T y) := fun x y => by
    rw [hT, symm_of_isAlt hβa, ← hT, symm_of_isAlt hβ'a]
  let A := {S : Module.End K D // (∀ x, S (c x) = c (S x)) ∧ ∀ x y, β' (S x) y = β' x (S y)}
  have : Finite (Module.End K D) := Module.finite_of_finite K
  have : Finite A := Subtype.finite
  let sq : A → A := fun S => ⟨S.1 * S.1, fun x => by
      rw [Module.End.mul_apply, Module.End.mul_apply, S.2.1, S.2.1],
    fun x y => by rw [Module.End.mul_apply, Module.End.mul_apply, S.2.2, S.2.2]⟩
  have hsqinj : Function.Injective sq := by
    intro S S' h
    have h1 : S.1 * S.1 = S'.1 * S'.1 := congrArg Subtype.val h
    have hc' : ∀ x, (S.1 - S'.1) (c x) = c ((S.1 - S'.1) x) := fun x => by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, S.2.1, S'.2.1, map_sub]
    have hcomm' := hcomm S.1 S'.1 S.2.1 S'.2.1
    have h0 : (S.1 - S'.1) * (S.1 - S'.1) = 0 := by
      have e : (S.1 - S'.1) * (S.1 - S'.1) =
          S.1 * S.1 + S'.1 * S'.1 - (S.1 * S'.1 + S.1 * S'.1) := by
        rw [sub_mul, mul_sub, mul_sub, ← hcomm']
        abel
      rw [e, end_add_self, sub_zero, h1, end_add_self]
    exact Subtype.ext (sub_eq_zero.mp (hred _ hc' h0))
  obtain ⟨S, hS⟩ := (Finite.injective_iff_surjective.mp hsqinj) ⟨T, hTc, hTsa⟩
  have hSS : S.1 * S.1 = T := congrArg Subtype.val hS
  have hSinj : Function.Injective S.1 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hβnd.1 x
    intro y
    rw [← hT, ← hSS, Module.End.mul_apply, hx, map_zero, LinearMap.map_zero₂]
  refine ⟨LinearEquiv.ofInjectiveEndo S.1 hSinj, fun x => S.2.1 x, fun x y => ?_⟩
  change β' (S.1 x) (S.1 y) = β x y
  rw [S.2.2, ← Module.End.mul_apply, hSS, ← hTsa, hT]

theorem mem_twistGroup_of_conj {p : ℕ} [NeZero p] {c : D ≃ₗ[K] D} (hc : c ^ p = 1)
    (htr : FormTransitive K D c) {β : LinearMap.BilinForm K D} (hβa : β.IsAlt)
    (hβnd : β.Nondegenerate) (hβc : ∀ x y, β (c x) (c y) = β x y) {u : (ZMod p)ˣ}
    (T₀ : D ≃ₗ[K] D) (hT₀ : ∀ x, T₀ ((c ^ (u : ZMod p).val) x) = c (T₀ x)) :
    u ∈ twistGroup β c hc := by
  set β₁ : LinearMap.BilinForm K D := β.comp T₀.toLinearMap T₀.toLinearMap with hβ₁def
  have hβ₁ : ∀ x y, β₁ x y = β (T₀ x) (T₀ y) := fun x y => rfl
  have hT₀c : ∀ x, T₀ (c x) = (c ^ ((u⁻¹ : (ZMod p)ˣ) : ZMod p).val) (T₀ x) := by
    intro x
    have h1 := apply_pow_of_conj hc hT₀ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) x
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, CoordSL.pow_val_one hc] at h1
  have hβ₁c : ∀ x y, β₁ (c x) (c y) = β₁ x y := fun x y => by
    rw [hβ₁, hβ₁, hT₀c, hT₀c, pow_isom hβc]
  have hβ₁a : β₁.IsAlt := fun x => hβa _
  have hβ₁nd : β₁.Nondegenerate := by
    refine ⟨fun x hx => T₀.injective ?_, fun y hy => T₀.injective ?_⟩
    · rw [map_zero]
      refine hβnd.1 _ fun y => ?_
      obtain ⟨y', rfl⟩ := T₀.surjective y
      exact hx y'
    · rw [map_zero]
      refine hβnd.2 _ fun x => ?_
      obtain ⟨x', rfl⟩ := T₀.surjective x
      exact hy x'
  obtain ⟨R, hRc, hR⟩ := htr β β₁ hβa hβ₁a hβnd hβ₁nd hβc hβ₁c
  refine ⟨R.trans T₀, fun x y => hR x y, fun x => ?_⟩
  have hR' : ∀ y, R ((c ^ (u : ZMod p).val) y) = (c ^ (u : ZMod p).val) (R y) :=
    fun y => apply_pow_of_comm (T := R.toLinearMap) (fun z => hRc z) _ y
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hR', hT₀]

end Trans

section NFrame

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [Nontrivial D] {p : ℕ}

theorem exists_normFrame {c : D →ₗ[K] D} {cE : D ≃ₗ[K] D} (hcE : ∀ x, cE x = c x)
    (hD : SpNS.SpBlockExists K p D c) (hp : 1 ≤ p) (hc1 : ∀ u : D, ∃ u₀, c u₀ - u₀ = u)
    (htr : FormTransitive K D cE) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hAlt : B.IsAlt)
    (hnd : B.Nondegenerate) (S : Set (Module.End K V))
    (hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x') (hSp : ∀ x ∈ S, x ^ p = 1)
    (hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w) (hS1 : ∃ x ∈ S, x ≠ 1) :
    ∃ (s : ℕ) (κ : Type) (_ : Fintype κ) (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V)
      (β : LinearMap.BilinForm K D), β.IsAlt ∧ β.Nondegenerate ∧
      (∀ x y, β (cE x) (cE y) = β x y) ∧
      (∀ x ∈ S, ∃ k : Fin s → ℕ, ∀ d w, x (Φ (d, w)) = Φ (fun i => (c ^ k i) (d i), w)) ∧
      ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
        ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')) := by
  classical
  obtain ⟨ι, κ, _, _, Φ₀, hΦS, hΦB⟩ := SpNS.exists_spFrame hD hp B S hAlt hnd hSc hSp hSB
  have hrefl : B.IsRefl := hAlt.isRefl
  have hdec := SpNS.frame_bilin_eq hrefl hc1 hΦB
  have hblockAlt : ∀ i, (SpNS.frameBlockForm B Φ₀ i).IsAlt := fun i u => hAlt _
  have hblockL : ∀ i u, (∀ v, SpNS.frameBlockForm B Φ₀ i u v = 0) → u = 0 := by
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
    have h3 : ((Pi.single i u : ι → D), (0 : κ → K)) = 0 :=
      Φ₀.injective (h2.trans (map_zero Φ₀).symm)
    have h4 := congrArg (fun x : (ι → D) × (κ → K) => x.1 i) h3
    simpa using h4
  have hblockNd : ∀ i, (SpNS.frameBlockForm B Φ₀ i).Nondegenerate := fun i =>
    ⟨hblockL i, fun v hv => hblockL i v fun u => by
      rw [← (hblockAlt i).neg_eq, hv u, neg_zero]⟩
  have hsingle : ∀ (i : ι) (u : D), (fun j => (c ^ (Pi.single i 1 : ι → ℕ) j)
      ((Pi.single i u : ι → D) j)) = Pi.single i (c u) := by
    intro i u
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  have hblockC : ∀ i x y, SpNS.frameBlockForm B Φ₀ i (cE x) (cE y) =
      SpNS.frameBlockForm B Φ₀ i x y := by
    intro i x y
    rw [SpNS.frameBlockForm_apply, SpNS.frameBlockForm_apply, hcE, hcE, ← hsingle, ← hsingle]
    exact hΦB (Pi.single i 1) (Pi.single i x) (Pi.single i y) 0 0
  obtain ⟨x₁, hx₁S, hx₁⟩ := hS1
  have hι : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    apply hx₁
    obtain ⟨k, hk⟩ := hΦS x₁ hx₁S
    refine LinearMap.ext fun v => ?_
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ₀.surjective v
    rw [hk, Module.End.one_apply]
    congr 2
    funext i
    exact isEmptyElim i
  obtain ⟨i₀⟩ := hι
  set β := SpNS.frameBlockForm B Φ₀ i₀ with hβ
  have hT : ∀ i, ∃ T : D ≃ₗ[K] D, (∀ x, T (cE x) = cE (T x)) ∧
      ∀ x y, SpNS.frameBlockForm B Φ₀ i (T x) (T y) = β x y := fun i =>
    htr β _ (hblockAlt i₀) (hblockAlt i) (hblockNd i₀) (hblockNd i) (hblockC i₀) (hblockC i)
  choose T hTc hTβ using hT
  have hTc' : ∀ i (m : ℕ) (x : D), T i ((c ^ m) x) = (c ^ m) (T i x) := by
    intro i m x
    induction m generalizing x with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← hcE, hTc, ih, hcE]
  set e := Fintype.equivFin ι with he
  set Φ : ((Fin (Fintype.card ι) → D) × (κ → K)) ≃ₗ[K] V :=
    ((LinearEquiv.funCongrLeft K D e).prodCongr (LinearEquiv.refl K (κ → K))).trans
      (((LinearEquiv.piCongrRight T).prodCongr (LinearEquiv.refl K (κ → K))).trans Φ₀) with hΦ
  have hΦa : ∀ d w, Φ (d, w) = Φ₀ (fun i => T i (d (e i)), w) := fun d w => rfl
  refine ⟨Fintype.card ι, κ, inferInstance, Φ, β, hblockAlt i₀, hblockNd i₀, hblockC i₀,
    fun x hx => ?_, fun d d' w w' => ?_⟩
  · obtain ⟨k, hk⟩ := hΦS x hx
    refine ⟨k ∘ e.symm, fun d w => ?_⟩
    rw [hΦa, hΦa, hk]
    congr 2
    funext i
    simp [hTc']
  · rw [hΦa, hΦa, hdec, hΦa, hΦa]
    have h0 : (fun i => T i ((0 : Fin (Fintype.card ι) → D) (e i))) = 0 := by
      funext i
      simp
    rw [h0]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hTβ]

end NFrame

end CoordSpNs

end CFSG.StandardType
