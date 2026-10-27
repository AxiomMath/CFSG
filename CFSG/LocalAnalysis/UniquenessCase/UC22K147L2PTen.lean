module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open scoped TensorProduct

theorem sup_induction_of_mul {G : Type*} [Group G] {K₁ K₂ : Subgroup G} {C : G → Prop}
    (h₁ : ∀ x ∈ K₁, C x) (h₂ : ∀ x ∈ K₂, C x) (one : C 1)
    (mul : ∀ x y, C x → C y → C (x * y)) {x : G} (hx : x ∈ K₁ ⊔ K₂) : C x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with hx | hx
    · exact h₁ x hx
    · exact h₂ x hx
  | inv_mem x hx =>
    rcases hx with hx | hx
    · exact h₁ _ (inv_mem hx)
    · exact h₂ _ (inv_mem hx)
  | one => exact one
  | mul x y _ _ ihx ihy => exact mul x y ihx ihy

section Tensor

variable {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem exists_tensor_field [Nontrivial Y] {K₁ K₂ : Subgroup (GLV Y)}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hirr : Offender.IsIrrAct (K₁ ⊔ K₂)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F) (_ : Module F Y),
      (∀ f : Module.End (ZMod 2) Y, (∀ h ∈ K₁ ⊔ K₂, ∀ w, f (h w) = h (f w)) →
        ∃ c : F, ∀ w, f w = c • w) ∧
      ∃ (V₀ V₁ : Type) (_ : AddCommGroup V₀) (_ : AddCommGroup V₁) (_ : Module F V₀)
        (_ : Module F V₁) (_ : Module.Finite F V₀) (_ : Module.Finite F V₁)
        (ρ₀ : ↥K₁ →* (V₀ ≃ₗ[F] V₀)) (ρ₁ : ↥K₂ →* (V₁ ≃ₗ[F] V₁)) (e : Y ≃+ V₀ ⊗[F] V₁),
        Nontrivial V₀ ∧ Nontrivial V₁ ∧
        (∀ (g : ↥K₁) (v : Y), e ((g : GLV Y) v) =
          TensorProduct.map (ρ₀ g : V₀ →ₗ[F] V₀) LinearMap.id (e v)) ∧
        (∀ (g : ↥K₂) (v : Y), e ((g : GLV Y) v) =
          TensorProduct.map LinearMap.id (ρ₁ g : V₁ →ₗ[F] V₁) (e v)) := by
  classical
  obtain ⟨F, _, _, _, _, _, hcommF, -, -, -, -⟩ :=
    Offender.finite_irreducible_endomorphism_field_density.{0, 0, 0} (K₁ ⊔ K₂) hirr
  have hFlin : ∀ h ∈ K₁ ⊔ K₂, ∀ (c : F) (w : Y), h (c • w) = c • h w := by
    intro h hh c w
    let f : Module.End (ZMod 2) Y :=
      { toFun := fun w => c • w
        map_add' := smul_add c
        map_smul' := fun r w => ZMod.map_smul (DistribSMul.toAddMonoidHom Y c) r w }
    exact ((hcommF f).mpr ⟨c, fun _ => rfl⟩ h hh w).symm
  let P : Fin 2 → Subgroup (GLV Y) := ![K₁, K₂]
  have hPle : ∀ i, P i ≤ K₁ ⊔ K₂ := fun i => by
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  let φ : ∀ i, ↥(P i) →* (Y ≃ₗ[F] Y) := fun i =>
    { toFun := fun g => CFSG.Quasithin.SmithD37.toFLin (g : GLV Y) (hFlin _ (hPle i g.2))
      map_one' := by ext w; rfl
      map_mul' := fun a b => by ext w; rfl }
  have hc : ∀ i j, i ≠ j → ∀ (x : ↥(P i)) (y : ↥(P j)), φ i x * φ j y = φ j y * φ i x := by
    intro i j hij x y
    have hxy : (x : GLV Y) * y = y * x := by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hcomm x x.2 y y.2
      · exact (hcomm y y.2 x x.2).symm
      · exact absurd rfl hij
    ext w
    exact LinearEquiv.congr_fun hxy w
  have hirrF : ∀ S : Submodule F Y,
      (∀ i (g : ↥(P i)), ∀ u ∈ S, φ i g u ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hinv : ∀ h ∈ K₁ ⊔ K₂, ∀ u ∈ S.restrictScalars (ZMod 2),
        h u ∈ S.restrictScalars (ZMod 2) := fun h hh =>
      sup_induction_of_mul (C := fun h : GLV Y => ∀ u ∈ S.restrictScalars (ZMod 2),
          h u ∈ S.restrictScalars (ZMod 2))
        (fun x hx u hu => hS 0 ⟨x, hx⟩ u hu) (fun x hx u hu => hS 1 ⟨x, hx⟩ u hu)
        (fun u hu => hu) (fun x y hx hy u hu => hx _ (hy u hu)) hh
    rcases hirr _ hinv with h | h
    · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff (ZMod 2) F Y).mp h)
    · exact Or.inr ((Submodule.restrictScalars_eq_top_iff (ZMod 2) F Y).mp h)
  have hendF : ∀ f : Module.End F Y,
      (∀ i (g : ↥(P i)), ∀ w, f (φ i g w) = φ i g (f w)) → ∃ c : F, ∀ w, f w = c • w := by
    intro f hf
    refine (hcommF (f.restrictScalars (ZMod 2))).mp fun h hh => ?_
    exact sup_induction_of_mul (C := fun h : GLV Y => ∀ w, f (h w) = h (f w))
      (fun x hx w => hf 0 ⟨x, hx⟩ w) (fun x hx w => hf 1 ⟨x, hx⟩ w) (fun w => rfl)
      (fun x y hx hy w => by
        show f (x (y w)) = x (y (f w))
        rw [hx, hy]) hh
  obtain ⟨V, _, _, ρ, e, hnt, hfin, hact, -⟩ :=
    Offender.tensor_decomposition_core 2 (fun i => ↥(P i)) φ hc hirrF hendF
  haveI : ∀ i, Finite (V i) := hfin
  haveI : ∀ i, Module.Finite F (V i) := fun i => Module.Finite.of_finite
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance,
    fun f hf => (hcommF f).mp hf, V 0, V 1, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ρ 0, ρ 1,
    (e.trans TensorAux.binEquiv).toAddEquiv, hnt 0, hnt 1, fun g v => ?_, fun g v => ?_⟩
  · exact (congrArg TensorAux.binEquiv (hact 0 g v)).trans (TensorAux.binEquiv_factorEnd_zero _ _)
  · exact (congrArg TensorAux.binEquiv (hact 1 g v)).trans (TensorAux.binEquiv_factorEnd_one _ _)

theorem exists_smul_eq_of_match {F : Type} [Field F] [Module F Y] {K₁ K₂ : Subgroup (GLV Y)}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hirr : Offender.IsIrrAct (K₁ ⊔ K₂))
    (hcom : ∀ f : Module.End (ZMod 2) Y, (∀ h ∈ K₁ ⊔ K₂, ∀ w, f (h w) = h (f w)) →
      ∃ a : F, ∀ w, f w = a • w)
    {c c' : Y} (hc : c ≠ 0) (h₁ : ∀ k ∈ K₁, ∃ y ∈ K₂, k c = y c)
    (h₂ : ∀ y ∈ K₂, ∃ k ∈ K₁, y c = k c ∧ y c' = k c') : ∃ a : F, c' = a • c := by
  classical
  let A := Offender.spanAlg K₁
  have hmem : ∀ k ∈ K₁, ((k : GLV Y) : Module.End (ZMod 2) Y) ∈ A := fun k hk =>
    Offender.mem_spanAlg_of_mem hk
  have hA₂ : ∀ y ∈ K₂, ∀ r ∈ A, ∀ w, y (r w) = r (y w) := fun y hy r hr =>
    Offender.comm_spanAlg (f := (y : Module.End (ZMod 2) Y))
      (fun h hh w => (LinearEquiv.congr_fun (hcomm h hh y hy) w).symm) hr
  let ev : ↥A →ₗ[ZMod 2] Y := (LinearMap.applyₗ c).comp A.val.toLinearMap
  have hinvU : ∀ h ∈ K₁ ⊔ K₂, ∀ u ∈ LinearMap.range ev, h u ∈ LinearMap.range ev := by
    intro h hh
    refine sup_induction_of_mul
      (C := fun h : GLV Y => ∀ u ∈ LinearMap.range ev, h u ∈ LinearMap.range ev) ?_ ?_
      (fun u hu => hu) (fun x y hx hy u hu => hx _ (hy u hu)) hh
    · rintro k hk _ ⟨r, rfl⟩
      exact ⟨⟨(k : Module.End (ZMod 2) Y) * r, mul_mem (hmem k hk) r.2⟩, rfl⟩
    · rintro y hy _ ⟨r, rfl⟩
      obtain ⟨k, hk, hyc, -⟩ := h₂ y hy
      refine ⟨⟨(r : Module.End (ZMod 2) Y) * (k : Module.End (ZMod 2) Y),
        mul_mem r.2 (hmem k hk)⟩, ?_⟩
      show (r : Module.End (ZMod 2) Y) (k c) = y ((r : Module.End (ZMod 2) Y) c)
      rw [hA₂ y hy r r.2 c, hyc]
  have hc0 : c ∈ LinearMap.range ev := ⟨1, rfl⟩
  have hsurj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top]
    refine (hirr _ hinvU).resolve_left fun h => hc ?_
    rw [h] at hc0
    exact (Submodule.mem_bot _).mp hc0
  have hA4 : ∀ b ∈ A, ∀ a ∈ A, a c = 0 → a (b c) = 0 := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨k, hk⟩, rfl⟩ := hx
      intro a ha hac
      obtain ⟨y, hy, hkc⟩ := h₁ k hk
      show a (k c) = 0
      rw [hkc, ← hA₂ y hy a ha c, hac, map_zero]
    | algebraMap r =>
      intro a _ hac
      rw [Module.algebraMap_end_apply, map_smul, hac, smul_zero]
    | add x y _ _ hx hy =>
      intro a ha hac
      rw [LinearMap.add_apply, map_add, hx a ha hac, hy a ha hac, add_zero]
    | mul x y hx' _ hx hy =>
      intro a ha hac
      exact hy (a * x) (mul_mem ha hx') (hx a ha hac)
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨a, ha⟩ hac
    refine (Submodule.mem_bot _).mpr (Subtype.ext (LinearMap.ext fun w => ?_))
    obtain ⟨⟨b, hb⟩, rfl⟩ := hsurj w
    exact hA4 b hb a ha (LinearMap.mem_ker.mp hac)
  let eqv : ↥A ≃ₗ[ZMod 2] Y := LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩
  let f : Module.End (ZMod 2) Y :=
    (LinearMap.applyₗ c').comp (A.val.toLinearMap.comp eqv.symm.toLinearMap)
  have hf : ∀ r : ↥A, f (ev r) = (r : Module.End (ZMod 2) Y) c' := fun r => by
    show ((eqv.symm (eqv r) : ↥A) : Module.End (ZMod 2) Y) c' = _
    rw [LinearEquiv.symm_apply_apply]
  have hfK : ∀ h ∈ K₁ ⊔ K₂, ∀ w, f (h w) = h (f w) := by
    intro h hh
    refine sup_induction_of_mul (C := fun h : GLV Y => ∀ w, f (h w) = h (f w)) ?_ ?_
      (fun w => rfl) (fun x y hx hy w => by
        show f (x (y w)) = x (y (f w))
        rw [hx, hy]) hh
    · intro k hk w
      obtain ⟨r, rfl⟩ := hsurj w
      have h1 : k (ev r) = ev ⟨(k : Module.End (ZMod 2) Y) * r, mul_mem (hmem k hk) r.2⟩ := rfl
      rw [h1, hf, hf]
      rfl
    · intro y hy w
      obtain ⟨r, rfl⟩ := hsurj w
      obtain ⟨k, hk, hyc, hyc'⟩ := h₂ y hy
      have h1 : y (ev r) = ev ⟨(r : Module.End (ZMod 2) Y) * (k : Module.End (ZMod 2) Y),
          mul_mem r.2 (hmem k hk)⟩ := by
        show y ((r : Module.End (ZMod 2) Y) c) = (r : Module.End (ZMod 2) Y) (k c)
        rw [hA₂ y hy r r.2 c, hyc]
      rw [h1, hf, hf]
      show (r : Module.End (ZMod 2) Y) (k c') = y ((r : Module.End (ZMod 2) Y) c')
      rw [hA₂ y hy r r.2 c', hyc']
  obtain ⟨a, ha⟩ := hcom f hfK
  have h1 : f c = c' := hf 1
  exact ⟨a, h1.symm.trans (ha c)⟩

end Tensor

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
