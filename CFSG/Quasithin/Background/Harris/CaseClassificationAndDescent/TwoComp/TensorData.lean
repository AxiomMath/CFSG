module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Struct
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.Background.SmithD37Lin

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
open scoped TensorProduct

namespace TensorAux

section PiTwo

variable {F : Type} [Field F] {W : Fin 2 → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)]

omit [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)] in
@[expose] def pairFam (a : W 0) (b : W 1) : ∀ i, W i := fun i => match i with | 0 => a | 1 => b

omit [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)] in
@[simp] theorem pairFam_zero (a : W 0) (b : W 1) : pairFam a b 0 = a := rfl

omit [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)] in
@[simp] theorem pairFam_one (a : W 0) (b : W 1) : pairFam a b 1 = b := rfl

omit [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)] in
theorem pairFam_eta (m : ∀ i, W i) : pairFam (m 0) (m 1) = m := by
  funext i
  fin_cases i <;> rfl

omit [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)] in
theorem pairFam_update_zero (a a' : W 0) (b : W 1) :
    Function.update (pairFam a b) 0 a' = pairFam a' b := by
  funext i
  fin_cases i <;> simp [Function.update_of_ne]

omit [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)] in
theorem pairFam_update_one (a : W 0) (b b' : W 1) :
    Function.update (pairFam a b) 1 b' = pairFam a b' := by
  funext i
  fin_cases i <;> simp [Function.update_of_ne]

@[expose] noncomputable def toBin : (⨂[F] i, W i) →ₗ[F] W 0 ⊗[F] W 1 :=
  PiTensorProduct.lift
    { toFun := fun m => m 0 ⊗ₜ m 1
      map_update_add' := by
        intro _ m i x y
        fin_cases i <;>
          simp [TensorProduct.add_tmul, TensorProduct.tmul_add, Function.update_of_ne]
      map_update_smul' := by
        intro _ m i c x
        fin_cases i <;>
          simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, Function.update_of_ne] }

theorem toBin_tprod (m : ∀ i, W i) :
    toBin (PiTensorProduct.tprod F m) = m 0 ⊗ₜ[F] m 1 := by
  simp [toBin]

@[expose] noncomputable def ofBin : W 0 ⊗[F] W 1 →ₗ[F] (⨂[F] i, W i) :=
  TensorProduct.lift
    (LinearMap.mk₂ F (fun a b => PiTensorProduct.tprod F (pairFam a b))
      (fun a a' b => by
        have := (PiTensorProduct.tprod F).map_update_add (pairFam a b) 0 a a'
        simpa [pairFam_update_zero] using this)
      (fun c a b => by
        have := (PiTensorProduct.tprod F).map_update_smul (pairFam a b) 0 c a
        simpa [pairFam_update_zero] using this)
      (fun a b b' => by
        have := (PiTensorProduct.tprod F).map_update_add (pairFam a b) 1 b b'
        simpa [pairFam_update_one] using this)
      (fun c a b => by
        have := (PiTensorProduct.tprod F).map_update_smul (pairFam a b) 1 c b
        simpa [pairFam_update_one] using this))

theorem ofBin_tmul (a : W 0) (b : W 1) :
    ofBin (a ⊗ₜ[F] b) = PiTensorProduct.tprod F (pairFam a b) := by
  simp [ofBin]

@[expose] noncomputable def binEquiv : (⨂[F] i, W i) ≃ₗ[F] W 0 ⊗[F] W 1 :=
  LinearEquiv.ofLinearMap toBin ofBin
    (TensorProduct.ext' fun a b => by simp [ofBin_tmul, toBin_tprod])
    (PiTensorProduct.ext (MultilinearMap.ext fun m => by
      simp [toBin_tprod, ofBin_tmul, pairFam_eta]))

theorem binEquiv_tprod (m : ∀ i, W i) :
    binEquiv (PiTensorProduct.tprod F m) = m 0 ⊗ₜ[F] m 1 :=
  toBin_tprod m

theorem binEquiv_factorEnd_zero (f : Module.End F (W 0)) (x : ⨂[F] i, W i) :
    binEquiv (CFSG.QuasithinUnique.Setup.Offender.factorEnd 0 f x) =
      TensorProduct.map f LinearMap.id (binEquiv x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, map_smul,
      CFSG.QuasithinUnique.Setup.Offender.factorEnd_tprod, binEquiv_tprod, binEquiv_tprod]
    simp [Function.update_of_ne]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem binEquiv_factorEnd_one (f : Module.End F (W 1)) (x : ⨂[F] i, W i) :
    binEquiv (CFSG.QuasithinUnique.Setup.Offender.factorEnd 1 f x) =
      TensorProduct.map LinearMap.id f (binEquiv x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, map_smul,
      CFSG.QuasithinUnique.Setup.Offender.factorEnd_tprod, binEquiv_tprod, binEquiv_tprod]
    simp [Function.update_of_ne]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end PiTwo

theorem end_comm_of_finrank_one {F X : Type} [Field F] [AddCommGroup X] [Module F X]
    (h : Module.finrank F X = 1) (f g : Module.End F X) : f * g = g * f := by
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 h
  obtain ⟨a, ha⟩ := hv (f v)
  obtain ⟨b, hb⟩ := hv (g v)
  ext w
  obtain ⟨c, rfl⟩ := hv w
  have hf : ∀ x : F, f (x • v) = (x * a) • v := fun x => by
    rw [map_smul, ← ha, smul_smul]
  have hg : ∀ x : F, g (x • v) = (x * b) • v := fun x => by
    rw [map_smul, ← hb, smul_smul]
  simp only [Module.End.mul_apply, hf, hg, mul_assoc, mul_comm a b]

theorem not_isQuasisimple_of_comm {G : Type*} [Group G] (hc : ∀ x y : G, x * y = y * x) :
    ¬ CFSG.Open.IsQuasisimple G := by
  rintro ⟨-, hs⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (G ⧸ Subgroup.center G)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  apply hxy
  rw [QuotientGroup.eq]
  exact Subgroup.mem_center_iff.2 fun g => hc _ _

end TensorAux

open TensorAux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_tensorData [Nontrivial V] {L L₂ : Subgroup (GLV V)}
    (hcomm : ∀ x ∈ L, ∀ y ∈ L₂, x * y = y * x) (hirr : IsIrr (L ⊔ L₂) ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F)
      (V₀ V₁ : Type) (_ : AddCommGroup V₀) (_ : AddCommGroup V₁)
      (_ : Module F V₀) (_ : Module F V₁) (_ : Module.Finite F V₀) (_ : Module.Finite F V₁)
      (ρ₀ : ↥L →* (V₀ ≃ₗ[F] V₀)) (ρ₁ : ↥L₂ →* (V₁ ≃ₗ[F] V₁)) (e : V ≃+ V₀ ⊗[F] V₁),
      Nontrivial V₀ ∧ Nontrivial V₁ ∧
      (∀ (g : ↥L) (v : V), e ((g : GLV V) v) =
        TensorProduct.map (ρ₀ g : V₀ →ₗ[F] V₀) LinearMap.id (e v)) ∧
      (∀ (g : ↥L₂) (v : V), e ((g : GLV V) v) =
        TensorProduct.map LinearMap.id (ρ₁ g : V₁ →ₗ[F] V₁) (e v)) ∧
      Submodule.span F (Set.range fun g => ((ρ₀ g : V₀ ≃ₗ[F] V₀) : Module.End F V₀)) = ⊤ ∧
      Submodule.span F (Set.range fun g => ((ρ₁ g : V₁ ≃ₗ[F] V₁) : Module.End F V₁)) = ⊤ := by
  classical
  have hU : ∀ u : Multiplicative V, u ^ 2 = 1 := multiplicative_sq_eq_one
  have hcomm' : ∀ x ∈ toMulSub L, ∀ y ∈ toMulSub L₂, x * y = y * x := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    show linEquivMulAut g * linEquivMulAut h = linEquivMulAut h * linEquivMulAut g
    rw [← map_mul, ← map_mul, hcomm g hg h hh]
  have hirr' : ∀ J : Subgroup (Multiplicative V),
      (∀ g ∈ toMulSub L ⊔ toMulSub L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤ := by
    have := (IrreducibleModulesAndBounds.isIrrOn_toMulSub hirr).2
    rw [toMulSub_sup] at this
    exact this
  have : Nontrivial (Multiplicative V) := inferInstanceAs (Nontrivial V)
  obtain ⟨F, hF, hFin, hAlg, W, hWg, hWm, ρ, e, hnt, hfin, hact, hspan, -⟩ :=
    SmithD37.exists_tensor_decomp hU hcomm' hirr'
  have : ∀ i, Finite (W i) := hfin
  have : ∀ i, Module.Finite F (W i) := fun i => Module.Finite.of_finite
  let θ : V ≃+ Additive (Multiplicative V) :=
    { toFun := fun v => Additive.ofMul (Multiplicative.ofAdd v)
      invFun := fun u => Multiplicative.toAdd (Additive.toMul u)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine ⟨F, hF, hFin, hAlg, W 0, W 1, hWg 0, hWg 1, hWm 0, hWm 1, inferInstance, inferInstance,
    (ρ 0).comp (toMulSubEquiv L).toMonoidHom, (ρ 1).comp (toMulSubEquiv L₂).toMonoidHom,
    (θ.trans e).trans binEquiv.toAddEquiv, hnt 0, hnt 1, ?_, ?_, ?_, ?_⟩
  · intro g v
    have h := hact 0 (toMulSubEquiv L g) (Multiplicative.ofAdd v)
    exact (congrArg binEquiv h).trans (binEquiv_factorEnd_zero _ _)
  · intro g v
    have h := hact 1 (toMulSubEquiv L₂ g) (Multiplicative.ofAdd v)
    exact (congrArg binEquiv h).trans (binEquiv_factorEnd_one _ _)
  · rw [← hspan 0]
    congr 1
    exact (toMulSubEquiv L).surjective.range_comp
      (fun g => ((ρ 0 g : W 0 ≃ₗ[F] W 0) : Module.End F (W 0)))
  · rw [← hspan 1]
    congr 1
    exact (toMulSubEquiv L₂).surjective.range_comp
      (fun g => ((ρ 1 g : W 1 ≃ₗ[F] W 1) : Module.End F (W 1)))

theorem Setting.half_module {Γ A L L₂ : Subgroup (GLV V)} {m : ℕ}
    (h : Setting Γ A L L₂ m) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (L' : Subgroup (GLV W)), Nonempty (↥L ≃* ↥L') ∧
      2 * Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V := by
  classical
  have := h.nontrivial_V
  obtain ⟨F, hF, hFin, hAlg, V₀, V₁, hg0, hg1, hm0, hm1, hf0, hf1, ρ₀, ρ₁, e, hn0, hn1,
    hact0, hact1, -, -⟩ := exists_tensorData (L := L) (L₂ := L₂) h.comm h.hyp.H_irr
  have : Finite V₀ := Module.finite_of_finite F
  let _ : Module (ZMod 2) V₀ := Module.compHom V₀ (algebraMap (ZMod 2) F)
  have : IsScalarTower (ZMod 2) F V₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hinj0 : Function.Injective ρ₀ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine LinearEquiv.ext fun v => e.injective ?_
    have := hact0 g v
    rw [hg] at this
    simpa using this
  have hinj1 : Function.Injective ρ₁ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine LinearEquiv.ext fun v => e.injective ?_
    have := hact1 g v
    rw [hg] at this
    simpa using this
  let ρ' : ↥L →* GLV V₀ :=
    { toFun := fun g => (ρ₀ g).restrictScalars (ZMod 2)
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp }
  have hρ' : Function.Injective ρ' := fun a b hab =>
    hinj0 (LinearEquiv.ext fun v => congrArg (fun f : GLV V₀ => f v) hab)
  have hd1 : 2 ≤ Module.finrank F V₁ := by
    have hpos : 0 < Module.finrank F V₁ := Module.finrank_pos
    by_contra hlt
    have h1 : Module.finrank F V₁ = 1 := by omega
    refine not_isQuasisimple_of_comm (G := ↥L₂) (fun x y => hinj1 ?_) h.comp₂.2.2
    rw [map_mul, map_mul]
    refine LinearEquiv.ext fun w => ?_
    have := LinearMap.congr_fun (end_comm_of_finrank_one h1 (ρ₁ x : Module.End F V₁)
      (ρ₁ y : Module.End F V₁)) w
    simpa [Module.End.mul_apply] using this
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hV : Nat.card V = Nat.card F ^ (Module.finrank F V₀ * Module.finrank F V₁) := by
    rw [Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := F),
      Module.finrank_tensorProduct]
  have hV0 : Nat.card V₀ = Nat.card F ^ Module.finrank F V₀ :=
    Module.natCard_eq_pow_finrank (K := F)
  have hV2 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  have hV02 : Nat.card V₀ = 2 ^ Module.finrank (ZMod 2) V₀ := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V₀)
    rwa [Nat.card_zmod] at this
  refine ⟨V₀, hg0, inferInstance, inferInstance, ρ'.range, ⟨MonoidHom.ofInjective hρ'⟩, ?_⟩
  have hle : (2 ^ Module.finrank (ZMod 2) V₀) ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) V := by
    rw [← hV02, ← hV2, hV, hV0, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  rw [← pow_mul] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  omega

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
