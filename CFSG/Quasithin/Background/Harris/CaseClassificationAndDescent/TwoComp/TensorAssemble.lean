module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Defs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin.G11 CFSG.Assembly.LowTwoRank
open scoped TensorProduct Matrix


section Aux

variable {F : Type} [Field F] {V₀ V₁ : Type} [AddCommGroup V₀] [AddCommGroup V₁]
  [Module F V₀] [Module F V₁] {d : ℕ}

@[expose] noncomputable def tensorMatrixEquiv (b₀ : Module.Basis (Fin d) F V₀) (b₁ : Module.Basis (Fin d) F V₁) :
    V₀ ⊗[F] V₁ ≃ₗ[F] Matrix (Fin d) (Fin d) F :=
  (b₀.tensorProduct b₁).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite F F (Fin d × Fin d) ≪≫ₗ
    LinearEquiv.curry F F (Fin d) (Fin d)

theorem tensorMatrixEquiv_apply (b₀ : Module.Basis (Fin d) F V₀) (b₁ : Module.Basis (Fin d) F V₁)
    (x : V₀ ⊗[F] V₁) (i j : Fin d) :
    tensorMatrixEquiv b₀ b₁ x i j = (b₀.tensorProduct b₁).repr x (i, j) := rfl

theorem tensorMatrixEquiv_map_left (b₀ : Module.Basis (Fin d) F V₀) (b₁ : Module.Basis (Fin d) F V₁)
    (f : V₀ →ₗ[F] V₀) (x : V₀ ⊗[F] V₁) :
    tensorMatrixEquiv b₀ b₁ (TensorProduct.map f LinearMap.id x) =
      LinearMap.toMatrix b₀ b₀ f * tensorMatrixEquiv b₀ b₁ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy, Matrix.mul_add]
  | tmul m n =>
    ext i j
    have h : b₀.repr (f m) i = ∑ k, LinearMap.toMatrix b₀ b₀ f i k * b₀.repr m k := by
      rw [← LinearMap.toMatrix_mulVec_repr b₀ b₀ f m]
      rfl
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorMatrixEquiv_apply,
      Module.Basis.tensorProduct_repr_tmul_apply, Matrix.mul_apply, h, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem tensorMatrixEquiv_map_right (b₀ : Module.Basis (Fin d) F V₀) (b₁ : Module.Basis (Fin d) F V₁)
    (f : V₁ →ₗ[F] V₁) (x : V₀ ⊗[F] V₁) :
    tensorMatrixEquiv b₀ b₁ (TensorProduct.map LinearMap.id f x) =
      tensorMatrixEquiv b₀ b₁ x * (LinearMap.toMatrix b₁ b₁ f)ᵀ := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy, Matrix.add_mul]
  | tmul m n =>
    ext i j
    have h : b₁.repr (f n) j = ∑ k, LinearMap.toMatrix b₁ b₁ f j k * b₁.repr n k := by
      rw [← LinearMap.toMatrix_mulVec_repr b₁ b₁ f n]
      rfl
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorMatrixEquiv_apply,
      Module.Basis.tensorProduct_repr_tmul_apply, Matrix.mul_apply, Matrix.transpose_apply, h,
      smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

@[expose] noncomputable def basisGL (b : Module.Basis (Fin d) F V₀) : (V₀ ≃ₗ[F] V₀) →* GL (Fin d) F where
  toFun g := ⟨LinearMap.toMatrix b b (g : V₀ →ₗ[F] V₀), LinearMap.toMatrix b b (g.symm : V₀ →ₗ[F] V₀),
    by
      rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one b]
      congr 1; ext x; simp,
    by
      rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one b]
      congr 1; ext x; simp⟩
  map_one' := by ext1; simp
  map_mul' g h := by
    ext1
    simp [← LinearMap.toMatrix_mul]

theorem coe_basisGL (b : Module.Basis (Fin d) F V₀) (g : V₀ ≃ₗ[F] V₀) :
    ((basisGL b g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      LinearMap.toMatrix b b (g : V₀ →ₗ[F] V₀) := by simp [basisGL]

theorem basisGL_injective (b : Module.Basis (Fin d) F V₀) :
    Function.Injective (basisGL b) := by
  intro g h hgh
  have := congrArg (fun u : GL (Fin d) F => (u : Matrix (Fin d) (Fin d) F)) hgh
  simp only [coe_basisGL] at this
  exact LinearEquiv.ext fun x => by
    have := (LinearMap.toMatrix b b).injective this
    exact LinearMap.congr_fun this x

theorem det_eq_one_of_perfect {G : Type} [Group G] [Group.IsPerfect G]
    (f : G →* GL (Fin d) F) (g : G) :
    ((f g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 := by
  have h : (Matrix.GeneralLinearGroup.det.comp f) g = 1 := by
    have := Group.IsPerfect.range (Matrix.GeneralLinearGroup.det.comp f)
    have hs : Subsingleton (Matrix.GeneralLinearGroup.det.comp f).range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    exact congrArg Subtype.val (hs.elim ⟨_, g, rfl⟩ 1)
  have h2 := congrArg Units.val h
  simpa using h2

end Aux

theorem isTensorModel_of_tensorData {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {L L₂ : Subgroup (GLV V)} (hcomm : ∀ x ∈ L, ∀ y ∈ L₂, x * y = y * x) (hinf : L ⊓ L₂ = ⊥)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {V₀ V₁ : Type} [AddCommGroup V₀] [AddCommGroup V₁] [Module F V₀] [Module F V₁]
    [Module.Finite F V₀] [Module.Finite F V₁]
    (ρ₀ : ↥L →* (V₀ ≃ₗ[F] V₀)) (ρ₁ : ↥L₂ →* (V₁ ≃ₗ[F] V₁)) (e : V ≃+ V₀ ⊗[F] V₁)
    (he₀ : ∀ (g : ↥L) (v : V), e ((g : GLV V) v) =
      TensorProduct.map (ρ₀ g : V₀ →ₗ[F] V₀) LinearMap.id (e v))
    (he₁ : ∀ (g : ↥L₂) (v : V), e ((g : GLV V) v) =
      TensorProduct.map LinearMap.id (ρ₁ g : V₁ →ₗ[F] V₁) (e v))
    {d : ℕ} (hd₀ : Module.finrank F V₀ = d) (hd₁ : Module.finrank F V₁ = d)
    (hL : Group.IsPerfect ↥L) (hL₂ : Group.IsPerfect ↥L₂)
    (hcL : Nat.card ↥L = Nat.card ↥(StatedSL d F)) (hcL₂ : Nat.card ↥L₂ = Nat.card ↥(StatedSL d F))
    (hinj₀ : Function.Injective ρ₀) (hinj₁ : Function.Injective ρ₁) :
    IsTensorModel d F (L ⊔ L₂) := by
  let b₀ : Module.Basis (Fin d) F V₀ := Module.finBasisOfFinrankEq F V₀ hd₀
  let b₁ : Module.Basis (Fin d) F V₁ := Module.finBasisOfFinrankEq F V₁ hd₁
  let R₀ : ↥L →* StatedSL d F := ((basisGL b₀).comp ρ₀).codRestrict (StatedSL d F)
    (fun g => Subgroup.subset_closure (det_eq_one_of_perfect ((basisGL b₀).comp ρ₀) g))
  let R₁ : ↥L₂ →* StatedSL d F := ((basisGL b₁).comp ρ₁).codRestrict (StatedSL d F)
    (fun g => Subgroup.subset_closure (det_eq_one_of_perfect ((basisGL b₁).comp ρ₁) g))
  have hR₀ : ∀ g, ((R₀ g : StatedSL d F) : GL (Fin d) F) = basisGL b₀ (ρ₀ g) := fun g => rfl
  have hR₁ : ∀ g, ((R₁ g : StatedSL d F) : GL (Fin d) F) = basisGL b₁ (ρ₁ g) := fun g => rfl
  have hRi₀ : Function.Injective R₀ := fun a c h =>
    hinj₀ (basisGL_injective b₀ (by simpa [hR₀] using congrArg Subtype.val h))
  have hRi₁ : Function.Injective R₁ := fun a c h =>
    hinj₁ (basisGL_injective b₁ (by simpa [hR₁] using congrArg Subtype.val h))
  have hRb₀ : Function.Bijective R₀ := hRi₀.bijective_of_nat_card_le hcL.symm.le
  have hRb₁ : Function.Bijective R₁ := hRi₁.bijective_of_nat_card_le hcL₂.symm.le
  let P : ↥L × ↥L₂ →* GLV V :=
    L.subtype.noncommCoprod L₂.subtype (fun a b => hcomm a a.2 b b.2)
  have hrange : P.range = L ⊔ L₂ := by
    refine (MonoidHom.noncommCoprod_range L.subtype L₂.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  let Ψ : ↥L × ↥L₂ →* ↥(L ⊔ L₂) := P.codRestrict (L ⊔ L₂) (fun x => by
    rw [← hrange]; exact ⟨x, rfl⟩)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · have hPi : Function.Injective P := by
        refine (MonoidHom.noncommCoprod_injective L.subtype L₂.subtype _).2
          ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
        rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
        exact hinf
      intro x y h
      exact hPi (congrArg Subtype.val h)
    · intro γ
      have : (γ : GLV V) ∈ P.range := by rw [hrange]; exact γ.2
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩
  let A : V ≃+ Matrix (Fin d) (Fin d) F := e.trans (tensorMatrixEquiv b₀ b₁).toAddEquiv
  let ψ : V ≃ₗ[ZMod 2] Matrix (Fin d) (Fin d) F :=
    { toLinearMap := A.toAddMonoidHom.toZModLinearMap 2
      invFun := A.symm
      left_inv := A.left_inv
      right_inv := A.right_inv }
  refine ⟨(MulEquiv.ofBijective Ψ hΨ).symm.trans
    (MulEquiv.prodCongr (MulEquiv.ofBijective R₀ hRb₀) (MulEquiv.ofBijective R₁ hRb₁)), ψ, ?_⟩
  intro γ v
  obtain ⟨⟨a, b⟩, hab⟩ := hΨ.2 γ
  have hγ : (γ : GLV V) = (a : GLV V) * (b : GLV V) := by
    rw [← hab]; rfl
  have hφ : ((MulEquiv.ofBijective Ψ hΨ).symm.trans
    (MulEquiv.prodCongr (MulEquiv.ofBijective R₀ hRb₀) (MulEquiv.ofBijective R₁ hRb₁))) γ =
      (R₀ a, R₁ b) := by
    have h : γ = (MulEquiv.ofBijective Ψ hΨ) (a, b) := hab.symm
    rw [h, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hψ : ∀ x, ψ x = tensorMatrixEquiv b₀ b₁ (e x) := fun x => rfl
  rw [hφ, hγ, hψ, hψ]
  show _ = ((R₀ a : StatedSL d F) : GL (Fin d) F).val * _ * (((R₁ b : StatedSL d F) : GL (Fin d) F).val)ᵀ
  rw [hR₀, hR₁, coe_basisGL, coe_basisGL]
  rw [LinearEquiv.mul_apply, he₀, tensorMatrixEquiv_map_left, he₁, tensorMatrixEquiv_map_right]
  simp [Matrix.mul_assoc]

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
