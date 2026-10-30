module

public import CFSG.Quasithin.Background.SimsG45Sylow
public import CFSG.Quasithin.Background.SimsG48
public import CFSG.Quasithin.Background.SimsG44Nonsplit
public import CFSG.Quasithin.Background.SimsG41
public import CFSG.Quasithin.Background.SimsG49Main
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChG

open CFSG.Open

section Sp

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

structure IsSymp4 (B : LinearMap.BilinForm F V) : Prop where
  finrank_eq : Module.finrank F V = 4
  alt : ∀ x, B x x = 0
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0

@[expose] def spGroup (B : LinearMap.BilinForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  mul_mem' := fun {g h} hg hh x y => by
    change B (g (h x)) (g (h y)) = B x y
    rw [hg, hh]
  one_mem' := fun x y => rfl
  inv_mem' := fun {g} hg x y => by
    have := hg (g⁻¹ x) (g⁻¹ y)
    simpa using this.symm

@[expose] def IsSympBasis (B : LinearMap.BilinForm F V) (b : Module.Basis (Fin 4) F V) : Prop :=
  ∀ i j : Fin 4, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0

@[expose] def subfieldSpOf (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) :
    Set (V ≃ₗ[F] V) :=
  {g | ∀ i j, LinearMap.toMatrix b b (g : V →ₗ[F] V) i j ∈ F₀}

@[expose] def IsTransv (g : V ≃ₗ[F] V) : Prop :=
  Module.finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) = 1 ∧
    ((g : V →ₗ[F] V) - LinearMap.id) ∘ₗ ((g : V →ₗ[F] V) - LinearMap.id) = 0

@[expose] def commSpace (g : V ≃ₗ[F] V) : Submodule F V :=
  LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)

@[expose] def IsMaximalSymplecticParabolic (B : LinearMap.BilinForm F V)
    (Qhat : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∃ isotropicSpace : Submodule F V,
    (Module.finrank F isotropicSpace = 1 ∨ Module.finrank F isotropicSpace = 2) ∧
    (∀ vector ∈ isotropicSpace, ∀ other ∈ isotropicSpace, B vector other = 0) ∧
    ∀ automorphism : V ≃ₗ[F] V,
      automorphism ∈ Qhat ↔ automorphism ∈ spGroup B ∧
        isotropicSpace.map (automorphism : V →ₗ[F] V) = isotropicSpace

@[expose] def twoPrimeResidual (H : Type*) [Group H] : Subgroup H :=
  sInf {N : Subgroup H | N.Normal ∧ Odd N.index}

@[expose] def twoPrimeResidualOf {A : Type*} [Group A] (H : Subgroup A) : Subgroup A :=
  (twoPrimeResidual ↥H).map H.subtype

@[expose] def transvSet (G₀ : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V) :=
  {d | d ∈ G₀ ∧ IsTransv d}

@[expose] def transvGen (G₀ : Subgroup (V ≃ₗ[F] V)) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure (transvSet G₀)

@[expose] def transvFix (G₀ : Subgroup (V ≃ₗ[F] V)) (X : Submodule F V) :
    Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {d | d ∈ transvSet G₀ ∧ ∀ x ∈ X, d x = x}

@[expose] def IsIrredOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∀ W : Submodule F V, (∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def IsImprimitiveOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∃ (r : ℕ) (W : Fin r → Submodule F V), 1 < r ∧ (∀ i, W i ≠ ⊥) ∧ iSupIndep W ∧
    (⨆ i, W i) = ⊤ ∧ ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j

@[expose] def rootGroupHat (B : LinearMap.BilinForm F V) (d : V ≃ₗ[F] V) :
    Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {g | g ∈ spGroup B ∧ IsTransv g ∧ commSpace g = commSpace d}

@[expose] def xHat (B : LinearMap.BilinForm F V) (d : V ≃ₗ[F] V) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {e | e ∈ spGroup B ∧ IsTransv e ∧ e * d = d * e}

@[expose] def advSet (G₀ : Subgroup (V ≃ₗ[F] V)) (d : V ≃ₗ[F] V) : Set (V ≃ₗ[F] V) :=
  {e | e ∈ transvSet G₀ ∧ e * d ≠ d * e}

@[expose] def dSet (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V))
    (d : V ≃ₗ[F] V) : Set (V ≃ₗ[F] V) :=
  {e | e ∈ transvSet G₀ ∧ e * d = d * e ∧ e ∉ rootGroupHat B d}

@[expose] def advGraph (G₀ : Subgroup (V ≃ₗ[F] V)) : SimpleGraph ↥(transvSet G₀) :=
  SimpleGraph.fromRel fun a b => (a : V ≃ₗ[F] V) * b ≠ b * a

@[expose] def invSet (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Set (V ≃ₗ[F] V) :=
  {i | i ∈ transvGen G₀ ∧ i ≠ 1 ∧ i * i = 1 ∧ ∃ a ∈ transvSet G₀, ∃ b ∈ dSet B G₀ a, i = a * b}

@[expose] def IsNondegLine (B : LinearMap.BilinForm F V) (W : Submodule F V) : Prop :=
  Module.finrank F W = 2 ∧ ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0

@[expose] def IsTotSingLine (B : LinearMap.BilinForm F V) (W : Submodule F V) : Prop :=
  Module.finrank F W = 2 ∧ ∀ w ∈ W, ∀ w' ∈ W, B w w' = 0

end Sp

section Orth

variable (K : Type) [Field K]

@[expose] def isometryGroup (q : (Fin 4 → K) → K) : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) where
  carrier := {M | ∀ v, q ((M : Matrix (Fin 4) (Fin 4) K).mulVec v) = q v}
  mul_mem' := fun {M N} hM hN v => by
    have h1 := hM ((N : Matrix (Fin 4) (Fin 4) K).mulVec v)
    have h2 := hN v
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h1 ⊢
    rw [h1, h2]
  one_mem' := fun v => by simp
  inv_mem' := fun {M} hM v => by
    have h := hM (((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v)
    rw [Matrix.mulVec_mulVec] at h
    have h2 : ((M : Matrix (Fin 4) (Fin 4) K) *
        ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, Matrix.one_mulVec] at h
    exact h.symm

@[expose] def qPlus (v : Fin 4 → K) : K := v 0 * v 1 + v 2 * v 3

@[expose] def qMinus (c : K) (v : Fin 4 → K) : K :=
  v 0 * v 1 + v 2 ^ 2 + v 2 * v 3 + c * v 3 ^ 2

@[expose] def IsO4Type (k : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* isometryGroup (GaloisField 2 k) (qPlus (GaloisField 2 k))) ∨
    ∃ c : GaloisField 2 k, (¬ ∃ x : GaloisField 2 k, x ^ 2 + x + c = 0) ∧
      Nonempty (X ≃* isometryGroup (GaloisField 2 k) (qMinus (GaloisField 2 k) c))

@[expose] def orthAct {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 3 → F) : Fin 3 → F :=
  let M : Matrix (Fin 2) (Fin 2) F := !![v 0, v 1; v 1, v 2]
  let N : Matrix (Fin 2) (Fin 2) F :=
    (g : Matrix (Fin 2) (Fin 2) F) * M * (g : Matrix (Fin 2) (Fin 2) F).transpose
  ![N 0 0, N 0 1, N 1 1]

end Orth

section Cases

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def fStarOf {A : Type*} [Group A] (H : Subgroup A) : Subgroup A :=
  (CFSG.generalizedFitting ↥H).map H.subtype

structure HypG41 (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop where
  le_sp : G₀ ≤ spGroup B
  kgroup : CFSG.SectionRank.IsKGroupCat ↥G₀
  irred : IsIrredOnV G₀
  nonempty : (transvSet G₀).Nonempty

@[expose] def G41Factor (n : ℕ) (X : Subgroup (V ≃ₗ[F] V)) : Prop :=
  (∃ k : ℕ, k ∣ n ∧ Nonempty (↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∨
    ∃ m : ℕ, (m ∣ 2 ^ n + 1 ∨ m ∣ 2 ^ n - 1) ∧ Nonempty (↥X ≃* DihedralGroup m)

@[expose] def G41Case1 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) (k : ℕ),
      IsSympBasis B b ∧ 0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) ∧
      Nonempty (↥G₀ ≃* ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 k)))

@[expose] def G41Case2 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (Q : QuadraticForm F V) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) (k : ℕ),
      (∀ x y, QuadraticMap.polar Q x y = B x y) ∧ IsSympBasis B b ∧
      0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V,
        g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀ ∧ ∀ x, Q (g x) = Q x) ∧
      IsO4Type k ↥G₀

@[expose] def G41Case2AtExponent (n k : ℕ) (B : LinearMap.BilinForm F V)
    (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (Q : QuadraticForm F V) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F),
      (∀ x y, QuadraticMap.polar Q x y = B x y) ∧ IsSympBasis B b ∧
      0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V,
        g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀ ∧ ∀ x, Q (g x) = Q x) ∧
      IsO4Type k ↥G₀

@[expose] def G41Case3 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  ∃ V₁ V₂ : Submodule F V, IsNondegLine B V₁ ∧ V₂ = LinearMap.BilinForm.orthogonal B V₁ ∧
    IsCompl V₁ V₂ ∧
    (∀ g ∈ G₀, (V₁.map (g : V →ₗ[F] V) = V₁ ∧ V₂.map (g : V →ₗ[F] V) = V₂) ∨
      (V₁.map (g : V →ₗ[F] V) = V₂ ∧ V₂.map (g : V →ₗ[F] V) = V₁)) ∧
    (∃ t ∈ G₀, t * t = 1 ∧ V₁.map (t : V →ₗ[F] V) = V₂ ∧
      G₀ = transvGen G₀ ⊔ Subgroup.zpowers t) ∧
    (transvGen G₀ = transvFix G₀ V₂ ⊔ transvFix G₀ V₁ ∧
      transvFix G₀ V₂ ⊓ transvFix G₀ V₁ = ⊥ ∧
      ∀ a ∈ transvFix G₀ V₂, ∀ b ∈ transvFix G₀ V₁, a * b = b * a) ∧
    G41Factor n (transvFix G₀ V₂) ∧ G41Factor n (transvFix G₀ V₁)

end Cases

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChG

@[expose] def G_4_1 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        G41Case1 n B G₀ ∨ G41Case2 n B G₀ ∨ G41Case3 n B G₀

section as_G_4_1

theorem as_G_4_1 : G_4_1 := by
  intro F _ _ _ n hn V _ _ B hB G₀ hG
  exact CFSG.Quasithin.SimsG4.g41 n hn B hB.alt hB.nondeg hB.finrank_eq G₀ hG.le_sp hG.irred
    hG.nonempty

end as_G_4_1

@[expose] def G_4_3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        pCoreOf 2 G₀ = ⊥ ∧ pCoreOf 2 (transvGen G₀) = ⊥ ∧
          ∃ a ∈ transvGen G₀, ∃ b ∈ transvGen G₀, a * b ≠ b * a

private lemma g4_mul_inv_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : V ≃ₗ[F] V) (y : V) : g (g⁻¹ y) = y :=
  congrArg (fun e : V ≃ₗ[F] V => e y) (mul_inv_cancel g)

private lemma g4_inv_mul_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : V ≃ₗ[F] V) (y : V) : g⁻¹ (g y) = y :=
  congrArg (fun e : V ≃ₗ[F] V => e y) (inv_mul_cancel g)

private lemma g4_mem_transvSet {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {G₀ : Subgroup (V ≃ₗ[F] V)} {d : V ≃ₗ[F] V} :
    d ∈ transvSet G₀ ↔ d ∈ G₀ ∧ IsTransv d :=
  Iff.rfl

private lemma g4_transv_mul_self {F V : Type} [Field F] [CharP F 2] [AddCommGroup V]
    [Module F V] (g : V ≃ₗ[F] V) (hg : IsTransv g) : g * g = 1 := by
  obtain ⟨-, h2⟩ := hg
  have hvv : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  apply LinearEquiv.ext
  intro x
  have hx := LinearMap.congr_fun h2 x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply,
    LinearEquiv.coe_coe, map_sub] at hx
  have h3 : g (g x) + x = 0 := by
    calc g (g x) + x = (g (g x) - g x - (g x - x)) + (g x + g x) := by abel
      _ = 0 := by rw [hx, hvv (g x), add_zero]
  calc g (g x) = g (g x) + (x + x) := by rw [hvv x, add_zero]
    _ = (g (g x) + x) + x := by abel
    _ = x := by rw [h3, zero_add]

private lemma g4_transv_ne_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : V ≃ₗ[F] V) (hg : IsTransv g) : g ≠ 1 := by
  rintro rfl
  obtain ⟨h1, -⟩ := hg
  have h0 : ((1 : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id = 0 := by
    apply LinearMap.ext
    intro x
    simp
  rw [h0, LinearMap.range_zero, finrank_bot] at h1
  exact zero_ne_one h1

private lemma g4_isTransv_conj {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g d : V ≃ₗ[F] V) (hd : IsTransv d) : IsTransv (g * d * g⁻¹) := by
  obtain ⟨h1, h2⟩ := hd
  have hkey : ((g * d * g⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id
      = ((g : V →ₗ[F] V) ∘ₗ ((d : V →ₗ[F] V) - LinearMap.id)) ∘ₗ
          ((g⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_sub, g4_mul_inv_apply]
  refine ⟨?_, ?_⟩
  · rw [hkey, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range (g⁻¹ : V ≃ₗ[F] V)),
      LinearMap.range_comp, LinearEquiv.finrank_map_eq]
    exact h1
  · rw [hkey]
    apply LinearMap.ext
    intro x
    have hMM := LinearMap.congr_fun h2 ((g⁻¹ : V ≃ₗ[F] V) x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hMM
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe,
      g4_inv_mul_apply]
    rw [hMM, map_zero]

private lemma g4_core_trivial {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hirr : IsIrredOnV G₀) (heven : Even (Nat.card V))
    (P : Subgroup (V ≃ₗ[F] V)) (hP2 : IsPGroup 2 P)
    (hPG : ∀ g ∈ G₀, ∀ h ∈ P, g * h * g⁻¹ ∈ P) : P = ⊥ := by
  let W : Submodule F V :=
    { carrier := {v | ∀ h ∈ P, h v = v}
      add_mem' := by
        intro a b ha hb
        show ∀ h ∈ P, h (a + b) = a + b
        intro h hh
        have ha' : ∀ h ∈ P, h a = a := ha
        have hb' : ∀ h ∈ P, h b = b := hb
        rw [map_add, ha' h hh, hb' h hh]
      zero_mem' := by
        show ∀ h ∈ P, h 0 = 0
        intro h _
        exact map_zero h
      smul_mem' := by
        intro c v hv
        show ∀ h ∈ P, h (c • v) = c • v
        intro h hh
        have hv' : ∀ h ∈ P, h v = v := hv
        rw [map_smul, hv' h hh] }
  have hcount := IsPGroup.card_modEq_card_fixedPoints (α := V) hP2
  have hex : ∃ v : V, v ≠ 0 ∧ ∀ h ∈ P, h v = v := by
    by_contra hcon
    push Not at hcon
    have hfix : MulAction.fixedPoints ↥P V = {0} := by
      ext v
      rw [Set.mem_singleton_iff]
      constructor
      · intro hv
        by_contra hv0
        obtain ⟨h, hh, hne⟩ := hcon v hv0
        exact hne (MulAction.mem_fixedPoints.mp hv ⟨h, hh⟩)
      · rintro rfl
        exact MulAction.mem_fixedPoints.mpr fun m => map_zero (m : V ≃ₗ[F] V)
    rw [hfix] at hcount
    have h1 : Nat.card (↥({0} : Set V)) = 1 := by simp
    rw [h1] at hcount
    have h2 := Nat.even_iff.mp heven
    unfold Nat.ModEq at hcount
    omega
  obtain ⟨v, hv0, hvfix⟩ := hex
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hvW : v ∈ W := hvfix
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0 hvW
  have hWinv : ∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    have hw' : ∀ h ∈ P, h w = w := hw
    show ∀ h ∈ P, h (g w) = g w
    intro h hh
    have hc := hPG g⁻¹ (G₀.inv_mem hg) h hh
    rw [inv_inv] at hc
    have e1 : (g⁻¹ * h * g) w = w := hw' _ hc
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at e1
    calc h (g w) = g (g⁻¹ (h (g w))) := (g4_mul_inv_apply g _).symm
      _ = g w := by rw [e1]
  rcases hirr W hWinv with hbot | htop
  · exact absurd hbot hWne
  · rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    apply LinearEquiv.ext
    intro x
    have hx : x ∈ W := by rw [htop]; exact Submodule.mem_top
    have hx' : ∀ h ∈ P, h x = x := hx
    exact hx' h hh

private lemma g4_sq_eq_one_of_comm {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (S : Set (V ≃ₗ[F] V)) (hS : ∀ d ∈ S, d * d = 1)
    (hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) :
    ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hyx := hcomm x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hyx]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ihx =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := (mul_inv_rev x x).symm
      _ = 1 := by rw [ihx, inv_one]

theorem as_G_4_3 : G_4_3 := by
  intro F _ _ _ n hn V _ _ B hB G₀ hG
  obtain ⟨-, -, hirr, hne⟩ := hG
  obtain ⟨d₀, hd₀⟩ := hne
  have hfinV : Module.Finite F V :=
    Module.finite_of_finrank_pos (by rw [hB.finrank_eq]; norm_num)
  haveI : Finite V := Module.finite_of_finite (R := F) (M := V)
  have hn1 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hn, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hF2 : Even (Nat.card F) := by
    rw [hn]
    exact even_two.pow_of_ne_zero hn1
  have heven : Even (Nat.card V) := by
    rw [Module.natCard_eq_pow_finrank (K := F), hB.finrank_eq]
    exact hF2.pow_of_ne_zero (by norm_num)
  have hconjD : ∀ g ∈ G₀, ∀ d ∈ transvSet G₀, g * d * g⁻¹ ∈ transvSet G₀ := by
    intro g hg d hd
    exact g4_mem_transvSet.mpr
      ⟨G₀.mul_mem (G₀.mul_mem hg (g4_mem_transvSet.mp hd).1) (G₀.inv_mem hg),
        g4_isTransv_conj g d (g4_mem_transvSet.mp hd).2⟩
  have hGnormal : ∀ g ∈ G₀, ∀ x ∈ transvGen G₀, g * x * g⁻¹ ∈ transvGen G₀ := by
    intro g hg
    have hsub : transvSet G₀ ⊆
        ((transvGen G₀).comap (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[F] V)) :=
      fun d hd => Subgroup.subset_closure (hconjD g hg d hd)
    intro x hx
    exact ((Subgroup.closure_le _).mpr hsub) hx
  have hcl1 : pCoreOf 2 G₀ = ⊥ := by
    have hP2 : IsPGroup 2 (pCoreOf 2 G₀) :=
      IsPGroup.map (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥G₀)) G₀.subtype
    have hPG : ∀ g ∈ G₀, ∀ h ∈ pCoreOf 2 G₀, g * h * g⁻¹ ∈ pCoreOf 2 G₀ := by
      intro g hg h hh
      have hh' : h ∈ (CFSG.pCore 2 ↥G₀).map G₀.subtype := hh
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh'
      refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : ↥G₀) * k * (⟨g, hg⟩ : ↥G₀)⁻¹, ?_, rfl⟩
      exact (CFSG.pCore_normal (p := 2) (G := ↥G₀)).conj_mem k hk ⟨g, hg⟩
    exact g4_core_trivial G₀ hirr heven _ hP2 hPG
  have hcl2 : pCoreOf 2 (transvGen G₀) = ⊥ := by
    have hPG : ∀ g ∈ G₀, ∀ h ∈ (CFSG.pCore 2 ↥(transvGen G₀)).map (transvGen G₀).subtype,
        g * h * g⁻¹ ∈ (CFSG.pCore 2 ↥(transvGen G₀)).map (transvGen G₀).subtype := by
      intro g hg h hh
      have heqG : (transvGen G₀).map (MulAut.conj g).toMonoidHom = transvGen G₀ := by
        apply le_antisymm
        · exact Subgroup.map_le_iff_le_comap.mpr fun x hx => hGnormal g hg x hx
        · intro x hx
          refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g⁻¹⁻¹, hGnormal g⁻¹ (G₀.inv_mem hg) x hx, ?_⟩
          show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
          group
      let φ : ↥(transvGen G₀) ≃* ↥(transvGen G₀) :=
        (MulEquiv.subgroupMap (MulAut.conj g) (transvGen G₀)).trans
          (MulEquiv.subgroupCongr heqG)
      have hchar : (CFSG.pCore 2 ↥(transvGen G₀)).map φ.toMonoidHom =
          CFSG.pCore 2 ↥(transvGen G₀) :=
        CFSG.pCore_map_iso 2 φ
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh
      have hφk : φ k ∈ CFSG.pCore 2 ↥(transvGen G₀) := by
        rw [← hchar]
        exact Subgroup.mem_map_of_mem φ.toMonoidHom hk
      exact Subgroup.mem_map.mpr ⟨φ k, hφk, rfl⟩
    have hP2 : IsPGroup 2
        ((CFSG.pCore 2 ↥(transvGen G₀)).map (transvGen G₀).subtype) :=
      IsPGroup.map (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥(transvGen G₀)))
        (transvGen G₀).subtype
    exact g4_core_trivial G₀ hirr heven _ hP2 hPG
  refine ⟨hcl1, hcl2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsq := g4_sq_eq_one_of_comm (transvSet G₀)
    (fun d hd => g4_transv_mul_self d (g4_mem_transvSet.mp hd).2) hcon
  have hP2 : IsPGroup 2 (transvGen G₀) := fun x =>
    ⟨1, Subtype.ext (by simpa [pow_one, pow_two] using hsq x.1 x.2)⟩
  have hGbot := g4_core_trivial G₀ hirr heven (transvGen G₀) hP2 hGnormal
  have hd0 : d₀ ∈ transvGen G₀ := Subgroup.subset_closure hd₀
  rw [hGbot, Subgroup.mem_bot] at hd0
  exact g4_transv_ne_one d₀ (g4_mem_transvSet.mp hd₀).2 hd0

@[expose] def G_4_4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      (∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → ∀ d ∈ transvSet G₀, (advSet G₀ d).Nonempty) ∧
      ∀ d : V ≃ₗ[F] V, d ∈ spGroup B → IsTransv d →
        (∃ φ : ↥(xHat B d) →* Matrix.SpecialLinearGroup (Fin 2) F,
          Function.Surjective φ ∧ φ.ker = CFSG.pCore 2 ↥(xHat B d) ∧
          ∃ ψ : ↥(CFSG.pCore 2 ↥(xHat B d)) ≃* Multiplicative (Fin 3 → F),
            ∀ (g : ↥(xHat B d)) (x y : ↥(CFSG.pCore 2 ↥(xHat B d))),
              g * (x : ↥(xHat B d)) * g⁻¹ = (y : ↥(xHat B d)) →
                Multiplicative.toAdd (ψ y) = orthAct (φ g) (Multiplicative.toAdd (ψ x))) ∧
        Subgroup.center ↥(xHat B d) = (rootGroupHat B d).subgroupOf (xHat B d) ∧
        (1 < n → ∀ W : Subgroup ↥(xHat B d), W ≤ CFSG.pCore 2 ↥(xHat B d) → W.Normal →
          W ⊓ Subgroup.center ↥(xHat B d) = ⊥ →
          W ⊔ Subgroup.center ↥(xHat B d) ≠ CFSG.pCore 2 ↥(xHat B d)) ∧
        ∃ Qhat : Subgroup (V ≃ₗ[F] V), IsMaximalSymplecticParabolic B Qhat ∧
          xHat B d = twoPrimeResidualOf Qhat

theorem as_G_4_4 : G_4_4 := by
  intro F _ _ _ n hn V _ _ B hB
  refine ⟨fun G₀ hG d hd => ?_, fun d hd hdT => ?_⟩
  · exact CFSG.Quasithin.SimsG4.advSet_nonempty hB.finrank_eq G₀ hG.irred hd
  · obtain ⟨h1, h2, h3⟩ :=
      CFSG.Quasithin.SimsG4.g44_xHat B hB.alt hB.nondeg hB.finrank_eq d hd hdT
    exact ⟨h1, h2, CFSG.Quasithin.SimsG4.g44_nonsplit n hn B hB.alt hB.nondeg hB.finrank_eq d
      hd hdT, h3⟩

@[expose] def G_4_5 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        (∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀, orderOf (a * b) = 2 ∨ Odd (orderOf (a * b))) ∧
        (∀ a ∈ transvSet G₀, ∀ b ∈ advSet G₀ a, IsNondegLine B (commSpace a ⊔ commSpace b)) ∧
        ∀ a ∈ transvSet G₀, ∀ b ∈ dSet B G₀ a,
          IsTotSingLine B (commSpace a ⊔ commSpace b) ∧
            IsSylowTwoOf (Subgroup.centralizer ({a * b} : Set (V ≃ₗ[F] V)) ⊓ spGroup B) (spGroup B)

theorem as_G_4_5 : G_4_5 := by
  intro F _ _ _ n hn V _ _ B hB G₀ hG
  have halt : ∀ x, B x x = 0 := hB.alt
  have hnd : ∀ x, (∀ y, B x y = 0) → x = 0 := hB.nondeg
  have hform : ∀ a ∈ transvSet G₀, ∃ u : V, u ≠ 0 ∧ ∃ c : F, c ≠ 0 ∧
      (∀ v, a v = v + (c * B v u) • u) ∧ commSpace a = F ∙ u := fun a ha =>
    CFSG.Quasithin.SimsG45.exists_transv_form B halt hnd a (hG.le_sp ha.1) ha.2.1
  refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_, fun a ha b hb => ?_⟩
  ·
    obtain ⟨u, hu, c, hc, hau, -⟩ := hform a ha
    obtain ⟨w, -, d, hd, hbw, -⟩ := hform b hb
    by_cases huw : B u w = 0
    · have hcomm : a * b = b * a :=
        (CFSG.Quasithin.SimsG45.transv_commute_iff B halt hnd hu hc hd hau hbw).mpr huw
      have hsq : (a * b) ^ 2 = 1 := by
        rw [pow_two, mul_assoc, ← mul_assoc b a b, ← hcomm, mul_assoc a b b,
          CFSG.Quasithin.SimsG45.transv_mul_self B halt hbw, mul_one,
          CFSG.Quasithin.SimsG45.transv_mul_self B halt hau]
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h | h
      · exact Or.inr (by rw [h]; exact odd_one)
      · exact Or.inl h
    · exact Or.inr (CFSG.Quasithin.SimsG45.odd_orderOf_transv_mul B hB.finrank_eq halt hc hd
        hau hbw huw)
  ·
    obtain ⟨u, -, c, hc, hau, hsa⟩ := hform a ha
    obtain ⟨w, hw, d, hd, hbw, hsb⟩ := hform b hb.1
    have hwu : B w u ≠ 0 := fun h =>
      hb.2 ((CFSG.Quasithin.SimsG45.transv_commute_iff B halt hnd hw hd hc hbw hau).mpr h)
    rw [hsa, hsb, sup_comm]
    exact CFSG.Quasithin.SimsG45.nondegLine_sup B halt hw hwu
  ·
    obtain ⟨hbD, hcomm, hroot⟩ := hb
    obtain ⟨u, hu, c, hc, hau, hsa⟩ := hform a ha
    obtain ⟨w, hw, d, hd, hbw, hsb⟩ := hform b hbD
    have hwu : B w u = 0 :=
      (CFSG.Quasithin.SimsG45.transv_commute_iff B halt hnd hw hd hc hbw hau).mp hcomm
    have huw : B u w = 0 := by
      rw [CFSG.Quasithin.SimsG45.bilin_skew B halt u w, hwu, neg_zero]
    have hne : (F ∙ u) ≠ (F ∙ w) := fun h =>
      hroot (Subgroup.subset_closure ⟨hG.le_sp hbD.1, hbD.2, by rw [hsa, hsb, h]⟩)
    refine ⟨?_, ?_⟩
    · rw [hsa, hsb]
      exact CFSG.Quasithin.SimsG45.totSingLine_sup B halt hu hw hne huw
    · have hab : ∀ v, (a * b) v = v + (c * B v u) • u + (d * B v w) • w := by
        intro v
        rw [LinearEquiv.mul_apply, hau, hbw]
        simp only [LinearMap.map_add₂, LinearMap.map_smul₂, smul_eq_mul, hwu, mul_zero,
          add_zero]
        abel
      have hSp : spGroup B =
          CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B :=
        Subgroup.ext fun g =>
          (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff
            B g).symm
      have hmem : a * b ∈
          CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B :=
        hSp ▸ (spGroup B).mul_mem (hG.le_sp ha.1) (hG.le_sp hbD.1)
      obtain ⟨bas, hbas, β, hβ, he⟩ :=
        CFSG.Quasithin.SimsG45.exists_isoAntiSp_eq_uElt B halt hnd hB.finrank_eq hne hu hw huw
          hc hd (a * b) hmem hab
      rw [hSp]
      exact CFSG.Quasithin.SimsG45.isSylowTwoOf_centralizer_of_mulEquiv _
        (CFSG.Quasithin.SimsG45.isoAntiSp B bas hbas) hmem hβ one_ne_zero he

@[expose] def G_4_6 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        (¬ (advGraph G₀).Connected ↔
          ¬ ∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀, ∃ g ∈ transvGen G₀, g * a * g⁻¹ = b) ∧
        (¬ (advGraph G₀).Connected ↔ IsImprimitiveOnV G₀) ∧
        (¬ (advGraph G₀).Connected ↔ G41Case3 n B G₀)

section as_G_4_6

theorem as_G_4_6 : G_4_6 := by
  intro F _ _ _ n hn V _ _ B hB G₀ hG
  exact CFSG.Quasithin.SimsG4.g46 n hn B hB.alt hB.nondeg hB.finrank_eq G₀ hG.le_sp hG.irred
    hG.nonempty (as_G_4_5 F n hn V B hB G₀ hG).1

end as_G_4_6

@[expose] def G_4_7 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → (advGraph G₀).Connected →
        G₀ = transvGen G₀

section as_G_4_7

theorem as_G_4_7 : G_4_7 := by
  intro F _ _ _ n hn V _ _ B hB G₀ hG hconn
  exact CFSG.Quasithin.SimsG4.g47 n hn B hB.alt hB.nondeg hB.finrank_eq G₀ hG.le_sp hG.irred
    hG.nonempty hconn

end as_G_4_7

@[expose] def G_4_8 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → (advGraph G₀).Connected →
      ∀ a ∈ transvSet G₀, ∀ H : Subgroup (V ≃ₗ[F] V), H ≤ transvGen G₀ →
        a ∈ Subgroup.normalizer (H : Set (V ≃ₗ[F] V)) → IsIrredOnV H →
      ∀ I : AddSubgroup V, I ≠ ⊥ →
        (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x ∈ I, g x ∈ I) →
        (∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ y ∈ Y, g y ∈ Y) →
          Y = ⊥ ∨ Y = I) →
        ∃ F₀ : Subfield F,
          (∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I) ∧
          (∀ f : V →+ V, (∀ x ∈ I, f x ∈ I) →
            (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x ∈ I, f (g x) = g (f x)) →
            ∃ c ∈ F₀, ∀ x ∈ I, f x = c • x) ∧
          (∀ f : V →+ V, (∀ x ∈ I, f x ∈ I) → (∀ h ∈ H, ∀ x ∈ I, f (h x) = h (f x)) →
            ∃ c ∈ F₀, ∀ x ∈ I, f x = c • x) ∧
          (∀ Y : AddSubgroup V, Y ≤ I → (∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y) →
            (∀ c ∈ F₀, ∀ y ∈ Y, c • y ∈ Y) → Y = ⊥ ∨ Y = I) ∧
          (∃ β : LinearMap.BilinForm F₀ V,
            (∀ h ∈ H, ∀ x ∈ I, ∀ y ∈ I, β (h x) (h y) = β x y) ∧
            ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, β x y ≠ 0) ∧
          (Submodule.span F (I : Set V) = ⊤ ∧
            ∀ (ι : Type) [Fintype ι] (v : ι → V), (∀ i, v i ∈ I) →
              LinearIndependent F₀ v → LinearIndependent F v) ∧
          (∃ b : Module.Basis (Fin 4) F V, IsSympBasis B b ∧
            ∀ g ∈ H ⊔ Subgroup.zpowers a, g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) ∧
          (∀ B' : LinearMap.BilinForm F V, IsSymp4 B' →
            (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x y, B' (g x) (g y) = B' x y) →
            ∃ c : F, c ≠ 0 ∧ B' = c • B)

theorem as_G_4_8 : G_4_8 := by
  intro F _ _ _ n hn V _ _ B hB G₀ hG hconn a ha H hH haN hHirr I hI0 hIinv hImin
  have hHSp : H ≤ spGroup B :=
    hH.trans ((Subgroup.closure_le G₀).mpr (fun g hg => hg.1) |>.trans hG.le_sp)
  obtain ⟨F₀, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    CFSG.Quasithin.SimsG4.g48_descent B hB.alt hB.nondeg hB.finrank_eq a (hG.le_sp ha.1) ha.2
      H hHSp haN hHirr I hI0 hIinv hImin
  exact ⟨F₀, h1, h2, h3, h4, h5, h6, h7, fun B' hB' hinv => h8 B' hB'.alt hB'.nondeg hinv⟩

@[expose] def G_4_9 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → (advGraph G₀).Connected →
        (IsSimpleGroup ↥(fStarOf (transvGen G₀)) ∧
            (∃ x ∈ fStarOf (transvGen G₀), ∃ y ∈ fStarOf (transvGen G₀), x * y ≠ y * x) ∧
            (∃ i ∈ invSet B G₀, i ∈ fStarOf (transvGen G₀)) ∧
            IsIrredOnV (fStarOf (transvGen G₀))) ∨
          (∃ k : ℕ, 1 < k ∧ k ∣ n ∧
            Nonempty (↥(fStarOf (transvGen G₀)) ≃*
              (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) ×
                Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∧
            G41Case2AtExponent n k B G₀)

section as_G_4_9

theorem as_G_4_9 : G_4_9 := by
  intro F _ _ _ n hn V _ _ B hB G₀ hG hconn
  exact CFSG.Quasithin.SimsG4.g49 n hn B hB.alt hB.nondeg hB.finrank_eq G₀ hG.le_sp hG.irred
    hG.nonempty hconn

end as_G_4_9

end CFSG.ASVolI
