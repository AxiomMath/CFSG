module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGKGLayerTransport

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.LayerSixE
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggRFix_map_eq {L' R S : Type} [Group L'] [Group R] [Group S]
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (Θ : R →* S) (hΘ : Function.Injective Θ)
    (F : Set (MulAut L')) (D : Set S)
    (hFD : ∀ f ∈ F, ∃ d ∈ D, ∀ l : L', Θ (ψ (f l)) = d * Θ (ψ l) * d⁻¹)
    (hDF : ∀ d ∈ D, ∃ f ∈ F, ∀ l : L', Θ (ψ (f l)) = d * Θ (ψ l) * d⁻¹) :
    ∀ y : S, y ∈ (ggRFix ψ F).map Θ ↔ y ∈ Θ.range ∧ ∀ d ∈ D, d * y * d⁻¹ = y := by
  intro y
  constructor
  · intro hy
    obtain ⟨r, hr, rfl⟩ := hy
    obtain ⟨l, rfl, hfix⟩ := hr
    refine ⟨⟨ψ l, rfl⟩, fun d hd => ?_⟩
    obtain ⟨f, hf, hfl⟩ := hDF d hd
    rw [← hfl, hfix f hf]
  · rintro ⟨hrange_mem, hcomm⟩
    obtain ⟨r, rfl⟩ := hrange_mem
    obtain ⟨l, rfl⟩ := hψ r
    refine ⟨ψ l, ⟨l, rfl, fun f hf => hΘ ?_⟩, rfl⟩
    obtain ⟨d, hd, hdl⟩ := hFD f hf
    rw [hdl, hcomm d hd]

private theorem ggRFix_map_eq_famCentralizer {K : Type} [Field K] {L' : Type} [Group L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (hψ : Function.Surjective ψ)
    (Θ : RecipeGroup Tag.E6 K →* ModGL Tag.E6 K) (hΘ : Function.Injective Θ)
    (hrange : Θ.range = adjointGroup Tag.E6 K)
    (F : Set (MulAut L')) (F' : Set (Fin Tag.E6.rank → Kˣ))
    (hFD : ∀ f ∈ F, ∃ a ∈ F', ∀ l : L',
      Θ (ψ (f l)) = rootDiagUnit Tag.E6 a * Θ (ψ l) * (rootDiagUnit Tag.E6 a)⁻¹)
    (hDF : ∀ a ∈ F', ∃ f ∈ F, ∀ l : L',
      Θ (ψ (f l)) = rootDiagUnit Tag.E6 a * Θ (ψ l) * (rootDiagUnit Tag.E6 a)⁻¹) :
    (ggRFix ψ F).map Θ = (famCentralizer F').map (adjointGroup Tag.E6 K).subtype := by
  have hmem : ∀ y : ModGL Tag.E6 K,
      y ∈ (famCentralizer F').map (adjointGroup Tag.E6 K).subtype ↔
        y ∈ adjointGroup Tag.E6 K ∧
          ∀ a ∈ F', rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹ = y := by
    intro y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [mem_famCentralizer] at hg
      exact ⟨g.2, hg⟩
    · rintro ⟨hy, hfix⟩
      exact ⟨⟨y, hy⟩, by rw [mem_famCentralizer]; exact hfix, rfl⟩
  have hFD' : ∀ f ∈ F, ∃ d ∈ rootDiagUnit Tag.E6 '' F', ∀ l : L',
      Θ (ψ (f l)) = d * Θ (ψ l) * d⁻¹ := by
    rintro f hf
    obtain ⟨a, ha, h⟩ := hFD f hf
    exact ⟨rootDiagUnit Tag.E6 a, ⟨a, ha, rfl⟩, h⟩
  have hDF' : ∀ d ∈ rootDiagUnit Tag.E6 '' F', ∃ f ∈ F, ∀ l : L',
      Θ (ψ (f l)) = d * Θ (ψ l) * d⁻¹ := by
    rintro d ⟨a, ha, rfl⟩
    obtain ⟨f, hf, h⟩ := hDF a ha
    exact ⟨f, hf, h⟩
  ext y
  rw [ggRFix_map_eq ψ hψ Θ hΘ F (rootDiagUnit Tag.E6 '' F') hFD' hDF' y, hrange, hmem y]
  constructor
  · rintro ⟨hy, hc⟩
    exact ⟨hy, fun a ha => hc _ ⟨a, ha, rfl⟩⟩
  · rintro ⟨hy, hc⟩
    exact ⟨hy, fun d hd => by obtain ⟨a, ha, rfl⟩ := hd; exact hc a ha⟩

theorem layer_of_famCentralizer {K : Type} [Field K] {L' : Type} [Group L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (hψ : Function.Surjective ψ)
    (Θ : RecipeGroup Tag.E6 K →* ModGL Tag.E6 K) (hΘ : Function.Injective Θ)
    (hrange : Θ.range = adjointGroup Tag.E6 K)
    (F : Set (MulAut L')) (F' : Set (Fin Tag.E6.rank → Kˣ))
    (hFD : ∀ f ∈ F, ∃ a ∈ F', ∀ l : L',
      Θ (ψ (f l)) = rootDiagUnit Tag.E6 a * Θ (ψ l) * (rootDiagUnit Tag.E6 a)⁻¹)
    (hDF : ∀ a ∈ F', ∃ f ∈ F, ∀ l : L',
      Θ (ψ (f l)) = rootDiagUnit Tag.E6 a * Θ (ψ l) * (rootDiagUnit Tag.E6 a)⁻¹)
    {L : Subgroup (ModGL Tag.E6 K)}
    (h : GGLayerOf ((famCentralizer F').map (adjointGroup Tag.E6 K).subtype) L) :
    GGLayerOf (ggRFix ψ F) (L.comap Θ) := by
  rw [← ggRFix_map_eq_famCentralizer ψ hψ Θ hΘ hrange F F' hFD hDF] at h
  exact ggLayerOf_comap Θ hΘ h

private theorem kgMap_conj_eq {M N : Type} [Group M] [Group N] (φ : M →* N) (x y : M) :
    φ (MulAut.conj x y) = MulAut.conj (φ x) (φ y) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]


@[expose] noncomputable def kgThetaHom {K : Type} [Field K] [Finite K] (g : ModGL Tag.E6 K) :
    RecipeGroup Tag.E6 K →* ModGL Tag.E6 K :=
  (MulAut.conj g⁻¹).toMonoidHom.comp
    ((adjointGroup Tag.E6 K).subtype.comp (recipeEquiv Tag.E6 K).toMonoidHom)

private theorem kgThetaHom_apply {K : Type} [Field K] [Finite K] (g : ModGL Tag.E6 K)
    (r : RecipeGroup Tag.E6 K) :
    kgThetaHom g r =
      g⁻¹ * ((recipeEquiv Tag.E6 K r : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * g := by
  simp [kgThetaHom, MulAut.conj_apply]

theorem kgThetaHom_injective {K : Type} [Field K] [Finite K] (g : ModGL Tag.E6 K) :
    Function.Injective (kgThetaHom g) := by
  intro r s h
  have h1 : ((recipeEquiv Tag.E6 K r : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      ((recipeEquiv Tag.E6 K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) := by
    rw [kgThetaHom_apply, kgThetaHom_apply] at h
    exact mul_left_cancel (mul_right_cancel h)
  exact (recipeEquiv Tag.E6 K).injective (Subtype.ext h1)

theorem kgThetaHom_range {K : Type} [Field K] [Finite K] (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) : (kgThetaHom g).range = adjointGroup Tag.E6 K := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    rw [kgThetaHom_apply]
    exact mul_mem (mul_mem (inv_mem hg) ((recipeEquiv Tag.E6 K r : adjointGroup Tag.E6 K)).2) hg
  · intro hy
    refine ⟨(recipeEquiv Tag.E6 K).symm ⟨g * y * g⁻¹, mul_mem (mul_mem hg hy) (inv_mem hg)⟩, ?_⟩
    rw [kgThetaHom_apply, MulEquiv.apply_symm_apply]
    group

theorem kgThetaHom_conj {K : Type} [Field K] [Finite K] (g : ModGL Tag.E6 K)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} (ψ : L' →* RecipeGroup Tag.E6 K)
    (D : A → ModGL Tag.E6 K)
    (hconj : ∀ (a : A) (l : L'),
      ((recipeEquiv Tag.E6 K (ψ ((a : MulAut L') l)) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        (g * D a * g⁻¹) * ((recipeEquiv Tag.E6 K (ψ l) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
          (g * D a * g⁻¹)⁻¹) :
    ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) = D a * kgThetaHom g (ψ l) * (D a)⁻¹ := by
  intro a l
  rw [kgThetaHom_apply, kgThetaHom_apply, hconj a l]
  group

abbrev kgZetaE6 {K : Type} [Field K] (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → Kˣ :=
  zetaVec (τ := Tag.E6) ζ hζ x

theorem kgZetaE6_add {K : Type} [Field K] (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x y : Fin Tag.E6.rank → ZMod 3) :
    kgZetaE6 ζ hζ (x + y) = kgZetaE6 ζ hζ x * kgZetaE6 ζ hζ y := by
  funext i
  simp only [kgZetaE6, zetaVec, Pi.add_apply, Pi.mul_apply, ofAdd_add, map_mul]

abbrev kgKernelE6 {K : Type} [Field K] (F : Set (Fin Tag.E6.rank → Kˣ)) :
    Set (Fin Tag.E6.rank → ℤ) :=
  famKernel (τ := Tag.E6) F

theorem kgKappa_toAdd_mul {K : Type} [Field K]
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (a b : A) :
    (Multiplicative.toAdd (κ (a * b)) : Fin Tag.E6.rank → ZMod 3) =
      (Multiplicative.toAdd (κ a) + Multiplicative.toAdd (κ b) : Fin Tag.E6.rank → ZMod 3) := by
  have h : Multiplicative.toAdd (κ (a * b)) =
      Multiplicative.toAdd (κ a) + Multiplicative.toAdd (κ b) := by
    rw [map_mul, toAdd_mul]
  exact h

theorem kgZetaE6_zero {K : Type} [Field K] (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    kgZetaE6 ζ hζ 0 = 1 := by
  funext i
  simp [kgZetaE6, zetaVec]

theorem kgZetaE6_neg {K : Type} [Field K] (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) :
    kgZetaE6 ζ hζ (-x) = (kgZetaE6 ζ hζ x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← kgZetaE6_add, neg_add_cancel, kgZetaE6_zero]

theorem kgThetaHom_conj_apply {K : Type} [Field K] [Finite K] (g : ModGL Tag.E6 K)
    {L' : Type} [Group L'] (ψ : L' →* RecipeGroup Tag.E6 K) (l x : L')
    {d : ModGL Tag.E6 K} (hd : kgThetaHom g (ψ l) = d) :
    kgThetaHom g (ψ (MulAut.conj l x)) = d * kgThetaHom g (ψ x) * d⁻¹ := by
  rw [kgMap_conj_eq ψ l x, kgMap_conj_eq (kgThetaHom g) (ψ l) (ψ x), hd, MulAut.conj_apply]

theorem kgThetaHom_conjAut_apply {K : Type} [Field K] [Finite K] (g : ModGL Tag.E6 K)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} (ψ : L' →* RecipeGroup Tag.E6 K)
    (D : A → ModGL Tag.E6 K)
    (hconj : ∀ (a : A) (w : L'), kgThetaHom g (ψ ((a : MulAut L') w)) =
      D a * kgThetaHom g (ψ w) * (D a)⁻¹)
    (l : L') (a : A) (z : L') {Dl : ModGL Tag.E6 K} (hdl : kgThetaHom g (ψ l) = Dl) :
    kgThetaHom g (ψ ((MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹) z)) =
      (Dl * D a * Dl⁻¹) * kgThetaHom g (ψ z) * (Dl * D a * Dl⁻¹)⁻¹ := by
  have harg : (MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹) z =
      MulAut.conj l ((a : MulAut L') ((MulAut.conj l)⁻¹ z)) := by
    rw [MulAut.mul_apply, MulAut.mul_apply]
  have hdl' : kgThetaHom g (ψ l⁻¹) = Dl⁻¹ := by simp only [map_inv, hdl]
  have hinv : (MulAut.conj l)⁻¹ = MulAut.conj l⁻¹ := by
    ext y
    rw [MulAut.conj_inv_apply, MulAut.conj_apply, inv_inv]
  have hw : kgThetaHom g (ψ ((MulAut.conj l)⁻¹ z)) = Dl⁻¹ * kgThetaHom g (ψ z) * Dl := by
    rw [hinv]
    simpa using kgThetaHom_conj_apply g ψ l⁻¹ z hdl'
  rw [harg, kgMap_conj_eq ψ l _, kgMap_conj_eq (kgThetaHom g) (ψ l) _, MulAut.conj_apply]
  rw [hconj a ((MulAut.conj l)⁻¹ z), hdl, hw]
  group

end CFSG.StandardType.KGL

end
