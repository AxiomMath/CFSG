module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProofSp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFree

public section

namespace CFSG.StandardType

namespace FieldFiveOm

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores LayerFacts ClNonsplit

theorem exists_not_mem_zpowers {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA5 : ∀ g ∈ A, g ^ 5 = 1) (h5 : 5 < Nat.card A) {u : G} (hu : u ∈ A) :
    ∃ v ∈ A, v ∉ Subgroup.zpowers u := by
  by_contra hall
  push Not at hall
  have h1 := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers u from fun d hd => hall d hd)
  rw [Nat.card_zpowers] at h1
  have h2 : orderOf u ≤ 5 := orderOf_le_of_pow_eq_one (by norm_num) (hA5 u hu)
  omega

theorem exists_ne_one {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA5 : ∀ g ∈ A, g ^ 5 = 1) (h5 : 5 < Nat.card A) : ∃ g ∈ A, g ≠ 1 := by
  obtain ⟨v, hvA, hv⟩ := exists_not_mem_zpowers hA5 h5 A.one_mem
  exact ⟨v, hvA, fun h1 => hv (by rw [h1]; exact Subgroup.one_mem _)⟩

section Adj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)

theorem exists_coreFamily_adjCent_fix {A : Subgroup (GL ι K)} (hAU : A ≤ unitaryOf hadj)
    (hAc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) (hA5 : ∀ g ∈ A, g ^ 5 = 1) (h5 : 5 < Nat.card A)
    (hsymd : ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + adj Y = 1) :
    ∃ (β : Type) (S : β → Subgroup (GL ι K)), IsCoreFamily (adjCent A hadj) S ∧
      ∀ c, ∃ T ∈ A, T ≠ 1 ∧ ∀ M ∈ S c,
        (M : Matrix ι ι K) * ((T : Matrix ι ι K) - 1) = (T : Matrix ι ι K) - 1 := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hAcard : (Nat.card A : K) ≠ 0 := FieldFiveSp.natCast_card_ne_zero_of_pow_five fun g =>
    Subtype.ext (by simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hA5 _ g.2)
  obtain ⟨r, E, e, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, hR, -, himg, -, hSle, hSn, hder,
    hq⟩ := exists_coreData hadj hAcard (fun X hX g hg => adj_mul_comm hadj (hAU hg) (hX g hg))
      hsymd
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hF : IsCoreFamily (adjCent A hadj)
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} =>
        (coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)) := by
    have h := (isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
    rwa [himg] at h
  refine ⟨_, _, hF, fun c => ?_⟩
  have hcoord : ∀ g ∈ A, ∃ a : (PiMat E e)ˣ, a ∈ unitaryOf hτ ∧
      Units.map Φ.toMonoidHom a = g ∧
        ∀ z : PiMat E e, z * (a : PiMat E e) = (a : PiMat E e) * z := by
    intro g hg
    have hgB : g ∈ adjCent A hadj :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => hAc h hh g hg, hAU hg⟩
    rw [← himg] at hgB
    obtain ⟨a, haU, hag⟩ := hgB
    refine ⟨a, haU, hag, fun z => hΦ ?_⟩
    have h1 := (hR (Φ z)).mp ⟨z, rfl⟩ g hg
    have hag' : (g : Matrix ι ι K) = Φ (a : PiMat E e) := by rw [← hag]; rfl
    rw [map_mul, map_mul, ← hag']
    exact h1
  have hscal5 : ∀ (u : (PiMat E e)ˣ) (γ : E c.1),
      (u : PiMat E e) c.1 = Matrix.scalar (Fin (e c.1)) γ → u ^ 5 = 1 → γ ^ 5 = 1 := by
    intro u γ hγ hu5
    have h1 := congrArg (fun v : (PiMat E e)ˣ => (v : PiMat E e) c.1) hu5
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, Units.val_one, Pi.one_apply] at h1
    rw [hγ, ← map_pow] at h1
    have i₀ : Fin (e c.1) := ⟨0, Nat.pos_of_ne_zero (NeZero.ne (e c.1))⟩
    have h2 := congrFun (congrFun h1 i₀) i₀
    simpa using h2
  obtain ⟨g₁, hg₁A, hg₁1⟩ := exists_ne_one hA5 h5
  obtain ⟨g₂, hg₂A, hg₂⟩ := exists_not_mem_zpowers hA5 h5 hg₁A
  obtain ⟨a₁, ha₁U, ha₁g, ha₁c⟩ := hcoord g₁ hg₁A
  obtain ⟨a₂, ha₂U, ha₂g, ha₂c⟩ := hcoord g₂ hg₂A
  obtain ⟨α, hα⟩ := exists_scalar_of_central ha₁c c.1
  obtain ⟨β, hβ⟩ := exists_scalar_of_central ha₂c c.1
  have ha₁5 : a₁ ^ 5 = 1 := hΦu (by rw [map_pow, ha₁g, hA5 g₁ hg₁A, map_one])
  have ha₂5 : a₂ ^ 5 = 1 := hΦu (by rw [map_pow, ha₂g, hA5 g₂ hg₂A, map_one])
  have hα5 := hscal5 a₁ α hα ha₁5
  have hβ5 := hscal5 a₂ β hβ ha₂5
  obtain ⟨T, hTA, hT1, w, hwU, hwT, hwc⟩ : ∃ T ∈ A, T ≠ 1 ∧ ∃ w : (PiMat E e)ˣ,
      w ∈ unitaryOf hτ ∧ Units.map Φ.toMonoidHom w = T ∧ (w : PiMat E e) c.1 = 1 := by
    by_cases hα1 : α = 1
    · exact ⟨g₁, hg₁A, hg₁1, a₁, ha₁U, ha₁g, by rw [hα, hα1, map_one]⟩
    · have hprim : IsPrimitiveRoot α 5 := (orderOf_eq_prime hα5 hα1) ▸ IsPrimitiveRoot.orderOf α
      obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hβ5
      refine ⟨g₂ * (g₁ ^ j)⁻¹, A.mul_mem hg₂A (A.inv_mem (A.pow_mem hg₁A j)), fun h => hg₂ ?_,
        a₂ * (a₁ ^ j)⁻¹, (unitaryOf hτ).mul_mem ha₂U ((unitaryOf hτ).inv_mem
          ((unitaryOf hτ).pow_mem ha₁U j)), by rw [map_mul, map_inv, map_pow, ha₁g, ha₂g], ?_⟩
      · rw [mul_inv_eq_one.mp h]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g₁) j
      · have h1 : ((a₁ ^ j : (PiMat E e)ˣ) : PiMat E e) c.1 = (a₂ : PiMat E e) c.1 := by
          rw [Units.val_pow_eq_pow_val, Pi.pow_apply, hα, hβ, ← map_pow, hj]
        rw [Units.val_mul, Pi.mul_apply, ← h1, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Pi.one_apply]
  refine ⟨T, hTA, hT1, fun M hM => ?_⟩
  have hfix := FieldFiveSp.fix_of_coord_eq_one (Φ := Φ) hτ hπ (Sf := Sf) hwU hwc
  rw [hwT] at hfix
  exact (hfix M hM).2

end Adj

section Orth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

theorem exists_coreFamily_orthFree_fix (hQ : (polarBilin Q).Nondegenerate)
    {A : Subgroup (W ≃ₗ[K] W)} (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hAc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) (hA5 : ∀ g ∈ A, g ^ 5 = 1) (h5 : 5 < Nat.card A)
    (hfree : ∀ w : W, (∀ a ∈ A, a w = w) → w = 0) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsCoreFamily (Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧
      ∀ c, ∃ T ∈ A, T ≠ 1 ∧ ∀ M ∈ S c, ∀ w : W, M (T w - w) = T w - w := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact FieldFiveSp.natCast_card_ne_zero_of_pow_five fun g =>
      Subtype.ext (by simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hA5 _ g.2)
  set b := Module.finBasis K W with hb
  set M := LinearMap.BilinForm.toMatrix b (polarBilin Q) with hM
  have hMt : Mᵀ = M := by
    ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      polar_comm]
  have hd : ∀ i, M i i = 0 := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hMd : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ)
  have hadj := isInvol_gramAdj hMd hMt
  have hU := mem_unitaryOf_gramAdj_iff b hM hMd hMt
  set A' := A.map (matEquiv b).toMonoidHom with hA'
  have hA'U : A' ≤ unitaryOf hadj := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hU a).mpr (polar_map_of_mem (hAO ha))
  have hA'card : Nat.card A' = Nat.card A := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ (matEquiv b).injective).toEquiv.symm]
  have hcard : (Nat.card A' : K) ≠ 0 := by
    rw [hA'card, Nat.card_eq_fintype_card]
    exact hA
  have hA'c : ∀ g ∈ A', ∀ h ∈ A', g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    show (matEquiv b) a * (matEquiv b) a' = (matEquiv b) a' * (matEquiv b) a
    rw [← map_mul, ← map_mul, hAc a ha a' ha']
  have hA'5 : ∀ g ∈ A', g ^ 5 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show (matEquiv b) a ^ 5 = 1
    rw [← map_pow, hA5 a ha, map_one]
  obtain ⟨Y₀, hY₀⟩ := exists_add_gramAdj_eq_one hMd hMt hd
  obtain ⟨Y, hYc, hY⟩ := exists_avg_add_eq_one hadj (gramAdj_smul M) hA'U hcard hY₀
  obtain ⟨β, S, hS, hST⟩ :=
    exists_coreFamily_adjCent_fix hadj hA'U hA'c hA'5 (hA'card ▸ h5) ⟨Y, hYc, hY⟩
  have h := hS.comap (matEquiv b).toMonoidHom (matEquiv b).injective fun g _ =>
    ⟨(matEquiv b).symm g, (matEquiv b).apply_symm_apply g⟩
  have hC : (adjCent A' hadj).comap (matEquiv b).toMonoidHom =
      Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hcent : (matEquiv b).toMonoidHom g ∈ Subgroup.centralizer (A' : Set (GL (Fin _) K)) ↔
        g ∈ Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) := by
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro h a ha
        exact (matEquiv b).injective (by
          rw [map_mul, map_mul]
          exact h _ ⟨a, ha, rfl⟩)
      · rintro h _ ⟨a, ha, rfl⟩
        show (matEquiv b) a * (matEquiv b) g = (matEquiv b) g * (matEquiv b) a
        rw [← map_mul, ← map_mul, h a ha]
    rw [hcent]
    constructor
    · rintro ⟨hgc, hgu⟩
      exact ⟨hgc, isometry_of_polar hAO hA hfree hgc ((hU g).mp hgu)⟩
    · rintro ⟨hgc, hgO⟩
      exact ⟨hgc, (hU g).mpr (polar_map_of_mem hgO)⟩
  rw [hC] at h
  refine ⟨β, _, h, fun c => ?_⟩
  obtain ⟨T', hT'A, hT'1, hT'M⟩ := hST c
  obtain ⟨T, hTA, rfl⟩ := hT'A
  refine ⟨T, hTA, fun h1 => hT'1 (by rw [h1]; exact map_one _), fun N hN w => ?_⟩
  have h2 := hT'M _ hN
  have h3 : LinearMap.toMatrix b b ((N : W →ₗ[K] W) ∘ₗ ((T : W →ₗ[K] W) - LinearMap.id)) =
      LinearMap.toMatrix b b ((T : W →ₗ[K] W) - LinearMap.id) := by
    rw [LinearMap.toMatrix_comp b b b, map_sub, LinearMap.toMatrix_id, ← coe_matEquiv,
      ← coe_matEquiv]
    exact h2
  have h4 := LinearMap.congr_fun ((LinearMap.toMatrix b b).injective h3) w
  simpa using h4

end Orth

end FieldFiveOm

end CFSG.StandardType
