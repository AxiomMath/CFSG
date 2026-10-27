module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFieldRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldFix
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaLang
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaOrder

public section

namespace CFSG.StandardType

namespace OrdPFieldNsOm

open QuadraticMap Module OrdPNsOm SUTB NoOffOm OrdPNsGen
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
open scoped Matrix

section Transfer

variable {K : Type} [Field K] {d : ℕ}

omit [Field K] in
theorem glFieldAut_eq_map [Field K] (σ : K ≃+* K) (g : GL (Fin d) K) :
    glFieldAut (Fin d) K σ g = Matrix.GeneralLinearGroup.map (σ : K →+* K) g :=
  Units.ext rfl

theorem mem_isometries_comp_iff {Q : QuadraticForm K (Fin d → K)} (H B : GL (Fin d) K) :
    B ∈ matrixIsometries (Q.comp (Matrix.toLin' H.val)) ↔ H * B * H⁻¹ ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff, mem_matrixIsometries_iff]
  have hHH : ∀ v : Fin d → K, H.val *ᵥ ((H⁻¹ : GL (Fin d) K).val *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro h v
    have h1 := h ((H⁻¹ : GL (Fin d) K).val *ᵥ v)
    simp only [QuadraticMap.comp_apply, Matrix.toLin'_apply, matrixLinearEquiv_apply] at h1
    rw [matrixLinearEquiv_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, h1, hHH]
  · intro h v
    have h1 := h (H.val *ᵥ v)
    have e : (H⁻¹ : GL (Fin d) K).val *ᵥ (H.val *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    simp only [QuadraticMap.comp_apply, Matrix.toLin'_apply, matrixLinearEquiv_apply]
    rw [matrixLinearEquiv_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, e] at h1
    exact h1

variable {K₀ : Subfield K}

theorem inclVec_mulVec (g₀ : GL (Fin d) K₀) (w : Fin d → K₀) :
    RecipeFieldOmega.inclVec K₀ (g₀.val *ᵥ w) =
      (Matrix.GeneralLinearGroup.map K₀.subtype g₀).val *ᵥ RecipeFieldOmega.inclVec K₀ w := by
  funext i
  exact RingHom.map_mulVec K₀.subtype g₀.val w i

theorem mem_isometries_descForm_iff {Q' : QuadraticForm K (Fin d → K)}
    (hQ' : ∀ w : Fin d → K₀, Q' (RecipeFieldOmega.inclVec K₀ w) ∈ K₀) (g₀ : GL (Fin d) K₀) :
    g₀ ∈ matrixIsometries (RecipeFieldOmega.descForm Q' hQ') ↔
      Matrix.GeneralLinearGroup.map K₀.subtype g₀ ∈ matrixIsometries Q' := by
  rw [mem_matrixIsometries_iff, mem_matrixIsometries_iff]
  constructor
  · intro h
    have hQ : Q'.comp (Matrix.toLin' (Matrix.GeneralLinearGroup.map K₀.subtype g₀).val) = Q' :=
      RecipeFieldOmega.eq_of_forall_inclVec K₀ fun w => by
        rw [QuadraticMap.comp_apply, Matrix.toLin'_apply, ← inclVec_mulVec,
          ← RecipeFieldOmega.descForm_apply Q' hQ', ← RecipeFieldOmega.descForm_apply Q' hQ']
        congr 1
        exact h w
    intro v
    rw [matrixLinearEquiv_apply]
    exact congrArg (fun q : QuadraticForm K (Fin d → K) => q v) hQ
  · intro h w
    apply Subtype.ext
    rw [matrixLinearEquiv_apply, RecipeFieldOmega.descForm_apply Q' hQ',
      RecipeFieldOmega.descForm_apply Q' hQ', inclVec_mulVec, ← matrixLinearEquiv_apply, h]

end Transfer

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem exists_descent_form (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hnd : (polarBilin Q).Nondegenerate)
    {p v : ℕ} (hp : p.Prime) {S : coordinateSemilinearGroup (2 * n) K}
    (hSQ : RecipeFieldOmega.IsIsoPair Q S)
    (hσ : orderOf S.right = p ^ v) (hSp : S ^ p ^ v = 1) :
    ∃ (H : GL (Fin (2 * n)) K)
      (hQ' : ∀ w : Fin (2 * n) → FixedPoints.subfield (Subgroup.zpowers S.right) K,
        Q.comp (Matrix.toLin' H.val)
          (RecipeFieldOmega.inclVec (FixedPoints.subfield (Subgroup.zpowers S.right) K) w) ∈
          FixedPoints.subfield (Subgroup.zpowers S.right) K),
      (∀ x, x ∈ FixedPoints.subfield (Subgroup.zpowers S.right) K ↔ S.right x = x) ∧
      S.left * glFieldAut (Fin (2 * n)) K S.right H = H ∧
      (polarBilin (RecipeFieldOmega.descForm
        (Q.comp (Matrix.toLin' H.val)) hQ')).Nondegenerate ∧
      (∃ T : Submodule (FixedPoints.subfield (Subgroup.zpowers S.right) K)
          (Fin (2 * n) → FixedPoints.subfield (Subgroup.zpowers S.right) K),
        finrank (FixedPoints.subfield (Subgroup.zpowers S.right) K) T = 3 ∧
        ∀ x ∈ T, RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ' x = 0) := by
  classical
  obtain ⟨H, hH⟩ :=
    RecipeFieldOmega.exists_fixed_basis_pair_of_pos (pow_pos hp.pos v) hσ rfl hSp
  set K₀ := FixedPoints.subfield (Subgroup.zpowers S.right) K with hK₀def
  have hK₀ : ∀ x, x ∈ K₀ ↔ S.right x = x := fun x =>
    ⟨fun hx => OrdPFieldNs.fixed_of_mem_fixed ⟨x, hx⟩, OrdPFieldNs.mem_fixed_of_fixed⟩
  have hQ' : ∀ w : Fin (2 * n) → K₀,
      Q.comp (Matrix.toLin' H.val) (RecipeFieldOmega.inclVec K₀ w) ∈ K₀ :=
    RecipeFieldOmega.mem_fixed_of_isIsoPair hSQ rfl hK₀ hH
  have hnd₀ : (polarBilin (RecipeFieldOmega.descForm
      (Q.comp (Matrix.toLin' H.val)) hQ')).Nondegenerate :=
    RecipeFieldOmega.nondegenerate_descForm hQ' (RecipeFieldOmega.nondegenerate_comp_GL hnd H)
  obtain ⟨c₀, hc₀⟩ := exists_not_mem_range_wp (K := K₀)
  obtain ⟨τ₀, e₀, f₀, a₀, b₀, -, hF₀, -⟩ :=
    exists_frame (Q := RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ') hc₀ (n - 1) ⊤
      (fun v _ hv => hnd₀.2 v fun x => hv x Submodule.mem_top)
      (by rw [finrank_top, Module.finrank_fin_fun]; omega)
  have hT₀ := exists_totallySingular_of_frame (show 3 ≤ n - 1 by omega) hF₀
  exact ⟨H, hQ', hK₀, hH, hnd₀, hT₀⟩

private theorem descent_field_facts {p v : ℕ} (hp : p.Prime) (hodd : Odd p)
    {S : coordinateSemilinearGroup (2 * n) K} {K₀ : Subfield K}
    (hσ : orderOf S.right = p ^ v) (hK₀ : ∀ x, x ∈ K₀ ↔ S.right x = x) :
    (∀ c : K₀, c ∉ (wp K₀).range → K₀.subtype c ∉ (wp K).range) ∧
      ((Nat.card K : ℤ) ≡ Nat.card K₀ [ZMOD p]) ∧
      (OrdPNS.ordQ K₀ p = OrdPNS.ordQ K p) := by
  have hK₀eq : K₀ = FixedPoints.subfield (Subgroup.zpowers S.right) K := by
    ext x
    rw [hK₀]
    exact ⟨OrdPFieldNs.mem_fixed_of_fixed,
      fun hx => hx ⟨S.right, Subgroup.mem_zpowers S.right⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have hσp : S.right ^ p ^ v = 1 := hσ ▸ pow_orderOf_eq_one S.right
  refine ⟨?_, ?_, ?_⟩
  · rintro c hc ⟨t, ht⟩
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h2₀ : (2 : K₀) = 0 := CharTwo.two_eq_zero
    have ht' : t ^ 2 + t = (c : K) := ht
    refine RecipeFieldOmega.rootFree_of_odd (p := p ^ v) (Odd.pow hodd) hσp hK₀ (β := 1)
      (γ := c) (fun s hs => hc ⟨s, ?_⟩) t ?_
    · rw [wp_apply]
      linear_combination hs - c * h2₀
    · rw [OneMemClass.coe_one, one_mul]
      linear_combination ht' + (c : K) * h2
  · rw [hK₀eq, OrdPFieldNs.card_eq_card_fixed_pow (ℓ := p ^ v) (σ := S.right) hσ,
      ← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact ZMod.pow_card_pow _
  · rw [hK₀eq]
    exact OrdPFieldNs.ordQ_fixed (ℓ := p) (v := v) (σ := S.right) hp hσ

private theorem exists_fixed_derived {p v : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : QuadraticForm K (Fin (2 * n) → K)}
    {S : coordinateSemilinearGroup (2 * n) K} (hSQ : RecipeFieldOmega.IsIsoPair Q S)
    (hSp : S ^ p ^ v = 1) {A : Subgroup (GL (Fin (2 * n)) K)}
    (hA : GenMax (polB Q) (matrixDerived Q) p A) (hAne : ∃ a ∈ A, a ≠ 1) :
    ∃ x : GL (Fin (2 * n)) K, x ∈ matrixDerived Q ∧ orderOf x = p ∧
      matrixConjugation S x = x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hSsim : S ∈ similarityPairs Q :=
    ⟨1, fun v => by rw [hSQ v, Units.val_one, one_mul]⟩
  set Φ : MulAut (GL (Fin (2 * n)) K) := matrixConjugation S with hΦ
  have hΦp : Φ ^ p ^ v = 1 := by
    have h1 : (matrixConjugationHom (d := 2 * n) (K := K)) S ^ p ^ v =
        matrixConjugationHom (S ^ p ^ v) := (map_pow _ S (p ^ v)).symm
    rw [hSp, map_one] at h1
    exact h1
  have hΦΓ : ∀ g ∈ matrixDerived Q, Φ g ∈ matrixDerived Q := fun g hg => by
    rw [← matrixDerived_invariant Q ⟨S, hSsim⟩]
    exact ⟨g, hg, rfl⟩
  obtain ⟨a, haA, ha1⟩ := hAne
  have hpΓ : p ∣ Nat.card (matrixDerived Q) := by
    have hao : orderOf a = p := orderOf_eq_prime (hA.pow a haA) ha1
    rw [← hao]
    exact Subgroup.orderOf_dvd_natCard _ (hA.le haA)
  obtain ⟨x, hxΓ, hxo, hxΦ⟩ :=
    OrdPFieldNs.exists_orderOf_eq_fixed_of_le (v := v) hp Φ hΦp hΦΓ hpΓ
  exact ⟨x, hxΓ, hxo, hxΦ⟩

private theorem exists_fixed_transfer {p : ℕ} (hp : p.Prime)
    {Q : QuadraticForm K (Fin (2 * n) → K)}
    {S : coordinateSemilinearGroup (2 * n) K} {H : GL (Fin (2 * n)) K}
    (hSH : S.left * glFieldAut (Fin (2 * n)) K S.right H = H)
    {x : GL (Fin (2 * n)) K} (hxΓ : x ∈ matrixDerived Q) (hxo : orderOf x = p)
    (hxΦ : matrixConjugation S x = x) :
    ∃ x' : GL (Fin (2 * n)) K,
      Matrix.GeneralLinearGroup.map (S.right : K →+* K) x' = x' ∧
      x' ∈ matrixIsometries (Q.comp (Matrix.toLin' H.val)) ∧ x' ^ p = 1 ∧ x' ≠ 1 := by
  have hσH : glFieldAut (Fin (2 * n)) K S.right H = S.left⁻¹ * H :=
    calc glFieldAut (Fin (2 * n)) K S.right H
        = S.left⁻¹ * (S.left * glFieldAut (Fin (2 * n)) K S.right H) := by group
      _ = S.left⁻¹ * H := by rw [hSH]
  have hσx : glFieldAut (Fin (2 * n)) K S.right x = S.left⁻¹ * x * S.left := by
    have h1 : S.left * glFieldAut (Fin (2 * n)) K S.right x * S.left⁻¹ = x := hxΦ
    calc glFieldAut (Fin (2 * n)) K S.right x
        = S.left⁻¹ * (S.left * glFieldAut (Fin (2 * n)) K S.right x * S.left⁻¹) * S.left := by
          group
      _ = S.left⁻¹ * x * S.left := by rw [h1]
  set x' := H⁻¹ * x * H with hx'
  have hx'σ : Matrix.GeneralLinearGroup.map (S.right : K →+* K) x' = x' := by
    rw [← glFieldAut_eq_map, hx', map_mul, map_mul, map_inv, hσH, hσx]
    group
  have hx'iso : x' ∈ matrixIsometries (Q.comp (Matrix.toLin' H.val)) := by
    rw [mem_isometries_comp_iff, hx', show H * (H⁻¹ * x * H) * H⁻¹ = x by group]
    exact matrixDerived_le_isometries Q hxΓ
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hx'p : x' ^ p = 1 := by
    rw [hx', show H⁻¹ * x * H = H⁻¹ * x * H⁻¹⁻¹ by rw [inv_inv], conj_pow, hxp, mul_one,
      mul_inv_cancel]
  have hx'1 : x' ≠ 1 := by
    intro h1
    have h2 : x = 1 := by
      have h3 : x = H * x' * H⁻¹ := by rw [hx']; group
      rw [h3, h1, mul_one, mul_inv_cancel]
    rw [h2, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  exact ⟨x', hx'σ, hx'iso, hx'p, hx'1⟩

private theorem exists_fixed_descend {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : QuadraticForm K (Fin (2 * n) → K)}
    {S : coordinateSemilinearGroup (2 * n) K} {H : GL (Fin (2 * n)) K}
    (hQ' : ∀ w : Fin (2 * n) → FixedPoints.subfield (Subgroup.zpowers S.right) K,
      Q.comp (Matrix.toLin' H.val)
        (RecipeFieldOmega.inclVec (FixedPoints.subfield (Subgroup.zpowers S.right) K) w) ∈
        FixedPoints.subfield (Subgroup.zpowers S.right) K)
    (hnd₀ : (polarBilin (RecipeFieldOmega.descForm
      (Q.comp (Matrix.toLin' H.val)) hQ')).Nondegenerate)
    (hT₀ : ∃ T : Submodule (FixedPoints.subfield (Subgroup.zpowers S.right) K)
        (Fin (2 * n) → FixedPoints.subfield (Subgroup.zpowers S.right) K),
        finrank (FixedPoints.subfield (Subgroup.zpowers S.right) K) T = 3 ∧
      ∀ x ∈ T, RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ' x = 0)
    {x' : GL (Fin (2 * n)) K}
    (hx'σ : Matrix.GeneralLinearGroup.map (S.right : K →+* K) x' = x')
    (hx'iso : x' ∈ matrixIsometries (Q.comp (Matrix.toLin' H.val)))
    (hx'p : x' ^ p = 1) (hx'1 : x' ≠ 1) :
    ∃ x₀ : GL (Fin (2 * n)) (FixedPoints.subfield (Subgroup.zpowers S.right) K),
      x₀ ∈ matrixDerived (RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ') ∧
      x₀ ^ p = 1 ∧ x₀ ≠ 1 := by
  classical
  set Q₀ := RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ' with hQ₀
  obtain ⟨x₀, hx₀⟩ := OrdPFieldNs.exists_gl_map_eq x' hx'σ
  have hmapinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin (2 * n))
        (FixedPoints.subfield (Subgroup.zpowers S.right) K).subtype) := by
    intro g g' hgg'
    apply Units.ext
    exact Matrix.map_injective Subtype.val_injective
      (congrArg (fun z : GL (Fin (2 * n)) K =>
        (z : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) hgg')
  have hx₀iso : x₀ ∈ matrixIsometries Q₀ :=
    (mem_isometries_descForm_iff hQ' x₀).mpr (by rw [hx₀]; exact hx'iso)
  have hx₀p : x₀ ^ p = 1 := hmapinj (by rw [map_pow, hx₀, map_one, hx'p])
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    apply hx'1
    rw [← hx₀, h1, map_one]
  have hx₀Γ : x₀ ∈ matrixDerived Q₀ :=
    CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd₀ hT₀ hx₀iso
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hx₀p))
  exact ⟨x₀, hx₀Γ, hx₀p, hx₀1⟩

private theorem exists_genMax_mem_of_fixed_x₀ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : QuadraticForm K (Fin (2 * n) → K)} {A : Subgroup (GL (Fin (2 * n)) K)}
    (hA : GenMax (polB Q) (matrixDerived Q) p A) {K₀ : Subfield K}
    {H : GL (Fin (2 * n)) K}
    (hQ' : ∀ w : Fin (2 * n) → K₀,
      Q.comp (Matrix.toLin' H.val) (RecipeFieldOmega.inclVec K₀ w) ∈ K₀)
    (hnd₀ : (polarBilin (RecipeFieldOmega.descForm
      (Q.comp (Matrix.toLin' H.val)) hQ')).Nondegenerate)
    (hT₀ : ∃ T : Submodule K₀ (Fin (2 * n) → K₀), finrank K₀ T = 3 ∧
      ∀ x ∈ T, RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ' x = 0)
    (hwp : ∀ c : K₀, c ∉ (wp K₀).range → K₀.subtype c ∉ (wp K).range)
    (hq : (Nat.card K : ℤ) ≡ Nat.card K₀ [ZMOD p])
    (hord : OrdPNS.ordQ K₀ p = OrdPNS.ordQ K p)
    {x₀ : GL (Fin (2 * n)) K₀}
    (hx₀Γ : x₀ ∈ matrixDerived (RecipeFieldOmega.descForm
      (Q.comp (Matrix.toLin' H.val)) hQ'))
    (hx₀p : x₀ ^ p = 1) (hx₀1 : x₀ ≠ 1) :
    ∃ E₀ : Subgroup (GL (Fin (2 * n)) K₀),
      GenMax (polB (RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ'))
        (matrixDerived (RecipeFieldOmega.descForm
          (Q.comp (Matrix.toLin' H.val)) hQ')) p E₀ ∧
      Nat.card A ≤ Nat.card E₀ := by
  classical
  set Q₀ := RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ' with hQ₀
  obtain ⟨E₀, hE₀, hx₀E⟩ := exists_genMax_mem_orth hnd₀ hT₀ hp hp2 hx₀Γ hx₀p
  set κ : (Fin (2 * n) → K₀) →+ (Fin (2 * n) → K) :=
    { toFun := fun w => H.val *ᵥ RecipeFieldOmega.inclVec K₀ w
      map_zero' := by
        change H.val *ᵥ RecipeFieldOmega.inclVec K₀ 0 = 0
        rw [show RecipeFieldOmega.inclVec K₀ (0 : Fin (2 * n) → K₀) = 0 by
          funext i; simp [RecipeFieldOmega.inclVec], Matrix.mulVec_zero]
      map_add' := fun w w' => by
        change H.val *ᵥ RecipeFieldOmega.inclVec K₀ (w + w') = H.val *ᵥ _ + H.val *ᵥ _
        rw [RecipeFieldOmega.inclVec_add, Matrix.mulVec_add] } with hκdef
  have hκ : ∀ w, Q (κ w) = K₀.subtype (Q₀ w) := fun w => by
    change Q (H.val *ᵥ RecipeFieldOmega.inclVec K₀ w) = ((Q₀ w : K₀) : K)
    rw [hQ₀, RecipeFieldOmega.descForm_apply]
    rfl
  exact ⟨E₀, hE₀, card_le_card_of_genMax_field K₀.subtype κ hκ hT₀ hwp hq hord hA hE₀
    ⟨x₀, hx₀E, hx₀1⟩⟩

private theorem exists_fixed_elemAb_image {p : ℕ} (hodd : Odd p)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {S : coordinateSemilinearGroup (2 * n) K} {K₀ : Subfield K}
    {H : GL (Fin (2 * n)) K}
    (hQ' : ∀ w : Fin (2 * n) → K₀,
      Q.comp (Matrix.toLin' H.val) (RecipeFieldOmega.inclVec K₀ w) ∈ K₀)
    (hK₀ : ∀ x, x ∈ K₀ ↔ S.right x = x)
    (hSH : S.left * glFieldAut (Fin (2 * n)) K S.right H = H)
    {A : Subgroup (GL (Fin (2 * n)) K)}
    {E₀ : Subgroup (GL (Fin (2 * n)) K₀)}
    (hE₀ : GenMax (polB (RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ'))
      (matrixDerived (RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ')) p E₀)
    (hcard : Nat.card A ≤ Nat.card E₀) :
    ∃ E : Subgroup (GL (Fin (2 * n)) K), E ≤ matrixDerived Q ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧
      Nat.card A ≤ Nat.card E ∧ ∀ e ∈ E, matrixConjugation S e = e := by
  classical
  set Q₀ := RecipeFieldOmega.descForm (Q.comp (Matrix.toLin' H.val)) hQ' with hQ₀
  have hmapinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin (2 * n)) K₀.subtype) := by
    intro g g' hgg'
    apply Units.ext
    exact Matrix.map_injective Subtype.val_injective
      (congrArg (fun z : GL (Fin (2 * n)) K =>
        (z : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) hgg')
  have hσH : glFieldAut (Fin (2 * n)) K S.right H = S.left⁻¹ * H :=
    calc glFieldAut (Fin (2 * n)) K S.right H
        = S.left⁻¹ * (S.left * glFieldAut (Fin (2 * n)) K S.right H) := by group
      _ = S.left⁻¹ * H := by rw [hSH]
  set ℓ : GL (Fin (2 * n)) K₀ →* GL (Fin (2 * n)) K :=
    (MulAut.conj H).toMonoidHom.comp (Matrix.GeneralLinearGroup.map K₀.subtype) with hℓ
  have hℓapply : ∀ g, ℓ g = H * Matrix.GeneralLinearGroup.map K₀.subtype g * H⁻¹ := fun g => rfl
  have hℓinj : Function.Injective ℓ := (MulAut.conj H).injective.comp hmapinj
  have hfix : ∀ g₀ : GL (Fin (2 * n)) K₀,
      Matrix.GeneralLinearGroup.map (S.right : K →+* K)
        (Matrix.GeneralLinearGroup.map K₀.subtype g₀) =
      Matrix.GeneralLinearGroup.map K₀.subtype g₀ := fun g₀ => by
    ext i j
    exact (hK₀ _).1 (g₀ i j).2
  refine ⟨E₀.map ℓ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g₀, hg₀, rfl⟩
    have h1 := (mem_isometries_descForm_iff hQ' g₀).mp
      (matrixDerived_le_isometries Q₀ (hE₀.le hg₀))
    have h2 := (mem_isometries_comp_iff H _).mp h1
    have hp' : (ℓ g₀) ^ p = 1 := by rw [← map_pow, hE₀.pow g₀ hg₀, map_one]
    rw [hℓapply] at hp' ⊢
    exact CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd hT h2
      (Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hp'))
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    rw [← map_mul, ← map_mul, hE₀.comm g hg g' hg']
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, hE₀.pow g hg, map_one]
  · rw [Subgroup.card_map_of_injective hℓinj]
    exact hcard
  · rintro _ ⟨g₀, -, rfl⟩
    rw [matrixConjugation_apply, hℓapply, map_mul, map_mul, map_inv, hσH,
      glFieldAut_eq_map S.right (Matrix.GeneralLinearGroup.map K₀.subtype g₀), hfix g₀]
    group

private theorem exists_fixed_elemAb_descent (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p v : ℕ} {S : coordinateSemilinearGroup (2 * n) K} (hSQ : RecipeFieldOmega.IsIsoPair Q S)
    (hσ : orderOf S.right = p ^ v) (hSp : S ^ p ^ v = 1)
    {A : Subgroup (GL (Fin (2 * n)) K)} (hA : GenMax (polB Q) (matrixDerived Q) p A)
    (hAne : ∃ a ∈ A, a ≠ 1) :
    ∃ E : Subgroup (GL (Fin (2 * n)) K), E ≤ matrixDerived Q ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧
      Nat.card A ≤ Nat.card E ∧ ∀ e ∈ E, matrixConjugation S e = e := by
  have hp := hA.prime
  have hp2 := hA.ne_two
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨H, hQ', hK₀, hSH, hnd₀, hT₀⟩ :=
    exists_descent_form hn hnd hp hSQ hσ hSp
  set K₀ := FixedPoints.subfield (Subgroup.zpowers S.right) K with hK₀def
  obtain ⟨hwp, hq, hord⟩ := descent_field_facts hp hodd hσ hK₀
  obtain ⟨x, hxΓ, hxo, hxΦ⟩ := exists_fixed_derived hp hp2 hSQ hSp hA hAne
  obtain ⟨x', hx'σ, hx'iso, hx'p, hx'1⟩ :=
    exists_fixed_transfer hp hSH hxΓ hxo hxΦ
  obtain ⟨x₀, hx₀Γ, hx₀p, hx₀1⟩ :=
    exists_fixed_descend hp hp2 hQ' hnd₀ hT₀ hx'σ hx'iso hx'p hx'1
  obtain ⟨E₀, hE₀, hcard⟩ :=
    exists_genMax_mem_of_fixed_x₀ hp hp2 hA hQ' hnd₀ hT₀ hwp hq hord hx₀Γ hx₀p hx₀1
  exact exists_fixed_elemAb_image hodd hnd hT hQ' hK₀ hSH hE₀ hcard

theorem exists_fixed_elemAb_of_orderOf (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p v : ℕ} {S : coordinateSemilinearGroup (2 * n) K} (hSQ : RecipeFieldOmega.IsIsoPair Q S)
    (hσ : orderOf S.right = p ^ v) (hSp : S ^ p ^ v = 1) {A : Subgroup (GL (Fin (2 * n)) K)}
    (hA : GenMax (polB Q) (matrixDerived Q) p A) :
    ∃ E : Subgroup (GL (Fin (2 * n)) K), E ≤ matrixDerived Q ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧ Nat.card A ≤ Nat.card E ∧
      ∀ e ∈ E, matrixConjugation S e = e := by
  classical
  have hodd : Odd p := hA.prime.odd_of_ne_two hA.ne_two
  by_cases hA1 : ∀ a ∈ A, a = 1
  · refine ⟨⊥, bot_le, fun a ha b hb => by rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb],
      fun a ha => by rw [Subgroup.mem_bot.mp ha, one_pow], ?_,
      fun e he => by rw [Subgroup.mem_bot.mp he, map_one]⟩
    rw [(Subgroup.eq_bot_iff_forall A).mpr hA1]
  push Not at hA1
  by_cases hσ1 : S.right = 1
  · have hpv1 : p ^ v = 1 := by rw [← hσ, hσ1, orderOf_one]
    have hS1 : S = 1 := by
      have h := hSp
      rwa [hpv1, pow_one] at h
    refine ⟨A, hA.le, hA.comm, hA.pow, le_rfl, fun e he => ?_⟩
    rw [hS1]
    change matrixConjugationHom (1 : coordinateSemilinearGroup (2 * n) K) e = e
    rw [matrixConjugationHom.map_one]
    rfl
  · exact exists_fixed_elemAb_descent hn hnd hT hSQ hσ hSp hA hA1

theorem exists_fixed_elemAb (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} {S : coordinateSemilinearGroup (2 * n) K} (hSQ : RecipeFieldOmega.IsIsoPair Q S)
    (hSp : S ^ p = 1) {A : Subgroup (GL (Fin (2 * n)) K)}
    (hA : GenMax (polB Q) (matrixDerived Q) p A) :
    ∃ E : Subgroup (GL (Fin (2 * n)) K), E ≤ matrixDerived Q ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧ Nat.card A ≤ Nat.card E ∧
      ∀ e ∈ E, matrixConjugation S e = e := by
  classical
  have hp := hA.prime
  have hp2 := hA.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hσp : S.right ^ p = 1 := by rw [← RecipeFieldOmega.right_pow, hSp]; rfl
  by_cases hA1 : ∀ a ∈ A, a = 1
  · refine ⟨⊥, bot_le, fun a ha b hb => by rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb],
      fun a ha => by rw [Subgroup.mem_bot.mp ha, one_pow], ?_,
      fun e he => by rw [Subgroup.mem_bot.mp he, map_one]⟩
    rw [(Subgroup.eq_bot_iff_forall A).mpr hA1]
  push Not at hA1
  by_cases hσ1 : S.right = 1
  ·
    have hL : ∀ v, coordinateSemilinearMap S v = S.left.val *ᵥ v := fun v => by
      rw [coordinateSemilinearMap_apply, hσ1]
      rfl
    have hLiso : S.left ∈ matrixIsometries Q := (mem_matrixIsometries_iff Q _).mpr fun v => by
      rw [matrixLinearEquiv_apply, ← hL, hSQ v, hσ1]
      rfl
    have hLk : ∀ k : ℕ, (S ^ k).left = S.left ^ k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', coordinateSemilinearGroup_mul_matrix, hσ1, map_one, MulAut.one_apply, ih,
          pow_succ']
    have hLp : S.left ^ p = 1 := by rw [← hLk, hSp]; rfl
    have hLΓ : S.left ∈ matrixDerived Q :=
      CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd hT hLiso
        (Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hLp))
    obtain ⟨E, hE, hLE⟩ := exists_genMax_mem_orth hnd hT hp hp2 hLΓ hLp
    refine ⟨E, hE.le, hE.comm, hE.pow, card_le_card_of_genMax hnd hT hA hE, fun e he => ?_⟩
    rw [matrixConjugation_apply, hσ1, map_one, MulAut.one_apply, hE.comm _ hLE _ he,
      mul_inv_cancel_right]
  · have hσo : orderOf S.right = p := orderOf_eq_prime hσp hσ1
    exact exists_fixed_elemAb_of_orderOf hn hnd hT (v := 1) hSQ
      (hσo.trans (pow_one p).symm) (by rwa [pow_one]) hA

end Fixed

end OrdPFieldNsOm

end CFSG.StandardType
