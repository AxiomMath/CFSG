module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkFix

public section

namespace CFSG.StandardType

namespace WitOmBlk

open QuadraticMap Module OrdPNsOm CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem exists_bilin_add_flip {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (γ : LinearMap.BilinForm K M) (hsymm : ∀ x y, γ x y = γ y x) (halt : ∀ x, γ x x = 0) :
    ∃ τ : LinearMap.BilinForm K M, ∀ x y, τ x y + τ y x = γ x y := by
  classical
  set bm := Module.finBasis K M with hbm
  set τ : LinearMap.BilinForm K M := bm.constr K fun i => bm.constr K fun j =>
    if i < j then γ (bm i) (bm j) else 0 with hτdef
  have hτ : ∀ i j, τ (bm i) (bm j) = if i < j then γ (bm i) (bm j) else 0 := by
    intro i j
    rw [hτdef, Basis.constr_basis, Basis.constr_basis]
  have h : τ + τ.flip = γ := by
    refine LinearMap.BilinForm.ext_basis bm fun i j => ?_
    change τ (bm i) (bm j) + τ (bm j) (bm i) = γ (bm i) (bm j)
    rw [hτ, hτ]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [ite_eq_left hij, ite_eq_right (not_lt.mpr hij.le), add_zero]
    · rw [ite_eq_right (lt_irrefl _), add_zero, halt]
    · rw [ite_eq_right (not_lt.mpr hij.le), ite_eq_left hij, zero_add, hsymm]
  refine ⟨τ, fun x y => ?_⟩
  have h1 := congrArg (fun F : LinearMap.BilinForm K M => F x y) h
  simpa using h1

omit [CharP K 2] in
theorem finrank_comap_le {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (N : V →ₗ[K] V) (P : Submodule K V) :
    finrank K (P.comap N) ≤ finrank K P + finrank K (LinearMap.ker N) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (N.domRestrict (P.comap N))
  have h2 : finrank K (LinearMap.range (N.domRestrict (P.comap N))) ≤ finrank K P := by
    apply Submodule.finrank_mono
    rintro _ ⟨x, rfl⟩
    exact x.2
  have h3 : finrank K (LinearMap.ker (N.domRestrict (P.comap N))) ≤
      finrank K (LinearMap.ker N) := by
    rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq]
    exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
  omega

section Swap

variable {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_swap_space [Finite K] [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {v : V ≃ₗ[K] V} (hO : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hvv : v * v = 1) {m : ℕ}
    (h : 2 * m + 5 ≤ finrank K (commSpace v) ∨
      ((∀ x, Q (v x - x) = 0) ∧ 2 * m + 4 ≤ finrank K (commSpace v))) :
    ∃ (W : Submodule K V) (m' : ℕ), m + 1 ≤ m' ∧ finrank K W = 2 * m' + 2 ∧
      SUTB.NondegOn (polarBilin Q) W ∧ ∀ x ∈ W, ∀ y ∈ W, polar Q x (v y) = 0 := by
  classical
  set β := wallForm Q v with hβdef
  have hβs : ∀ x y, β x y = β y x := wallForm_symm hO hvv
  let H : Submodule K V :=
    { carrier := {x | β x x = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [WitOm.wallForm_add_add hO hvv, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx, mul_zero] }
  have hH : ∀ x, x ∈ H ↔ β x x = 0 := fun x => Iff.rfl
  set Rad : Submodule K V := H ⊓ LinearMap.BilinForm.orthogonal β H with hRad
  obtain ⟨Y', hY'⟩ := Rad.exists_isCompl
  have hRadH : Rad ≤ H := inf_le_left
  have hsup : Rad ⊔ Y' ⊓ H = H := by
    rw [← sup_inf_assoc_of_le _ hRadH, hY'.sup_eq_top, top_inf_eq]
  have hinf : Rad ⊓ (Y' ⊓ H) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : x ∈ Rad ⊓ Y' := ⟨hx.1, hx.2.1⟩
    rw [hY'.inf_eq_bot] at h1
    exact h1
  set Y := Y' ⊓ H with hYdef
  have hYH : Y ≤ H := inf_le_right
  have hYnd : ∀ y ∈ Y, (∀ y' ∈ Y, β y y' = 0) → y = 0 := by
    intro y hy hy'
    have hyRad : y ∈ Rad := by
      refine ⟨hYH hy, LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => ?_⟩
      rw [← hsup] at hx
      obtain ⟨r, hr, y', hy'', rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, LinearMap.add_apply, hβs y' y, hy' y' hy'', add_zero, hβs]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp hr.2 y (hYH hy)
    have h1 : y ∈ Rad ⊓ Y := ⟨hyRad, hy⟩
    rw [hinf] at h1
    exact h1
  have hdimY : finrank K Rad + finrank K Y = finrank K H := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Rad Y
    rw [hsup, hinf, finrank_bot, add_zero] at h1
    omega
  have hRadle : finrank K Rad + finrank K H + finrank K (commSpace v) ≤ 2 * finrank K V := by
    have h1 : LinearMap.BilinForm.orthogonal β H =
        (LinearMap.BilinForm.orthogonal (polarBilin Q) H).comap ((v : V →ₗ[K] V) - 1) := by
      ext x
      simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_comap,
        hβdef, wallForm_apply, polarBilin_apply_apply,
        LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]
    have h2 := finrank_comap_le ((v : V →ₗ[K] V) - 1)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) H)
    have h3 := LinearMap.BilinForm.finrank_orthogonal hQ H
    have h4 := finrank_commSpace_add_finrank_fixSpace v
    have h5 : finrank K Rad ≤ finrank K (LinearMap.BilinForm.orthogonal β H) :=
      Submodule.finrank_mono inf_le_right
    rw [h1] at h5
    have h6 := Submodule.finrank_le H
    change finrank K (commSpace v) + finrank K (LinearMap.ker ((v : V →ₗ[K] V) - 1)) =
      finrank K V at h4
    omega
  have hH1 : finrank K V ≤ finrank K H + 1 := by
    by_cases hall : ∀ x, β x x = 0
    · have : H = ⊤ := eq_top_iff.mpr fun x _ => (hH x).mpr (hall x)
      rw [this, finrank_top]
      omega
    push Not at hall
    obtain ⟨x₀, hx₀⟩ := hall
    have hsupH : H ⊔ Submodule.span K {x₀} = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨c, hc⟩ := isSquare_of_charTwo' (β x x / β x₀ x₀)
      have hmem : x + c • x₀ ∈ H := by
        rw [hH, WitOm.wallForm_add_add hO hvv]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← hc, div_mul_cancel₀ _ hx₀]
        linear_combination (β x x) * (CharTwo.two_eq_zero : (2 : K) = 0)
      refine Submodule.mem_sup.mpr ⟨x + c • x₀, hmem, (-c) • x₀,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x₀), ?_⟩
      rw [neg_smul, add_neg_cancel_right]
    have hspan : finrank K (Submodule.span K {x₀}) ≤ 1 := by
      have := finrank_span_finset_le_card (R := K) ({x₀} : Finset V)
      rwa [Finset.coe_singleton, Finset.card_singleton] at this
    have h1 := Submodule.finrank_add_le_finrank_add_finrank H (Submodule.span K {x₀})
    rw [hsupH, finrank_top] at h1
    omega
  have hHalt : (∀ x, Q (v x - x) = 0) → finrank K H = finrank K V := by
    intro hz
    have : H = ⊤ := eq_top_iff.mpr fun x _ => (hH x).mpr (by rw [hβdef, wallForm_self hO, hz])
    rw [this, finrank_top]
  have hYrefl : ((wallForm Q v).restrict Y).IsRefl := ((wallForm_isSymm hO hvv).restrict Y).isRefl
  have hβY : ((wallForm Q v).restrict Y).Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hYrefl).mpr fun y hy => ?_
    exact Subtype.ext (hYnd y y.2 fun y' hy' => hy ⟨y', hy'⟩)
  have hYalt : ((wallForm Q v).restrict Y).IsAlt := fun y => (hH y).mp (hYH y.2)
  obtain ⟨k, hk⟩ := LinearMap.BilinForm.IsAlt.even_finrank hYalt hβY
  have hYdim : 2 * m + 4 ≤ finrank K Y := by
    rcases h with h | ⟨hz, h⟩
    · omega
    · have := hHalt hz
      omega
  set γ : LinearMap.BilinForm K Y :=
    (polarBilin Q).compl₁₂ Y.subtype ((v : V →ₗ[K] V) ∘ₗ Y.subtype) with hγdef
  have hγapp : ∀ y y' : Y, γ y y' = polar Q y (v y') := fun y y' => rfl
  have hγs : ∀ y y' : Y, γ y y' = γ y' y := by
    intro y y'
    rw [hγapp, hγapp, ← polar_apply_eq_polar_apply hO hvv, polar_comm]
  have hvy : ∀ x y : V, polar Q x (v y) = polar Q x y + β x y := by
    intro x y
    have h1 : v y = y + (v y - y) := by abel
    rw [h1, polar_add_right, hβdef, wallForm_apply]
  have hγa : ∀ y : Y, γ y y = 0 := by
    intro y
    rw [hγapp, hvy, polar_self_charTwo, zero_add]
    exact (hH y).mp (hYH y.2)
  obtain ⟨τ, hτ⟩ := exists_bilin_add_flip γ hγs hγa
  set S : Y →ₗ[K] Y := (LinearMap.BilinForm.toDual _ hβY).symm.toLinearMap ∘ₗ τ.flip with hSdef
  have hSβ : ∀ y y' : Y, β (S y' : V) y = τ y y' := by
    intro y y'
    have h1 : (LinearMap.BilinForm.toDual _ hβY (S y')) y =
        ((wallForm Q v).restrict Y) (S y') y := LinearMap.BilinForm.toDual_def hβY
    have h2 : LinearMap.BilinForm.toDual _ hβY (S y') = τ.flip y' := by
      rw [hSdef, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [h2] at h1
    exact h1.symm
  set Φ : Y →ₗ[K] V := Y.subtype + ((v : V →ₗ[K] V) - 1) ∘ₗ Y.subtype ∘ₗ S with hΦdef
  have hΦapp : ∀ y : Y, Φ y = (y : V) + (v (S y : V) - (S y : V)) := fun y => rfl
  have hNN : ∀ a b : V, polar Q (v a - a) (v b - b) = 0 := fun a b =>
    polar_commSpace_eq_zero hO hvv (sub_mem_commSpace v a) (sub_mem_commSpace v b)
  have hxN : ∀ x z : V, polar Q x (v z - z) = β x z := fun x z => (wallForm_apply Q v x z).symm
  have hNx : ∀ x z : V, polar Q (v z - z) x = β x z := fun x z => by rw [polar_comm]; exact hxN x z
  have hvN : ∀ z : V, v (v z - z) = v z - z := WitOm.apply_sub_eq hvv
  have hP1 : ∀ y y' : Y, polar Q (Φ y) (Φ y') = β y y' := by
    intro y y'
    have e1 : β (y : V) (S y' : V) = τ y y' := by rw [hβs]; exact hSβ y y'
    have e2 : β (y' : V) (S y : V) = τ y' y := by rw [hβs]; exact hSβ y' y
    have e3 : τ y y' + τ y' y = polar Q y y' + β y y' := by rw [hτ, hγapp, hvy]
    rw [hΦapp, hΦapp, polar_add_left, polar_add_right, polar_add_right, hNN, hxN, hNx, e1, e2,
      add_zero]
    linear_combination e3 + (polar Q (y : V) y') * (CharTwo.two_eq_zero : (2 : K) = 0)
  have hP2 : ∀ y y' : Y, polar Q (Φ y) (v (Φ y')) = 0 := by
    intro y y'
    have e1 : β (y : V) (S y' : V) = τ y y' := by rw [hβs]; exact hSβ y y'
    have e2 : β (y' : V) (S y : V) = τ y' y := by rw [hβs]; exact hSβ y' y
    have e3 : τ y y' + τ y' y = polar Q y (v y') := by rw [hτ, hγapp]
    have e4 : polar Q (v (S y : V) - (S y : V)) (v y') = β y' (S y : V) := by
      rw [← polar_apply_eq_polar_apply hO hvv, hvN, hNx]
    rw [hΦapp, hΦapp, map_add, hvN, polar_add_left, polar_add_right, polar_add_right, hNN, hxN,
      e4, e1, e2, add_zero]
    linear_combination e3 + (polar Q (y : V) (v y')) * (CharTwo.two_eq_zero : (2 : K) = 0)
  have hΦ0 : ∀ y : Y, (∀ y' : Y, polar Q (Φ y) (Φ y') = 0) → y = 0 := by
    intro y hy
    exact Subtype.ext (hYnd y y.2 fun y' hy' => by rw [← hP1 y ⟨y', hy'⟩]; exact hy _)
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    exact hΦ0 y fun y' => by rw [hy, polar_zero_left]
  refine ⟨LinearMap.range Φ, k - 1, by omega, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hΦinj]
    omega
  · rintro _ ⟨y, rfl⟩ hw
    have hy0 : y = 0 := hΦ0 y fun y' => by
      rw [polar_comm]
      exact hw _ ⟨y', rfl⟩
    rw [hy0, map_zero]
  · rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    exact hP2 y y'

theorem exists_frame_swap [Finite K] [FiniteDimensional K V] [Finite V] {c₀ : K}
    (hc₀ : c₀ ∉ (wp K).range) (hQ : Q.polarBilin.Nondegenerate) {v : V ≃ₗ[K] V}
    (hO : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hvv : v * v = 1) {m : ℕ} (τ₀ : Bool)
    (h : 2 * m + 5 ≤ finrank K (commSpace v) ∨
      ((∀ x, Q (v x - x) = 0) ∧ 2 * m + 4 ≤ finrank K (commSpace v))) :
    ∃ (e f : Fin m → V) (a b : V), IsFrame Q c₀ τ₀ e f a b ∧
      ∀ x y, polar Q (fvec e f a b x) (v (fvec e f a b y)) = 0 := by
  obtain ⟨W, m', hm', hdim, hnd, horth⟩ := exists_swap_space hQ hO hvv h
  obtain ⟨τ, e, f, a, b, hmem, hF, -⟩ := exists_frame hc₀ m' W hnd hdim
  obtain ⟨e', f', a', b', hF', hmem'⟩ := exists_frame_of_type hm' hF τ₀ hmem
  exact ⟨e', f', a', b', hF', fun x y => horth _ (hmem' x) _ (hmem' y)⟩

theorem exists_frame_fix_or_swap [Finite K] [FiniteDimensional K V] [Finite V] {c₀ : K}
    (hc₀ : c₀ ∉ (wp K).range) (hQ : Q.polarBilin.Nondegenerate) {v : V ≃ₗ[K] V}
    (hO : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hvv : v * v = 1) {m : ℕ} (hm : 1 ≤ m)
    (hdim : 4 * (2 * m + 2) ≤ finrank K V) (τ₀ : Bool) :
    ∃ (e f : Fin m → V) (a b : V), IsFrame Q c₀ τ₀ e f a b ∧
      ((∀ x, fvec e f a b x ∈ fixSpace v) ∨
        ∀ x y, polar Q (fvec e f a b x) (v (fvec e f a b y)) = 0) := by
  obtain ⟨k, hk⟩ := even_finrank_of_nondeg hQ
  by_cases h1 : 2 * m + 4 + 2 * finrank K (commSpace v) ≤ finrank K V
  · obtain ⟨e, f, a, b, hF, hmem⟩ := exists_frame_fix hc₀ hQ hO hvv τ₀ (Or.inl h1)
    exact ⟨e, f, a, b, hF, Or.inl hmem⟩
  by_cases hz : ∀ x, Q (v x - x) = 0
  · obtain ⟨e, f, a, b, hF, horth⟩ :=
      exists_frame_swap hc₀ hQ hO hvv (m := m) τ₀ (Or.inr ⟨hz, by omega⟩)
    exact ⟨e, f, a, b, hF, Or.inr horth⟩
  push Not at hz
  by_cases h2 : 2 * m + 2 + 2 * finrank K (commSpace v) = finrank K V
  · obtain ⟨e, f, a, b, hF, hmem⟩ := exists_frame_fix hc₀ hQ hO hvv τ₀ (Or.inr ⟨h2, hz⟩)
    exact ⟨e, f, a, b, hF, Or.inl hmem⟩
  · obtain ⟨e, f, a, b, hF, horth⟩ :=
      exists_frame_swap hc₀ hQ hO hvv (m := m) τ₀ (Or.inl (by omega))
    exact ⟨e, f, a, b, hF, Or.inr horth⟩

end Swap

end WitOmBlk

end CFSG.StandardType
