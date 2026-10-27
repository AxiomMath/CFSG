module

public import CFSG.RankThree.GF2n.Smith81.S81BNAut
public import CFSG.RankThree.GF2n.Smith81.S81BNQuot

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube
open scoped commutatorElement

section Action

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] def ActsOnQtAs (ψ : M₀.E ≃ₗ[K] Cube K) (m : G) (T : Cube K ≃ₗ[K] Cube K) : Prop :=
  ∀ x ∈ Q, T (ψ (M₀.π x)) = ψ (M₀.π (m * x * m⁻¹))

theorem ActsOnQtAs.one (ψ : M₀.E ≃ₗ[K] Cube K) : ActsOnQtAs ψ (1 : G) 1 := by
  intro x hx
  simp

theorem ActsOnQtAs.mul (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] Cube K} {m m' : G}
    {T T' : Cube K ≃ₗ[K] Cube K} (hm' : m' ∈ M) (h : ActsOnQtAs ψ m T) (h' : ActsOnQtAs ψ m' T') :
    ActsOnQtAs ψ (m * m') (T * T') := by
  intro x hx
  have h1 := h' x hx
  have h2 := h (m' * x * m'⁻¹) (CFSG.RankThree.GF2n.Smith81.conj_mem_Q H hm' hx)
  calc (T * T') (ψ (M₀.π x)) = T (T' (ψ (M₀.π x))) := rfl
    _ = T (ψ (M₀.π (m' * x * m'⁻¹))) := by rw [h1]
    _ = ψ (M₀.π (m * (m' * x * m'⁻¹) * m⁻¹)) := h2
    _ = ψ (M₀.π (m * m' * x * (m * m')⁻¹)) := by
      rw [show m * (m' * x * m'⁻¹) * m⁻¹ = m * m' * x * (m * m')⁻¹ by group]

theorem ActsOnQtAs.unique (ψ : M₀.E ≃ₗ[K] Cube K) {m : G} {T T' : Cube K ≃ₗ[K] Cube K}
    (h : ActsOnQtAs ψ m T) (h' : ActsOnQtAs ψ m T') : T = T' := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, hx, hxv⟩ := M₀.π_surj (ψ.symm v)
  have hv : ψ (M₀.π x) = v := by rw [hxv]; simp
  rw [← hv, h x hx, h' x hx]

theorem ActsOnQtAs.pow (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] Cube K} {m : G}
    {T : Cube K ≃ₗ[K] Cube K} (hm : m ∈ M) (h : ActsOnQtAs ψ m T) (j : ℕ) :
    ActsOnQtAs ψ (m ^ j) (T ^ j) := by
  induction j with
  | zero => simpa using ActsOnQtAs.one ψ
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul H hm h

theorem ActsOnQtAs.pow_eq_one (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] Cube K} {m : G}
    {T : Cube K ≃ₗ[K] Cube K} (hm : m ∈ M) (h : ActsOnQtAs ψ m T) {n : ℕ} (hn : m ^ n = 1) :
    T ^ n = 1 := by
  have h1 := h.pow H hm n
  rw [hn] at h1
  exact h1.unique ψ (ActsOnQtAs.one ψ)

theorem exists_actsOnQtAs (hg : GlobalModelData M Q Z γ M₀) (ψ : M₀.E ≃ₗ[K] Cube K) {m : G}
    (hm : m ∈ H0 M Z) : ∃ T : Cube K ≃ₗ[K] Cube K, ActsOnQtAs ψ m T := by
  obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.mp hm
  have hc : ∀ z ∈ Z, m * z * m⁻¹ = z := fun z hz => by
    have h1 := Subgroup.mem_centralizer_iff.mp hmC z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  obtain ⟨T', hT', -⟩ := hg.linear_of_centralizes hmM hc
  refine ⟨ψ.symm.trans (T'.trans ψ), fun x hx => ?_⟩
  simp [LinearEquiv.trans_apply, hT' x hx]

theorem ActsOnQtAs.mem_Q (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] Cube K} {m : G} (hm : m ∈ M)
    (h : ActsOnQtAs ψ m 1) : m ∈ Q := by
  refine H.centralizer_Qt m hm fun y hy => ?_
  have h1 := h y hy
  have hmy : m * y * m⁻¹ ∈ Q := CFSG.RankThree.GF2n.Smith81.conj_mem_Q H hm hy
  have hπ : M₀.π (m * y * m⁻¹) = M₀.π y := ψ.injective (by simpa using h1.symm)
  have e : ⁅m, y⁆ = (m * y * m⁻¹) * y⁻¹ := by
    simp only [commutatorElement_def]
  rw [e]
  refine (M₀.π_ker _ (Q.mul_mem hmy (Q.inv_mem hy))).mp ?_
  rw [M₀.π_mul _ hmy _ (Q.inv_mem hy), quadModel_pi_inv M₀ hy, hπ]
  abel

section Uniform

private theorem q_le_lgen (M Q B : Subgroup G) : Q ≤ Lgen M (LB M Q B) := by
  calc Q ≤ LB M Q B := le_sup_left
    _ = conjSubgroup 1 (LB M Q B) := (conjSubgroup_one _).symm
    _ ≤ Lgen M (LB M Q B) :=
        le_iSup₂ (f := fun m (_ : m ∈ M) => conjSubgroup m (LB M Q B)) 1 M.one_mem

private theorem lgen_le_M (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ M := by
  refine iSup₂_le fun m hm => ?_
  calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.LB_le_M
    _ = M := hc.conj_M_eq hm

variable {ψ : M₀.E ≃ₗ[K] Cube K} {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)}

theorem actsOnQtAs_phi (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    (s : Lgen M (LB M Q B)) : ActsOnQtAs ψ (s : G) (φ s) :=
  fun x hx => (d.equivariant s x hx).symm

theorem ActsOnQtAs.mem_Lgen (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {m : G} {T : Cube K ≃ₗ[K] Cube K}
    (hm : m ∈ M) (h : ActsOnQtAs ψ m T) (hT : T ∈ Gam K) : m ∈ Lgen M (LB M Q B) := by
  have hH := hc.hyp
  rw [← d.range] at hT
  obtain ⟨s, hs⟩ := hT
  have hsM : (s : G) ∈ M := lgen_le_M hc s.2
  have h1 : ActsOnQtAs ψ ((s⁻¹ : Lgen M (LB M Q B)) : G) (φ s⁻¹) := actsOnQtAs_phi d s⁻¹
  rw [map_inv, Subgroup.coe_inv] at h1
  have h2 := ActsOnQtAs.mul hH hm h1 h
  rw [hs, inv_mul_cancel] at h2
  have hq : (s : G)⁻¹ * m ∈ Q := ActsOnQtAs.mem_Q hH (M.mul_mem (M.inv_mem hsM) hm) h2
  have e : m = (s : G) * ((s : G)⁻¹ * m) := by group
  rw [e]
  exact mul_mem s.2 (q_le_lgen M Q B hq)

theorem ActsOnQtAs.normalizesSL (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {m : G} {T : Cube K ≃ₗ[K] Cube K}
    (hm : m ∈ M) (h : ActsOnQtAs ψ m T) : NormalizesSL T := by
  intro g hg
  have hH := hc.hyp
  have hgS : g ∈ StatedSL 6 K := CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hg
  have hgG : rhoEquiv K g ∈ Gam K := Subgroup.mem_map_of_mem _ hgS
  rw [← d.range] at hgG
  obtain ⟨s, hs⟩ := hgG
  have hsM : (s : G) ∈ M := lgen_le_M hc s.2
  let s' : Lgen M (LB M Q B) :=
    ⟨m * (s : G) * m⁻¹,
      (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) hm) (s : G)).mp s.2⟩
  have h1 : ActsOnQtAs ψ (m * (s : G)) (T * φ s) := ActsOnQtAs.mul hH hsM h (actsOnQtAs_phi d s)
  have h2 : ActsOnQtAs ψ ((s' : G) * m) (φ s' * T) := ActsOnQtAs.mul hH hm (actsOnQtAs_phi d s') h
  have hmm : m * (s : G) = (s' : G) * m := by
    show m * (s : G) = m * (s : G) * m⁻¹ * m
    group
  rw [hmm] at h1
  have h3 : T * φ s = φ s' * T := h1.unique ψ h2
  have h4 : φ s' ∈ Gam K := by
    rw [← d.range]
    exact ⟨s', rfl⟩
  obtain ⟨g', hg'S, hg'⟩ := Subgroup.mem_map.mp h4
  refine ⟨g', CFSG.Open.StatedAPI.mem_statedSL_iff.mp hg'S, fun ξ => ?_⟩
  have h5 := congrArg (fun F : Cube K ≃ₗ[K] Cube K => F ξ) h3
  simp only [LinearEquiv.mul_apply] at h5
  rw [hs, ← hg', rhoEquiv_apply, rhoEquiv_apply] at h5
  exact h5

end Uniform

end Action

theorem normQuotE3L_of_uniform (hFE1 : Smith24E3LUniformStatement) :
    NormQuotE3LStatement := by
  intro G _ _ M Q Z B IH hc h3L E hEH0 hE2
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3L K γ M₀ hg
  have hctx : Ctx M Q Z B := hc.ctx
  have hH : StrothHyp M Q Z := hctx.hyp
  have hEM : ∀ m ∈ E, m ∈ M := fun m hm => (Subgroup.mem_inf.mp (hEH0 hm)).1
  have hpow : ∀ m ∈ E, ∃ k : ℕ, m ^ (2 ^ k) = 1 := by
    intro m hm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE2) ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have h1 := pow_orderOf_eq_one (⟨m, hm⟩ : E)
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have hact : ∀ m ∈ E, ∃ T : Cube K ≃ₗ[K] Cube K, ActsOnQtAs ψ m T ∧ NormalizesSL T ∧
      ∃ k : ℕ, T ^ (2 ^ k) = 1 := by
    intro m hm
    obtain ⟨T, hT⟩ := exists_actsOnQtAs hg ψ (hEH0 hm)
    obtain ⟨k, hk⟩ := hpow m hm
    exact ⟨T, hT, hT.normalizesSL hctx d (hEM m hm), k, hT.pow_eq_one hH (hEM m hm) hk⟩
  have hinner : ∀ m ∈ E, ∀ T : Cube K ≃ₗ[K] Cube K, ActsOnQtAs ψ m T → (∃ k : ℕ, T ^ (2 ^ k) = 1) →
      InnerType T → m ∈ Lgen M (LB M Q B) := by
    intro m hm T hT hk hI
    obtain ⟨k, hk⟩ := hk
    exact hT.mem_Lgen hctx d (hEM m hm) (mem_Gam_of_innerType_pow hI hk)
  have hmul : ∀ m₁ ∈ E, ∀ m ∈ E, m₁ ∉ Lgen M (LB M Q B) → m ∉ Lgen M (LB M Q B) →
      m₁ * m ∈ Lgen M (LB M Q B) := by
    intro m₁ hm₁ m hm hn₁ hn
    obtain ⟨T₁, hT₁, hN₁, hk₁⟩ := hact m₁ hm₁
    obtain ⟨T, hT, hN, hk⟩ := hact m hm
    have hg₁ : GraphType T₁ :=
      (normalizer_dichotomy hN₁).resolve_left fun hI => hn₁ (hinner m₁ hm₁ T₁ hT₁ hk₁ hI)
    have hg₂ : GraphType T :=
      (normalizer_dichotomy hN).resolve_left fun hI => hn (hinner m hm T hT hk hI)
    have hI : InnerType (T₁ * T) := innerType_mul_of_graphType hg₁ hg₂
    have hTT : ActsOnQtAs ψ (m₁ * m) (T₁ * T) := ActsOnQtAs.mul hH (hEM m hm) hT₁ hT
    obtain ⟨k, hk'⟩ := hpow (m₁ * m) (E.mul_mem hm₁ hm)
    have hTk : (T₁ * T) ^ (2 ^ k) = 1 :=
      hTT.pow_eq_one hH (M.mul_mem (hEM m₁ hm₁) (hEM m hm)) hk'
    exact hinner (m₁ * m) (E.mul_mem hm₁ hm) (T₁ * T) hTT ⟨k, hTk⟩ hI
  by_cases hE1 : E ≤ Lgen M (LB M Q B)
  · rw [inf_eq_left.mpr hE1]
    omega
  · obtain ⟨m₁, hm₁E, hm₁⟩ : ∃ m₁ ∈ E, m₁ ∉ Lgen M (LB M Q B) := by
      by_contra hcon
      push Not at hcon
      exact hE1 hcon
    have hsub : (E : Set G) ⊆ ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G) ∪
        (fun x => m₁⁻¹ * x) '' ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G) := by
      intro m hm
      by_cases hmL : m ∈ Lgen M (LB M Q B)
      · exact Or.inl ⟨hm, hmL⟩
      · refine Or.inr ⟨m₁ * m, ⟨E.mul_mem hm₁E hm, hmul m₁ hm₁E m hm hm₁ hmL⟩, ?_⟩
        simp
    have h1 : Nat.card ↥E ≤ ((E : Set G)).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact le_refl _
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 := Set.ncard_union_le ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G)
      ((fun x => m₁⁻¹ * x) '' ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G))
    have h4 := Set.ncard_image_le (f := fun x => m₁⁻¹ * x)
      (Set.toFinite ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G))
    have h5 : Nat.card ↥(E ⊓ Lgen M (LB M Q B)) =
        ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact le_antisymm le_rfl le_rfl
    omega

end CFSG.RankThree.GF2n.Smith81
