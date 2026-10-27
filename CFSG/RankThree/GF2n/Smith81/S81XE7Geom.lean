module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Fin
public import CFSG.RankThree.GF2n.Smith81.S81XE7Pf
public import CFSG.RankThree.GF2n.Smith81.S81XE7Nrm
public import CFSG.RankThree.GF2n.Smith81.S81XE7Mon
public import CFSG.RankThree.GF2n.Smith81.S81WGeomE7
public import CFSG.RankThree.GF2n.Smith81.S81XCore

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

@[expose] def betaL (K : Type) [Field K] : V K →ₗ[K] V K →ₗ[K] K :=
  LinearMap.mk₂ K (beta (K := K)) beta_add_left
    (fun c x y => by simpa only [smul_eq_mul] using beta_smul_left c x y) beta_add_right
    (fun c x y => by simpa only [smul_eq_mul] using beta_smul_right c x y)

theorem betaL_apply (x y : V K) : betaL K x y = beta x y := rfl

@[expose] def ιV (K : Type) [Field K] : Gp K →* (V K ≃ₗ[K] V K) :=
  (vAut K).toMonoidHom.comp (e7Data_valid.minGroup K).subtype

theorem ιV_injective : Function.Injective (ιV K) :=
  (vAut K).injective.comp Subtype.val_injective

theorem mem_EAut_iff_range {g : V K ≃ₗ[K] V K} : g ∈ EAut K ↔ ∃ g₀ : Gp K, ιV K g₀ = g := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  · rintro ⟨g₀, rfl⟩
    exact ⟨g₀.1, g₀.2, rfl⟩

theorem ιV_mem_EAut (g₀ : Gp K) : ιV K g₀ ∈ EAut K := mem_EAut_iff_range.2 ⟨g₀, rfl⟩

theorem rootRad7_eq : rootRad7 K = (UA K a7).map (ιV K) := by
  rw [UA, MonoidHom.map_closure, rootRad7]
  congr 1
  ext g
  constructor
  · rintro ⟨γ, hγ, h1, c, rfl⟩
    exact ⟨xE γ c, ⟨γ, mem_Phi.2 ⟨hγ, h1⟩, c, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, (mem_Phi.1 hγ).1, (mem_Phi.1 hγ).2, c, rfl⟩

theorem endoE_inv_endoE (g : Gp K) (x : V K) : endoE g⁻¹ (endoE g x) = x := by
  rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]

theorem endoE_endoE_inv (g : Gp K) (x : V K) : endoE g (endoE g⁻¹ x) = x := by
  rw [← Module.End.mul_apply, e7Data_valid.endo_mul_inv, Module.End.one_apply]

variable [CharP K 2]

theorem w0_ne_zero : (w0 : V K) ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero

set_option maxRecDepth 20000 in
theorem single_mem_W0_iff (b : Fin e7Data.d) :
    (Finsupp.single b 1 : V K) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) ↔ NearW a7 b := by
  rw [rootRad7, mem_Wsp_closure_iff (rootSet7_fix (K := K))]
  constructor
  · intro h γ hγ h1 h2
    have h3 := h (vAut K (e7Data_valid.xu K γ 1)) ⟨γ, hγ, h1, 1, rfl⟩
    rw [vAut_apply, e7Data_valid.xu_apply, add_sub_cancel_left, one_smul, rootOp_single hγ,
      if_pos h2] at h3
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h3
    have h4 := congrArg (fun f : V K => f (shift γ b)) ht
    have h5 : shift γ b = a7 := by
      by_contra hne
      simp only [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hne), if_true,
        smul_eq_mul, mul_zero] at h4
      exact zero_ne_one h4
    have := wt_shift hγ h2
    rw [h5] at this
    exact this
  · rintro h s ⟨γ, hγ, h1, c, rfl⟩
    rw [vAut_apply, e7Data_valid.xu_apply, add_sub_cancel_left, rootOp_single hγ]
    by_cases h2 : pr b γ = -1
    · rw [if_pos h2, shift_eq (h γ hγ h1 h2).symm.symm]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    · rw [if_neg h2, smul_zero]
      exact Submodule.zero_mem _

theorem bor_line {b : Gp K} (hb : b ∈ Bor K) :
    ∃ c : K, c ≠ 0 ∧ endoE b (w0 : V K) = c • w0 := by
  obtain ⟨c, hc⟩ := endo_bor_w0 hb
  refine ⟨c, ?_, hc⟩
  rintro rfl
  have h1 := endoE_inv_endoE b (w0 : V K)
  rw [hc, zero_smul, map_zero] at h1
  exact w0_ne_zero h1.symm

theorem W0_map_of_bor {b : Gp K} (hb : b ∈ Bor K) {v : V K}
    (hv : v ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K)) :
    endoE b v ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) := by
  intro u hu
  rw [rootRad7_eq] at hu
  obtain ⟨u₁, hu₁, rfl⟩ := Subgroup.mem_map.1 hu
  have hmem : ιV K (b⁻¹ * u₁ * b) ∈ rootRad7 K := by
    rw [rootRad7_eq]
    refine Subgroup.mem_map.2 ⟨b⁻¹ * u₁ * b, ?_, rfl⟩
    have := conj_UA_bor7 (inv_mem hb) u₁ hu₁
    simpa using this
  have h1 := hv _ hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨c, hc0, hc⟩ := bor_line hb
  have h2 : ιV K u₁ (endoE b v) - endoE b v = endoE b (ιV K (b⁻¹ * u₁ * b) v - v) := by
    rw [map_sub]
    congr 1
    show endoE u₁ (endoE b v) = endoE b (endoE b⁻¹ (endoE u₁ (endoE b v)))
    rw [endoE_endoE_inv]
  rw [h2, ← ht, map_smul, hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem line_nf {g₀ b₁ b₂ n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (hb₂ : b₂ ∈ Bor K)
    (hn : IsMon n σ ρ) (hg : g₀ = b₁ * n * b₂) :
    ∃ κ : K, κ ≠ 0 ∧ endoE g₀ (w0 : V K) = κ • endoE b₁ (Finsupp.single (σ a7) 1) := by
  obtain ⟨c, hc0, hc⟩ := bor_line hb₂
  refine ⟨c, hc0, ?_⟩
  rw [hg]
  show endoE b₁ (endoE n (endoE b₂ w0)) = _
  rw [hc, map_smul, map_smul]
  have h1 := hn.weight a7
  rw [show (w0 : V K) = Finsupp.single a7 1 from rfl, h1]

theorem conj_UA7_of_line {g₀ : Gp K} {c : K} (hc : c ≠ 0) (h : endoE g₀ (w0 : V K) = c • w0) :
    ∀ x ∈ UA K a7, g₀ * x * g₀⁻¹ ∈ UA K a7 := by
  obtain ⟨b₁, hb₁, b₂, hb₂, n, σ, ρ, hn, hg⟩ := bruhat_mon g₀
  obtain ⟨κ, hκ, hnf⟩ := line_nf hb₂ hn hg
  have hσ : σ a7 = a7 := by
    obtain ⟨c', hc', hb1⟩ := bor_line (inv_mem hb₁)
    have h0 : κ • endoE b₁ (Finsupp.single (σ a7) 1) = c • (w0 : V K) := hnf.symm.trans h
    have h1 : endoE b₁ (Finsupp.single (σ a7) 1) = (κ⁻¹ * c) • (w0 : V K) := by
      rw [mul_smul, ← h0, smul_smul, inv_mul_cancel₀ hκ, one_smul]
    have h2 : Finsupp.single (σ a7) (1 : K) = ((κ⁻¹ * c) * c') • (w0 : V K) := by
      have := congrArg (endoE b₁⁻¹) h1
      rw [endoE_inv_endoE, map_smul, hb1, smul_smul] at this
      exact this
    by_contra hne
    have hL : (Finsupp.single (σ a7) (1 : K) : V K) (σ a7) = 1 := Finsupp.single_eq_same
    rw [h2] at hL
    have hR : (((κ⁻¹ * c) * c') • (w0 : V K)) (σ a7) = 0 := by
      rw [Finsupp.smul_apply, show (w0 : V K) = Finsupp.single a7 1 from rfl, Finsupp.single_apply,
        if_neg (Ne.symm hne), smul_zero]
    rw [hR] at hL
    exact zero_ne_one hL
  intro x hx
  have e : g₀ * x * g₀⁻¹ = b₁ * (n * (b₂ * x * b₂⁻¹) * n⁻¹) * b₁⁻¹ := by
    rw [hg]
    group
  rw [e]
  have h3 := conj_UA_bor7 hb₂ x hx
  have h4 := hn.conj_UA a7 _ h3
  rw [hσ] at h4
  exact conj_UA_bor7 hb₁ _ h4

theorem conj_rootRad_of_line {h : V K ≃ₗ[K] V K} (hh : h ∈ EAut K) {c : K} (hc : c ≠ 0)
    (hw : h (w0 : V K) = c • w0) : ∀ x ∈ rootRad7 K, h * x * h⁻¹ ∈ rootRad7 K := by
  obtain ⟨g₀, rfl⟩ := mem_EAut_iff_range.1 hh
  intro x hx
  rw [rootRad7_eq] at hx ⊢
  obtain ⟨x₁, hx₁, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨g₀ * x₁ * g₀⁻¹, conj_UA7_of_line hc hw x₁ hx₁, ?_⟩
  simp only [map_mul, map_inv]

theorem e7_U_norm : ∀ h ∈ EAut K, (∃ c : K, c ≠ 0 ∧ h (w0 : V K) = c • w0) →
    conjSub h (rootRad7 K) = rootRad7 K := by
  rintro h hh ⟨c, hc, hw⟩
  have hw' : h⁻¹ (w0 : V K) = c⁻¹ • w0 := by
    have h1 : h (c⁻¹ • (w0 : V K)) = w0 := by
      rw [map_smul, hw, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 := congrArg (fun v => h⁻¹ v) h1
    simp only [LinearEquiv.coe_inv] at h2 ⊢
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  apply le_antisymm
  · intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := mem_conjSub.1 hu
    exact conj_rootRad_of_line hh hc hw u₀ hu₀
  · intro u hu
    refine mem_conjSub.2 ⟨h⁻¹ * u * h, ?_, by group⟩
    have := conj_rootRad_of_line (inv_mem hh) (inv_ne_zero hc) hw' u hu
    simpa using this

theorem special_nf {g₀ b₁ b₂ n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (hb₁ : b₁ ∈ Bor K) (hb₂ : b₂ ∈ Bor K)
    (hn : IsMon n σ ρ) (hg : g₀ = b₁ * n * b₂)
    (hsp : SpecialAt (betaL K) (w0 : V K) (rootRad7 K) (ιV K g₀)) : SpecW a7 (σ a7) := by
  obtain ⟨κ, hκ, hnf⟩ := line_nf hb₂ hn hg
  obtain ⟨hβ, hW⟩ := hsp
  have hgw : (ιV K g₀) (w0 : V K) = κ • endoE b₁ (Finsupp.single (σ a7) 1) := hnf
  constructor
  · intro hnear
    apply hW
    rw [hgw]
    exact Submodule.smul_mem _ _ (W0_map_of_bor hb₁ ((single_mem_W0_iff _).2 hnear))
  · intro hopp
    obtain ⟨c', hc', hb1⟩ := bor_line (inv_mem hb₁)
    have h1 : beta (w0 : V K) (endoE b₁ (Finsupp.single (σ a7) 1)) = c' := by
      have e := E_isometry (K := K) (g := (b₁ : (Module.End K (V K))ˣ)) b₁.2 (endoE b₁⁻¹ w0)
        (Finsupp.single (σ a7) 1)
      have e2 : ((b₁ : (Module.End K (V K))ˣ) : Module.End K (V K)) (endoE b₁⁻¹ w0) = w0 :=
        endoE_endoE_inv b₁ w0
      rw [e2] at e
      rw [e, hb1, beta_smul_left, show (w0 : V K) = Finsupp.single a7 1 from rfl, beta_single, hopp]
      simp
    rw [hgw] at hβ
    change beta (w0 : V K) (κ • endoE b₁ (Finsupp.single (σ a7) 1)) = 0 at hβ
    rw [beta_smul_right, h1] at hβ
    exact mul_ne_zero hκ hc' hβ

theorem e7_lemmaT : ∀ g ∈ EAut K, SpecialAt (betaL K) (w0 : V K) (rootRad7 K) g →
    ∀ u ∈ rootRad7 K ⊓ conjSub g (rootRad7 K), u ≠ 1 → IsRootElt ((vAut K).symm u) := by
  intro g hg hsp u hu hu1
  obtain ⟨g₀, rfl⟩ := mem_EAut_iff_range.1 hg
  obtain ⟨b₁, hb₁, b₂, hb₂, n, σ, ρ, hn, hgeq⟩ := bruhat_mon g₀
  have hspec : SpecW a7 (σ a7) := special_nf hb₁ hb₂ hn hgeq hsp
  obtain ⟨huU, huC⟩ := hu
  rw [rootRad7_eq] at huU
  obtain ⟨u₁, hu₁, rfl⟩ := Subgroup.mem_map.1 huU
  obtain ⟨u₀, hu₀, hu₀eq⟩ := mem_conjSub.1 huC
  rw [rootRad7_eq] at hu₀
  obtain ⟨u₂, hu₂, rfl⟩ := Subgroup.mem_map.1 hu₀
  have hu12 : u₁ = g₀ * u₂ * g₀⁻¹ := by
    apply ιV_injective
    rw [map_mul, map_mul, map_inv]
    exact hu₀eq.symm
  have hy7 : b₁⁻¹ * u₁ * b₁ ∈ UA K a7 := by
    have := conj_UA_bor7 (inv_mem hb₁) u₁ hu₁
    simpa using this
  have hyσ : b₁⁻¹ * u₁ * b₁ ∈ UA K (σ a7) := by
    have e : b₁⁻¹ * u₁ * b₁ = n * (b₂ * u₂ * b₂⁻¹) * n⁻¹ := by
      rw [hu12, hgeq]
      group
    rw [e]
    exact hn.conj_UA a7 _ (conj_UA_bor7 hb₂ u₂ hu₂)
  have hU : ∀ γ γ' : Fin (Tag.rank .E7) → ℤ, γ ∈ Phi a7 → γ ∈ Phi (σ a7) → γ' ∈ Phi a7 →
      γ' ∈ Phi (σ a7) → γ = γ' := by
    intro γ γ' h1 h2 h3 h4
    obtain ⟨hr1, hp1⟩ := mem_Phi.1 h1
    obtain ⟨-, hp2⟩ := mem_Phi.1 h2
    obtain ⟨hr3, hp3⟩ := mem_Phi.1 h3
    obtain ⟨-, hp4⟩ := mem_Phi.1 h4
    exact spec_unique (σ a7) hspec γ γ' hr1 hr3 hp1 hp2 hp3 hp4
  rcases UA_inf_UA hU _ ⟨hy7, hyσ⟩ with h1 | ⟨δ, c, hδ, hc, h2⟩
  · exfalso
    apply hu1
    have h3 : u₁ = 1 := by
      have e : u₁ = b₁ * (b₁⁻¹ * u₁ * b₁) * b₁⁻¹ := by group
      rw [e, h1]
      group
    rw [h3, map_one]
  · have hu1e : u₁ = b₁ * xE δ c * b₁⁻¹ := by
      rw [← h2]
      group
    refine ⟨(b₁ : (Module.End K (V K))ˣ), b₁.2, δ, c, hδ, hc, ?_⟩
    rw [hu1e]
    exact (vAut K).symm_apply_apply _

theorem e7_lemmaS : ∀ g ∈ EAut K, SpecialAt (betaL K) (w0 : V K) (rootRad7 K) g →
    ∃ h₁ ∈ EAut K, ∃ h₂ ∈ EAut K,
      h₁ (w0 : V K) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) ∧
      h₂ (w0 : V K) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) ∧
      g⁻¹ (h₁ (w0 : V K)) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) ∧
      g⁻¹ (h₂ (w0 : V K)) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) ∧
      SpecialAt (betaL K) (w0 : V K) (rootRad7 K) (h₁⁻¹ * h₂) := by
  intro g hg hsp
  obtain ⟨g₀, rfl⟩ := mem_EAut_iff_range.1 hg
  obtain ⟨b₁, hb₁, b₂, hb₂, n, σ, ρ, hn, hgeq⟩ := bruhat_mon g₀
  have hspec : SpecW a7 (σ a7) := special_nf hb₁ hb₂ hn hgeq hsp
  obtain ⟨c₁, c₂, h1, h2, h3, h4, h5, h6⟩ := spec_witness (σ a7) hspec
  obtain ⟨m₁, τ₁, ρ₁, hm₁, hτ₁⟩ := exists_isMon_of_weight (K := K) c₁
  obtain ⟨m₂, τ₂, ρ₂, hm₂, hτ₂⟩ := exists_isMon_of_weight (K := K) c₂
  have hw1 : endoE m₁ (w0 : V K) = Finsupp.single c₁ 1 := by
    rw [show (w0 : V K) = Finsupp.single a7 1 from rfl, hm₁.weight a7, hτ₁]
  have hw2 : endoE m₂ (w0 : V K) = Finsupp.single c₂ 1 := by
    rw [show (w0 : V K) = Finsupp.single a7 1 from rfl, hm₂.weight a7, hτ₂]
  have hpre : ∀ c : Fin e7Data.d, NearW (σ a7) c → ∀ v : V K, v = endoE n⁻¹ (Finsupp.single c 1) →
      v ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) := by
    intro c hc v hv
    obtain ⟨x, rfl⟩ := hn.sigma_surjective c
    rw [hv, hn.endo_inv_single]
    exact (single_mem_W0_iff x).2 ((hn.nearW_iff a7 x).1 hc)
  have hcol : ∀ (c : Fin e7Data.d) (m : Gp K) (τ : Fin e7Data.d → Fin e7Data.d) (ρ'),
      IsMon m τ ρ' → τ a7 = c → NearW a7 c → NearW (σ a7) c →
      (ιV K (b₁ * m)) (w0 : V K) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) ∧
      (ιV K g₀)⁻¹ ((ιV K (b₁ * m)) (w0 : V K)) ∈
        Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) := by
    intro c m τ ρ' hm hτ hc1 hc2
    have hwm : endoE m (w0 : V K) = Finsupp.single c 1 := by
      rw [show (w0 : V K) = Finsupp.single a7 1 from rfl, hm.weight a7, hτ]
    constructor
    · show endoE b₁ (endoE m (w0 : V K)) ∈ _
      rw [hwm]
      exact W0_map_of_bor hb₁ ((single_mem_W0_iff c).2 hc1)
    · have e : (ιV K g₀)⁻¹ ((ιV K (b₁ * m)) (w0 : V K)) =
          endoE b₂⁻¹ (endoE n⁻¹ (endoE m (w0 : V K))) := by
        have e1 : g₀⁻¹ * (b₁ * m) = b₂⁻¹ * n⁻¹ * m := by
          rw [hgeq]
          group
        have e2 : (ιV K g₀)⁻¹ ((ιV K (b₁ * m)) (w0 : V K)) = ιV K (g₀⁻¹ * (b₁ * m)) (w0 : V K) := rfl
        rw [e2, e1]
        rfl
      rw [e, hwm]
      exact W0_map_of_bor (inv_mem hb₂) (hpre c hc2 _ rfl)
  obtain ⟨hA1, hA2⟩ := hcol c₁ m₁ τ₁ ρ₁ hm₁ hτ₁ h1 h3
  obtain ⟨hB1, hB2⟩ := hcol c₂ m₂ τ₂ ρ₂ hm₂ hτ₂ h2 h4
  refine ⟨ιV K (b₁ * m₁), ιV_mem_EAut _, ιV K (b₁ * m₂), ιV_mem_EAut _, hA1, hB1, hA2, hB2, ?_⟩
  have hprod : (ιV K (b₁ * m₁))⁻¹ * ιV K (b₁ * m₂) = ιV K (m₁⁻¹ * m₂) := by
    rw [← map_inv, ← map_mul]
    congr 1
    group
  rw [hprod]
  obtain ⟨x₁, hx₁⟩ := hm₁.sigma_surjective c₂
  have hv : (ιV K (m₁⁻¹ * m₂)) (w0 : V K) = Finsupp.single x₁ 1 := by
    show endoE m₁⁻¹ (endoE m₂ (w0 : V K)) = _
    rw [hw2, ← hx₁, hm₁.endo_inv_single]
  rw [SpecialAt, hv]
  constructor
  · show beta (w0 : V K) (Finsupp.single x₁ 1) = 0
    have e := E_isometry (K := K) (g := (m₁ : (Module.End K (V K))ˣ)) m₁.2 (w0 : V K)
      (Finsupp.single x₁ 1)
    have e1 : ((m₁ : (Module.End K (V K))ˣ) : Module.End K (V K)) (w0 : V K) = Finsupp.single c₁ 1 :=
      hw1
    have e2 : ((m₁ : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single x₁ 1) =
        Finsupp.single c₂ 1 := by
      rw [← hx₁]
      exact hm₁.weight x₁
    rw [e1, e2, beta_single, if_neg (Ne.symm h6)] at e
    exact e.symm
  · intro hmem
    have := (single_mem_W0_iff x₁).1 hmem
    have h7 := (hm₁.nearW_iff a7 x₁).2 this
    rw [hτ₁, hx₁] at h7
    exact h5 h7

theorem e7_fe2Geom [Finite K] : Fe2Geom (EAut K) (w0 : V K) (rootRad7 K) (betaL K) 28 where
  geom := e7MinuscGeom
  β_inv := fun g hg v w => by
    obtain ⟨g₀, rfl⟩ := mem_EAut_iff_range.1 hg
    exact E_isometry g₀.2 v w
  β_skew := fun v w => by
    rw [betaL_apply, betaL_apply, beta_comm v w, CharTwo.neg_eq]
  U_card := by
    have h1 := card_UA_ge (K := K) a7
    rw [show (Phi a7).card = 27 from phi7_card] at h1
    have h2 : Nat.card ↥(UA K a7) = Nat.card ↥(rootRad7 K) := by
      rw [rootRad7_eq]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ ιV_injective).toEquiv
    rw [← h2]
    simpa using h1
  U_norm := e7_U_norm
  lemmaS := e7_lemmaS

end CFSG.RankThree.GF2n.Smith81.E7X
