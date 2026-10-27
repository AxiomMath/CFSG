module

public import CFSG.RankThree.GF2n.Smith81.S81XD6Mon
public import CFSG.RankThree.GF2n.Smith81.S81XD6Nrm
public import CFSG.RankThree.GF2n.Smith81.S81XD6Rad2
public import CFSG.RankThree.GF2n.Smith81.S81XE7Geom
public import CFSG.RankThree.GF2n.Smith81.S81WGeomD6

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

@[expose] def betaWL (K : Type) [Field K] : W K →ₗ[K] W K →ₗ[K] K :=
  LinearMap.mk₂ K (betaW (K := K))
    (fun x x' y => by simp only [betaW, map_add, beta_add_left])
    (fun c x y => by simp only [betaW, map_smul, beta_smul_left, smul_eq_mul])
    (fun x y y' => by simp only [betaW, map_add, beta_add_right])
    (fun c x y => by simp only [betaW, map_smul, beta_smul_right, smul_eq_mul])

theorem betaWL_apply (x y : W K) : betaWL K x y = betaW x y := rfl

theorem emb_p0 : emb K (p0 K) = (Finsupp.single b0 1 : V K) := emb_single a0 1

variable [CharP K 2]

set_option maxRecDepth 20000 in
theorem single_mem_W0D_iff (a : Idx0) :
    (Finsupp.single a (1 : K) : W K) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) ↔
      NearW b0 (a : Fin e7Data.d) := by
  show (Finsupp.single a (1 : K) : W K) ∈
    Wsp (Submodule.span K {(Finsupp.single a0 1 : W K)}) (rootRad0 K) ↔ _
  rw [rootRad0, EGeom.mem_Wsp_closure_iff (rootSet0_fix (K := K))]
  constructor
  · intro h
    refine (nearP_iff (a : Fin e7Data.d) (mem_idx0.1 a.2)).1 ?_
    intro γ hγ h1 h2
    have h3 := h (vAut0 K (xuWUnit hγ 1)) ⟨γ, hγ, h1, 1, fun w => xuWUnit_induces hγ 1 w⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h3
    have e1 : emb K (vAut0 K (xuWUnit hγ 1) (Finsupp.single a (1 : K)) - Finsupp.single a 1) =
        Finsupp.single (shift γ (a : Fin e7Data.d)) 1 := by
      rw [map_sub, vAut0_apply, xuWUnit_induces hγ 1, emb_single, e7Data_valid.xu_apply, one_smul,
        rootOp_single hγ.1, if_pos h2]
      abel
    have h4 := congrArg (emb K) ht
    rw [map_smul, emb_single, e1] at h4
    have h5 := congrArg (fun f : V K => f (shift γ (a : Fin e7Data.d))) h4
    have h6 : shift γ (a : Fin e7Data.d) = (a0 : Fin e7Data.d) := by
      by_contra hne
      simp only [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hne), if_true, smul_eq_mul,
        mul_zero] at h5
      exact zero_ne_one h5
    have := wt_shift hγ.1 h2
    rw [h6] at this
    exact this
  · intro h s ⟨γ, hγ, h1, c, hs⟩
    have e1 : emb K (s (Finsupp.single a (1 : K)) - Finsupp.single a 1) =
        c • (if pr (a : Fin e7Data.d) γ = -1 then Finsupp.single (shift γ (a : Fin e7Data.d)) 1
          else 0) := by
      rw [map_sub, hs, emb_single, e7Data_valid.xu_apply, rootOp_single hγ.1]
      abel
    by_cases h2 : pr (a : Fin e7Data.d) γ = -1
    · have h3 : shift γ (a : Fin e7Data.d) = (a0 : Fin e7Data.d) := shift_eq (h γ hγ.1 h1 h2)
      have h4 : s (Finsupp.single a (1 : K)) - Finsupp.single a 1 = c • Finsupp.single a0 1 :=
        emb_injective (by rw [e1, if_pos h2, h3, map_smul, emb_single])
      rw [h4]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · have h4 : s (Finsupp.single a (1 : K)) - Finsupp.single a 1 = 0 :=
        emb_injective (by rw [e1, if_neg h2, smul_zero, map_zero])
      rw [h4]
      exact Submodule.zero_mem _

theorem indW_p0_of_ULG {u : Gp K} (hu : u ∈ ULG K) {x : W K ≃ₗ[K] W K} (hx : IndW u x) :
    x (p0 K) = p0 K := by
  apply emb_injective
  rw [hx (p0 K), emb_p0, ULG_fix hu]

theorem W0D_map_of_ULG {u : Gp K} (hu : u ∈ ULG K) {x : W K ≃ₗ[K] W K} (hx : IndW u x) {v : W K}
    (hv : v ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K)) :
    x v ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) := by
  intro ũ hũ
  obtain ⟨y, hyU, hyL, hy⟩ := mem_rootRad0_iff.1 hũ
  have hy' : u⁻¹ * y * u ∈ UA K b0 := by
    have := conj_UA_ULG (inv_mem hu) y hyU
    simpa using this
  have hyL' : u⁻¹ * y * u ∈ LamG K :=
    mul_mem (mul_mem (inv_mem (ULG_le_LamG hu)) hyL) (ULG_le_LamG hu)
  have hind : IndW (u⁻¹ * y * u) (x⁻¹ * ũ * x) := (hx.inv.mul hy).mul hx
  have hũ' : x⁻¹ * ũ * x ∈ rootRad0 K := mem_rootRad0_iff.2 ⟨u⁻¹ * y * u, hy', hyL', hind⟩
  have h1 := hv _ hũ'
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h1
  have e : ũ (x v) - x v = x ((x⁻¹ * ũ * x) v - v) := by
    rw [map_sub]
    congr 1
    show ũ (x v) = x (x⁻¹ (ũ (x v)))
    simp
  rw [e, ← ht, map_smul, indW_p0_of_ULG hu hx]
  exact Submodule.mem_span_singleton.2 ⟨t, rfl⟩

theorem torMon_weight {t₁ t₂ n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (ht₁ : t₁ ∈ Tor K) (ht₂ : t₂ ∈ Tor K)
    (hn : IsMon n σ ρ) (a : Fin e7Data.d) :
    ∃ s : K, s ≠ 0 ∧ endoE (t₁ * n * t₂) (Finsupp.single a 1) = s • Finsupp.single (σ a) 1 := by
  obtain ⟨s₁, hs₁, h₁⟩ := tor_diag ht₁ (σ a)
  obtain ⟨s₂, hs₂, h₂⟩ := tor_diag ht₂ a
  refine ⟨s₂ * s₁, mul_ne_zero hs₂ hs₁, ?_⟩
  show endoE t₁ (endoE n (endoE t₂ (Finsupp.single a 1))) = _
  rw [h₂, map_smul, hn.weight a, map_smul, h₁, smul_smul]

theorem torMon_inv_weight {t₁ t₂ n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (ht₁ : t₁ ∈ Tor K) (ht₂ : t₂ ∈ Tor K)
    (hn : IsMon n σ ρ) (a : Fin e7Data.d) :
    ∃ s : K, s ≠ 0 ∧ endoE (t₁ * n * t₂)⁻¹ (Finsupp.single (σ a) 1) = s • Finsupp.single a 1 := by
  obtain ⟨s₁, hs₁, h₁⟩ := tor_diag (inv_mem ht₁) (σ a)
  obtain ⟨s₂, hs₂, h₂⟩ := tor_diag (inv_mem ht₂) a
  refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
  have e : (t₁ * n * t₂)⁻¹ = t₂⁻¹ * (n⁻¹ * t₁⁻¹) := by group
  rw [e]
  show endoE t₂⁻¹ (endoE n⁻¹ (endoE t₁⁻¹ (Finsupp.single (σ a) 1))) = _
  rw [h₁, map_smul, hn.endo_inv_single a, map_smul, h₂, smul_smul]

theorem conj_UA0_of_line {g₀ : Gp K} (hg : g₀ ∈ LamG K) {c : K} (hc : c ≠ 0)
    (h : endoE g₀ (Finsupp.single b0 1) = c • Finsupp.single b0 1) :
    ∀ x ∈ UA K b0, g₀ * x * g₀⁻¹ ∈ UA K b0 := by
  obtain ⟨u₁, hu₁, t₁, ht₁, t₂, ht₂, u₂, hu₂, n, σ, ρ, hn, hgeq⟩ := bruhat_L hg
  obtain ⟨s, hs, hM⟩ := torMon_weight ht₁ ht₂ hn b0
  have h0 : endoE g₀ (Finsupp.single b0 1) = s • endoE u₁ (Finsupp.single (σ b0) 1) := by
    rw [hgeq]
    show endoE u₁ (endoE (t₁ * n * t₂) (endoE u₂ (Finsupp.single b0 1))) = _
    rw [ULG_fix hu₂, hM, map_smul]
  have hσ : σ b0 = b0 := by
    have h1 : s • endoE u₁ (Finsupp.single (σ b0) 1) = c • Finsupp.single b0 1 := h0.symm.trans h
    have h2 : endoE u₁ (Finsupp.single (σ b0) 1) = (s⁻¹ * c) • (Finsupp.single b0 1 : V K) := by
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hs, one_smul]
    have h3 : (Finsupp.single (σ b0) (1 : K) : V K) = (s⁻¹ * c) • (Finsupp.single b0 1 : V K) := by
      have := congrArg (endoE u₁⁻¹) h2
      rw [endoE_inv_endoE, map_smul, ULG_fix (inv_mem hu₁)] at this
      exact this
    by_contra hne
    have hL : (Finsupp.single (σ b0) (1 : K) : V K) (σ b0) = 1 := Finsupp.single_eq_same
    rw [h3] at hL
    have hR : ((s⁻¹ * c) • (Finsupp.single b0 1 : V K)) (σ b0) = 0 := by
      rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hne), smul_zero]
    rw [hR] at hL
    exact zero_ne_one hL
  intro x hx
  have e : g₀ * x * g₀⁻¹ =
      u₁ * (t₁ * (n * (t₂ * (u₂ * x * u₂⁻¹) * t₂⁻¹) * n⁻¹) * t₁⁻¹) * u₁⁻¹ := by
    rw [hgeq]
    group
  rw [e]
  have h1 := conj_UA_ULG hu₂ x hx
  have h2 := conj_UA_tor b0 ht₂ _ h1
  have h3 := hn.conj_UA b0 _ h2
  rw [hσ] at h3
  exact conj_UA_ULG hu₁ _ (conj_UA_tor b0 ht₁ _ h3)

theorem conj_rootRad0_of_line {h : W K ≃ₗ[K] W K} (hh : h ∈ EAut0 K) {c : K} (hc : c ≠ 0)
    (hw : h (p0 K) = c • p0 K) : ∀ x ∈ rootRad0 K, h * x * h⁻¹ ∈ rootRad0 K := by
  obtain ⟨g₀, hg, hind⟩ := mem_EAut0_iff.1 hh
  have hline : endoE g₀ (Finsupp.single b0 1) = c • Finsupp.single b0 1 := by
    have := hind (p0 K)
    rw [hw, map_smul, emb_p0] at this
    exact this.symm
  intro x hx
  obtain ⟨y, hyU, hyL, hy⟩ := mem_rootRad0_iff.1 hx
  exact mem_rootRad0_iff.2 ⟨g₀ * y * g₀⁻¹, conj_UA0_of_line hg hc hline y hyU,
    mul_mem (mul_mem hg hyL) (inv_mem hg), (hind.mul hy).mul hind.inv⟩

theorem d6_U_norm : ∀ h ∈ EAut0 K, (∃ c : K, c ≠ 0 ∧ h (p0 K) = c • p0 K) →
    conjSub h (rootRad0 K) = rootRad0 K := by
  rintro h hh ⟨c, hc, hw⟩
  have hw' : h⁻¹ (p0 K) = c⁻¹ • p0 K := by
    have h1 : h (c⁻¹ • p0 K) = p0 K := by
      rw [map_smul, hw, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 := congrArg (fun v => h⁻¹ v) h1
    simp only [LinearEquiv.coe_inv] at h2 ⊢
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  apply le_antisymm
  · intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := mem_conjSub.1 hu
    exact conj_rootRad0_of_line hh hc hw u₀ hu₀
  · intro u hu
    refine mem_conjSub.2 ⟨h⁻¹ * u * h, ?_, by group⟩
    have := conj_rootRad0_of_line (inv_mem hh) (inv_ne_zero hc) hw' u hu
    simpa using this

theorem indW_p0_mon {m : Gp K} {τ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (hm : IsMon m τ ρ)
    {x : W K ≃ₗ[K] W K} (hx : IndW m x) (c' : Idx0) (hc : τ b0 = (c' : Fin e7Data.d)) :
    x (p0 K) = Finsupp.single c' 1 := by
  apply emb_injective
  rw [hx (p0 K), emb_p0, hm.weight b0, hc, emb_single]

theorem point_nf {g₀ u₁ u₂ t₁ t₂ n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (hu₂ : u₂ ∈ ULG K) (ht₁ : t₁ ∈ Tor K)
    (ht₂ : t₂ ∈ Tor K) (hn : IsMon n σ ρ) (hg : g₀ = u₁ * (t₁ * n * t₂) * u₂) :
    ∃ s : K, s ≠ 0 ∧
      endoE g₀ (Finsupp.single b0 1) = s • endoE u₁ (Finsupp.single (σ b0) 1) := by
  obtain ⟨s, hs, hM⟩ := torMon_weight ht₁ ht₂ hn b0
  refine ⟨s, hs, ?_⟩
  rw [hg]
  show endoE u₁ (endoE (t₁ * n * t₂) (endoE u₂ (Finsupp.single b0 1))) = _
  rw [ULG_fix hu₂, hM, map_smul]

theorem special_nf_L {g₀ u₁ u₂ t₁ t₂ n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (hg0 : g₀ ∈ LamG K)
    (hu₁ : u₁ ∈ ULG K) (hu₂ : u₂ ∈ ULG K) (ht₁ : t₁ ∈ Tor K) (ht₂ : t₂ ∈ Tor K)
    (hn : IsMon n σ ρ) (hg : g₀ = u₁ * (t₁ * n * t₂) * u₂) {x : W K ≃ₗ[K] W K} (hx : IndW g₀ x)
    (hsp : SpecialAt (betaWL K) (p0 K) (rootRad0 K) x) : pr (σ b0) theta = 0 ∧ SpecW b0 (σ b0) := by
  obtain ⟨s, hs, hnf⟩ := point_nf hu₂ ht₁ ht₂ hn hg
  have hM : t₁ * n * t₂ ∈ LamG K := by
    have e : t₁ * n * t₂ = u₁⁻¹ * g₀ * u₂⁻¹ := by
      rw [hg]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (ULG_le_LamG hu₁)) hg0) (inv_mem (ULG_le_LamG hu₂))
  obtain ⟨s', hs', hM0⟩ := torMon_weight ht₁ ht₂ hn b0
  have hV0 : (Finsupp.single b0 (1 : K) : V K) ∈ V0 K := by
    rw [mem_V0]
    intro b hb
    have hne : b ≠ b0 := fun h => hb (h ▸ mem_idx0.2 pr_b0_theta)
    rw [Finsupp.single_apply, if_neg (Ne.symm hne)]
  have hσ0 : pr (σ b0) theta = 0 := by
    have h1 := Lam_stabilizes_V0 (mem_LamG.1 hM) hV0
    have h2 : endoE (t₁ * n * t₂) (Finsupp.single b0 1) ∈ V0 K := h1
    rw [hM0] at h2
    by_contra hne
    have h3 := (mem_V0.1 h2) (σ b0) (fun h => hne (mem_idx0.1 h))
    rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h3
    exact hs' h3
  refine ⟨hσ0, ?_, ?_⟩
  · intro hnear
    obtain ⟨xu₁, hxu₁⟩ := exists_indW (ULG_le_LamG hu₁)
    have hxp : x (p0 K) = s • xu₁ (Finsupp.single (⟨σ b0, mem_idx0.2 hσ0⟩ : Idx0) 1) := by
      apply emb_injective
      rw [hx (p0 K), emb_p0, hnf, map_smul, hxu₁ _, emb_single]
    apply hsp.2
    rw [hxp]
    exact Submodule.smul_mem _ _ (W0D_map_of_ULG hu₁ hxu₁ ((single_mem_W0D_iff _).2 hnear))
  · intro hopp
    have h1 := hsp.1
    change betaW (p0 K) (x (p0 K)) = 0 at h1
    unfold betaW at h1
    rw [hx (p0 K), emb_p0, hnf, beta_smul_right] at h1
    have h2 : beta (Finsupp.single b0 (1 : K) : V K) (endoE u₁ (Finsupp.single (σ b0) 1)) = 1 := by
      have e := E_isometry (K := K) (g := (u₁ : (Module.End K (V K))ˣ)) u₁.2
        (endoE u₁⁻¹ (Finsupp.single b0 1)) (Finsupp.single (σ b0) 1)
      have e2 : ((u₁ : (Module.End K (V K))ˣ) : Module.End K (V K))
          (endoE u₁⁻¹ (Finsupp.single b0 1)) = Finsupp.single b0 1 := endoE_endoE_inv u₁ _
      rw [e2, ULG_fix (inv_mem hu₁), beta_single, if_pos hopp.symm] at e
      exact e
    rw [h2, mul_one] at h1
    exact hs h1

theorem single_mem_V0_of {b : Fin e7Data.d} (hb : pr b theta = 0) :
    (Finsupp.single b (1 : K) : V K) ∈ V0 K := by
  rw [mem_V0]
  intro b' hb'
  have hne : b' ≠ b := fun h => hb' (h ▸ mem_idx0.2 hb)
  rw [Finsupp.single_apply, if_neg (Ne.symm hne)]

theorem pr_theta_of_smul_single_mem_V0 {a : Fin e7Data.d} {s : K} (hs : s ≠ 0)
    (h : s • (Finsupp.single a (1 : K) : V K) ∈ V0 K) : pr a theta = 0 := by
  by_contra hne
  have h3 := (mem_V0.1 h) a (fun h' => hne (mem_idx0.1 h'))
  rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h3
  exact hs h3

theorem d6_lemmaS : ∀ g ∈ EAut0 K, SpecialAt (betaWL K) (p0 K) (rootRad0 K) g →
    ∃ h₁ ∈ EAut0 K, ∃ h₂ ∈ EAut0 K,
      h₁ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) ∧
      h₂ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) ∧
      g⁻¹ (h₁ (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) ∧
      g⁻¹ (h₂ (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) ∧
      SpecialAt (betaWL K) (p0 K) (rootRad0 K) (h₁⁻¹ * h₂) := by
  intro g hg hsp
  obtain ⟨g₀, hg₀, hind⟩ := mem_EAut0_iff.1 hg
  obtain ⟨u₁, hu₁, t₁, ht₁, t₂, ht₂, u₂, hu₂, n, σ, ρ, hn, hgeq⟩ := bruhat_L hg₀
  obtain ⟨hσ0, hspec⟩ := special_nf_L hg₀ hu₁ hu₂ ht₁ ht₂ hn hgeq hind hsp
  obtain ⟨c₁, c₂, hc₁0, hc₂0, h1, h2, h3, h4, h5, h6⟩ := spec0_witness (σ b0) hσ0 hspec
  obtain ⟨m₁, τ₁, ρ₁, hm₁L, hm₁, hτ₁⟩ := exists_isMonL_of_weight (K := K) c₁ hc₁0
  obtain ⟨m₂, τ₂, ρ₂, hm₂L, hm₂, hτ₂⟩ := exists_isMonL_of_weight (K := K) c₂ hc₂0
  obtain ⟨xu₁, hxu₁⟩ := exists_indW (ULG_le_LamG hu₁)
  obtain ⟨xu₂, hxu₂⟩ := exists_indW (ULG_le_LamG (inv_mem hu₂))
  obtain ⟨xm₁, hxm₁⟩ := exists_indW hm₁L
  obtain ⟨xm₂, hxm₂⟩ := exists_indW hm₂L
  have hM : t₁ * n * t₂ ∈ LamG K := by
    have e : t₁ * n * t₂ = u₁⁻¹ * g₀ * u₂⁻¹ := by
      rw [hgeq]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (ULG_le_LamG hu₁)) hg₀) (inv_mem (ULG_le_LamG hu₂))
  have hcol : ∀ (c : Fin e7Data.d) (m : Gp K) (τ : Fin e7Data.d → Fin e7Data.d)
      (ρ' : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)) (xm : W K ≃ₗ[K] W K),
      pr c theta = 0 → IsMon m τ ρ' → τ b0 = c → IndW m xm → NearW b0 c → NearW (σ b0) c →
      (xu₁ * xm) (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) ∧
      g⁻¹ ((xu₁ * xm) (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) := by
    intro c m τ ρ' xm hc0 hm hτ hxm hn1 hn2
    have hxp : xm (p0 K) = Finsupp.single (⟨c, mem_idx0.2 hc0⟩ : Idx0) 1 :=
      indW_p0_mon hm hxm _ hτ
    constructor
    · show xu₁ (xm (p0 K)) ∈ _
      rw [hxp]
      exact W0D_map_of_ULG hu₁ hxu₁ ((single_mem_W0D_iff _).2 hn1)
    · have hI : IndW (u₂⁻¹ * (t₁ * n * t₂)⁻¹ * m) (g⁻¹ * (xu₁ * xm)) := by
        have e : g₀⁻¹ * (u₁ * m) = u₂⁻¹ * (t₁ * n * t₂)⁻¹ * m := by
          rw [hgeq]
          group
        rw [← e]
        exact hind.inv.mul (hxu₁.mul hxm)
      obtain ⟨x, rfl⟩ := hn.sigma_surjective c
      obtain ⟨s, hs, hMs⟩ := torMon_inv_weight ht₁ ht₂ hn x
      have hv : endoE (t₁ * n * t₂)⁻¹ (Finsupp.single (σ x) 1) ∈ V0 K :=
        Lam_stabilizes_V0 (mem_LamG.1 (inv_mem hM)) (single_mem_V0_of hc0)
      rw [hMs] at hv
      have hx0 : pr x theta = 0 := pr_theta_of_smul_single_mem_V0 hs hv
      have hnx : NearW b0 x := (hn.nearW_iff b0 x).1 hn2
      have e2 : g⁻¹ ((xu₁ * xm) (p0 K)) =
          s • xu₂ (Finsupp.single (⟨x, mem_idx0.2 hx0⟩ : Idx0) 1) := by
        apply emb_injective
        have h1' : emb K ((g⁻¹ * (xu₁ * xm)) (p0 K)) =
            endoE (u₂⁻¹ * (t₁ * n * t₂)⁻¹ * m) (emb K (p0 K)) := hI (p0 K)
        have h2' : emb K (g⁻¹ ((xu₁ * xm) (p0 K))) = _ := h1'
        rw [h2', emb_p0, map_smul, hxu₂ _, emb_single]
        show endoE u₂⁻¹ (endoE (t₁ * n * t₂)⁻¹ (endoE m (Finsupp.single b0 1))) = _
        rw [hm.weight b0, hτ, hMs, map_smul]
      rw [e2]
      exact Submodule.smul_mem _ _ (W0D_map_of_ULG (inv_mem hu₂) hxu₂
        ((single_mem_W0D_iff _).2 hnx))
  obtain ⟨hA1, hA2⟩ := hcol c₁ m₁ τ₁ ρ₁ xm₁ hc₁0 hm₁ hτ₁ hxm₁ h1 h3
  obtain ⟨hB1, hB2⟩ := hcol c₂ m₂ τ₂ ρ₂ xm₂ hc₂0 hm₂ hτ₂ hxm₂ h2 h4
  refine ⟨xu₁ * xm₁, mem_EAut0_iff.2 ⟨u₁ * m₁, mul_mem (ULG_le_LamG hu₁) hm₁L, hxu₁.mul hxm₁⟩,
    xu₁ * xm₂, mem_EAut0_iff.2 ⟨u₁ * m₂, mul_mem (ULG_le_LamG hu₁) hm₂L, hxu₁.mul hxm₂⟩,
    hA1, hB1, hA2, hB2, ?_⟩
  have hI : IndW (m₁⁻¹ * m₂) ((xu₁ * xm₁)⁻¹ * (xu₁ * xm₂)) := by
    have e : (u₁ * m₁)⁻¹ * (u₁ * m₂) = m₁⁻¹ * m₂ := by group
    rw [← e]
    exact (hxu₁.mul hxm₁).inv.mul (hxu₁.mul hxm₂)
  obtain ⟨x₁, hx₁⟩ := hm₁.sigma_surjective c₂
  have hv : endoE m₁⁻¹ (Finsupp.single c₂ 1) = Finsupp.single x₁ 1 := by
    rw [← hx₁, hm₁.endo_inv_single]
  have hx10 : pr x₁ theta = 0 := by
    have h' := Lam_stabilizes_V0 (mem_LamG.1 (inv_mem hm₁L)) (single_mem_V0_of hc₂0)
    have h'' : endoE m₁⁻¹ (Finsupp.single c₂ 1) ∈ V0 K := h'
    rw [hv] at h''
    have := pr_theta_of_smul_single_mem_V0 (K := K) (s := 1) one_ne_zero (by rwa [one_smul])
    exact this
  have hvec : ((xu₁ * xm₁)⁻¹ * (xu₁ * xm₂)) (p0 K) = Finsupp.single (⟨x₁, mem_idx0.2 hx10⟩ : Idx0) 1 := by
    apply emb_injective
    rw [hI (p0 K), emb_p0, emb_single]
    show endoE m₁⁻¹ (endoE m₂ (Finsupp.single b0 1)) = _
    rw [hm₂.weight b0, hτ₂, hv]
  show betaWL K (p0 K) (((xu₁ * xm₁)⁻¹ * (xu₁ * xm₂)) (p0 K)) = 0 ∧
    ((xu₁ * xm₁)⁻¹ * (xu₁ * xm₂)) (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (rootRad0 K)
  rw [hvec]
  constructor
  · change beta (emb K (p0 K)) (emb K (Finsupp.single (⟨x₁, mem_idx0.2 hx10⟩ : Idx0) 1)) = 0
    rw [emb_p0, emb_single]
    have e := E_isometry (K := K) (g := (m₁ : (Module.End K (V K))ˣ)) m₁.2
      (Finsupp.single b0 1) (Finsupp.single x₁ 1)
    have e1 : ((m₁ : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single b0 1) =
        Finsupp.single c₁ 1 := by
      rw [← hτ₁]
      exact hm₁.weight b0
    have e2 : ((m₁ : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single x₁ 1) =
        Finsupp.single c₂ 1 := by
      rw [← hx₁]
      exact hm₁.weight x₁
    rw [e1, e2, beta_single, if_neg (Ne.symm h6)] at e
    exact e.symm
  · intro hmem
    have := (single_mem_W0D_iff _).1 hmem
    have h7 := (hm₁.nearW_iff b0 x₁).2 this
    rw [hτ₁, hx₁] at h7
    exact h5 h7

set_option maxRecDepth 20000 in
theorem d6_lemmaT : ∀ g ∈ EAut0 K, SpecialAt (betaWL K) (p0 K) (rootRad0 K) g →
    ∀ u ∈ rootRad0 K ⊓ conjSub g (rootRad0 K), u ≠ 1 → IsRootEltW ((vAut0 K).symm u) := by
  intro g hg hsp u hu hu1
  obtain ⟨g₀, hg₀, hind⟩ := mem_EAut0_iff.1 hg
  obtain ⟨u₁, hu₁, t₁, ht₁, t₂, ht₂, u₂, hu₂, n, σ, ρ, hn, hgeq⟩ := bruhat_L hg₀
  obtain ⟨hσ0, hspec⟩ := special_nf_L hg₀ hu₁ hu₂ ht₁ ht₂ hn hgeq hind hsp
  obtain ⟨huU, huC⟩ := hu
  obtain ⟨a₁, ha₁U, ha₁L, ha₁⟩ := mem_rootRad0_iff.1 huU
  obtain ⟨w₀, hw₀, hwu⟩ := mem_conjSub.1 huC
  obtain ⟨a₂, ha₂U, ha₂L, ha₂⟩ := mem_rootRad0_iff.1 hw₀
  have hb : IndW (g₀ * a₂ * g₀⁻¹) u := by
    rw [← hwu]
    exact (hind.mul ha₂).mul hind.inv
  have hy7 : u₁⁻¹ * a₁ * u₁ ∈ UA K b0 := by
    have := conj_UA_ULG (inv_mem hu₁) a₁ ha₁U
    simpa using this
  have hyL : u₁⁻¹ * a₁ * u₁ ∈ LamG K :=
    mul_mem (mul_mem (inv_mem (ULG_le_LamG hu₁)) ha₁L) (ULG_le_LamG hu₁)
  have hy'e : u₁⁻¹ * (g₀ * a₂ * g₀⁻¹) * u₁ =
      t₁ * (n * (t₂ * (u₂ * a₂ * u₂⁻¹) * t₂⁻¹) * n⁻¹) * t₁⁻¹ := by
    rw [hgeq]
    group
  have hy'7 : u₁⁻¹ * (g₀ * a₂ * g₀⁻¹) * u₁ ∈ UA K (σ b0) := by
    rw [hy'e]
    have h1 := conj_UA_ULG hu₂ a₂ ha₂U
    have h2 := conj_UA_tor b0 ht₂ _ h1
    have h3 := hn.conj_UA b0 _ h2
    exact conj_UA_tor (σ b0) ht₁ _ h3
  have hy'L : u₁⁻¹ * (g₀ * a₂ * g₀⁻¹) * u₁ ∈ LamG K :=
    mul_mem (mul_mem (inv_mem (ULG_le_LamG hu₁))
      (mul_mem (mul_mem hg₀ ha₂L) (inv_mem hg₀))) (ULG_le_LamG hu₁)
  have hV : ∀ b : Fin e7Data.d, pr b theta = 0 →
      endoE (u₁⁻¹ * a₁ * u₁) (Finsupp.single b 1) =
        endoE (u₁⁻¹ * (g₀ * a₂ * g₀⁻¹) * u₁) (Finsupp.single b 1) := by
    intro b hb0
    have hmem : endoE u₁ (Finsupp.single b 1) ∈ V0 K :=
      Lam_stabilizes_V0 (mem_LamG.1 (ULG_le_LamG hu₁)) (single_mem_V0_of hb0)
    obtain ⟨w, hw⟩ := exists_emb_eq hmem
    show endoE u₁⁻¹ (endoE a₁ (endoE u₁ (Finsupp.single b 1))) =
      endoE u₁⁻¹ (endoE (g₀ * a₂ * g₀⁻¹) (endoE u₁ (Finsupp.single b 1)))
    rw [← hw, ← ha₁ w, ← hb w]
  have hU : ∀ γ γ' : Fin (Tag.rank .E7) → ℤ, γ ∈ Phi b0 → γ ∈ Phi (σ b0) → γ' ∈ Phi b0 →
      γ' ∈ Phi (σ b0) → γ = γ' := by
    intro γ γ' h1 h2 h3 h4
    obtain ⟨hr1, hp1⟩ := mem_Phi.1 h1
    obtain ⟨-, hp2⟩ := mem_Phi.1 h2
    obtain ⟨hr3, hp3⟩ := mem_Phi.1 h3
    obtain ⟨-, hp4⟩ := mem_Phi.1 h4
    exact spec0_unique (σ b0) hσ0 hspec γ γ' hr1 hr3 hp1 hp2 hp3 hp4
  rcases UA_inf_UA_V0 hU hy7 hy'7 hyL hy'L hV with h1 | ⟨δ, c, hδ, hc, h2⟩
  · exfalso
    apply hu1
    have h3 : a₁ = 1 := by
      have e : a₁ = u₁ * (u₁⁻¹ * a₁ * u₁) * u₁⁻¹ := by group
      rw [e, h1]
      group
    rw [h3] at ha₁
    exact indW_one_iff.1 ha₁
  · have hae : a₁ = u₁ * xE δ c * u₁⁻¹ := by
      rw [← h2]
      group
    refine ⟨(u₁ : (Module.End K (V K))ˣ), mem_LamG.1 (ULG_le_LamG hu₁), δ, hδ, c, hc, ?_⟩
    intro w
    have := ha₁ w
    rw [hae] at this
    exact this

theorem d6_fe2Geom [Finite K] : Fe2Geom (EAut0 K) (p0 K) (rootRad0 K) (betaWL K) 16 where
  geom := d6MinuscGeom
  β_inv := fun g hg v w => by
    obtain ⟨g₀, hg₀, hind⟩ := mem_EAut0_iff.1 hg
    show beta (emb K (g v)) (emb K (g w)) = beta (emb K v) (emb K w)
    rw [hind v, hind w]
    exact E_isometry g₀.2 _ _
  β_skew := fun v w => by
    rw [betaWL_apply, betaWL_apply]
    unfold betaW
    rw [beta_comm (emb K v), CharTwo.neg_eq]
  U_card := by simpa using card_rootRad0_ge (K := K)
  U_norm := d6_U_norm
  lemmaS := d6_lemmaS

end CFSG.RankThree.GF2n.Smith81.D6X
