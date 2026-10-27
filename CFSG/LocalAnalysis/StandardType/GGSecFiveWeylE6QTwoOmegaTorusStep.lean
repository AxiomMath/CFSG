module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalEA

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

theorem exists_block_step_of_maximal (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hG : IsRestrClosed B G) {U : Submodule (ZMod 2) V} (hU : Nondeg B U)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEU : E ≤ G ⊓ ptw (B.orthogonal U))
    (hE : IsElemAbelian p E)
    (hmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ F → F ≤ G ⊓ ptw (B.orthogonal U) →
      IsElemAbelian p F → F = E) (hne : E ≠ ⊥) :
    ∃ (b : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V), b ∈ E ∧ IsBlock B b W ∧ W ≤ U ∧
      Nondeg B (U ⊓ B.orthogonal W) ∧
      finrank (ZMod 2) ↥(U ⊓ B.orthogonal W) < finrank (ZMod 2) ↥U ∧
      E ⊓ ptw W ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) ∧
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), E ⊓ ptw W ≤ F →
        F ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) → IsElemAbelian p F →
        F = E ⊓ ptw W) ∧
      E = (E ⊓ ptw W) ⊔ Subgroup.zpowers b ∧ Nat.card E = p * Nat.card ↥(E ⊓ ptw W) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hkey : ∀ k : ℕ, k + k * (p - 1) = p * k := fun k => by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hq, Nat.add_sub_cancel]
    ring
  have hEG : ∀ g ∈ E, g ∈ G := fun g hg => (hEU hg).1
  have hEiso : ∀ g ∈ E, IsIsom B g := fun g hg => hG.1 g (hEG g hg)
  have hEfix : ∀ g ∈ E, ∀ x ∈ B.orthogonal U, g x = x := fun g hg => (hEU hg).2
  have hEp : ∀ g ∈ E, g ^ p = 1 := fun g hg => hE.2 g hg
  have hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh => hE.comm hg hh
  have hEU' : ∀ g ∈ E, ∀ u ∈ U, g u ∈ U := fun g hg u hu =>
    apply_mem_of_ptw hBs hB (hEiso g hg) (hEfix g hg) hu
  have hUc : IsCompl U (B.orthogonal U) := isCompl_of_nondeg hBs hU
  let InS : Submodule (ZMod 2) V → Prop := fun W => W ≤ U ∧ W ≠ ⊥ ∧ Nondeg B W ∧
    (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) ∧ ∀ w ∈ W, (∀ g ∈ E, g w = w) → w = 0
  obtain ⟨e, heE, he1⟩ := (E.bot_or_exists_ne_one).resolve_left hne
  have hS0 : InS (commSp e) := by
    refine ⟨fun w hw => ?_, commSp_ne_bot he1,
      nondeg_commSp hBs hB (hEiso e heE) hpo (hEp e heE),
      fun g hg w hw => commSp_invariant (hEc g hg e heE) hw,
      fun w hw hfix => commSp_fpf hpo (hEp e heE) hw (hfix e heE)⟩
    obtain ⟨v, rfl⟩ := mem_commSp_iff.1 hw
    obtain ⟨u, hu, x, hx, rfl⟩ := exists_add_of_isCompl hUc v
    have : e (u + x) - (u + x) = e u - u := by rw [map_add, hEfix e heE x hx]; abel
    rw [this]
    exact U.sub_mem (hEU' e heE u hu) hu
  have hex : ∃ d, ∃ W, InS W ∧ finrank (ZMod 2) W = d := ⟨_, _, hS0, rfl⟩
  obtain ⟨W, hWS, hWd⟩ := Nat.find_spec hex
  have hmin : ∀ W', InS W' → W' ≤ W → W' = W := fun W' hW' hle =>
    Submodule.eq_of_le_of_finrank_le hle (hWd ▸ Nat.find_min' hex ⟨W', hW', rfl⟩)
  obtain ⟨hWU, hW0, hWnd, hWE, hWC⟩ := hWS
  have hWc : IsCompl W (B.orthogonal W) := isCompl_of_nondeg hBs hWnd
  have hWperpE : ∀ g ∈ E, ∀ x ∈ B.orthogonal W, g x ∈ B.orthogonal W := fun g hg x hx =>
    apply_mem_orth_of_invariant hBs (hEiso g hg) (hWE g hg) hx
  have hA : ∀ g ∈ E, (∃ w ∈ W, g w ≠ w) → ∀ w ∈ W, g w = w → w = 0 := by
    intro g hg hmov
    by_cases h : W ⊓ fixSp g.toLinearMap = ⊥
    · intro w hw hgw
      have hw' : w ∈ W ⊓ fixSp g.toLinearMap := Submodule.mem_inf.2 ⟨hw, mem_fixSp_equiv.2 hgw⟩
      rw [h] at hw'
      exact (Submodule.mem_bot _).1 hw'
    · exfalso
      have hS : InS (W ⊓ fixSp g.toLinearMap) := by
        refine ⟨inf_le_left.trans hWU, h,
          nondeg_inf_fixSp hBs (hEiso g hg) hpo (hEp g hg) hWnd (hWE g hg), ?_, ?_⟩
        · intro g' hg' w hw
          obtain ⟨hwW, hwg⟩ := Submodule.mem_inf.1 hw
          refine Submodule.mem_inf.2 ⟨hWE g' hg' w hwW, mem_fixSp_equiv.2 ?_⟩
          have : g (g' w) = g' (g w) := by
            rw [← LinearEquiv.mul_apply, hEc g hg g' hg', LinearEquiv.mul_apply]
          rw [this, mem_fixSp_equiv.1 hwg]
        · intro w hw hfix
          exact hWC w (Submodule.mem_inf.1 hw).1 hfix
      have heq := hmin _ hS inf_le_left
      obtain ⟨w, hw, hgw⟩ := hmov
      apply hgw
      have hw' : w ∈ W ⊓ fixSp g.toLinearMap := heq.symm ▸ hw
      exact mem_fixSp_equiv.1 (Submodule.mem_inf.1 hw').2
  have hmove : ∃ e₀ ∈ E, ∃ w ∈ W, e₀ w ≠ w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    exact hw0 (hWC w hw fun g hg => hcon g hg w hw)
  have hB' : ∀ e₁ ∈ E, (∃ w ∈ W, e₁ w ≠ w) → ∀ g ∈ E, ∃ k : ℕ, ∀ w ∈ W, g w = (e₁ ^ k) w := by
    intro e₁ he₁ hmov₁ g hg
    by_contra hcon
    push Not at hcon
    apply hW0
    refine eq_bot_of_fpf_pair hp hp2 (hEc g hg e₁ he₁) (hEp g hg) (hEp e₁ he₁) (hWE g hg)
      (hWE e₁ he₁) (hA e₁ he₁ hmov₁) fun k => ?_
    have hgk : g * e₁ ^ k ∈ E := mul_mem hg (pow_mem he₁ k)
    refine hA _ hgk ?_
    by_contra hcon'
    push Not at hcon'
    obtain ⟨w, hw, hne⟩ := hcon (k * (p - 1))
    apply hne
    have h1 : (e₁ ^ k) ((e₁ ^ (k * (p - 1))) w) = w := by
      rw [← LinearEquiv.mul_apply, ← pow_add, hkey k, pow_mul, hEp e₁ he₁, one_pow]
      rfl
    have h2 := hcon' ((e₁ ^ (k * (p - 1))) w) (pow_apply_mem (hWE e₁ he₁) (k * (p - 1)) hw)
    rw [LinearEquiv.mul_apply, h1] at h2
    exact h2
  set K := E ⊓ ptw W with hK
  have hKE : K ≤ E := inf_le_left
  have hdecomp : ∀ e₁ ∈ E, (∃ w ∈ W, e₁ w ≠ w) →
      E = K ⊔ Subgroup.zpowers e₁ ∧ Nat.card E = p * Nat.card K := by
    intro e₁ he₁ hmov₁
    have he₁W : e₁ ∉ ptw W := fun h => by
      obtain ⟨w, hw, hne⟩ := hmov₁
      exact hne (h w hw)
    have he₁1 : e₁ ≠ 1 := fun h => he₁W (h ▸ one_mem _)
    have hEq : E = K ⊔ Subgroup.zpowers e₁ := by
      refine le_antisymm (fun g hg => ?_) (sup_le hKE (Subgroup.zpowers_le.2 he₁))
      obtain ⟨k, hk⟩ := hB' e₁ he₁ hmov₁ g hg
      have hgK : g * e₁ ^ (k * (p - 1)) ∈ K := by
        refine Subgroup.mem_inf.2 ⟨mul_mem hg (pow_mem he₁ _), fun w hw => ?_⟩
        rw [LinearEquiv.mul_apply, hk _ (pow_apply_mem (hWE e₁ he₁) _ hw),
          ← LinearEquiv.mul_apply, ← pow_add, hkey k, pow_mul, hEp e₁ he₁, one_pow]
        rfl
      have : g = g * e₁ ^ (k * (p - 1)) * e₁ ^ k := by
        rw [mul_assoc, ← pow_add, add_comm, hkey k, pow_mul, hEp e₁ he₁, one_pow, mul_one]
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hgK)
        (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers e₁) k))
    refine ⟨hEq, ?_⟩
    have hcomm : ∀ a ∈ K, ∀ c ∈ Subgroup.zpowers e₁, a * c = c * a := fun a ha c hc =>
      hEc a (hKE ha) c (Subgroup.zpowers_le.2 he₁ hc)
    have hinf : K ⊓ Subgroup.zpowers e₁ = ⊥ := by
      rw [eq_bot_iff, ← zpowers_inf_ptw_eq_bot hp (hEp e₁ he₁) he₁W]
      intro x hx
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2⟩
    conv_lhs => rw [hEq]
    rw [card_sup_of_inf_eq_bot hcomm hinf, card_zpowers_of_prime hp (hEp e₁ he₁) he₁1, mul_comm]
  obtain ⟨e₀, he₀E, hmov₀⟩ := hmove
  have hD : ∃ b ∈ E, b ≠ 1 ∧ ∀ x ∈ B.orthogonal W, b x = x := by
    set c := glueE hWc e₀ (hWE e₀ he₀E) with hc
    have hcW : ∀ w ∈ W, c w = e₀ w := fun w hw => glueE_left hWc _ _ hw
    have hcW' : ∀ x ∈ B.orthogonal W, c x = x := fun x hx => glueE_right hWc _ _ hx
    have hcp : c ^ p = 1 := by
      rw [hc, glueE_pow]
      refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
      · rw [glueE_left hWc _ _ hw, hEp e₀ he₀E]
      · rw [glueE_right hWc _ _ hx]; rfl
    have hcptw : c ∉ ptw W := fun h => by
      obtain ⟨w, hw, hne⟩ := hmov₀
      exact hne ((hcW w hw).symm.trans (h w hw))
    have hc1 : c ≠ 1 := fun h => hcptw (h ▸ one_mem _)
    have hUW : B.orthogonal U ≤ B.orthogonal W :=
      LinearMap.BilinForm.orthogonal_le hWU
    have hcG : c ∈ G ⊓ ptw (B.orthogonal U) := by
      refine Subgroup.mem_inf.2 ⟨hG.2 e₀ (hEG e₀ he₀E) W hWnd (hWE e₀ he₀E) c hcW hcW',
        fun x hx => hcW' x (hUW hx)⟩
    have hcomm : ∀ a ∈ E, ∀ d ∈ Subgroup.zpowers c, a * d = d * a := by
      intro a ha d hd
      have h1 : a * c = c * a := by
        refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hcW w hw,
            hcW _ (hWE a ha w hw), ← LinearEquiv.mul_apply, hEc a ha e₀ he₀E,
            LinearEquiv.mul_apply]
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hcW' x hx,
            hcW' _ (hWperpE a ha x hx)]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact ((Commute.zpow_right h1) j).eq
    have hFEA : IsElemAbelian p (E ⊔ Subgroup.zpowers c) :=
      IsElemAbelian.sup_of_commute hE (CFSG.Open.isElemAbelian_zpowers hcp) hcomm
    have hFG : E ⊔ Subgroup.zpowers c ≤ G ⊓ ptw (B.orthogonal U) :=
      sup_le hEU (Subgroup.zpowers_le.2 hcG)
    have hcE : c ∈ E := by
      have h1 := hmax (E ⊔ Subgroup.zpowers c) le_sup_left hFG hFEA
      rw [← h1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    exact ⟨c, hcE, hc1, hcW'⟩
  obtain ⟨b, hbE, hb1, hbW⟩ := hD
  have hbmov : ∃ w ∈ W, b w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hb1 (linearEquiv_ext_of_isCompl hWc (fun w hw => hcon w hw) (fun x hx => hbW x hx))
  have hbfpf := hA b hbE hbmov
  obtain ⟨hEeq, hcardE'⟩ := hdecomp b hbE hbmov
  have hbW' : b ∉ ptw W := fun h => by
    obtain ⟨w, hw, hne⟩ := hbmov
    exact hne (h w hw)
  have hblock : IsBlock B b W := by
    refine ⟨hWnd, hW0, hWE b hbE, hbW, hbfpf, fun W' hle hW'0 hW'nd hW'b => ?_⟩
    refine hmin W' ⟨hle.trans hWU, hW'0, hW'nd, fun g hg w hw => ?_,
      fun w hw hfix => hWC w (hle hw) hfix⟩ hle
    obtain ⟨k, hk⟩ := hB' b hbE hbmov g hg
    rw [hk w (hle hw)]
    exact pow_apply_mem hW'b k hw
  have hU'nd : Nondeg B (U ⊓ B.orthogonal W) := by
    rw [nondeg_iff]
    intro x hx hperp
    have hx' : x ∈ B.orthogonal (U ⊓ B.orthogonal W) := hperp
    rw [orth_inf_orth hBs hB] at hx'
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.1 hx
    have hyU : y ∈ U := by
      have := U.sub_mem hxU (hWU hw)
      simpa using this
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hU) y hyU hy
    subst hy0
    rw [zero_add] at hxW ⊢
    exact (Submodule.disjoint_def.1 hWnd) w hw hxW
  have hU'lt : finrank (ZMod 2) ↥(U ⊓ B.orthogonal W) < finrank (ZMod 2) ↥U := by
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hW0 ?_)
    rw [eq_bot_iff]
    intro w hw
    have hwU' : w ∈ U ⊓ B.orthogonal W := by rw [h]; exact hWU hw
    exact (Submodule.disjoint_def.1 hWnd) w hw (Submodule.mem_inf.1 hwU').2
  have hU'perp := orth_inf_orth hBs hB U W
  have hKsupp : K ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) := by
    intro g hg
    obtain ⟨hgE, hgW⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hEG g hgE, fun x hx => ?_⟩
    rw [hU'perp] at hx
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hEfix g hgE y hy, hgW w hw]
  have hKmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), K ≤ F →
      F ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) → IsElemAbelian p F →
        F = K := by
    intro F hKF hF hFea
    have hFW : ∀ f ∈ F, ∀ w ∈ W, f w = w := fun f hf w hw =>
      (hF hf).2 w (hU'perp ▸ Submodule.mem_sup_right hw)
    have hFU : ∀ f ∈ F, ∀ x ∈ B.orthogonal U, f x = x := fun f hf x hx =>
      (hF hf).2 x (hU'perp ▸ Submodule.mem_sup_left hx)
    have hcomm : ∀ f ∈ F, ∀ d ∈ Subgroup.zpowers b, f * d = d * f := by
      intro f hf d hd
      have hfiso : IsIsom B f := hG.1 f (hF hf).1
      have h1 : f * b = b * f := by
        refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hFW f hf _ (hWE b hbE w hw),
            hFW f hf w hw]
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbW x hx,
            hbW _ (apply_mem_orth_of_ptw hBs hfiso (hFW f hf) hx)]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact ((Commute.zpow_right h1) j).eq
    have hle : F ⊔ Subgroup.zpowers b ≤ G ⊓ ptw (B.orthogonal U) :=
      sup_le (fun f hf => Subgroup.mem_inf.2 ⟨(hF hf).1, hFU f hf⟩)
        (Subgroup.zpowers_le.2 (hEU hbE))
    have hea :=
      IsElemAbelian.sup_of_commute hFea (CFSG.Open.isElemAbelian_zpowers (hEp b hbE)) hcomm
    have hEF : E ≤ F ⊔ Subgroup.zpowers b := by
      rw [hEeq]
      exact sup_le (hKF.trans le_sup_left) le_sup_right
    have h1 := hmax (F ⊔ Subgroup.zpowers b) hEF hle hea
    have hFE : F ≤ E := h1 ▸ le_sup_left
    have hFK : F ≤ K := by
      rw [hK]
      exact le_inf hFE fun f hf => hFW f hf
    exact le_antisymm hFK hKF
  exact ⟨b, W, hbE, hblock, hWU, hU'nd, hU'lt, hKsupp, hKmax, hEeq, hcardE'⟩

end CFSG.StandardType.E6QTwo

end
