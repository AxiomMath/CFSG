module

public import CFSG.Quasithin.Background.RonanF13Comb
public import CFSG.Quasithin.Background.RonanF13Eigen

public section

namespace CFSG.Quasithin.RonanF13

open Module

section

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]

private theorem pow_apply_of_mem_eigenspace (g : End K W) {μ : K} {w : W} (hw : g w = μ • w)
    (j : ℕ) : (g ^ j) w = μ ^ j • w := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hw, smul_smul, pow_succ]

private theorem restrict_pow_apply (g : End K W) (W₁ : Submodule K W)
    (hg : ∀ w ∈ W₁, g w ∈ W₁) (j : ℕ) (w : W₁) :
    (((g.restrict hg) ^ j) w : W) = (g ^ j) (w : W) := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih]
    rfl

theorem eigen_frobenius [Module.Finite K W] (hW : Module.finrank K W = 3)
    (g g' β : End K W) (φ : K ≃+* K) (ν : ℕ) (hν : ∀ c, φ c = c ^ ν)
    (ψ : W → W) (hψadd : ∀ v w, ψ (v + w) = ψ v + ψ w)
    (hψsm : ∀ (c : K) w, ψ (c • w) = φ c • ψ w) (hψbij : Function.Bijective ψ)
    (hg : g ^ (Fintype.card K - 1) = 1)
    (hψg : ∀ w, ψ (g w) = β (ψ w)) (hψg' : ∀ w, ψ (g' w) = g (ψ w))
    (hg'sc : ∀ μ : K, ∃ c : K, ∀ w ∈ Module.End.eigenspace g μ, g' w = c • w)
    (r : ℕ) (hr : Odd r)
    (hψr : ∀ w, ψ^[r] (g w) = g (ψ^[r] w)) (hψr' : ∀ (c : K) w, ψ^[r] (c • w) = c • ψ^[r] w)
    (W₁ : Submodule K W) (hW₁ : W₁ ≠ ⊥) (hW₁' : W₁ ≠ ⊤) (hgW₁ : ∀ w ∈ W₁, g w ∈ W₁)
    (hψW₁ : ∀ w ∈ W₁, ψ w ∈ W₁) : β = g ^ ν := by
  classical
  have hψ0 : ψ 0 = 0 := by
    have := hψadd 0 0
    simpa using this
  have hψne : ∀ w, w ≠ 0 → ψ w ≠ 0 := fun w hw h0 =>
    hw (hψbij.1 (h0.trans hψ0.symm))
  have hψrinj : Function.Injective (ψ^[r]) := hψbij.1.iterate r
  have hψrne : ∀ w, w ≠ 0 → ψ^[r] w ≠ 0 := by
    intro w hw h0
    apply hw
    apply hψrinj
    rw [h0]
    have h1 : ∀ j : ℕ, ψ^[j] 0 = 0 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, hψ0]
    exact (h1 r).symm
  set E : K → Submodule K W := fun μ => Module.End.eigenspace g μ with hE
  have hmemE : ∀ μ w, w ∈ E μ ↔ g w = μ • w := fun μ w => Module.End.mem_eigenspace_iff
  have hdecomp : ⨆ μ, E μ = ⊤ := iSup_eigenspace_eq_top_of_pow g hg
  choose c hc using hg'sc
  set π : K → K := fun μ => φ (c μ) with hπ
  have hψE : ∀ μ w, w ∈ E μ → ψ w ∈ E (π μ) := by
    intro μ w hw
    rw [hmemE, ← hψg', hc μ w hw, hψsm]
  set Λ : Finset K := Finset.univ.filter (fun μ => E μ ≠ ⊥) with hΛ
  have hΛmem : ∀ μ, μ ∈ Λ ↔ E μ ≠ ⊥ := by
    intro μ
    simp [hΛ]
  have hnz : ∀ μ, μ ∈ Λ → ∃ w ∈ E μ, w ≠ 0 := fun μ hμ =>
    Submodule.exists_mem_ne_zero_of_ne_bot ((hΛmem μ).mp hμ)
  have hmaps : ∀ μ ∈ Λ, π μ ∈ Λ := by
    intro μ hμ
    obtain ⟨w, hw, hw0⟩ := hnz μ hμ
    rw [hΛmem]
    intro hbot
    have := hψE μ w hw
    rw [hbot] at this
    exact hψne w hw0 (Submodule.mem_bot K |>.mp this)
  have hψiter : ∀ (j : ℕ) μ w, w ∈ E μ → ψ^[j] w ∈ E (π^[j] μ) := by
    intro j
    induction j with
    | zero => intro μ w hw; exact hw
    | succ j ih =>
      intro μ w hw
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hψE _ _ (ih μ w hw)
  have heig_unique : ∀ {a b : K} {v : W}, v ≠ 0 → v ∈ E a → v ∈ E b → a = b := by
    intro a b v hv ha hb
    rw [hmemE] at ha hb
    have : (a - b) • v = 0 := by rw [sub_smul, ← ha, ← hb, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  have hper : ∀ μ ∈ Λ, π^[r] μ = μ := by
    intro μ hμ
    obtain ⟨w, hw, hw0⟩ := hnz μ hμ
    have h1 : ψ^[r] w ∈ E (π^[r] μ) := hψiter r μ w hw
    have h2 : ψ^[r] w ∈ E μ := by
      rw [hmemE, ← hψr, (hmemE μ w).mp hw, hψr']
    exact heig_unique (hψrne w hw0) h1 h2
  have hinj : ∀ x ∈ Λ, ∀ y ∈ Λ, π x = π y → x = y := by
    intro x hx y hy hxy
    obtain ⟨k, hk⟩ := hr
    have hs : ∀ z : K, π^[r] z = π^[2 * k] (π z) := by
      intro z
      rw [hk]
      exact Function.iterate_succ_apply π (2 * k) z
    calc x = π^[r] x := (hper x hx).symm
      _ = π^[2 * k] (π x) := hs x
      _ = π^[2 * k] (π y) := by rw [hxy]
      _ = π^[r] y := (hs y).symm
      _ = y := hper y hy
  have hchoose : ∀ μ : Λ, ∃ w : W, w ∈ E μ ∧ w ≠ 0 := fun μ => by
    obtain ⟨w, hw, hw0⟩ := hnz μ μ.2
    exact ⟨w, hw, hw0⟩
  choose v hvE hv0 using hchoose
  have hli : LinearIndependent K v :=
    (g).eigenvectors_linearIndependent' (fun μ : Λ => (μ : K)) Subtype.val_injective v
      (fun μ => ⟨hvE μ, hv0 μ⟩)
  have hcard : Λ.card ≤ 3 := by
    have := hli.fintype_card_le_finrank
    rw [hW, Fintype.card_coe] at this
    exact this
  set S : Finset K := Λ.filter (fun μ => E μ ⊓ W₁ ≠ ⊥) with hS
  have hSmem : ∀ μ, μ ∈ S ↔ μ ∈ Λ ∧ E μ ⊓ W₁ ≠ ⊥ := by
    intro μ
    simp [hS]
  have hSsub : S ⊆ Λ := Finset.filter_subset _ _
  have hSne : S.Nonempty := by
    have hres : g.restrict hgW₁ ^ (Fintype.card K - 1) = 1 := by
      refine LinearMap.ext fun w => Subtype.ext ?_
      rw [restrict_pow_apply g W₁ hgW₁, hg]
      simp
    have hdec₁ : ⨆ μ, Module.End.eigenspace (g.restrict hgW₁) μ = ⊤ :=
      iSup_eigenspace_eq_top_of_pow _ hres
    obtain ⟨w₁, hw₁, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₁
    obtain ⟨μ, hμ⟩ : ∃ μ, Module.End.eigenspace (g.restrict hgW₁) μ ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      have hbot : ⨆ μ, Module.End.eigenspace (g.restrict hgW₁) μ = ⊥ :=
        iSup_eq_bot.mpr hcon
      have hmem : (⟨w₁, hw₁⟩ : W₁) ∈ (⊤ : Submodule K W₁) := Submodule.mem_top
      rw [← hdec₁, hbot] at hmem
      exact hw₁0 (congrArg Subtype.val (Submodule.mem_bot K |>.mp hmem))
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    have hgu : g (u : W) = μ • (u : W) := by
      have := Module.End.mem_eigenspace_iff.mp hu
      have h2 := congrArg Subtype.val this
      simpa using h2
    have hu0' : (u : W) ≠ 0 := fun h0 => hu0 (Subtype.ext h0)
    refine ⟨μ, (hSmem μ).mpr ⟨(hΛmem μ).mpr ?_, ?_⟩⟩
    · intro hbot
      have : (u : W) ∈ E μ := (hmemE μ _).mpr hgu
      rw [hbot] at this
      exact hu0' ((Submodule.mem_bot K).mp this)
    · intro hbot
      have : (u : W) ∈ E μ ⊓ W₁ := ⟨(hmemE μ _).mpr hgu, u.2⟩
      rw [hbot] at this
      exact hu0' ((Submodule.mem_bot K).mp this)
  have hSinv : ∀ μ ∈ S, π μ ∈ S := by
    intro μ hμ
    obtain ⟨hμΛ, hμW⟩ := (hSmem μ).mp hμ
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμW
    refine (hSmem _).mpr ⟨hmaps μ hμΛ, ?_⟩
    intro hbot
    have : ψ w ∈ E (π μ) ⊓ W₁ := ⟨hψE μ w hw.1, hψW₁ w hw.2⟩
    rw [hbot] at this
    exact hψne w hw0 ((Submodule.mem_bot K).mp this)
  have hSproper : Λ.card = 3 → S ≠ Λ := by
    intro h3 hSΛ
    apply hW₁'
    have hchoose₁ : ∀ μ : Λ, ∃ w : W, w ∈ E μ ∧ w ∈ W₁ ∧ w ≠ 0 := fun μ => by
      have hμS : (μ : K) ∈ S := by rw [hSΛ]; exact μ.2
      obtain ⟨-, hμW⟩ := (hSmem μ).mp hμS
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμW
      exact ⟨w, hw.1, hw.2, hw0⟩
    choose v₁ hv₁E hv₁W hv₁0 using hchoose₁
    have hli₁ : LinearIndependent K v₁ :=
      (g).eigenvectors_linearIndependent' (fun μ : Λ => (μ : K)) Subtype.val_injective v₁
        (fun μ => ⟨hv₁E μ, hv₁0 μ⟩)
    have hcard₁ : Fintype.card Λ = Module.finrank K W := by
      rw [Fintype.card_coe, h3, hW]
    haveI : Nonempty Λ := by
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [h3]; norm_num : 0 < Λ.card)
      exact ⟨⟨x, hx⟩⟩
    have hspan := hli₁.span_eq_top_of_card_eq_finrank hcard₁
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    exact hv₁W μ
  have hfix : ∀ μ ∈ Λ, π μ = μ :=
    odd_perm_fixed Λ S π r hr hmaps hinj hper hcard hSsub hSne hSinv hSproper
  have hkey : ∀ μ w, w ∈ E μ → β (ψ w) = (g ^ ν) (ψ w) := by
    intro μ w hw
    by_cases hbot : E μ = ⊥
    · rw [hbot, Submodule.mem_bot] at hw
      rw [hw, hψ0]
      simp
    · have hμΛ : μ ∈ Λ := (hΛmem μ).mpr hbot
      have hψw : ψ w ∈ E μ := by
        have := hψE μ w hw
        rwa [hfix μ hμΛ] at this
      have h1 : β (ψ w) = μ ^ ν • ψ w := by
        rw [← hψg, (hmemE μ w).mp hw, hψsm, hν]
      rw [h1, pow_apply_of_mem_eigenspace g ((hmemE μ _).mp hψw)]
  refine LinearMap.ext fun u => ?_
  obtain ⟨w, rfl⟩ := hψbij.2 u
  have hw : w ∈ ⨆ μ, E μ := by rw [hdecomp]; exact Submodule.mem_top
  refine Submodule.iSup_induction E (motive := fun w => β (ψ w) = (g ^ ν) (ψ w)) hw
    (fun μ w hw => hkey μ w hw) ?_ ?_
  · rw [hψ0]; simp
  · intro x y hx hy
    rw [hψadd, map_add, map_add, hx, hy]

end

end CFSG.Quasithin.RonanF13
