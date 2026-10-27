module

public import CFSG.RankThree.GF2n.Stroth80.Sec101FlagHat

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel QF V K γ}

private theorem exists_B_eq_one {b : M₀.E} (hb0 : b ≠ 0) :
    ∃ f₀ : M₀.E, M₀.B f₀ b = 1 := by
  obtain ⟨f, hf⟩ := Tim79.QuadModel.exists_B_ne_zero hb0
  exact ⟨(M₀.B f b)⁻¹ • f, by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩

private theorem FlagData.fix_of_mem_F' {d₀ : M₀.E} {Dd : Submodule K M₀.E}
    {Λd F' : Subgroup (M₀.E ≃ₗ[K] M₀.E)} (hd : FlagData M₀ d₀ Dd Λd)
    {W : AddSubgroup M₀.E} (hF' : F' ≤ Λd) (hF'W : ∀ g ∈ F', ∀ w ∈ W, g w ∈ W)
    (hWDd : ∀ w ∈ W, w ∈ Dd → w = 0) :
    ∀ g ∈ F', ∀ w ∈ W, M₀.B w d₀ = 0 → g w = w :=
  fun g hg w hw hwd => hd.fix_of_perp hWDd (hF' hg) (hF'W g hg) hw hwd

private theorem FlagData.fix_of_mem_E' {c₀ d₀ : M₀.E} {Dc : Submodule K M₀.E}
    {Λc E' F' : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {W : AddSubgroup M₀.E}
    (hc : FlagData M₀ c₀ Dc Λc) (hWDc : ∀ w ∈ W, w ∈ Dc)
    (hcomm : ∀ l ∈ Λc, l ∉ E' → ∀ e ∈ E', ∃ g ∈ F', e = l * g * l⁻¹ * g⁻¹)
    (hgc : ∀ g ∈ F', g c₀ = c₀)
    (hfixW : ∀ g ∈ F', ∀ w ∈ W, M₀.B w d₀ = 0 → g w = w)
    {l₀ : M₀.E ≃ₗ[K] M₀.E} (hl₀ : l₀ ∈ Λc) (hl₀E : l₀ ∉ E') :
    ∀ e ∈ E', ∀ w ∈ W, M₀.B w d₀ = 0 → e w = w := by
  intro e he w hw hwd
  obtain ⟨g, hg, rfl⟩ := hcomm l₀ hl₀ hl₀E e he
  exact hc.comm_apply_eq hl₀ (hgc g hg) (hWDc w hw) (hfixW g hg w hw hwd)

private theorem FlagData.B_hat_eq_zero_of_fix {c₀ d₀ : M₀.E} {Dc : Submodule K M₀.E}
    {Λc E' : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {W : AddSubgroup M₀.E}
    (hc : FlagData M₀ c₀ Dc Λc) {f₀ : M₀.E} (hf₀ : M₀.B f₀ c₀ = 1)
    (hE' : E' ≤ Λc) (hWDc : ∀ w ∈ W, w ∈ Dc)
    (hfix : ∀ e ∈ E', ∀ w ∈ W, M₀.B w d₀ = 0 → e w = w) :
    ∀ e ∈ E', ∀ w ∈ W, M₀.B w d₀ = 0 → M₀.B (e f₀ - f₀) w = 0 := by
  intro e he w hw hwd
  rw [hc.B_hat hf₀ (hE' he) (hWDc w hw)]
  have h1 := hc.sub_eq hf₀ (hE' he) (hWDc w hw)
  rw [hfix e he w hw hwd, sub_self] at h1
  have : flagPsi M₀ f₀ e w = 0 := by
    rcases smul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hc.hb0
  rw [this, neg_zero]

private theorem FlagData.exists_scalar_add_mem_Dc {c₀ d₀ : M₀.E} {Dc Dd : Submodule K M₀.E}
    {Λc Λd E' F' : Subgroup (M₀.E ≃ₗ[K] M₀.E)}
    (hc : FlagData M₀ c₀ Dc Λc) (hd : FlagData M₀ d₀ Dd Λd) (hF' : F' ≤ Λd)
    (hF'N : F' ≤ Subgroup.normalizer (Λc : Set (M₀.E ≃ₗ[K] M₀.E)))
    (hF'Dc : ∀ g ∈ F', ∀ x ∈ Dc, g x ∈ Dc)
    {f₀ x : M₀.E} (hf₀ : M₀.B f₀ c₀ = 1) (hgc : ∀ g ∈ F', g c₀ = c₀)
    (hcomm : ∀ l ∈ Λc, l ∉ E' → ∀ e ∈ E', ∃ g ∈ F', e = l * g * l⁻¹ * g⁻¹)
    {l : M₀.E ≃ₗ[K] M₀.E} (hl : l ∈ Λc) (hlE : l ∉ E')
    (hx : x ∈ Dd) (hlx : l f₀ - f₀ - x ∈ Dc) :
    ∀ e ∈ E', ∃ κ : K, e f₀ - f₀ + κ • d₀ ∈ Dc := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := hcomm l hl hlE e he
  obtain ⟨κ, hκ⟩ := hd.flag3 g (hF' hg) x hx
  refine ⟨κ, ?_⟩
  have hS : g * l⁻¹ * g⁻¹ ∈ Λc :=
    (Subgroup.mem_normalizer_iff.mp (hF'N hg) _).mp (Λc.inv_mem hl)
  have h1 := hc.hat_mul_mem (f₀ := f₀) hl hS
  have h2 := hc.hat_conj_mem hf₀ (Λc.inv_mem hl) (hd.iso g (hF' hg)) (hgc g hg)
    (hF'Dc g hg)
  have h4 := hF'Dc g hg _ (hc.hat_inv_mem (f₀ := f₀) hl)
  have h5 := hF'Dc g hg _ hlx
  have e1 : l * g * l⁻¹ * g⁻¹ = l * (g * l⁻¹ * g⁻¹) := by group
  rw [e1]
  have := Dc.sub_mem (Dc.add_mem (Dc.add_mem (Dc.add_mem h1 hlx) h2) h4) h5
  convert this using 1
  rw [← hκ]
  simp only [map_add, map_sub]
  abel

private theorem FlagData.exists_hat_sub_mem_of_mem_Dd [Finite K]
    {c₀ d₀ : M₀.E} {Dc Dd : Submodule K M₀.E}
    {Λc Λd E' F' : Subgroup (M₀.E ≃ₗ[K] M₀.E)}
    (hc : FlagData M₀ c₀ Dc Λc) (hcinj : ∀ T ∈ Λc, (∀ e ∈ Dc, T e = e) → T = 1)
    (hd : FlagData M₀ d₀ Dd Λd)
    {n : ℕ} (hDc : Module.finrank K Dc = n) (hΛc : Nat.card Λc = Nat.card K ^ (n - 1))
    (hE' : E' ≤ Λc) (hF' : F' ≤ Λd)
    (hF'N : F' ≤ Subgroup.normalizer (Λc : Set (M₀.E ≃ₗ[K] M₀.E)))
    (hF'Dc : ∀ g ∈ F', ∀ x ∈ Dc, g x ∈ Dc)
    {f₀ : M₀.E} (hf₀ : M₀.B f₀ c₀ = 1) (hgc : ∀ g ∈ F', g c₀ = c₀)
    (hcomm : ∀ l ∈ Λc, l ∉ E' → ∀ e ∈ E', ∃ g ∈ F', e = l * g * l⁻¹ * g⁻¹)
    (hq : Nat.card K < Nat.card E')
    {x : M₀.E} (hx : x ∈ Dd) (hxc : M₀.B x c₀ = 0) :
    ∃ e ∈ E', e f₀ - f₀ - x ∈ Dc := by
  obtain ⟨l, hl, hlx⟩ := hc.exists_hat_sub_mem hcinj hf₀ hDc hΛc hxc
  by_cases hlE : l ∈ E'
  · exact ⟨l, hlE, hlx⟩
  exfalso
  have hκ := hc.exists_scalar_add_mem_Dc hd hF' hF'N hF'Dc hf₀ hgc hcomm hl hlE hx hlx
  choose κ hκ using hκ
  have hinj : Function.Injective (fun e : ↥E' => κ e e.2) := by
    intro e e' h
    simp only at h
    apply Subtype.ext
    apply hc.eq_of_hat_sub_mem hcinj hf₀ (hE' e.2) (hE' e'.2)
    have := Dc.sub_mem (hκ e e.2) (hκ e' e'.2)
    rw [h] at this
    convert this using 1
    abel
  have := Nat.card_le_card_of_injective _ hinj
  omega

private theorem FlagData.exists_mem_Dd_B_ne_zero {c₀ d₀ : M₀.E} {Dc Dd : Submodule K M₀.E}
    {Λc Λd : Subgroup (M₀.E ≃ₗ[K] M₀.E)} (hc : FlagData M₀ c₀ Dc Λc)
    (hd : FlagData M₀ d₀ Dd Λd) {W : AddSubgroup M₀.E}
    (hcW : ∀ s : K, s • c₀ ∈ W) (hWDd : ∀ w ∈ W, w ∈ Dd → w = 0) :
    ∃ δ ∈ Dd, M₀.B δ c₀ ≠ 0 := by
  by_contra hall
  push Not at hall
  have hc₀D : c₀ ∈ Dd := hd.hWperp c₀ fun u hu => by
    rw [Tim79.QuadModel.B_comm, hall u hu, neg_zero]
  exact hc.hb0 (hWDd c₀ (by simpa using hcW 1) hc₀D)

private theorem FlagData.exists_smul_c₀_of_mem_W [Finite K]
    {c₀ d₀ : M₀.E} {Dc Dd : Submodule K M₀.E}
    {Λc Λd E' : Subgroup (M₀.E ≃ₗ[K] M₀.E)}
    (hc : FlagData M₀ c₀ Dc Λc) (hd : FlagData M₀ d₀ Dd Λd) {W : AddSubgroup M₀.E}
    (hcW : ∀ s : K, s • c₀ ∈ W) (hWDc : ∀ w ∈ W, w ∈ Dc)
    (hWDd : ∀ w ∈ W, w ∈ Dd → w = 0)
    {f₀ : M₀.E}
    (hDd_hat : ∀ x ∈ Dd, M₀.B x c₀ = 0 → ∃ e ∈ E', e f₀ - f₀ - x ∈ Dc)
    (hBhat_w : ∀ e ∈ E', ∀ w ∈ W, M₀.B w d₀ = 0 → M₀.B (e f₀ - f₀) w = 0)
    {w : M₀.E} (hw : w ∈ W) (hwd : M₀.B w d₀ = 0) :
    ∃ s : K, w = s • c₀ := by
  obtain ⟨δ, hδ, hδc⟩ := hc.exists_mem_Dd_B_ne_zero hd hcW hWDd
  set δ₁ := (M₀.B δ c₀)⁻¹ • δ with hδ₁def
  have hδ₁ : δ₁ ∈ Dd := Dd.smul_mem _ hδ
  have hδ₁c : M₀.B δ₁ c₀ = 1 := by
    rw [hδ₁def, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hδc]
  have hperp : ∀ x ∈ Dd, M₀.B x c₀ = 0 → M₀.B x w = 0 := by
    intro x hx hxc
    obtain ⟨e, he, hex⟩ := hDd_hat x hx hxc
    have h1 := hBhat_w e he w hw hwd
    have h2 : M₀.B (e f₀ - f₀ - x) w = 0 := hc.B_eq_zero hex (hWDc w hw)
    rw [map_sub, LinearMap.sub_apply, h1, zero_sub, neg_eq_zero] at h2
    exact h2
  refine ⟨M₀.B δ₁ w, ?_⟩
  have hw' : w - M₀.B δ₁ w • c₀ ∈ W := W.sub_mem hw (hcW _)
  have hw'D : w - M₀.B δ₁ w • c₀ ∈ Dd := by
    refine hd.hWperp _ fun u hu => ?_
    have hu' : u - M₀.B u c₀ • δ₁ ∈ Dd := Dd.sub_mem hu (Dd.smul_mem _ hδ₁)
    have hu'c : M₀.B (u - M₀.B u c₀ • δ₁) c₀ = 0 := by
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hδ₁c,
        mul_one, sub_self]
    have h1 := hperp _ hu' hu'c
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Tim79.QuadModel.B_comm w u, Tim79.QuadModel.B_comm c₀ u]
    linear_combination -h1
  exact sub_eq_zero.mp (hWDd _ hw' hw'D)

private theorem FlagData.injective_scalar_of_sub_mem {c₀ d₀ : M₀.E}
    {Dd : Submodule K M₀.E} {Λd F' : Subgroup (M₀.E ≃ₗ[K] M₀.E)}
    (hd : FlagData M₀ d₀ Dd Λd)
    (hdinj : ∀ T ∈ Λd, (∀ e ∈ Dd, T e = e) → T = 1)
    {f₁ y : M₀.E} (hf₁ : M₀.B f₁ d₀ = 1) (hyd : M₀.B y d₀ ≠ 0)
    (hF' : F' ≤ Λd) {κ : ↥F' → K}
    (hκ : ∀ g : ↥F', (g : M₀.E ≃ₗ[K] M₀.E) y - y = κ g • c₀) :
    Function.Injective κ := by
  intro g g' h
  apply Subtype.ext
  apply hd.eq_of_hat_sub_mem hdinj hf₁ (hF' g.2) (hF' g'.2)
  have h1 := hd.sub_sub_smul_mem hf₁ (hF' g.2) y
  have h2 := hd.sub_sub_smul_mem hf₁ (hF' g'.2) y
  have h3 : M₀.B y d₀ • (((g : M₀.E ≃ₗ[K] M₀.E) f₁ - f₁) -
      ((g' : M₀.E ≃ₗ[K] M₀.E) f₁ - f₁)) ∈ Dd := by
    have := Dd.sub_mem h2 h1
    rw [hκ g, hκ g', h] at this
    convert this using 1
    rw [smul_sub]
    abel
  have := Dd.smul_mem (M₀.B y d₀)⁻¹ h3
  rwa [smul_smul, inv_mul_cancel₀ hyd, one_smul] at this

theorem FlagData.false_of_two_flags [Finite K] {c₀ d₀ : M₀.E} {Dc Dd : Submodule K M₀.E}
    {Λc Λd E' F' : Subgroup (M₀.E ≃ₗ[K] M₀.E)}
    (hc : FlagData M₀ c₀ Dc Λc) (hcinj : ∀ T ∈ Λc, (∀ e ∈ Dc, T e = e) → T = 1)
    (hd : FlagData M₀ d₀ Dd Λd) (hdinj : ∀ T ∈ Λd, (∀ e ∈ Dd, T e = e) → T = 1)
    {n : ℕ} (hDc : Module.finrank K Dc = n) (hΛc : Nat.card Λc = Nat.card K ^ (n - 1))
    (hE' : E' ≤ Λc) (hF' : F' ≤ Λd)
    (hF'N : F' ≤ Subgroup.normalizer (Λc : Set (M₀.E ≃ₗ[K] M₀.E)))
    (hF'Dc : ∀ g ∈ F', ∀ x ∈ Dc, g x ∈ Dc) (hcd : M₀.B c₀ d₀ = 0)
    (W : AddSubgroup M₀.E) (hcW : ∀ s : K, s • c₀ ∈ W) (hWDc : ∀ w ∈ W, w ∈ Dc)
    (hWDd : ∀ w ∈ W, w ∈ Dd → w = 0) (hy : ∃ y ∈ W, ∀ s : K, y ≠ s • c₀)
    (hF'W : ∀ g ∈ F', ∀ w ∈ W, g w ∈ W)
    (hcomm : ∀ l ∈ Λc, l ∉ E' → ∀ e ∈ E', ∃ g ∈ F', e = l * g * l⁻¹ * g⁻¹)
    (hl : ∃ l ∈ Λc, l ∉ E') (hq : Nat.card K < Nat.card E')
    (hEF : Nat.card E' ≤ Nat.card F') : False := by
  classical
  obtain ⟨f₀, hf₀⟩ := exists_B_eq_one hc.hb0
  obtain ⟨f₁, hf₁⟩ := exists_B_eq_one hd.hb0
  have hfixW := hd.fix_of_mem_F' hF' hF'W hWDd
  have hc₀W : c₀ ∈ W := by simpa using hcW 1
  have hgc : ∀ g ∈ F', g c₀ = c₀ := fun g hg => hfixW g hg c₀ hc₀W hcd
  obtain ⟨l₀, hl₀, hl₀E⟩ := hl
  have hfixE := hc.fix_of_mem_E' hWDc hcomm hgc hfixW hl₀ hl₀E
  have hBhat_w := hc.B_hat_eq_zero_of_fix hf₀ hE' hWDc hfixE
  have hDd_hat : ∀ x ∈ Dd, M₀.B x c₀ = 0 → ∃ e ∈ E', e f₀ - f₀ - x ∈ Dc :=
    fun x hx hxc => hc.exists_hat_sub_mem_of_mem_Dd hcinj hd hDc hΛc hE' hF' hF'N hF'Dc
      hf₀ hgc hcomm hq hx hxc
  have hW_smul_c₀ : ∀ w ∈ W, M₀.B w d₀ = 0 → ∃ s : K, w = s • c₀ :=
    fun w hw hwd => hc.exists_smul_c₀_of_mem_W hd hcW hWDc hWDd hDd_hat hBhat_w hw hwd
  obtain ⟨y, hyW, hyc⟩ := hy
  have hyd : M₀.B y d₀ ≠ 0 := by
    intro h0
    obtain ⟨s, hs⟩ := hW_smul_c₀ y hyW h0
    exact hyc s hs
  have hκ : ∀ g ∈ F', ∃ s : K, g y - y = s • c₀ := fun g hg =>
    hW_smul_c₀ _ (W.sub_mem (hF'W g hg y hyW) hyW) (hd.B_sub_self (hF' hg) y)
  choose κ hκ using hκ
  have hinj : Function.Injective (fun g : ↥F' => κ g g.2) :=
    hd.injective_scalar_of_sub_mem hdinj hf₁ hyd hF' (fun g => hκ g g.2)
  have := Nat.card_le_card_of_injective _ hinj
  omega

end CFSG.RankThree.GF2n.Stroth80
