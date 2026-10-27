module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeX
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeTau
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeGlobal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Loc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23ne_fibre_fixed {X V₀ : Subgroup G} {z v : G} (hX : X ≤ centralizer (V₀ : Set G))
    (hzX : ∀ g ∈ X, g * z = z * g) (hvz : v * z⁻¹ ∈ V₀) : ∀ g ∈ X, g * v = v * g := by
  intro g hg
  have hge : g * (v * z⁻¹) = (v * z⁻¹) * g := (Subgroup.mem_centralizer_iff.1 (hX hg) _ hvz).symm
  have hv_eq : v = (v * z⁻¹) * z := by group
  calc g * v = g * ((v * z⁻¹) * z) := by rw [← hv_eq]
    _ = (g * (v * z⁻¹)) * z := by group
    _ = ((v * z⁻¹) * g) * z := by rw [hge]
    _ = (v * z⁻¹) * (g * z) := by group
    _ = (v * z⁻¹) * (z * g) := by rw [hzX g hg]
    _ = ((v * z⁻¹) * z) * g := by group
    _ = v * g := by rw [← hv_eq]

theorem c23ne_cent_le_fibre (D : Data G) (h145 : Thm145 D) (h63 : R16_63 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hsit : Sit1663 D V₀ V hV L) {x : G} {K₁ K₂ X : Subgroup G}
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V) (hV₀V : V₀ ≤ V)
    (hgood : c23neY V K₁ K₂ = V₀ ∨ C23NeSplit V₀ V (c23neY V K₁ K₂) (K₁ ⊔ K₂))
    (hH141 : Hyp141 D K₁ K₂ X) (hXsyl : CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂))
    {y : G} (hyM : y ∈ D.M) (hy7 : orderOf y = 7) (hyV : ∀ v ∈ V, y * v = v * y)
    {z : IntMod V hV}
    (hΩ : mkTil V₀ V hV z ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)))
    (hzX : ∀ g ∈ X, g * z.val = z.val * g)
    (hzN : ∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G), n * z.val * n⁻¹ * (z.val)⁻¹ ∈ V₀)
    {v : G} (hv : v ∈ V) (hvz : v * (z.val)⁻¹ ∈ V₀) : centralizer ({v} : Set G) ≤ D.M := by
  have hv1 : v ≠ 1 := by
    intro h1
    have hz : z.val ∈ V₀ := by
      have h2 : (z.val)⁻¹ ∈ V₀ := by simpa [h1] using hvz
      simpa using V₀.inv_mem h2
    have hz1 : mkTil V₀ V hV z = 1 := by
      show (z : Vtil V₀ V hV) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hz
    rw [hz1] at hΩ
    exact hΩ.1 (Subgroup.one_mem _)
  have hv2 : v ^ 2 = 1 := hV.2 v hv
  have hvX := c23ne_fibre_fixed (hXsyl.le.trans hctx.cent₀) hzX hvz
  refine h145 K₁ K₂ X hH141 (centralizer ({v} : Set G)) ?_ (c23_fstar_centralizer D hv1 hv2)
    (c23ne_odd_relIndex_centralizer D h63 hS hsit hv hv1)
    (c23ne_aut_cond hctx hMs hV₀V hgood hXsyl hΩ hzX hzN hv hvz) ?_
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hvX g hg
  · have hle : Subgroup.zpowers y ≤ centralizer ({v} : Set G) ⊓ D.M := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hyV v hv), hyM⟩
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hy7] at h

theorem c23ne_false_of_good (D : Data G) (hSg : UC6S846.SigmaStd D) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h129 : R129_1 D) (h1217 : R1217 D) (h145 : Thm145 D)
    (h63 : R16_63 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L) (h154 : Hyp154 D V₀ V L) {x : G} {K₁ K₂ : Subgroup G}
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hgood : c23neY V K₁ K₂ = V₀ ∨ C23NeSplit V₀ V (c23neY V K₁ K₂) (K₁ ⊔ K₂)) : False := by
  have h151 := hS.setting.hyp151
  have hP := h151.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  have hsit : Sit1663 D V₀ V hV L := ⟨Or.inl hc, h154⟩
  obtain ⟨z, X, hΩ, hzX, hXsyl, hperm, hzN⟩ := c23ne_exists_X_z hctx hMs
  have hH141 : Hyp141 D K₁ K₂ X := c23ne_hyp141 D hx h115 h127 h1217 hS hc hctx hXsyl hperm
  obtain ⟨y, hyM, hy7, hyV⟩ := c23ne_exists_y0 D hSg h1217 hS hc
  have hfib : ∀ v ∈ V, v * (z.val)⁻¹ ∈ V₀ → centralizer ({v} : Set G) ≤ D.M :=
    fun v hv hvz => c23ne_cent_le_fibre D h145 h63 hS hsit hctx hMs hP.le hgood hH141 hXsyl hyM
      hy7 hyV hΩ hzX hzN hv hvz
  have hcent : ∀ w ∈ V, w ≠ 1 → centralizer ({w} : Set G) ≤ D.M := by
    intro w hw hw1
    by_cases h1 : w ∈ wSub V₀ V hV L
    · exact c23a_cent_union D h154 hctx.hxM (Or.inl h1) hw1
    by_cases h2 : w ∈ conjSubgroup (wSub V₀ V hV L) x
    · exact c23a_cent_union D h154 hctx.hxM (Or.inr h2) hw1
    have h2' : w ∉ wSub V₀ V hV (conjSubgroup L x) := by
      rw [s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hctx.hxM)]
      exact h2
    have hΩw := c23ne_omega_of_generic (L := L) (x := x) hw h1 h2'
    obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := c23_omega_trans hctx.core hΩw hΩ
    obtain ⟨g₁, hg₁M, rfl⟩ := (mem_barSub V₀ V hV D.M a₁).1 (hctx.core.le₁ ha₁)
    obtain ⟨g₂, hg₂M, rfl⟩ := (mem_barSub V₀ V hV D.M b₁).1 (hctx.core.le₂ hb₁)
    rw [actTil_mk, actTil_mk, mkTil_eq_iff, actStab_apply_val, actStab_apply_val] at hab
    have hgM : (g₁ : G) * g₂ ∈ D.M := D.M.mul_mem hg₁M hg₂M
    have hvV : (g₁ : G) * g₂ * w * ((g₁ : G) * g₂)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hP.le_normalizer hgM) w).1 hw
    have hvz : (g₁ : G) * g₂ * w * ((g₁ : G) * g₂)⁻¹ * (z.val)⁻¹ ∈ V₀ := by
      have e : (g₁ : G) * g₂ * w * ((g₁ : G) * g₂)⁻¹ =
          (g₁ : G) * ((g₂ : G) * w * (g₂ : G)⁻¹) * (g₁ : G)⁻¹ := by group
      rw [e]
      exact hab
    intro u hu
    have hu' : ((g₁ : G) * g₂) * u * ((g₁ : G) * g₂)⁻¹ ∈
        centralizer ({(g₁ : G) * g₂ * w * ((g₁ : G) * g₂)⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hu2 : u * w = w * u := Subgroup.mem_centralizer_singleton_iff.1 hu
      calc ((g₁ : G) * g₂) * u * ((g₁ : G) * g₂)⁻¹ * ((g₁ : G) * g₂ * w * ((g₁ : G) * g₂)⁻¹)
          = ((g₁ : G) * g₂) * (u * w) * ((g₁ : G) * g₂)⁻¹ := by group
        _ = ((g₁ : G) * g₂) * (w * u) * ((g₁ : G) * g₂)⁻¹ := by rw [hu2]
        _ = ((g₁ : G) * g₂ * w * ((g₁ : G) * g₂)⁻¹) *
            (((g₁ : G) * g₂) * u * ((g₁ : G) * g₂)⁻¹) := by
          group
    have h3 := hfib _ hvV hvz hu'
    have h4 : u = ((g₁ : G) * g₂)⁻¹ * (((g₁ : G) * g₂) * u * ((g₁ : G) * g₂)⁻¹) *
        ((g₁ : G) * g₂) := by
      group
    rw [h4]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hgM) h3) hgM
  exact h129 V₀ V h151.hyp125 (c23ne_isTI_of_centralizers hV hP.le_normalizer
    (c23ne_sp_seven D hSg hc hctx.mem₁) hyM hy7 hyV hcent)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
