module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7P2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChCent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.P

open S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem inter_planes (x : orth.W)
    (h : ∀ σ : Perm (Fin 5), orth.act σ⁻¹ x ∈ commW orth (Subgroup.zpowers zStd) ⊤) :
    x = 1 := by
  simp only [mem_commW_zpowers_iff] at h
  revert x
  decide +kernel

@[expose] def f0 (hS : Sit H M S) {γ : Geo H M} (c : Ch.Chart γ) (u : G)
    (hu : ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ) : ↥(Wb γ) →* orth.W :=
  c.π.comp (phiHom hS γ u hu)

theorem f0_apply (hS : Sit H M S) {γ : Geo H M} (c : Ch.Chart γ) (u : G)
    (hu : ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ) (w : ↥(Wb γ)) :
    f0 hS c u hu w = c.π ⟨⁅(w : G), u⁆, hu _ w.2⟩ := rfl

theorem f0_mem_img (hC : Ch.Ctx H M S) {γ : Geo H M} (hγ : vtype γ = false) (c : Ch.Chart γ)
    {u : G} (hu1 : ∀ v ∈ Vn γ, ⁅u, v⁆ = 1) (hu2 : ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ)
    (hpl : ∀ μ ∈ nbrs γ, ∀ δ ∈ nbrs μ, δ ≠ γ → ∀ v ∈ Vn δ, ⁅v, u⁆ ∈ Vn γ ⊓ Vn δ)
    {l : Geo H M} (hl : l ∈ nbrs γ) {w : G} (hw : w ∈ Wl l) :
    ∃ h : w ∈ Wb γ, f0 hC.sit c u hu2 ⟨w, h⟩ ∈ c.img (Ch.Rl γ l) := by
  obtain ⟨h, hmem⟩ := comm_Wl_mem hC hγ hu1 hu2 hpl hl hw
  exact ⟨h, (Ch.Chart.mem_img_iff' c).mpr ⟨_, hmem, rfl⟩⟩

@[expose] def sm {H M : Subgroup G} {γ : Geo H M} (g : ↥(stab γ)) : ↥(H ⊔ M) :=
  ⟨(g : G), stab_le γ g.2⟩

omit [Finite G] in
@[simp] theorem coe_sm {H M : Subgroup G} {γ : Geo H M} (g : ↥(stab γ)) : ((sm g : ↥(H ⊔ M)) : G) =
    (g : G) := rfl

theorem img_Rl_smul (hC : Ch.Ctx H M S) {γ : Geo H M} (hγ : vtype γ = false) (c : Ch.Chart γ)
    (g : ↥(stab γ)) {l : Geo H M} (hl : l ∈ nbrs γ) :
    c.img (Ch.Rl γ (sm g • l)) = mp (c.θ g) (c.img (Ch.Rl γ l)) := by
  have hl' : sm g • l ∈ nbrs γ := Std.smul_mem_nbrs_of_stab (g := sm g) g.2 hl
  have hD := c.card_Dl hC.sit hl
  have hDs : c.Dl (sm g • l) = cj (c.θ g) (c.Dl l) := c.Dl_smul (g := sm g) g.2 l
  rw [c.img_Rl hC hγ hl', c.img_Rl hC hγ hl, hDs]
  have hz : zc (cj (c.θ g) (c.Dl l)) = c.θ g * zc (c.Dl l) * (c.θ g)⁻¹ := by
    refine zc_eq (by rw [card_cj]; exact hD) (isCentInv_cj_iff.mpr ?_)
    have : (c.θ g)⁻¹ * (c.θ g * zc (c.Dl l) * (c.θ g)⁻¹) * c.θ g = zc (c.Dl l) := by group
    rw [this]
    exact isCentInv_zc hD
  rw [hz, ← cj_zpowers, commW_cj_top]

theorem eq_one_of_mem_all_img (hC : Ch.Ctx H M S) {γ : Geo H M} (hγ : vtype γ = false)
    (c : Ch.Chart γ) {l₀ : Geo H M} (hl₀ : l₀ ∈ nbrs γ) (hD : c.Dl l₀ = S5Syl) {x : orth.W}
    (hx : ∀ l ∈ nbrs γ, x ∈ c.img (Ch.Rl γ l)) : x = 1 := by
  apply inter_planes
  intro σ
  obtain ⟨g, hg⟩ := c.surj σ
  have h1 := hx _ (Std.smul_mem_nbrs_of_stab (g := sm g) g.2 hl₀)
  rw [img_Rl_smul hC hγ c g hl₀, hg, mem_mp, c.img_Rl hC hγ hl₀, hD] at h1
  have hz : zc S5Syl = zStd := zc_eq card_S5Syl ((isCentInv_std_iff zStd).mpr rfl)
  rw [hz] at h1
  exact h1

end S35.G7.P

end F53.Stellmacher

end CFSG.Quasithin
