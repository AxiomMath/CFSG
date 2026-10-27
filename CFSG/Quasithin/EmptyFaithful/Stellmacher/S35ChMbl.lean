module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChZl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Mbl (δ l : Geo H M) : Subgroup G := Subgroup.normalizer (Zv l : Set G) ⊓ stab δ

namespace Chart

variable {δ : Geo H M} (c : Chart δ)

@[expose] noncomputable def pt (l : Geo H M) : Fin 5 := fixPt (c.Dl l)

theorem isFixPt_pt (hS : Sit H M S) {l : Geo H M} (hl : l ∈ nbrs δ) :
    IsFixPt (c.Dl l) (c.pt l) := isFixPt_fixPt (c.card_Dl hS hl)

include c

theorem Mbl_eq_preθ (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    Mbl δ l = c.preθ (ptStab (c.pt l)) := by
  set p := c.pt l with hp
  have hZl := Zv_le_Zv_of_nbr hS hδ hl
  have hlV : Zv l ≤ Vn δ := Zv_le_Vn hl
  have himg : c.img (Zv l) = Subgroup.zpowers (vp p) := c.img_Zv_nbr hS hδ hl
  have hmem : ∀ z : ↥(Vn δ), (z : G) ∈ Zv l ↔ c.π z ∈ Subgroup.zpowers (vp p) := fun z => by
    rw [← himg, c.mem_img_iff hZl]
  have hvp : ∀ y ∈ Subgroup.zpowers (vp p), ∀ σ ∈ ptStab p,
      orth.act σ y ∈ Subgroup.zpowers (vp p) := by
    intro y hy σ hσ
    rcases (mem_zpowers_iff_of_mul_self (vp_mul_self p)).mp hy with rfl | rfl
    · rw [map_one]; exact Subgroup.one_mem _
    · rw [act_vp, mem_ptStab.mp hσ]; exact Subgroup.mem_zpowers _
  have hle : c.preθ (ptStab p) ≤ Subgroup.normalizer (Zv l : Set G) := by
    refine le_normalizer_of_forall' fun k hk z hz => ?_
    have hkS : k ∈ stab δ := c.preθ_le_stab _ hk
    have hz' := (hmem ⟨z, hlV hz⟩).mp hz
    refine (hmem ⟨k * z * k⁻¹, conj_mem_Vn hkS (hlV hz)⟩).mpr ?_
    have := c.π_conj ⟨k, hkS⟩ ⟨z, hlV hz⟩
    have e : c.π ⟨k * z * k⁻¹, conj_mem_Vn hkS (hlV hz)⟩ =
        orth.act (c.θ ⟨k, hkS⟩) (c.π ⟨z, hlV hz⟩) := this
    rw [e]
    exact hvp _ hz' _ ((c.mem_preθ_iff ⟨k, hkS⟩).mp hk)
  apply le_antisymm
  · intro g hg
    have hgS : g ∈ stab δ := hg.2
    refine (c.mem_preθ_iff ⟨g, hgS⟩).mpr (mem_ptStab.mpr ?_)
    have h1 : vp p ∈ c.img (Zv l) := by rw [himg]; exact Subgroup.mem_zpowers _
    obtain ⟨z, hz, hzπ⟩ := (c.mem_img_iff').mp h1
    have hgz : g * (z : G) * g⁻¹ ∈ Zv l := (Subgroup.mem_normalizer_iff.mp hg.1 _).mp hz
    have h2 := (hmem ⟨g * (z : G) * g⁻¹, conj_mem_Vn hgS z.2⟩).mp hgz
    have e : c.π ⟨g * (z : G) * g⁻¹, conj_mem_Vn hgS z.2⟩ = orth.act (c.θ ⟨g, hgS⟩) (c.π z) :=
      c.π_conj ⟨g, hgS⟩ z
    rw [e, hzπ, act_vp] at h2
    rcases (mem_zpowers_iff_of_mul_self (vp_mul_self p)).mp h2 with h3 | h3
    · exact absurd h3 (vp_ne_one _)
    · exact vp_injective h3
  · exact fun g hg => ⟨hle hg, c.preθ_le_stab _ hg⟩

theorem inf_le_Mbl (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    stab δ ⊓ stab l ≤ Mbl δ l := by
  rw [c.Mbl_eq_preθ hS hδ hl, ← c.preθ_Dl hS hδ hl]
  intro g hg
  refine (c.mem_preθ_iff ⟨g, c.preθ_le_stab _ hg⟩).mpr (le_ptStab (c.isFixPt_pt hS hl) ?_)
  exact (c.mem_preθ_iff ⟨g, c.preθ_le_stab _ hg⟩).mp hg

theorem Qv_le_Mbl (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    Qv δ ≤ Mbl δ l := (Qv_le_inf' hS hl).trans (c.inf_le_Mbl hS hδ hl)

theorem Zv_eq_iff (hS : Sit H M S) (hδ : vtype δ = false) {l l' : Geo H M} (hl : l ∈ nbrs δ)
    (hl' : l' ∈ nbrs δ) : Zv l = Zv l' ↔ c.pt l = c.pt l' := by
  constructor
  · intro h
    have h1 := c.img_Zv_nbr hS hδ hl
    have h2 := c.img_Zv_nbr hS hδ hl'
    rw [h] at h1
    exact zpowers_vp_inj (h1.symm.trans h2)
  · intro h
    apply c.img_injOn (Zv_le_Zv_of_nbr hS hδ hl) (Zv_le_Vn hl) (Zv_le_Zv_of_nbr hS hδ hl')
      (Zv_le_Vn hl')
    rw [c.img_Zv_nbr hS hδ hl, c.img_Zv_nbr hS hδ hl']
    unfold pt at h
    rw [h]

theorem eq_or_le_Mbl (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ)
    {P : Subgroup G} (hP : P ≤ stab δ) (hinf : stab δ ⊓ stab l ≤ P) :
    P = stab δ ∨ P ≤ Mbl δ l := by
  by_cases hbar : c.bar P = ⊤
  · left
    have := c.preθ_bar hS hδ hP ((Qv_le_inf' hS hl).trans hinf)
    rw [hbar] at this
    rw [← this]
    ext x
    constructor
    · exact fun hx => c.preθ_le_stab _ hx
    · intro hx
      exact (c.mem_preθ_iff ⟨x, hx⟩).mpr (Subgroup.mem_top _)
  · right
    have hD : c.Dl l ≤ c.bar P := c.bar_mono hinf
    have := le_ptStab_of_le (c.card_Dl hS hl) hD hbar
    rw [c.Mbl_eq_preθ hS hδ hl, ← c.preθ_bar hS hδ hP ((Qv_le_inf' hS hl).trans hinf)]
    intro x hx
    have hxs : x ∈ stab δ := c.preθ_le_stab _ hx
    exact (c.mem_preθ_iff ⟨x, hxs⟩).mpr (this ((c.mem_preθ_iff ⟨x, hxs⟩).mp hx))

theorem exists_nbr_pt (hS : Sit H M S) (hδ : vtype δ = false) (p : Fin 5) :
    ∃ l ∈ nbrs δ, c.pt l = p := by
  have hD : Nat.card (cj (swap 4 p) S5Syl) = 8 := card_cj_S5Syl _
  obtain ⟨l, hl, hlD⟩ := c.Dl_surjOn hS hδ hD
  refine ⟨l, hl, ?_⟩
  have h1 : IsFixPt (c.Dl l) p := by
    rw [hlD]
    exact isFixPt_cj_std_iff.mpr (by simp)
  exact (IsFixPt.unique (c.card_Dl hS hl) (c.isFixPt_pt hS hl) h1)

theorem iInf_Mbl (hS : Sit H M S) (hδ : vtype δ = false) :
    ⨅ l ∈ nbrs δ, Mbl δ l = Qv δ := by
  apply le_antisymm
  · intro g hg
    have hg' : ∀ l ∈ nbrs δ, g ∈ Mbl δ l := fun l hl => (Subgroup.mem_iInf.mp
      ((Subgroup.mem_iInf.mp hg) l)) hl
    obtain ⟨μ, hμ⟩ := exists_adj δ
    have hgS : g ∈ stab δ := (hg' μ hμ).2
    rw [← c.ker_iff hS hδ ⟨g, hgS⟩]
    have : c.θ ⟨g, hgS⟩ = 1 := by
      refine Equiv.ext fun p => ?_
      obtain ⟨l, hl, hlp⟩ := c.exists_nbr_pt hS hδ p
      have h1 := hg' l hl
      rw [c.Mbl_eq_preθ hS hδ hl, c.mem_preθ_iff ⟨g, hgS⟩, mem_ptStab, hlp] at h1
      simpa using h1
    exact this
  · refine le_iInf₂ fun l hl => c.Qv_le_Mbl hS hδ hl

end Chart

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
