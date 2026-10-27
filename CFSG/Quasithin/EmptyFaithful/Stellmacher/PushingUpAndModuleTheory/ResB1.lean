module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA1

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def toGeoElt (μ : Geo H M) {g : G} (hg : g ∈ stab μ) : ↥(H ⊔ M) :=
  ⟨g, stab_le μ hg⟩

omit [Finite G] in
theorem toGeoElt_smul {μ : Geo H M} {g : G} (hg : g ∈ stab μ) : toGeoElt μ hg • μ = μ :=
  smul_eq_of_mem_stab (g := toGeoElt μ hg) hg

omit [Finite G] in
theorem conjSub_stab_mu {μ : Geo H M} {g : G} (hg : g ∈ stab μ) : conjSub g (stab μ) = stab μ := by
  have := stab_smul (toGeoElt μ hg) μ
  rw [toGeoElt_smul hg] at this
  exact this.symm

omit [Finite G] in
theorem conjSub_Qv_mu {μ : Geo H M} {g : G} (hg : g ∈ stab μ) : conjSub g (Qv μ) = Qv μ := by
  have := Qv_smul (toGeoElt μ hg) μ
  rw [toGeoElt_smul hg] at this
  exact this.symm

omit [Finite G] in
theorem conjSub_Zv_mu {μ : Geo H M} {g : G} (hg : g ∈ stab μ) :
    conjSub g (Zv μ) = Zv μ := by
  have := Zv_smul (toGeoElt μ hg) μ
  rw [toGeoElt_smul hg] at this
  exact this.symm

theorem SitSigma.smul_stab {δ μ : Geo H M} {U : Subgroup G} (h : SitSigma δ μ U) {g : G}
    (hg : g ∈ stab μ) : SitSigma (toGeoElt μ hg • δ) μ (conjSub g U) where
  adj := by
    have := (smul_adj (toGeoElt μ hg)).mpr h.adj
    rwa [toGeoElt_smul hg] at this
  le_stab := by
    rw [stab_smul]
    exact conjSub_mono g h.le_stab
  sylow := by
    have := isSylowTwoOf_conj h.sylow g
    rwa [conjSub_inf, conjSub_Qv_mu hg] at this
  zle := by
    have := conjSub_mono g h.zle
    rwa [conjSub_Zv_mu hg, ← pCoreOf_conjSub] at this
  gen := by
    have := congrArg (conjSub g) h.gen
    rw [conjSub_sup, conjSub_inf, conjSub_stab_mu hg] at this
    rw [stab_smul]
    exact this

omit [Finite G] in
theorem conjSub_le_conjSub_iff (g : G) {A B : Subgroup G} : conjSub g A ≤ conjSub g B ↔ A ≤ B := by
  refine ⟨fun h => ?_, conjSub_mono g⟩
  have := conjSub_mono g⁻¹ h
  rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem smul_stab (h : ConfR δ μ U) {g : G} (hg : g ∈ stab μ) :
    ConfR (toGeoElt μ hg • δ) μ (conjSub g U) where
  b := h.b
  sig := h.sig.smul_stab hg
  hQ := by
    rw [← conjSub_Qv_mu hg]
    exact conjSub_mono g h.hQ
  hR := by
    rw [Qv_smul, pCoreOf_conjSub]
    exact fun hle => h.hR ((conjSub_le_conjSub_iff g).mp hle)
  hQδ := by
    rw [Qv_smul]
    rw [← conjSub_Qv_mu hg]
    exact conjSub_mono g h.hQδ

end ConfR

end CFSG.Quasithin.F53
