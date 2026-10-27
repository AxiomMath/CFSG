module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB7
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB6
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem Qv_le_R (h : ConfR δ μ U) : Qv δ ≤ pCoreOf 2 U :=
  h.sig.inf_Qv_le_R.trans' (le_inf (h.hQδ.trans h.hQ) le_rfl)

theorem exists_not_Zv_le (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ n ∈ nbrs μ, n ≠ δ ∧ ¬ Zv n ≤ Qv δ := by
  by_contra hcon
  push Not at hcon
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  have hμ : μ ∈ nbrs δ := h.sig.adj
  obtain ⟨c, V₀, hcU, hc3, hVO, -, -, hRc, hUV, hUX⟩ := h.rdata hA
  set W := Vn μ with hW
  have hWQ : W ≤ Qv δ := by
    refine iSup₂_le fun n hn => ?_
    by_cases hnδ : n = δ
    · subst hnδ; exact Zv_le_Qv hA n
    · exact hcon n hn hnδ
  have hZW : Zv δ ≤ W := le_iSup₂ (f := fun n (_ : n ∈ nbrs μ) => Zv n) δ hδ
  have hV0W : V₀ ≤ W := hVO.trans ((h.Oo_le_Zv hA).trans hZW)
  have hμN : stab μ ≤ Subgroup.normalizer (W : Set G) := stab_le_normalizer_Vn μ
  have hcN : c ∈ Subgroup.normalizer (W : Set G) := by
    refine mem_normalizer_of_cj_le (g := c) (H := W) ?_
    intro x hx
    rw [mem_cj] at hx
    have hw : c⁻¹ * x * c ∈ W := hx
    have h1 := hRc _ (h.Qv_le_R (hWQ hw))
    have h2 : c * (c⁻¹ * x * c) * c⁻¹ * (c⁻¹ * x * c)⁻¹ ∈ V₀ := h1
    have h3 : x * (c⁻¹ * x * c)⁻¹ ∈ W := by
      have : c * (c⁻¹ * x * c) * c⁻¹ * (c⁻¹ * x * c)⁻¹ = x * (c⁻¹ * x * c)⁻¹ := by group
      rw [← this]; exact hV0W h2
    have h4 := W.mul_mem h3 hw
    have e : x * (c⁻¹ * x * c)⁻¹ * (c⁻¹ * x * c) = x := by group
    rwa [e] at h4
  have hUN : U ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hUX]
    exact sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 (stab μ)).trans hμN)
      ((Subgroup.zpowers_le).mpr hcN)
  have hδN : stab δ ≤ Subgroup.normalizer (W : Set G) := by
    rw [← h.sig.gen]
    exact sup_le hUN (inf_le_right.trans hμN)
  have hle : W ≤ stab δ ⊓ stab μ :=
    le_inf (hWQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) (hWQ.trans (Qv_le_stab_of_mem_nbrs hA hμ))
  have hbot := eq_bot_of_normalizes_both hA h.sig.adj hle hδN hμN
  exact Zv_ne_bot hA δ (le_bot_iff.mp (hbot ▸ hZW))

end ConfR

end CFSG.Quasithin.F53
