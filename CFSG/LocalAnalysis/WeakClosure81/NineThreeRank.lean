module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_conj_iSup' {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

private theorem nineThree_mem_normalizer_of_le {P : Subgroup G} {n : G}
    (h1 : conjSubgroup P n ≤ P) (h2 : conjSubgroup P n⁻¹ ≤ P) : n ∈ normalizer (P : Set G) := by
  have h3 := E3.conjSubgroup_mono_left n h2
  rw [E3.conjSubgroup_inv_conj] at h3
  exact conjSubgroup_eq_iff_mem_normalizer.mp (le_antisymm h1 h3)

namespace Nine3Choice

theorem conjSubgroup_nineZ_le (hc : Nine3Choice V T A K S X p g x) {r : G}
    (hr : r ∈ pCoreOf 2 K) : conjSubgroup (nineZ V K S) r ≤ nineZ V K S := by
  unfold nineZ
  rw [nineThree_conj_iSup']
  refine iSup_le fun B => ?_
  rw [nineThree_conj_iSup']
  refine iSup_le fun hB => ?_
  exact le_iSup₂_of_le (conjSubgroup B r) (hc.core.conjSubgroup_mem_nineOmegaIn hB hr) le_rfl

theorem nineD_le_normalizer_nineDp (hc : Nine3Choice V T A K S X p g x) :
    nineD K A x ≤ normalizer (nineDp K A x : Set G) := by
  have hmem : ∀ d ∈ nineD K A x, conjSubgroup (nineDp K A x) d ≤ nineDp K A x := by
    intro d hd
    have hdR : d ∈ pCoreOf 2 K := Nine3Core.nineD_le_pCoreOf hd
    have hdK : d ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hdR
    rw [hc.core.nineDp_eq hc.x_mem, E3.conjSubgroup_inf, Nine3Core.conjSubgroup_pCoreOf K hdK]
    exact inf_le_inf_right _ (hc.conjSubgroup_nineZ_le hdR)
  exact fun d hd => nineThree_mem_normalizer_of_le (hmem d hd)
    (hmem d⁻¹ ((nineD K A x).inv_mem hd))

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
