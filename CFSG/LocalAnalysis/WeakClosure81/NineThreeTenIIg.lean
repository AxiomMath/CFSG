module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoice

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

namespace Nine3Choice

theorem nineI_inf_conj_le_nineW0
    (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    nineI V K ⊓ conjSubgroup (nineI V K) g ≤ nineW0 V K S g := by
  have hIgC : conjSubgroup (nineI V K) g ≤ Subgroup.centralizer (A : Set G) := by
    have h := E3.conjSubgroup_mono_left g (hc.core.nineI_le_centralizer (V := V) (K := K))
    rwa [E3.conjSubgroup_centralizer, hc.V_g] at h
  refine (inf_le_inf le_rfl hIgC).trans ?_
  rw [nine3_centralizer_A_eq_J hc hI]
  exact le_sup_right

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
