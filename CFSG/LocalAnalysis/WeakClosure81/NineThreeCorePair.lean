module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairThree
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_core_gen (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) (hUS : ¬ U ≤ S) {w : G} (hw : w ∈ U ⊓ pCoreOf 2 K) :
    ∀ h ∈ nineH V K, ⁅h, g⁻¹ * w * g⁆ ∈ nineI V K := by
  rcases h35 with h3 | h5
  · exact nine3_pair_three hc hc' hI (Or.inl h3) hU hUS hw h3
  · exact nine3_pair_five hc hc' hI (Or.inr h5) hU hUS hw h5

end CFSG.LocalAnalysis.WeakClosure81
