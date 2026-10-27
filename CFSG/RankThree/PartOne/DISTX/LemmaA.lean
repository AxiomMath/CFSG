module

public import CFSG.RankThree.PartOne.K1320X.CommRes

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.DISTX

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem commute_of_member_centre (hS : SchreierFor InCatalog) (hRe : Sec13Reinst)
    (hSame : KFCommSame) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E ≠ A)
    {s t : MulAut E} (hs : s ∈ reflectionSet p E) (ht : t ∈ reflectionSet p E)
    (hLs : KFLiftAt p E s) (hLt : KFLiftAt p E t) (hst : s ≠ t) (hcomm : s * t = t * s)
    {X : Subgroup G} (hX : X ∈ thetaCompZeroStarE p E) (hsX : s ∈ torusImage E X) {cX : G}
    (hcX : X ∈ thetaComponentsAt p cX) (hcXt : cX ∈ autFixedInG E t) (hcX1 : cX ≠ 1) :
    kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) := by
  have hp := h.prime
  obtain ⟨B, c', hB, hc'B, hc'1, hX12, hXF, hX13, hXT⟩ := hRe G p A c L E h hF13 hT X hX
  have hXq : CFSG.IsQuasisimple ↥X := by
    rcases hXF.two with h2 | h2
    · exact h2.quasisimple
    · exact h2.quasisimple
  have hKsX : kZero p E s ≤ X := hF13.kt_le X hX s hs hsX (kZero p E s) hLs.isKt
  have hDel : IsElementaryAbelian p ↥(autFixedInG E t) :=
    isElementaryAbelian_of_le' h.E_elem (Subgroup.map_subtype_le _)
  obtain ⟨I, hI, hKtI⟩ := exists_thetaComponentsAt_ge_of_hyp h hS hcX1 hDel hcXt
    (kZero_le_centralizer_fixed p E t) (kZero_mem_thetaComponents hp hLt.1)
  by_cases hIX : I = X
  · subst hIX
    obtain ⟨kt, hkt, hktK, hkt_eq⟩ := hLt.2.2.2.2
    have htX : t ∈ torusImage E I :=
      Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKtI hktK, hkt, hkt_eq⟩
    exact (hSame G p B c' I E hX12 hXF hX13 hXT (hcase_of_reinst h hB (Or.inl hEA)) s hs hsX t ht
      htX hst hcomm).1
  · exact centralizes_of_distinct_components hp hcX hI (Ne.symm hIX) hKsX hKtI hLs.1.1
      (hKsX.trans (K1320X.le_centralizer_theta_of_quasisimple hp hcX hXq))

end CFSG.RankThree.PartOne.DISTX
