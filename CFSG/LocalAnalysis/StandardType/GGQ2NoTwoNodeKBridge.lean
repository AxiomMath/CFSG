module

public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoNoTwoNodeKSide
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

theorem ggQ2_noTwoNodeK_of_placement
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (catalogue : FrameKind → RawFrameData)
    (hpl : PlacementCoreInput catalogue) (h3 : ∀ kind, ActualCutThreeInput (catalogue kind))
    (h5 : ∀ kind, ActualCutFiveInput (catalogue kind))
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hrow : GGQTwoTwoNodeRowAt p K J) : y ∉ K := by
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨kind, hframe⟩ := hpl hS rfl
  have hexcl : ActualInternalExclusion (catalogue kind) := by
    by_cases hcl : IsClassical (catalogue kind).kind
    · exact h3 kind hcl
    · exact h5 kind hcl
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hBstar : GGBstar 3 B Bs := hS.1.1.2.1
  have hStdSub : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hpre : LargeEvenStdSubPre 3 B x L D J := hS.1.1.2.2.1
  have hDBs : D ≤ Bs := hpre.1.trans hBstar.1
  have hD9 : Nat.card D = 9 := by
    have h := hpre.2.2.1
    norm_num at h
    exact h
  have hyD : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hy3 : y ^ 3 = 1 := hBstar.2.1.2 y (hDBs hyD)
  have hord : orderOf y = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hy3 hy1
  obtain ⟨hsimple, hnab, hKP, -, -, hβ, hSS, hst⟩ := hI
  have hKc : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hStdSub hnb)).1
  have hKH : K ≤ ggG0 3 B x L D J := le_ggG0_of_ggNbr hnb
  have hKcH : IsComponentOf K (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({y} : Set G)) :=
    hKc.of_le_of_le (le_inf hKH hKc.1) inf_le_right
  have hpJ : 3 ∣ Nat.card J := hP G 3 B x L D J hS.1.1.1 hStdSub
  have hJK : J ≤ K := le_of_ggNbr hLB hS.1.1.1 hStdSub hpJ hnb
  have hC1 : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    ggQ2_bstar_centralizer_nbr_eq_zpowers hLB hP hS hI1 hnb
  have hJc : IsComponentOf J (ggG0 3 B x L D J ⊓ Subgroup.centralizer (D : Set G)) :=
    ggQ2_isComponentOf_jointCentralizer hS
  exact hexcl hframe hDBs hD9 hyD hord hKcH hJc hJK hC1 hI1 hrow

end CFSG.StandardType

end
