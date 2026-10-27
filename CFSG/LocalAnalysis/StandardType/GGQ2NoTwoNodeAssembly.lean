module

public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeKBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSmall
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

theorem ggQ2_noTwoNodeL_of_placement
    (catalogue : FrameKind → RawFrameData)
    (hpl : PlacementCoreInput catalogue) (h3 : ∀ kind, ActualCutThreeInput (catalogue kind))
    (h5 : ∀ kind, ActualCutFiveInput (catalogue kind))
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hrow : GGQTwoTwoNodeRowAt p L J) : x ∉ L := by
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
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert x _)
  have hSstar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hxBs : x ∈ Bs := hBstar.1 hSstar.2.1
  have hx3 : x ^ 3 = 1 := hBstar.2.1.2 x hxBs
  have hord : orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSstar.2.2.2.1
  have hLH : IsComponentOf L (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hLcomp.of_le_of_le (le_inf (le_ggG0_left 3 B x L D J) hLcomp.1) inf_le_right
  have hJc : IsComponentOf J (ggG0 3 B x L D J ⊓ Subgroup.centralizer (D : Set G)) :=
    ggQ2_isComponentOf_jointCentralizer hS
  have hJL : J ≤ L := hStdSub.1.2.2.2.2.2.1.1.trans inf_le_left
  have hC1 : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBstar.2.1 hxBs hx1 hLcomp.1
      hSstar.2.2.2.2
  exact hexcl hframe hDBs hD9 hxD hord hLH hJc hJL hC1 hI1 hrow

theorem ggQTwoNoTwoNodeIndInput_of_cuts
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (catalogue : FrameKind → RawFrameData)
    (hpl : PlacementCoreInput catalogue) (h3 : ∀ kind, ActualCutThreeInput (catalogue kind))
    (h5 : ∀ kind, ActualCutFiveInput (catalogue kind)) : GGQTwoNoTwoNodeIndInput := by
  intro G _ _ p B Bs x L D J hS hI1 _ y K hnb
  exact ⟨fun hrow => ggQ2_noTwoNodeL_of_placement catalogue hpl h3 h5 hS hI1 hnb hrow,
    fun hrow => ggQ2_noTwoNodeK_of_placement hLB hP catalogue hpl h3 h5 hS hI1 hnb hrow⟩

theorem ggQTwoNoTwoNodeIndInput_of_halves
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hrig : GGLabelRigidInput)
    (ex : FrameKind → RawFrameData) (hexKind : ∀ k, IsExceptional k → (ex k).kind = k)
    (hexEq : ∀ k, IsExceptional k → ∀ c : (ex k).Code, (ex k).admissible c →
      ∀ lab : LargeEvenLabel, GGLabelIso ((ex k).label c) lab → lab ∈ (ex k).equivLabels c)
    (hexRaw : ∀ k, IsExceptional k → RawNoInternalTwoNode (ex k))
    (hplCl : PlacementCoreInputOn ClassicalLabel (catalogueOf classicalCatalogue ex))
    (hplEx : PlacementCoreInputOn ExceptionalLabel (catalogueOf classicalCatalogue ex)) :
    GGQTwoNoTwoNodeIndInput :=
  ggQTwoNoTwoNodeIndInput_of_cuts hLB hP (catalogueOf classicalCatalogue ex)
    (placementCoreInput_of_split _ hplCl hplEx (placementCoreInputOn_small _))
    (actualCutThreeInput_catalogueOf classicalCatalogue ex hexKind
      (fun k _ => classicalCatalogue_actualCutThreeInput hrig k))
    (actualCutFiveInput_catalogueOf classicalCatalogue ex (fun k _ => classicalCatalogue_kind k)
      (fun k hk => actualCutFiveInput_of_raw (ex k) (fun _ => hexRaw k hk)
        (literalDictionaryInput_of_rigid hrig (ex k) (hexEq k hk))))

end CFSG.StandardType

end
