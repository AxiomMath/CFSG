module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6Adapt
public import CFSG.LocalAnalysis.StandardType.GGE6D4LocalJ
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2s08_ce6_card_le_six (hRig : GGLabelRigidInput) (hD : GGTBTorD)
    (hLift : GGTBTorLiftRows) (hQ1 : GGBstarInnerDiagJInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hI1 : GGQTwoI1 Bs D J)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) (hrow : ggRowTwoNode 3 labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) : Nat.card ↥Bs ≤ 3 ^ 6 := by
  obtain ⟨n, rfl, hcase⟩ := E6D4J.row_cases hrow htag
  have h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hInnJ : GGInnerDiagOn Bs J :=
    hQ1 G 3 B Bs x L D J hH.1 hH.2.2.1.1
  obtain ⟨hN, hTor⟩ := E6D4J.torData_J hRig hD hLift hH hInnJ hJΛ hJl h3
  obtain ⟨hm, h3m⟩ := E6D4J.odd_and_dvd_ggTorMpm (n := n) hJΛ.1 h3
  obtain ⟨w, hw⟩ := hTor
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hAle : Nat.card (ggGamma J hN).range ≤ 3 ^ 4 := ggTD_card_range_le_pow hm h3m hBs hSC hN w hw
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hN
  have hle : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := fun b hb =>
    hI1 b hb.1 fun j hj => (Subgroup.mem_centralizer_iff.mp hb.2 j hj).symm
  have hCD : Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ 3 ^ 2 := by
    have hD : Nat.card D = 3 ^ 2 := hH.1.2.2.1.2.2.1
    rw [← hD]
    exact Subgroup.card_le_of_le hle
  calc Nat.card ↥Bs = Nat.card (ggGamma J hN).range *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hmul.symm
    _ ≤ 3 ^ 4 * 3 ^ 2 := Nat.mul_le_mul hAle hCD
    _ = 3 ^ 6 := by norm_num

end CFSG.StandardType

end
