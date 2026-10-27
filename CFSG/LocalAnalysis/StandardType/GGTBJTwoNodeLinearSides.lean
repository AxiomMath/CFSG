module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearNbr
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeParabolic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem ggResTwoNodeSideDatum_of_diagonal_linear_block
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hr : 4 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ a t)
    (S : Finset (Fin (r + 1))) (hS : S.card = r - 1)
    (hJ : J = (blockSpecialLinear S).map (X.subtype.comp ψ)) :
    GGResTwoNodeSideDatum p Bs X J := by
  obtain ⟨V, hVadd, hVmod, ι, φ, h, α, hlin, hrefl, hpair, ⟨e, he⟩, hclos, hJgen⟩ :=
    exists_adapted_weyl_datum_of_diagonal_linear_block hp2 hpF (by omega : 4 ≤ r)
      hBs hSC hN hψ hker hdiag S hS hJ
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  exact ggTBJTwoNodeParabolic hp2 hr rfl rfl hlin hrefl hpair he hclos hJgen

theorem ggResTwoNodeSideDatum_large_linear_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hJLab : GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    GGResTwoNodeSideDatum p Bs L J := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS, hJ⟩ :=
    exists_corank_two_block_of_large_linear_L hRig hH hr hpq hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggResTwoNodeSideDatum_of_diagonal_linear_block hH.1.1.2.2.2.2.2.1.2.1
    (by simpa only [hF] using hpq) hr hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2
    hN hφs hker hdiag S hS hJ

theorem ggResTwoNodeSideDatum_large_linear_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hJLab : GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    GGResTwoNodeSideDatum p Bs K J := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS, hJ⟩ :=
    exists_corank_two_block_of_large_linear_K hRig hLB hH hr hpq hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggResTwoNodeSideDatum_of_diagonal_linear_block hH.1.1.2.2.2.2.2.1.2.1
    (by simpa only [hF] using hpq) hr hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2
    hN hφs hker hdiag S hS hJ

end CFSG.StandardType

end
