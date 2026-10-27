module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndSplit
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

@[expose] def GGE6CoverModel
    (p : ℕ) [NeZero p] {G : Type} [Group G] (Bs X : Subgroup G) : Prop :=
  ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
    (_ : CharP Fq 2) (ψ : ↥X →* adjointGroup .E6 Fq) (Λ : adjointGroup .E6 Fq →* MulAut ↥X)
    (ζ : Fqˣ) (hζ : ζ ^ p = 1)
    (ι₀ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* adjointGroup .E6 Fq) (m : ℕ)
    (wt : GGTorusTorWit m 6 ↥X (ggGamma X hN).range),
    4 ≤ Nat.card Fq ∧ Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center ↥X ∧
    (∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1) ∧
    Function.Injective Λ ∧ (∀ x, Λ (ψ x) = MulAut.conj x) ∧
    (∀ g l, ψ (Λ g l) = g * ψ l * g⁻¹) ∧
    (ggGamma X hN).range = (TableBExc.torusPow .E6 Fq p).map Λ ∧
    orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = TableBExc.torusPow .E6 Fq p ∧
    (∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL .E6 Fq) = ExcFrames.frameDiag ζ hζ s) ∧
    (∀ k s, ψ (wt.n k) * ι₀ (Multiplicative.ofAdd s) * (ψ (wt.n k))⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 k) s))) ∧
    (∀ g ∈ Subgroup.normalizer ((TableBExc.torusPow .E6 Fq p) : Set (adjointGroup .E6 Fq)),
      ∃ v : WeylGroup .E6, ∀ s, g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p v s))) ∧
    wt.Holds CartanMatrix.E₆ CoxeterMatrix.E₆

private theorem ggE6Split_coverModel_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {Bs X : Subgroup G} {n : ℕ} {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    (hFqcard : Nat.card Fq = 2 ^ n)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* TableBExc.RecipeGroup .E6 Fq)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTB : GGTorusTBGroup p 6 (TableBExc.RecipeGroup .E6 Fq) (TableBExc.RecipeID .E6 Fq)
      ↥X (ggQuotHom θ) (ggGamma X hN).range)
    (hpn : p ∣ 2 ^ n - 1) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    GGE6CoverModel p Bs X := by
  classical
  have hp : p.Prime := Fact.out
  have hpq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  obtain ⟨ψa, hψa, hka, Λ, hΛ, hΛn, hΛmap, hA⟩ :=
    TBE6Ind.exists_aligned_adjoint hp hp2 hp3 hpq (ggQuotHom θ) _ hTB
  obtain ⟨w, hw, hwn⟩ := TBE6Ind.torData_aligned hp hp2 hp3 hpq ψa hψa hka hTB.2.2.1
    _ hTB.2.2.2.1 Λ hΛ hΛn hΛmap hA
  obtain ⟨ζ, hζ, ι₀, hζo, hι₀, hrange, hcoe, hweyl, hnorm⟩ := e6Split_frame hp2 hp3 hpq
  have hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1 := by
    have hdvd : ¬ p ∣ Nat.card (Subgroup.center ↥X) :=
      ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3 ↥X (ggQuotHom θ)
        (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hTB.2.2.1
    intro z hz hzp
    by_contra hne
    have hord : orderOf z = p := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hzp) with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact hp'
    have hd := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥X) hz
    rw [hord] at hd
    exact hdvd hd
  have hcard4 : 4 ≤ Nat.card Fq := by
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hgt : 1 < Nat.card Fq := Finite.one_lt_card
    rw [hFqcard] at hgt
    have hpos : 0 < 2 ^ n - 1 := by omega
    have hle : p ≤ 2 ^ n - 1 := Nat.le_of_dvd hpos hpn
    rw [hFqcard]
    omega
  refine ⟨hN, Fq, inferInstance, inferInstance, inferInstance, ψa, Λ, ζ, hζ, ι₀,
    Nat.card Fq - 1, w, hcard4, hψa, hka, hZp, hΛ, hΛn, hΛmap, hA.symm, hζo, hι₀,
    hrange, hcoe, ?_, hnorm, hw⟩
  intro k s
  rw [hwn k]
  exact hweyl k s

theorem ggE6Split_coverModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3) :
    GGE6CoverModel p Bs L := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn
  have hinner : GGInnerDiagOn Bs L := hH.2.2.1.1
  obtain ⟨hperf, lab, _hlab, hraw⟩ := ggInnerDiagOn_relabel hRig hinner hΛ hL
  obtain ⟨_, _, _, _, _, _, _, hEq, _, _⟩ := largeEvenRawDatum_exists hraw
  subst hEq
  obtain ⟨Fq, _instFq, _finFq, hFqcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hN, hBsI⟩ := hQ
  haveI : CharP Fq 2 := charP_two_of_card hFqcard
  have hpq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  have hlift : GGTorusLift p 6 (TableBExc.RecipeGroup .E6 Fq) :=
    TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq
  have hTB : GGTorusTBGroup p 6 (TableBExc.RecipeGroup .E6 Fq) (TableBExc.RecipeID .E6 Fq)
      ↥L (ggQuotHom θ) (ggGamma L hN).range :=
    ggTorusTBGroup_of_L hH.1 hperf θ hN
      (fun b hb => ggLAut_mem_of_induces L θ hN hBsI hb) hlift
  exact ggE6Split_coverModel_of_marking hFqcard θ hN hTB hpn hp2 hp3

theorem ggE6Split_coverModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3) :
    GGE6CoverModel p Bs K := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hinner : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨hperf, lab, _hlab, hraw⟩ := ggInnerDiagOn_relabel hRig hinner hΛ hK
  obtain ⟨_, _, _, _, _, _, _, hEq, _, _⟩ := largeEvenRawDatum_exists hraw
  subst hEq
  obtain ⟨Fq, _instFq, _finFq, hFqcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hN, hBsI⟩ := hQ
  haveI : CharP Fq 2 := charP_two_of_card hFqcard
  have hpq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  have hlift : GGTorusLift p 6 (TableBExc.RecipeGroup .E6 Fq) :=
    TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq
  have hTB : GGTorusTBGroup p 6 (TableBExc.RecipeGroup .E6 Fq) (TableBExc.RecipeID .E6 Fq)
      ↥K (ggQuotHom θ) (ggGamma K hN).range :=
    ggTorusTBGroup_of_nbr hH.1 hnb hperf θ hN
      (fun b hb => ggLAut_mem_of_induces K θ hN hBsI hb) hlift
  exact ggE6Split_coverModel_of_marking hFqcard θ hN hTB hpn hp2 hp3

end CFSG.StandardType

end
