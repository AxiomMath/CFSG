module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcNormCore
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepTwo
public import CFSG.Assembly.OpenBridges
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator

private theorem mem_of_pow_prime_of_pow_three_mem {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {β : G} {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hβp : β ^ p = 1) (hβ3 : β ^ 3 ∈ N) :
    β ∈ N := by
  have hcop : Nat.Coprime p 3 := by
    rw [hp.coprime_iff_not_dvd]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  have hdvd : orderOf (QuotientGroup.mk β : G ⧸ N) ∣ p ∧
      orderOf (QuotientGroup.mk β : G ⧸ N) ∣ 3 := by
    constructor
    · rw [orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, hβp, QuotientGroup.mk_one]
    · rw [orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 hβ3
  have hone : orderOf (QuotientGroup.mk β : G ⧸ N) = 1 := by
    have hg : orderOf (QuotientGroup.mk β : G ⧸ N) ∣ Nat.gcd p 3 :=
      Nat.dvd_gcd hdvd.1 hdvd.2
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    exact Nat.dvd_one.mp hg
  exact (QuotientGroup.eq_one_iff β).1 (orderOf_eq_one_iff.mp hone)

private theorem pow_three_mem_of_mul_mem_normal {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {c d : G} (hc : c ∈ N) (hd3 : d ^ 3 ∈ N) : (c * d) ^ 3 ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  have hc' : (QuotientGroup.mk c : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff c).2 hc
  have hcd : (QuotientGroup.mk (c * d) : G ⧸ N) = QuotientGroup.mk d := by
    rw [QuotientGroup.mk_mul, hc', one_mul]
  rw [QuotientGroup.mk_pow, hcd, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff (d ^ 3)).2 hd3

private theorem mem_torusSubgroup_E6_of_not_three_dvd {K : Type} [Field K]
    (h3K : ¬ 3 ∣ Nat.card K - 1) (b : Fin Tag.E6.rank → Kˣ) :
    b ∈ TableB.torusSubgroup Tag.E6.cartan K := by
  have hcop : Nat.Coprime (Nat.card Kˣ) 3 := by
    rw [Nat.card_units, Nat.coprime_comm]
    exact (Nat.prime_three.coprime_iff_not_dvd).2 h3K
  have hsurj : ∀ i : Fin Tag.E6.rank, ∃ y : Kˣ, y ^ 3 = b i := fun i => by
    obtain ⟨y, hy⟩ := (powCoprime hcop).surjective (b i)
    exact ⟨y, by rwa [powCoprime_apply] at hy⟩
  choose c' hc' using hsurj
  have hbc : b = c' ^ 3 := by
    funext i
    simpa using (hc' i).symm
  rw [hbc]
  exact TableBExc.pow_three_mem_torusSubgroup_E6 c'

theorem ggE0_e6_mem_inn_of_pow
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hsh : ¬ (p = 3 ∧ 3 ∣ Nat.card K - 1)) {β : MulAut ↥(adjointGroup .E6 K)}
    (hβI : β ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range ⊔
      (AutSt.e6DiagHom K).range)
    (hβp : β ^ p = 1) :
    β ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range := by
  classical
  have hInnN : (MulAut.conj : ↥(adjointGroup .E6 K) →*
      MulAut ↥(adjointGroup .E6 K)).range.Normal :=
    AutSt.normal_range_conj (S := ↥(adjointGroup .E6 K))
  obtain ⟨_, ⟨c, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_left (hs := hInnN)).mp hβI
  by_cases hp3 : p = 3
  · have h3K : ¬ 3 ∣ Nat.card K - 1 := fun h => hsh ⟨hp3, h⟩
    have hbT := mem_torusSubgroup_E6_of_not_three_dvd h3K b
    exact mul_mem ⟨c, rfl⟩ (e6DiagHom_mem_inn_of_mem_torusSubgroup hbT)
  · have hd3 : (AutSt.e6DiagHom K b) ^ 3 ∈
        (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range := by
      rw [← map_pow]
      exact e6DiagHom_mem_inn_of_mem_torusSubgroup (TableBExc.pow_three_mem_torusSubgroup_E6 b)
    exact mem_of_pow_prime_of_pow_three_mem hp hp3 hβp
      (pow_three_mem_of_mul_mem_normal ⟨c, rfl⟩ hd3)


private theorem fixSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

theorem ggE0_e6_normalizes
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsh : ¬ (p = 3 ∧ 3 ∣ Nat.card K - 1)) {s : ↥(adjointGroup .E6 K)} (hs1 : s ≠ 1)
    (hsp : s ^ p = 1)
    {X : Subgroup ↥(adjointGroup .E6 K)} (hX : IsComponentOf X (Subgroup.centralizer {s})) :
    Subgroup.centralizer {s} ≤ Subgroup.normalizer (X : Set ↥(adjointGroup .E6 K)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hqK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hqK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  let C := ↥(adjointGroup .E6 K)
  let β : MulAut C := MulAut.conj s
  have hβp : β ^ p = 1 := by
    have h1 : (MulAut.conj : C →* MulAut C) (s ^ p) = (MulAut.conj s) ^ p := map_pow _ s p
    rw [hsp, map_one] at h1
    simpa [β] using h1.symm
  have hβ1 : β ≠ 1 := by
    intro h
    apply hs1
    have hz : s ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hc : s * c * s⁻¹ = c := by
        have h' := congrArg (fun f : MulAut C => f c) h
        simpa [β, MulAut.conj_apply] using h'
      calc c * s = (s * c * s⁻¹) * s := by rw [hc]
        _ = s * c := by group
    have hbot : Subgroup.center C = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    rw [hbot] at hz
    exact Subgroup.mem_bot.mp hz
  have hfix : fixSubgroup β = Subgroup.centralizer ({s} : Set C) :=
    fixSubgroup_conj_eq_centralizer s
  have hX' : CFSG.Open.IsComponentOf X (fixSubgroup β) := by
    rw [hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hX
  have hCN : CFSG.LocalAnalysis.GLTheoremA.S267.Gen.CompNormal β := by
    by_cases hp3 : p = 3
    · have h3K : ¬ 3 ∣ Nat.card K - 1 := fun h => hsh ⟨hp3, h⟩
      have hsp3 : s ^ 3 = 1 := by simpa [hp3] using hsp
      have := CFSG.LocalAnalysis.GLTheoremA.F151.compNormal_E6_charTwo_three h3K s hs1 hsp3
      simpa [β] using this
    · have hβmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived C :=
        CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived C
          (show β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner C from ⟨s, rfl⟩)
      have hG2 : (Tag.E6 : Tag) = .G2 → 3 ≤ Nat.card K := fun h => absurd h (by decide)
      exact CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_adjointGroup
        (τ := .E6) (K := K) (Or.inr (Or.inr (Or.inl rfl))) hG2 hp hp2 hpK (fun _ => hp3)
        β hβmem hβp hβ1
  have hmain : fixSubgroup β ≤ Subgroup.normalizer (X : Set C) := hCN X hX'
  rw [hfix] at hmain
  exact hmain


end CFSG.StandardType
