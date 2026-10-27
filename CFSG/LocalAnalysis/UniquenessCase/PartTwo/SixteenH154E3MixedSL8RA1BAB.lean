module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Goldschmidt.Steps.G63Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qc
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem s16h_sl28_join_elemAbelian_seven {A B : Subgroup X}
    (hA : IsSimpleGroup ↥A) (hcard : Nat.card ↥A = Nat.card ↥B) (hne : B ≠ A)
    (hcomm : ⁅A, B⁆ = ⊥) (h7 : 7 ∣ Nat.card ↥A) :
    ∃ E : Subgroup X, E ≤ A ⊔ B ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 := by
  classical
  have h7B : 7 ∣ Nat.card ↥B := by rw [← hcard]; exact h7
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 7 h7
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7 h7B
  have haX : orderOf (a : X) = 7 := by rw [Subgroup.orderOf_coe, ha]
  have hbX : orderOf (b : X) = 7 := by rw [Subgroup.orderOf_coe, hb]
  have haX7 : (a : X) ^ 7 = 1 := by rw [← haX, pow_orderOf_eq_one]
  have hbX7 : (b : X) ^ 7 = 1 := by rw [← hbX, pow_orderOf_eq_one]
  have ha1 : (a : X) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at haX
    omega
  have hcen : A ≤ Subgroup.centralizer (B : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
  have hnorm : A ≤ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_inf] at hx ⊢
      refine ⟨A.mul_mem (A.mul_mem ha hx.1) (A.inv_mem ha), ?_⟩
      have hax : a * x = x * a :=
        (Subgroup.mem_centralizer_iff.mp (hcen ha) x hx.2).symm
      have hconj : a * x * a⁻¹ = x := by rw [hax]; group
      rw [hconj]; exact hx.2
    · intro hx
      rw [Subgroup.mem_inf] at hx ⊢
      refine ⟨?_, ?_⟩
      · have hmem : a⁻¹ * (a * x * a⁻¹) * a ∈ A :=
          A.mul_mem (A.mul_mem (A.inv_mem ha) hx.1) ha
        rwa [show a⁻¹ * (a * x * a⁻¹) * a = x from by group] at hmem
      · have hmem : a⁻¹ * (a * x * a⁻¹) * a ∈ B := by
          have hc : (a * x * a⁻¹) * a⁻¹ = a⁻¹ * (a * x * a⁻¹) :=
            Subgroup.mem_centralizer_iff.mp (hcen (A.inv_mem ha)) (a * x * a⁻¹) hx.2
          rw [← hc]
          rw [show (a * x * a⁻¹) * a⁻¹ * a = a * x * a⁻¹ from by group]
          exact hx.2
        rwa [show a⁻¹ * (a * x * a⁻¹) * a = x from by group] at hmem
  haveI : ((A ⊓ B).subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  haveI : IsSimpleGroup ↥A := hA
  have hdisj : A ⊓ B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ B).subgroupOf A) with h | h
    · refine le_bot_iff.mp fun x hx => ?_
      have hx' : (⟨x, hx.1⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      rw [h] at hx'
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hx')
    · exfalso
      have hAleB : A ≤ B := by
        intro a ha
        have hmem : (⟨a, ha⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A := by rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.mp hmem).2
      have hAB : A = B := Subgroup.eq_of_le_of_card_ge hAleB (le_of_eq hcard.symm)
      exact hne hAB.symm
  have hb_not : (b : X) ∉ Subgroup.zpowers (a : X) := by
    intro hmem
    have hbA : (b : X) ∈ A := Subgroup.zpowers_le.mpr a.2 hmem
    have hb1 : (b : X) = 1 := by
      have hmem' : (b : X) ∈ (⊥ : Subgroup X) :=
        hdisj ▸ Subgroup.mem_inf.mpr ⟨hbA, b.2⟩
      exact Subgroup.mem_bot.mp hmem'
    rw [hb1, orderOf_one] at hbX
    omega
  have hcomm' : (b : X) * (a : X) = (a : X) * (b : X) :=
    Subgroup.mem_centralizer_iff.mp (hcen a.2) (b : X) b.2
  obtain ⟨hEab, hEcard⟩ :=
    CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian (p := 7) Nat.prime_seven
      hbX7 haX7 ha1 hb_not hcomm'
  refine ⟨Subgroup.zpowers (b : X) ⊔ Subgroup.zpowers (a : X), ?_, hEab, hEcard⟩
  exact sup_le ((Subgroup.zpowers_le.mpr b.2).trans le_sup_right)
    ((Subgroup.zpowers_le.mpr a.2).trans le_sup_left)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
