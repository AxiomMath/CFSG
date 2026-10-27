module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.ClassicalInvolution.Q3.TL4ConnBendOut
public import CFSG.LocalAnalysis.GH72.OuterFacts
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitInputs
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.TwoSignalizer

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section ConnLemmas

theorem exists_conj_of_mul_mem {Y : Type} [Group Y] [Finite Y] {Λ : Set Y} (hS : Setup Y Λ)
    (M : Subgroup Y) [M.Normal] (hC : Subgroup.centralizer (M : Set Y) = ⊥) {d a : Y}
    (hcl : IsOddTranspClass (conjSet M d)) (hd : d ∈ Λ) (ha : a ∈ Λ) (hmem : d * a ∈ M) :
    ∃ m ∈ M, m * d * m⁻¹ = a := by
  classical
  let L : Subgroup Y := M ⊔ Subgroup.zpowers d
  have hdL : d ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have haL : a ∈ L := by
    have h1 : d ∈ L := hdL
    have h2 : d * a ∈ L := Subgroup.mem_sup_left hmem
    have h3 : d * (d * a) ∈ L := Subgroup.mul_mem _ h1 h2
    have hdd : d * d = 1 := hS.oddT.mul_self_eq_one hd
    have h4 : (d * d) * a ∈ L := by simpa [mul_assoc] using h3
    simpa [hdd] using h4
  let aL : L := ⟨a, haL⟩
  by_contra hnot
  have hcommConj : ∀ u ∈ conjSet M d, Commute (u : Y) a := by
    intro u hu
    by_contra hnc
    have huSet : u ∈ conjSet M d := hu
    obtain ⟨m, hm, hu_eq⟩ := hu
    have huΛ : (u : Y) ∈ Λ := by
      rw [hu_eq]
      exact hS.conj_mem m hd
    have huL : (u : Y) ∈ L := by
      rw [hu_eq]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) hdL)
        (Subgroup.mem_sup_left (M.inv_mem hm))
    obtain ⟨g, hg_mem, hg_conj⟩ := hS.oddT.exists_conj huΛ ha hnc
    have hgL : g ∈ L := by
      refine (Subgroup.closure_le (K := L)).mpr ?_ hg_mem
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact huL
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact haL
    let gL : L := ⟨g, hgL⟩
    let uL : L := u
    have hstep : IsConj uL (gL * uL * gL⁻¹) := isConj_iff.mpr ⟨gL, rfl⟩
    have htarget : gL * uL * gL⁻¹ = aL := Subtype.ext hg_conj
    obtain ⟨d₀, hcls⟩ := hcl.1
    have huMem : uL ∈ conjSet M d := huSet
    have huClass : IsConj d₀ uL := by
      rw [hcls] at huMem
      exact huMem
    have haClass : IsConj d₀ aL := by
      rw [← htarget]
      exact huClass.trans hstep
    have haMem : aL ∈ conjSet M d := by
      rw [hcls]
      exact haClass
    obtain ⟨m', hm', hval⟩ := haMem
    exact hnot ⟨m', hm', hval.symm⟩
  have haCent : a ∈ Subgroup.centralizer (M : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hmL : m ∈ L := Subgroup.mem_sup_left hm
    let mL : L := ⟨m, hmL⟩
    have hle : Subgroup.closure (conjSet M d) ≤
        Subgroup.centralizer ({aL} : Set L) := by
      rw [Subgroup.closure_le]
      intro u hu
      change u ∈ Subgroup.centralizer ({aL} : Set L)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hc : Commute (u : Y) a := hcommConj u hu
      have hc' : a * (u : Y) = (u : Y) * a := hc.symm.eq
      show aL * u = u * aL
      exact Subtype.ext hc'
    have hmClosure : mL ∈ Subgroup.closure (conjSet M d) := by
      rw [hcl.2.2]
      exact Subgroup.mem_top mL
    have hcL := hle hmClosure
    rw [Subgroup.mem_centralizer_iff] at hcL
    have hc : Commute aL mL := hcL aL (Set.mem_singleton aL)
    have hc' : a * m = m * a := by
      have := congrArg (Subtype.val : L → Y) hc.eq
      simpa using this
    exact hc'.symm
  have haBot : a ∈ (⊥ : Subgroup Y) := by
    rw [← hC]
    exact haCent
  have ha1 : a = 1 := Subgroup.mem_bot.mp haBot
  have hord : orderOf a = 2 := hS.oddT.orderOf_eq_two ha
  rw [ha1, orderOf_one] at hord
  exact absurd hord (by decide)

end ConnLemmas

end CFSG.OddTranspositions.PartThree
