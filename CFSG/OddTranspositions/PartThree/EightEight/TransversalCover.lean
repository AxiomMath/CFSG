module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Closure.MinCex
import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Opposite.Moufang
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate43
public import Mathlib
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def transversalGroup (E : Set X) (m : X) : Subgroup X :=
  Subgroup.closure {p | p ∈ E ∧ Commute p m}

theorem transversalGroup_le_centralizer (E : Set X) (m : X) :
    transversalGroup E m ≤ Subgroup.centralizer {m} := by
  rw [transversalGroup, Subgroup.closure_le]
  rintro p ⟨-, hpm⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr hpm.eq

private theorem commute_of_mem_transversalGroup {E : Set X} {m : X} {x : X}
    (hx : x ∈ transversalGroup E m) : Commute x m :=
  (commute_iff_eq x m).mpr (Subgroup.mem_centralizer_singleton_iff.mp
    (transversalGroup_le_centralizer E m hx))

theorem surjective_transversalGroup {π : X →* Y} (hπ : Function.Surjective π) {E : Set X}
    (hgen : Subgroup.closure E = ⊤) {m : X}
    (hex : ∀ p ∈ E, ∃ q, q ∈ E ∧ π q = π p ∧ Commute q m) :
    Function.Surjective (π.comp (transversalGroup E m).subtype) := by
  have hE₀ : π '' E ⊆ π '' {p : X | p ∈ E ∧ Commute p m} := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hqE, hqπ, hqm⟩ := hex p hp
    exact ⟨q, ⟨hqE, hqm⟩, hqπ⟩
  have htop : (transversalGroup E m).map π = ⊤ := by
    rw [transversalGroup, MonoidHom.map_closure]
    have htop' : Subgroup.closure (π '' E) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective π hπ]
    have hmono := Subgroup.closure_mono hE₀
    rw [htop'] at hmono
    exact top_le_iff.mp hmono
  rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, htop]

theorem ker_transversalGroup_eq_center {π : X →* Y} (hπ : Function.Surjective π)
    (hY : Subgroup.center Y = ⊥) {E : Set X} (hnorm : IsNormalSet E)
    (hgen : Subgroup.closure E = ⊤) {m : X}
    (huniq : ∀ p ∈ E, ∃! q, q ∈ E ∧ π q = π p ∧ Commute q m) :
    (π.comp (transversalGroup E m).subtype).ker = Subgroup.center (transversalGroup E m) := by
  apply le_antisymm
  · intro k hk
    have hπk : π (k : X) = 1 := by simpa using hk
    have hcomm : ∀ q ∈ {p : X | p ∈ E ∧ Commute p m},
        (k : X) * q * (k : X)⁻¹ = q := by
      intro q hq
      have hkm : Commute (k : X) m := commute_of_mem_transversalGroup k.2
      have hconjm : Commute ((k : X) * q * (k : X)⁻¹) m :=
        (hkm.mul_left hq.2).mul_left hkm.inv_left
      have hconjE : (k : X) * q * (k : X)⁻¹ ∈ E := hnorm (k : X) q hq.1
      have hπconj : π ((k : X) * q * (k : X)⁻¹) = π q := by
        simp [map_mul, hπk]
      obtain ⟨r, -, huniqr⟩ := huniq q hq.1
      exact (huniqr _ ⟨hconjE, hπconj, hconjm⟩).trans
        (huniqr q ⟨hq.1, rfl, hq.2⟩).symm
    have hle : transversalGroup E m ≤ Subgroup.centralizer ({(k : X)} : Set X) := by
      change Subgroup.closure {p : X | p ∈ E ∧ Commute p m} ≤
        Subgroup.centralizer ({(k : X)} : Set X)
      rw [Subgroup.closure_le]
      intro q hq
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc q * (k : X) = ((k : X) * q * (k : X)⁻¹) * (k : X) := by rw [hcomm q hq]
          _ = (k : X) * q := by group)
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (by
      simpa only [Subgroup.coe_mul] using
        Subgroup.mem_centralizer_singleton_iff.mp (hle h.2))
  · intro k hk
    have hsurj := surjective_transversalGroup hπ hgen
      (fun p hp => (huniq p hp).exists)
    have hcenter : π (k : X) ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, hh⟩ := hsurj y
      have hh' : π (h : X) = y := by simpa using hh
      have hkh : h * k = k * h := Subgroup.mem_center_iff.mp hk h
      have hkhX : (h : X) * (k : X) = (k : X) * (h : X) := by
        simpa only [Subgroup.coe_mul] using congrArg (fun t : transversalGroup E m => (t : X)) hkh
      calc y * π (k : X) = π ((h : X) * (k : X)) := by rw [← hh', map_mul]
        _ = π ((k : X) * (h : X)) := by rw [hkhX]
        _ = π (k : X) * y := by rw [map_mul, hh']
    have hbot : π (k : X) = 1 := by
      rw [hY, Subgroup.mem_bot] at hcenter
      exact hcenter
    simpa using hbot

private theorem isConjClass_transversalGroup {π : X →* Y} (hπ : Function.Surjective π)
    {E : Set X} (hclassE : ∃ d₀ : X, E = {g | IsConj d₀ g})
    (hgen : Subgroup.closure E = ⊤) {m : X}
    (huniq : ∀ p ∈ E, ∃! q, q ∈ E ∧ π q = π p ∧ Commute q m)
    (q₀H : transversalGroup E m) (hq₀E : (q₀H : X) ∈ E) :
    ((transversalGroup E m).subtype ⁻¹' {p : X | p ∈ E ∧ Commute p m}) =
      {g : transversalGroup E m | IsConj q₀H g} := by
  have hsurj := surjective_transversalGroup hπ hgen (fun p hp => (huniq p hp).exists)
  ext g
  constructor
  · intro hgS
    have hgE : (g : X) ∈ E := hgS.1
    have hgcomm : Commute (g : X) m := hgS.2
    obtain ⟨a, ha⟩ := isConj_iff.mp (isConj_of_isClass hclassE hq₀E hgE)
    obtain ⟨h, hh⟩ := hsurj (π a)
    let k : transversalGroup E m := h * q₀H * h⁻¹
    have hkE : (k : X) ∈ E := by
      have hconj := conj_mem_of_isClass hclassE (h : X) hq₀E
      simpa [k] using hconj
    have hkcomm : Commute (k : X) m := commute_of_mem_transversalGroup k.2
    have hkcoe : (k : X) = (h : X) * (q₀H : X) * (h : X)⁻¹ := by simp [k]
    have hh' : π (h : X) = π a := by simpa using hh
    have hπk : π (k : X) = π (g : X) := by
      rw [hkcoe, ← ha]
      simp [map_mul, hh']
    obtain ⟨r, -, huniqr⟩ := huniq (g : X) hgE
    have hkr : (k : X) = r := huniqr (k : X) ⟨hkE, hπk, hkcomm⟩
    have hgr : (g : X) = r := huniqr (g : X) ⟨hgE, rfl, hgcomm⟩
    change IsConj q₀H g
    rw [isConj_iff]
    exact ⟨h, Subtype.ext (hkr.trans hgr.symm)⟩
  · intro hg
    change IsConj q₀H g at hg
    rw [isConj_iff] at hg
    obtain ⟨c, hc⟩ := hg
    have hcX : (c : X) * (q₀H : X) * (c : X)⁻¹ = (g : X) := by
      simpa using congrArg (fun t : transversalGroup E m => (t : X)) hc
    constructor
    · change (g : X) ∈ E
      rw [← hcX]
      exact conj_mem_of_isClass hclassE (c : X) hq₀E
    · exact commute_of_mem_transversalGroup g.2

theorem isOddTranspClass_transversalGroup {π : X →* Y} (hπ : Function.Surjective π) {E : Set X}
    (hE : IsOddTranspClass E) {m : X}
    (huniq : ∀ p ∈ E, ∃! q, q ∈ E ∧ π q = π p ∧ Commute q m) :
    IsOddTranspClass ((transversalGroup E m).subtype ⁻¹' {p | p ∈ E ∧ Commute p m}) := by
  obtain ⟨⟨d₀, hclassE⟩, hoddE, hgenE⟩ := hE
  have hd₀E : d₀ ∈ E := by
    rw [hclassE]
    exact IsConj.refl d₀
  obtain ⟨q₀, hq₀, -⟩ := huniq d₀ hd₀E
  have hq₀E : q₀ ∈ E := hq₀.1
  let q₀H : transversalGroup E m := ⟨q₀, Subgroup.subset_closure ⟨hq₀E, hq₀.2.2⟩⟩
  have hclass := isConjClass_transversalGroup hπ ⟨d₀, hclassE⟩ hgenE huniq q₀H hq₀E
  have hoddS : IsOddTransp ((transversalGroup E m).subtype ⁻¹'
      {p : X | p ∈ E ∧ Commute p m}) :=
    (hoddE.mono (fun _ hp => hp.1)).preimage (transversalGroup E m)
  change (∃ d₀ : transversalGroup E m,
      ((transversalGroup E m).subtype ⁻¹' {p : X | p ∈ E ∧ Commute p m}) =
        {g : transversalGroup E m | IsConj d₀ g}) ∧
    IsOddTransp ((transversalGroup E m).subtype ⁻¹' {p : X | p ∈ E ∧ Commute p m}) ∧
    Subgroup.closure ((transversalGroup E m).subtype ⁻¹' {p : X | p ∈ E ∧ Commute p m}) = ⊤
  refine ⟨⟨q₀H, hclass⟩, hoddS, ?_⟩
  exact Subgroup.closure_closure_coe_preimage

end CFSG.OddTranspositions.PartThree.EightEight

end
