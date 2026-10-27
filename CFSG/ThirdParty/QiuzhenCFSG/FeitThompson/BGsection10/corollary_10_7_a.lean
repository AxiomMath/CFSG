module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_6
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Corollary 10.7(a) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section10_global_pSubgroup_proper_of_min_ce
    {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hRp : IsPGroup p R) :
    R ≠ ⊤ := by
  exact IsMinCE.pSubgroup_ne_top (G := G) (p := p) hRp

public theorem CFSG.section10_sylow_normalizer_ne_top_of_ne_bot
    {p : Nat.Primes} (P : Sylow p.val G) (hPne : (P : Subgroup G) ≠ ⊥) :
    Subgroup.normalizer (((P : Subgroup G) : Set G)) ≠ ⊤ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  intro hnorm_top
  have hPnormal : (P : Subgroup G).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hnorm_top
  let : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hPnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G)) with hPbot | hPtop
  · exact hPne hPbot
  · exact section10_global_pSubgroup_proper_of_min_ce (G := G)
      (p := p.val) P.isPGroup' hPtop

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_normalizer_map_subtype_eq_of_map_eq
    {M P : Subgroup G} {Q : Subgroup M}
    (hQmap : Q.map M.subtype = P)
    (hN_le_M : Subgroup.normalizer (P : Set G) ≤ M) :
    (Subgroup.normalizer (Q : Set M)).map M.subtype =
      Subgroup.normalizer (P : Set G) := by
  classical
  have hP_le_M : P ≤ M := by
    intro x hxP
    have hxmap : x ∈ Q.map M.subtype := by simpa [hQmap] using hxP
    rcases Subgroup.mem_map.mp hxmap with ⟨y, _hy, rfl⟩
    exact y.property
  ext x
  constructor
  · rintro ⟨y, hyNorm, rfl⟩
    have hyNorm' := (Subgroup.mem_normalizer_iff.mp hyNorm)
    change (y : G) ∈ Subgroup.normalizer (P : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hzP
      have hzQmap : z ∈ Q.map M.subtype := by simpa [hQmap] using hzP
      rcases Subgroup.mem_map.mp hzQmap with ⟨zM, hzQ, hz_eq⟩
      have hconjQ : y * zM * y⁻¹ ∈ Q := (hyNorm' zM).1 hzQ
      have hconjMap :
          (((y * zM * y⁻¹ : M) : G)) ∈ Q.map M.subtype :=
        Subgroup.mem_map_of_mem M.subtype hconjQ
      have hconjP : (y : G) * z * (y : G)⁻¹ ∈ P := by
        simpa [hQmap, ← hz_eq, mul_assoc] using hconjMap
      simpa using hconjP
    · intro hzConjP
      have hzConjM : (y : G) * z * (y : G)⁻¹ ∈ M := hP_le_M hzConjP
      have hzM : z ∈ M := by
        have hz' :
            (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) ∈ M :=
          M.mul_mem (M.mul_mem (M.inv_mem y.property) hzConjM) y.property
        simpa [mul_assoc] using hz'
      let zM : M := ⟨z, hzM⟩
      have hconjQmap :
          (((y * zM * y⁻¹ : M) : G)) ∈ Q.map M.subtype := by
        simpa [hQmap, zM, mul_assoc] using hzConjP
      rcases Subgroup.mem_map.mp hconjQmap with ⟨w, hwQ, hw_eq⟩
      have hw_eq' : w = y * zM * y⁻¹ := Subtype.ext hw_eq
      have hconjQ : y * zM * y⁻¹ ∈ Q := by simpa [← hw_eq'] using hwQ
      have hzQ : zM ∈ Q := (hyNorm' zM).2 hconjQ
      have hzQmap : z ∈ Q.map M.subtype :=
        Subgroup.mem_map_of_mem M.subtype hzQ
      simpa [hQmap, zM] using hzQmap
  · intro hxNorm
    have hxNorm' := (Subgroup.mem_normalizer_iff.mp hxNorm)
    have hxM : x ∈ M := hN_le_M hxNorm
    let xM : M := ⟨x, hxM⟩
    refine ⟨xM, ?_, rfl⟩
    change xM ∈ Subgroup.normalizer (Q : Set M)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hzQ
      have hzP : (z : G) ∈ P := by
        have hzmap : (z : G) ∈ Q.map M.subtype :=
          Subgroup.mem_map_of_mem M.subtype hzQ
        simpa [hQmap] using hzmap
      have hconjP : x * (z : G) * x⁻¹ ∈ P := (hxNorm' (z : G)).1 hzP
      have hconjQmap :
          (((xM * z * xM⁻¹ : M) : G)) ∈ Q.map M.subtype := by
        simpa [hQmap, xM, mul_assoc] using hconjP
      rcases Subgroup.mem_map.mp hconjQmap with ⟨w, hwQ, hw_eq⟩
      have hw_eq' : w = xM * z * xM⁻¹ := Subtype.ext hw_eq
      simpa [← hw_eq'] using hwQ
    · intro hzConjQ
      have hzConjP : x * (z : G) * x⁻¹ ∈ P := by
        have hzmap :
            (((xM * z * xM⁻¹ : M) : G)) ∈ Q.map M.subtype :=
          Subgroup.mem_map_of_mem M.subtype hzConjQ
        simpa [hQmap, xM, mul_assoc] using hzmap
      have hzP : (z : G) ∈ P := (hxNorm' (z : G)).2 hzConjP
      have hzQmap : (z : G) ∈ Q.map M.subtype := by simpa [hQmap] using hzP
      rcases Subgroup.mem_map.mp hzQmap with ⟨w, hwQ, hw_eq⟩
      have hw_eq' : w = z := Subtype.ext hw_eq
      simpa [← hw_eq'] using hwQ

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_subgroupOf_normalizer_isHall
    {p : Nat.Primes} (P : Sylow p.val G) :
    IsHallSubgroup ({p} : Set Nat.Primes)
      ((P : Subgroup G).subgroupOf
        (Subgroup.normalizer (((P : Subgroup G) : Set G)))) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
  let Psub : Subgroup N := (P : Subgroup G).subgroupOf N
  have hP_le_N : (P : Subgroup G) ≤ N := by
    simpa [N] using (Subgroup.le_normalizer : (P : Subgroup G) ≤
      Subgroup.normalizer (((P : Subgroup G) : Set G)))
  let PN : Sylow p.val N := P.subtype hP_le_N
  have hPsub_eq : Psub = (PN : Subgroup N) := by
    ext x
    simp [Psub, PN, Sylow.subtype, N, Subgroup.mem_subgroupOf]
  refine isHallSubgroup_of (G := N) (π := ({p} : Set Nat.Primes)) (H := Psub) ?_ ?_
  · intro q hq_dvd
    have hPsubp : IsPGroup p.val Psub := by
      change IsPGroup p.val ((P : Subgroup G).subgroupOf N)
      exact P.isPGroup'.of_equiv
        (Subgroup.subgroupOfEquivOfLe hP_le_N).symm
    exact section8_isPiSubgroup_singleton_of_isPGroup hPsubp q hq_dvd
  · intro q hq_mem hq_dvd_index
    have hq_eq : q = p := by simpa using hq_mem
    subst q
    exact PN.not_dvd_index (by simpa [hPsub_eq] using hq_dvd_index)

private theorem CFSG.section10_sylow_le_ambientDerived_normalizer
    {p : Nat.Primes} (P : Sylow p.val G) (hPne : (P : Subgroup G) ≠ ⊥) :
    (P : Subgroup G) ≤
      ambientDerivedSubgroup (Subgroup.normalizer (((P : Subgroup G) : Set G))) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
  have hNproper : N ≠ ⊤ := by
    simpa [N] using section10_sylow_normalizer_ne_top_of_ne_bot (G := G) P hPne
  obtain ⟨M, hMcont⟩ :=
    section10_exists_maximalSubgroupsContaining_of_ne_top (G := G) hNproper
  have hM : M ∈ section9MaximalSubgroups G := hMcont.1
  have hNM : N ≤ M := hMcont.2
  have hP_le_N : (P : Subgroup G) ≤ N := by
    simpa [N] using (Subgroup.le_normalizer : (P : Subgroup G) ≤
      Subgroup.normalizer (((P : Subgroup G) : Set G)))
  have hP_le_M : (P : Subgroup G) ≤ M := hP_le_N.trans hNM
  let PM : Sylow p.val M := P.subtype hP_le_M
  have hPMmap : (PM : Subgroup M).map M.subtype = (P : Subgroup G) := by
    change ((P : Subgroup G).subgroupOf M).map M.subtype = (P : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (P : Subgroup G)) (K := M) hP_le_M
  have hp_dvd_P : p.val ∣ Nat.card (P : Subgroup G) := by
    rcases P.isPGroup'.card_eq_or_dvd with hcard | hdiv
    · exact False.elim (hPne ((Subgroup.card_eq_one (H := (P : Subgroup G))).mp hcard))
    · exact hdiv
  have hpM : p ∈ subgroupPrimeSet M := by
    simpa [subgroupPrimeSet] using hp_dvd_P.trans (Subgroup.card_dvd_of_le hP_le_M)
  have hpσ : p ∈ section10SigmaPrimes M := by
    refine ⟨hpM, PM, ?_⟩
    simpa [section10AmbientSylowSubgroup, hPMmap, N] using hNM
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hplM : HasPLengthOne p.val M :=
    theorem_10_6 (G := G) (H := M) (p := p) hM.1
  have hPM_le_der : (PM : Subgroup M) ≤ derivedSubgroup M :=
    section10_sigma_sylow_le_derivedSubgroup hM hpσ PM
  let NM : Subgroup M := Subgroup.normalizer (((PM : Subgroup M) : Set M))
  have hPM_le_comm : (PM : Subgroup M) ≤ ⁅NM, NM⁆ := by
    simpa [NM] using
      lemma_6_6_b (G := M) (p := p.val) hplM (S := PM) hPM_le_der
  have hNMmap : NM.map M.subtype = N := by
    simpa [NM, N] using
      section10_normalizer_map_subtype_eq_of_map_eq
        (G := G) (M := M) (P := (P : Subgroup G)) (Q := (PM : Subgroup M))
        hPMmap (by simpa [N] using hNM)
  have hcomm_map : (⁅NM, NM⁆).map M.subtype = ⁅N, N⁆ := by
    calc
      (⁅NM, NM⁆).map M.subtype =
          ⁅NM.map M.subtype, NM.map M.subtype⁆ := by
        simpa using (Subgroup.map_commutator (H₁ := NM) (H₂ := NM) M.subtype)
      _ = ⁅N, N⁆ := by rw [hNMmap]
  have hP_le_map_comm : (P : Subgroup G) ≤ (⁅NM, NM⁆).map M.subtype := by
    intro x hxP
    have hxPMmap : x ∈ (PM : Subgroup M).map M.subtype := by
      simpa [hPMmap] using hxP
    rcases Subgroup.mem_map.mp hxPMmap with ⟨xM, hxPM, rfl⟩
    exact Subgroup.mem_map_of_mem M.subtype (hPM_le_comm hxPM)
  intro x hxP
  have hxNN : x ∈ ⁅N, N⁆ := by
    simpa [hcomm_map] using hP_le_map_comm hxP
  have hxmap : x ∈ (_root_.commutator N).map N.subtype := by
    simpa [Subgroup.map_subtype_commutator] using hxNN
  change x ∈ (derivedSeries N 1).map N.subtype
  rw [derivedSeries_one]
  exact hxmap

private theorem CFSG.section10_complement_commutator_eq_sylow
    {p : Nat.Primes} (P : Sylow p.val G) {V : Subgroup G}
    (hVcomp : section10ComplementInNormalizer P V)
    (hNproper : Subgroup.normalizer (((P : Subgroup G) : Set G)) ≠ ⊤)
    (hPder :
      (P : Subgroup G) ≤
        ambientDerivedSubgroup (Subgroup.normalizer (((P : Subgroup G) : Set G)))) :
    ⁅(P : Subgroup G), V⁆ = (P : Subgroup G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
  rcases hVcomp with ⟨hVleN, hcomp'⟩
  let Psub : Subgroup N := (P : Subgroup G).subgroupOf N
  let Vsub : Subgroup N := V.subgroupOf N
  have hP_le_N : (P : Subgroup G) ≤ N := by
    simpa [N] using (Subgroup.le_normalizer : (P : Subgroup G) ≤
      Subgroup.normalizer (((P : Subgroup G) : Set G)))
  have : Psub.Normal := by
    simpa [Psub, N] using
      (Subgroup.normal_in_normalizer (H := (P : Subgroup G)))
  have : Group.IsSolvable N :=
    IsMinCE.proper_subgroups_solvable N (lt_top_iff_ne_top.2 (by simpa [N] using hNproper))
  have hHall : IsHallSubgroup ({p} : Set Nat.Primes) Psub := by
    simpa [Psub, N] using section10_sylow_subgroupOf_normalizer_isHall (G := G) P
  have hld : Psub ≤ derivedSubgroup N := by
    intro x hxPsub
    have hxP : ((x : N) : G) ∈ (P : Subgroup G) := by
      simpa [Psub, Subgroup.mem_subgroupOf] using hxPsub
    have hxDer : ((x : N) : G) ∈ ambientDerivedSubgroup N := hPder hxP
    rcases Subgroup.mem_map.mp hxDer with ⟨d, hd, hd_eq⟩
    have hxd : x = d := Subtype.ext hd_eq.symm
    simpa [hxd] using hd
  have hlocal :
      Psub = ⁅Psub, Vsub⁆ :=
    lemma_6_3_a_1 (G := N) (H := Psub) ⟨({p} : Set Nat.Primes), hHall⟩
      hcomp'.isCompl hld
  have hmap_eq :
      Psub.map N.subtype = (⁅Psub, Vsub⁆).map N.subtype :=
    congrArg (fun K : Subgroup N => K.map N.subtype) hlocal
  have hPmap : Psub.map N.subtype = (P : Subgroup G) := by
    simpa [Psub, N] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (P : Subgroup G)) (K := N) hP_le_N)
  have hcomm_map :
      (⁅Psub, Vsub⁆).map N.subtype = ⁅(P : Subgroup G), V⁆ := by
    simpa [Psub, Vsub, N] using
      (commutator_subgroupOf_map_eq (S := N) (H := V) (R := (P : Subgroup G))
        hVleN hP_le_N)
  have hP_eq_comm : (P : Subgroup G) = ⁅(P : Subgroup G), V⁆ := by
    simpa [hPmap, hcomm_map] using hmap_eq
  exact hP_eq_comm.symm

/-- Corollary 10.7(a). -/
public theorem CFSG.corollary_10_7_a
    {p : Nat.Primes} (P : Sylow p.val G) {V : Subgroup G}
    (hVcomp : section10ComplementInNormalizer P V) :
    (P : Subgroup G) ≤ ambientDerivedSubgroup (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      ⁅(P : Subgroup G), V⁆ = (P : Subgroup G) := by
  classical
  by_cases hPbot : (P : Subgroup G) = ⊥
  · constructor
    · simp [hPbot]
    · rw [hPbot, Subgroup.commutator_bot_left]
  · have hPder :
        (P : Subgroup G) ≤
          ambientDerivedSubgroup (Subgroup.normalizer (((P : Subgroup G) : Set G))) :=
      section10_sylow_le_ambientDerived_normalizer (G := G) P hPbot
    have hNproper :
        Subgroup.normalizer (((P : Subgroup G) : Set G)) ≠ ⊤ :=
      section10_sylow_normalizer_ne_top_of_ne_bot (G := G) P hPbot
    exact ⟨hPder,
      section10_complement_commutator_eq_sylow (G := G) P hVcomp hNproper hPder⟩

end Section10
