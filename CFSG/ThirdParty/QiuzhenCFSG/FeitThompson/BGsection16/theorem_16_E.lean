module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_D
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 16 e from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_conjugatesOfSetBySet_univ_eq_section14ConjugacyClosure
    (X : Set G) :
    section16ConjugatesOfSetBySet X Set.univ = section14ConjugacyClosure X := by
  ext z
  constructor
  · rintro ⟨x, hx, g, _hg, rfl⟩
    refine ⟨x, hx, g⁻¹, ?_⟩
    simp [mul_assoc]
  · rintro ⟨x, hx, g, rfl⟩
    refine ⟨x, hx, g⁻¹, by simp, ?_⟩
    simp [mul_assoc]

private theorem CFSG.section16_tildeM_section14R_eq
    (M : Subgroup G) :
    section16TildeM M (fun x : G => section14R x) = section14Tilde M := by
  ext y
  constructor
  · rintro ⟨x, hxMσ, hxne, r, hr, rfl⟩
    exact ⟨x, hxMσ, hxne, r, hr, rfl⟩
  · rintro ⟨x, hxMσ, hxne, r, hr, rfl⟩
    exact ⟨x, hxMσ, hxne, r, hr, rfl⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_conjugacyClassRepresentatives_of_list
    {Ms : List (Subgroup G)}
    (hMs : section16MaximalConjugacyRepresentatives (G := G) Ms) :
    section14ConjugacyClassRepresentatives (fun i : Fin Ms.length => Ms.get i) := by
  classical
  constructor
  · intro i
    exact hMs.1 (Ms.get i) (List.get_mem Ms i)
  · intro H hH
    rcases hMs.2.2 H hH with ⟨M0, hM0, huniq⟩
    rcases List.mem_iff_get.mp hM0.1 with ⟨i0, hi0⟩
    refine ⟨i0, ?_, ?_⟩
    · change section14ConjugateSubgroups H (Ms.get i0)
      rw [hi0]
      simpa [section14ConjugateSubgroups] using hM0.2
    · intro j hj
      have hMj :
          Ms.get j ∈ Ms ∧ ∃ g : G, H = (Ms.get j).conjBy g := by
        exact ⟨List.get_mem Ms j, by simpa [section14ConjugateSubgroups] using hj⟩
      have hget_j : Ms.get j = M0 := huniq (Ms.get j) hMj
      have hget_i : Ms.get i0 = M0 := by
        simpa [hi0]
      exact (hMs.2.1.get_inj_iff).1 (hget_j.trans hget_i.symm)

private theorem CFSG.section16_tildeGForRepresentatives_section14_iUnion_eq
    (Ms : List (Subgroup G)) :
    section16TildeGForRepresentatives Ms (fun _ x => section14R x) =
      ⋃ i : Fin Ms.length, section14ConjugacyClosure (section14Tilde (Ms.get i)) := by
  ext y
  constructor
  · rintro ⟨M, hMmem, hyM⟩
    rcases List.mem_iff_get.mp hMmem with ⟨i, hi⟩
    rw [section16_conjugatesOfSetBySet_univ_eq_section14ConjugacyClosure,
      section16_tildeM_section14R_eq] at hyM
    exact Set.mem_iUnion.mpr ⟨i, by rw [hi]; exact hyM⟩
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    refine ⟨Ms.get i, List.get_mem Ms i, ?_⟩
    rw [section16_conjugatesOfSetBySet_univ_eq_section14ConjugacyClosure,
      section16_tildeM_section14R_eq]
    exact hyi


/-- Theorem E(2): the prime divisors of `G` are the disjoint union of the
sets `sigma(M_i)` for maximal subgroup conjugacy-class representatives. -/
public theorem CFSG.theorem_16_E_2
    (Ms : List (Subgroup G))
    (hMs : section16MaximalConjugacyRepresentatives (G := G) Ms) :
    section16ListDisjointUnion (Ms.map section10SigmaPrimes)
      (subgroupPrimeSet (⊤ : Subgroup G)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro q
    constructor
    · intro hq
      haveI : Fact q.val.Prime := ⟨q.property⟩
      let P : Sylow q.val G := Classical.choice (Sylow.nonempty (p := q.val) (G := G))
      have hPne : (P : Subgroup G) ≠ ⊥ := by
        intro hPbot
        have hqG : q.val ∣ Nat.card G := by
          simpa [subgroupPrimeSet] using hq
        have hqIndex : q.val ∣ (P : Subgroup G).index := by
          simpa [hPbot, Subgroup.index_bot] using hqG
        exact P.not_dvd_index hqIndex
      have hPnontrivial : Nontrivial (P : Subgroup G) :=
        (Subgroup.nontrivial_iff_ne_bot (H := (P : Subgroup G))).2 hPne
      have hnorm_proper : Subgroup.normalizer ((P : Subgroup G) : Set G) ≠ ⊤ :=
        section10_sylow_normalizer_ne_top_of_ne_bot (G := G) P hPne
      rcases section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) hnorm_proper with
        ⟨M, hMcont⟩
      have hM : M ∈ section9MaximalSubgroups G := hMcont.1
      have hP_le_M : (P : Subgroup G) ≤ M :=
        (Subgroup.le_normalizer : (P : Subgroup G) ≤
          Subgroup.normalizer ((P : Subgroup G) : Set G)).trans hMcont.2
      let PM : Sylow q.val M := P.subtype hP_le_M
      have hPMmap : section10AmbientSylowSubgroup M PM = (P : Subgroup G) := by
        change Subgroup.map M.subtype ((P : Subgroup G).subgroupOf M) = (P : Subgroup G)
        exact Subgroup.map_subgroupOf_eq_of_le hP_le_M
      have hqP : q ∈ subgroupPrimeSet (P : Subgroup G) := by
        rcases (IsPGroup.nontrivial_iff_card (p := q.val) (G := P) (hG := P.isPGroup')).mp
            hPnontrivial with ⟨n, hnpos, hcard⟩
        rw [subgroupPrimeSet, hcard]
        exact dvd_pow_self _ hnpos.ne'
      have hqM : q ∈ subgroupPrimeSet M :=
        section8_subgroupPrimeSet_mono hP_le_M hqP
      have hpσM : q ∈ section10SigmaPrimes M := by
        refine ⟨hqM, PM, ?_⟩
        simpa [hPMmap] using hMcont.2
      rcases hMs.2.2 M hM with ⟨R, hR, huniq⟩
      rcases hR with ⟨hRmem, ⟨g, hMg⟩⟩
      have hpσR : q ∈ section10SigmaPrimes R := by
        rw [hMg, section16_sigmaPrimes_conjBy (G := G) R g] at hpσM
        exact hpσM
      rcases List.mem_iff_get.mp hRmem with ⟨iM, hiM⟩
      let i : Fin (Ms.map section10SigmaPrimes).length :=
        ⟨iM.1, by simp [List.length_map]⟩
      refine ⟨i, ?_⟩
      have hpσMi : q ∈ section10SigmaPrimes (Ms.get iM) := by
        simpa [hiM.symm] using hpσR
      simpa [i, List.length_map] using hpσMi
    · rintro ⟨i, hqi⟩
      let iM : Fin Ms.length := ⟨i.1, by simpa [List.length_map] using i.2⟩
      have hqiM : q ∈ section10SigmaPrimes (Ms.get iM) := by
        simpa [iM, List.length_map] using hqi
      exact section8_subgroupPrimeSet_mono
        (le_top : Ms.get iM ≤ (⊤ : Subgroup G)) hqiM.1
  · intro i j hij
    let iM : Fin Ms.length := ⟨i.1, by simpa [List.length_map] using i.2⟩
    let jM : Fin Ms.length := ⟨j.1, by simpa [List.length_map] using j.2⟩
    let Mi : Subgroup G := Ms.get iM
    let Mj : Subgroup G := Ms.get jM
    have hMi_mem : Mi ∈ Ms := by
      simp [Mi]
    have hMj_mem : Mj ∈ Ms := by
      simp [Mj]
    have hMi : Mi ∈ section9MaximalSubgroups G := hMs.1 Mi hMi_mem
    have hMj : Mj ∈ section9MaximalSubgroups G := hMs.1 Mj hMj_mem
    have hnotconj : section12NotConjugate Mj Mi := by
      intro g hconj
      rcases hMs.2.2 Mi hMi with ⟨R, hR, huniq⟩
      have hMi_eq_R : Mi = R := huniq Mi
        ⟨hMi_mem, ⟨1, by simpa using (section8_conjBy_one (G := G) Mi).symm⟩⟩
      have hMj_eq_R : Mj = R := huniq Mj ⟨hMj_mem, ⟨g, hconj.symm⟩⟩
      have hget_eq : Mi = Mj := hMi_eq_R.trans hMj_eq_R.symm
      have hlist_eq : Ms.get iM = Ms.get jM := by
        simpa [Mi, Mj] using hget_eq
      have hidx : iM = jM := (hMs.2.1.get_inj_iff).1 hlist_eq
      have hij' : i = j := by
        apply Fin.ext
        simpa [iM, jM] using congrArg Fin.val hidx
      exact hij hij'
    have hdis := theorem_13_9 (G := G) hMi hMj hnotconj
    simpa [Mi, Mj, iM, jM, List.length_map] using hdis


/-- The no-Type-`P` cover component of Theorem E(3), split out so PF8 can use
it without choosing a Type-`P` representative. -/
public theorem CFSG.theorem_16_E_3_noP_nonidentity_eq_tildeG
    (Ms : List (Subgroup G))
    (hMs : section16MaximalConjugacyRepresentatives (G := G) Ms)
    (hNoP : ∀ H : Subgroup G, ¬ section16MaximalTypeP H) :
    section16NonidentityElements (Set.univ : Set G) =
      section16TildeGForRepresentatives Ms (fun _ x => section14R x) := by
  classical
  let Ms14 : Fin Ms.length → Subgroup G := fun i => Ms.get i
  have hMs14 : section14ConjugacyClassRepresentatives (G := G) Ms14 := by
    simpa [Ms14] using section16_conjugacyClassRepresentatives_of_list (G := G) hMs
  have hTildeUnion :
      section16TildeGForRepresentatives Ms (fun _ x => section14R x) =
        ⋃ i : Fin Ms.length, section14ConjugacyClosure (section14Tilde (Ms14 i)) := by
    simpa [Ms14] using
      section16_tildeGForRepresentatives_section14_iUnion_eq (G := G) Ms
  have hPempty : section14MFamilyP G = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro H hH
    exact hNoP H (by simpa [section16MaximalTypeP] using hH)
  have hcover :=
    (corollary_14_9_a (G := G) (Ms := Ms14) hMs14 hPempty).2
  calc
    section16NonidentityElements (Set.univ : Set G) = ({g : G | g ≠ 1} : Set G) := by
      ext g
      simp [section16NonidentityElements]
    _ = ⋃ i : Fin Ms.length, section14ConjugacyClosure (section14Tilde (Ms14 i)) := hcover
    _ = section16TildeGForRepresentatives Ms (fun _ x => section14R x) :=
      hTildeUnion.symm


end MainResults
