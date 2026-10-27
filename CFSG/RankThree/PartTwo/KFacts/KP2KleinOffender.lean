module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.LinearAlgebra.SL2MinimalFaithful
import CFSG.CGT.PushingUpLit.CGT6X.End4Perm
import CFSG.GH74.GLS.IVK.L2.ExistCyclic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.Assembly.QuasithinDefs
import CFSG.GH74.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP2

open Equiv

private abbrev Alt7 : Subgroup (Perm (Fin 7)) := alternatingGroup (Fin 7)

private theorem vTwo_le_alternatingGroup : vTwo ≤ Alt7 := by
  rintro x ⟨m, rfl⟩
  exact (vTwoF_spec m).2

private def V1A : Subgroup Alt7 := vTwo.comap Alt7.subtype

private theorem V1A_map : V1A.map Alt7.subtype = vTwo :=
  Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact vTwo_le_alternatingGroup)

private theorem card_V1A : Nat.card V1A = 4 := by
  rw [← Subgroup.card_map_of_injective Alt7.subtype_injective, V1A_map, card_vTwo]

private def sAlt7 : Alt7 :=
  ⟨swap (3 : Fin 7) 6 * swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap,
      Equiv.Perm.sign_swap] <;> decide⟩

private theorem sAlt7_conj_one :
    (sAlt7 : Perm (Fin 7)) * (1 : Perm (Fin 7)) * (sAlt7 : Perm (Fin 7))⁻¹ =
      vTwoF 0 := by
  decide +kernel

private theorem sAlt7_conj_kA :
    (sAlt7 : Perm (Fin 7)) * (CFSG.CGT.PushingUpLit.CGT6X.End4.kA : Perm (Fin 7)) *
      (sAlt7 : Perm (Fin 7))⁻¹ = vTwoF 1 := by
  decide +kernel

private theorem sAlt7_conj_kB :
    (sAlt7 : Perm (Fin 7)) * (CFSG.CGT.PushingUpLit.CGT6X.End4.kB : Perm (Fin 7)) *
      (sAlt7 : Perm (Fin 7))⁻¹ = vTwoF 2 := by
  decide +kernel

private theorem sAlt7_conj_kAkB :
    (sAlt7 : Perm (Fin 7)) *
      ((CFSG.CGT.PushingUpLit.CGT6X.End4.kA * CFSG.CGT.PushingUpLit.CGT6X.End4.kB :
        Alt7) : Perm (Fin 7)) * (sAlt7 : Perm (Fin 7))⁻¹ = vTwoF 3 := by
  decide +kernel

private theorem V1A_eq_map_kleinA7 :
    V1A = CFSG.CGT.PushingUpLit.CGT6X.End4.kleinA7.map
      (MulAut.conjNormal (H := Alt7) (sAlt7 : Perm (Fin 7))).toMonoidHom := by
  let kA := CFSG.CGT.PushingUpLit.CGT6X.End4.kA
  let kB := CFSG.CGT.PushingUpLit.CGT6X.End4.kB
  have hkA : kA ∈ CFSG.CGT.PushingUpLit.CGT6X.End4.kleinA7 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hkB : kB ∈ CFSG.CGT.PushingUpLit.CGT6X.End4.kleinA7 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hkAB : kA * kB ∈ CFSG.CGT.PushingUpLit.CGT6X.End4.kleinA7 := mul_mem hkA hkB
  ext x
  constructor
  · intro hx
    rcases mem_vTwo.mp hx with ⟨m, hm⟩
    change (x : Perm (Fin 7)) = vTwoF m at hm
    fin_cases m
    · refine Subgroup.mem_map.mpr ⟨1, one_mem _, ?_⟩
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hm]
      exact sAlt7_conj_one
    · refine Subgroup.mem_map.mpr ⟨kA, hkA, ?_⟩
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hm]
      exact sAlt7_conj_kA
    · refine Subgroup.mem_map.mpr ⟨kB, hkB, ?_⟩
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hm]
      exact sAlt7_conj_kB
    · refine Subgroup.mem_map.mpr ⟨kA * kB, hkAB, ?_⟩
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hm]
      exact sAlt7_conj_kAkB
  · rintro ⟨y, hy, rfl⟩
    have hy1 : y = 1 ∨ y = kA ∨ y = kB ∨ y = kA * kB := by
      simpa only [CFSG.CGT.PushingUpLit.CGT6X.End4.coe_kleinA7, Finset.coe_insert,
        Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] using hy
    change ((MulAut.conjNormal (H := Alt7) (sAlt7 : Perm (Fin 7))) y : Perm (Fin 7)) ∈ vTwo
    rw [mem_vTwo]
    rcases hy1 with rfl | rfl | rfl | rfl
    · exact ⟨0, by simpa [MulAut.conjNormal_apply] using sAlt7_conj_one⟩
    · exact ⟨1, by simpa [MulAut.conjNormal_apply] using sAlt7_conj_kA⟩
    · exact ⟨2, by simpa [MulAut.conjNormal_apply] using sAlt7_conj_kB⟩
    · exact ⟨3, by simpa [MulAut.conjNormal_apply] using sAlt7_conj_kAkB⟩

private def e0 : Alt7 := ⟨cOne, eNine_le_alternatingGroup cOne_mem_eNine⟩

private theorem cOne_conj_vTwoF : ∀ m : Fin 4, ∃ k : Fin 4,
    cOne * vTwoF m * cOne⁻¹ = vTwoF k := by
  decide +kernel

private theorem e0_mem_V1A_map : V1A.map
    (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))).toMonoidHom ≤ V1A := by
  rintro x ⟨y, hy, rfl⟩
  rcases mem_vTwo.mp hy with ⟨m, hm⟩
  change (y : Perm (Fin 7)) = vTwoF m at hm
  change ((MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))) y : Perm (Fin 7)) ∈ vTwo
  rw [mem_vTwo]
  obtain ⟨k, hk⟩ := cOne_conj_vTwoF m
  refine ⟨k, ?_⟩
  simp only [e0, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
  rw [hm]
  exact hk

private theorem e0_V1A_map : V1A.map
    (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))).toMonoidHom = V1A := by
  refine Subgroup.eq_of_le_of_card_ge e0_mem_V1A_map ?_
  have hmapcard : Nat.card (V1A.map
      (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))).toMonoidHom) = Nat.card V1A :=
    Subgroup.card_map_of_injective (K := V1A)
      (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))).injective
  rw [hmapcard, card_V1A]

private theorem e0_no_fixed {x : Alt7} (hx : x ∈ V1A) (hx1 : x ≠ 1) :
    (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))) x ≠ x := by
  intro hconj
  rcases mem_vTwo.mp hx with ⟨m, hm⟩
  change (x : Perm (Fin 7)) = vTwoF m at hm
  have hm0 : m ≠ 0 := by
    intro h
    apply hx1
    apply Subtype.ext
    change (x : Perm (Fin 7)) = 1
    rw [hm, h]
    decide +kernel
  have h' : cOne * (x : Perm (Fin 7)) * cOne⁻¹ = (x : Perm (Fin 7)) := by
    simpa only [e0, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply] using
      congrArg (fun y : Alt7 => (y : Perm (Fin 7))) hconj
  rw [hm] at h'
  have hcomm : vTwoF m * cOne = cOne * vTwoF m := by
    calc
      vTwoF m * cOne = (cOne * vTwoF m * cOne⁻¹) * cOne := by rw [h']
      _ = cOne * vTwoF m := by group
  exact vTwoF_not_commute m hm0 hcomm

private def conjugateKleinA7 (g : Perm (Fin 7)) : Subgroup Alt7 :=
  (vTwo.map (MulAut.conj g).toMonoidHom).comap Alt7.subtype

private theorem conjugateKleinA7_eq (g : Perm (Fin 7)) :
    conjugateKleinA7 g = V1A.map
      (MulAut.conjNormal (H := Alt7) g).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hyx⟩
    have hya : y ∈ Alt7 := vTwo_le_alternatingGroup hy
    refine Subgroup.mem_map.mpr ⟨⟨y, hya⟩, hy, ?_⟩
    apply Subtype.ext
    change g * (y : Perm (Fin 7)) * g⁻¹ = ((x : Alt7) : Perm (Fin 7))
    simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype] using hyx
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(a : Perm (Fin 7)), ?_, ?_⟩
    · exact ha
    · change g * (a : Perm (Fin 7)) * g⁻¹ = ((MulAut.conjNormal (H := Alt7) g) a : Perm (Fin 7))
      rw [MulAut.conjNormal_apply]

private theorem card_conjugateKleinA7 (g : Perm (Fin 7)) :
    Nat.card (conjugateKleinA7 g) = 4 := by
  have hmapcard : Nat.card (V1A.map
      (MulAut.conjNormal (H := Alt7) g).toMonoidHom) = Nat.card V1A :=
    Subgroup.card_map_of_injective (K := V1A) (MulAut.conjNormal (H := Alt7) g).injective
  rw [conjugateKleinA7_eq, hmapcard, card_V1A]

private abbrev fixedSubgroup {X M : Type*} [Group X] [Group M]
    (ρ : X →* MulAut M) (H : Subgroup X) : Subgroup M :=
  CFSG.SL2MinimalFaithful.fixedPoints ρ H

private theorem fixedSubgroup_inf {X M : Type*} [Group X] [Group M]
    (ρ : X →* MulAut M) (H K : Subgroup X) :
    fixedSubgroup ρ H ⊓ fixedSubgroup ρ K = fixedSubgroup ρ (H ⊔ K) :=
  CFSG.SL2MinimalFaithful.fixedPoints_inf ρ H K

private theorem map_fixedSubgroup_conj {X M : Type*} [Group X] [Group M]
    (ρ : X →* MulAut M) (H : Subgroup X) (g : X) :
    (fixedSubgroup ρ H).map (ρ g).toMonoidHom =
      fixedSubgroup ρ (H.map (MulAut.conj g).toMonoidHom) :=
  CFSG.SL2MinimalFaithful.map_fixedPoints_conj ρ H g

private theorem fixedSubgroup_top_eq_bot {M : Type*} [Group M]
    (ρ : Alt7 →* MulAut M) (hfix : ∀ m : M, (∀ a, ρ a m = m) → m = 1) :
    fixedSubgroup ρ ⊤ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  exact hfix m fun a => hm a (Subgroup.mem_top a)

private theorem index_map_fixedSubgroup_conj {X M : Type*} [Group X] [Group M]
    [Finite M] (ρ : X →* MulAut M) (H : Subgroup X) (g : X) :
    (fixedSubgroup ρ (H.map (MulAut.conj g).toMonoidHom)).index =
      (fixedSubgroup ρ H).index := by
  have hmap := map_fixedSubgroup_conj ρ H g
  have hcard : Nat.card (fixedSubgroup ρ (H.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (fixedSubgroup ρ H) := by
    rw [← hmap, Subgroup.card_map_of_injective (ρ g).injective]
  have h1 := Subgroup.card_mul_index (fixedSubgroup ρ H)
  have h2 := Subgroup.card_mul_index (fixedSubgroup ρ (H.map (MulAut.conj g).toMonoidHom))
  rw [hcard] at h2
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)


private theorem eq_of_ne_one_of_card_two {F : Subgroup Alt7} (hF : Nat.card F = 2)
    {x y : Alt7} (hx : x ∈ F) (hx1 : x ≠ 1) (hy : y ∈ F) (hy1 : y ≠ 1) : y = x := by
  have hord : orderOf x = 2 := by
    have hdvd : orderOf x ∣ 2 := by
      rw [← hF]
      exact Subgroup.orderOf_dvd_natCard F hx
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 (by simpa using hx1)
    · exact h1
  have hx2 : x * x = 1 := by
    rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have htop : Subgroup.zpowers x = F := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_
    rw [Nat.card_zpowers, hord, hF]
  have hyz : y ∈ Subgroup.zpowers x := by
    rw [htop]
    exact hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
  have hyk : y = x ^ k := hk.symm
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : m + m = 2 * m := by ring
    rw [hm, zpow_mul, zpow_ofNat, pow_two, hx2, one_zpow] at hyk
    exact (hy1 hyk).elim
  · rw [zpow_add, zpow_mul, zpow_ofNat, pow_two, hx2, one_zpow, one_mul, zpow_one] at hyk
    exact hyk

private theorem map_conj_ne_of_card_two {V F : Subgroup Alt7} (e : Alt7)
    (heV : V.map (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))).toMonoidHom = V)
    (hefree : ∀ x ∈ V, x ≠ 1 →
      (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))) x ≠ x)
    (hF : F ≤ V) (hFcard : Nat.card F = 2) :
    F.map (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))).toMonoidHom ≠ F := by
  intro hEq
  have hnt : Nontrivial F := by
    refine (Subgroup.nontrivial_iff_ne_bot F).mpr ?_
    intro hbot
    rw [hbot, Subgroup.card_bot] at hFcard
    omega
  obtain ⟨d, hd1⟩ := exists_ne (1 : F)
  have hdF : (d : Alt7) ∈ F := d.2
  have hdne : (d : Alt7) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hconj_mem : (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))) (d : Alt7) ∈ F := by
    have hm := Subgroup.mem_map_of_mem
      (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))).toMonoidHom hdF
    rwa [hEq] at hm
  have hconj_ne : (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))) (d : Alt7) ≠ 1 := by
    intro h
    apply hdne
    have h1 : (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))) (d : Alt7) =
        (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))) 1 := by simpa using h
    exact (MulAut.conjNormal (H := Alt7) (e : Perm (Fin 7))).injective h1
  have heq_d := eq_of_ne_one_of_card_two hFcard hdF hdne hconj_mem hconj_ne
  exact hefree (d : Alt7) (hF hdF) hdne (by simpa [heq_d] using heq_d)

private theorem conj_e0_normalizes_and_free (g : Perm (Fin 7)) :
    let e' : Alt7 := (MulAut.conjNormal (H := Alt7) g) e0
    (conjugateKleinA7 g).map
        (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom =
        conjugateKleinA7 g ∧
      (∀ x ∈ conjugateKleinA7 g, x ≠ 1 →
        (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))) x ≠ x) := by
  intro e'
  constructor
  · have hcomp : (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom.comp
        (MulAut.conjNormal (H := Alt7) g).toMonoidHom =
        (MulAut.conjNormal (H := Alt7) g).toMonoidHom.comp
          (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
      subst e'
      simp only [MulAut.conjNormal_apply]
      group
    calc
      (conjugateKleinA7 g).map
          (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom =
          V1A.map ((MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom.comp
            (MulAut.conjNormal (H := Alt7) g).toMonoidHom) := by
        rw [conjugateKleinA7_eq, Subgroup.map_map]
      _ = V1A.map ((MulAut.conjNormal (H := Alt7) g).toMonoidHom.comp
            (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))).toMonoidHom) := by
        rw [hcomp]
      _ = (V1A.map (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))).toMonoidHom).map
            (MulAut.conjNormal (H := Alt7) g).toMonoidHom := by
        rw [Subgroup.map_map]
      _ = conjugateKleinA7 g := by
        rw [e0_V1A_map]
        exact (conjugateKleinA7_eq g).symm
  · intro x hx hx1 hconj
    rw [conjugateKleinA7_eq] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy1 : y ≠ 1 := by
      intro h
      apply hx1
      subst h
      simp
    have hcomp : (MulAut.conjNormal (H := Alt7) g)
        ((MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))) y) =
        (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7)))
          ((MulAut.conjNormal (H := Alt7) g) y) := by
      subst e'
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hconj' : (MulAut.conjNormal (H := Alt7) (e0 : Perm (Fin 7))) y = y :=
      (MulAut.conjNormal (H := Alt7) g).injective (hcomp.trans hconj)
    exact e0_no_fixed hy hy1 hconj'


private theorem index_conjugateKleinA7_le_four {M : Type*} [Group M] [Finite M] [Nontrivial M]
    (hM : IsPGroup 2 M) (ρ : Alt7 →* MulAut M)
    (hfix : ∀ m : M, (∀ a, ρ a m = m) → m = 1)
    (F : Subgroup Alt7) (hF : F ≠ ⊥) (g : Perm (Fin 7))
    (hFV : F.map Alt7.subtype ≤ vTwo.map (MulAut.conj g).toMonoidHom)
    (hidx : (fixedSubgroup ρ F).index ≤ Nat.card F) :
    (fixedSubgroup ρ (conjugateKleinA7 g)).index ≤ 4 := by
  let V := conjugateKleinA7 g
  have hFV' : F ≤ V := by
    change F ≤ (vTwo.map (MulAut.conj g).toMonoidHom).comap Alt7.subtype
    exact (Subgroup.map_le_iff_le_comap).mp hFV
  have hdvd : Nat.card F ∣ 4 := by
    have h := Subgroup.card_dvd_of_le hFV'
    rwa [card_conjugateKleinA7 g] at h
  have hF2le : 2 ≤ Nat.card F := by
    have hnt : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).mpr hF
    letI : Nontrivial F := hnt
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hcardF : Nat.card F = 2 ∨ Nat.card F = 4 := by
    have hdvd' : Nat.card F ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd' 
    interval_cases k
    · rw [hk_eq] at hF2le
      norm_num at hF2le
    · left
      rw [hk_eq]
      norm_num
    · right
      rw [hk_eq]
      norm_num
  rcases hcardF with hFcard | hFcard
  · let e' : Alt7 := (MulAut.conjNormal (H := Alt7) g) e0
    have he' := conj_e0_normalizes_and_free g
    have heV : V.map
        (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom = V := he'.1
    have hefree : ∀ x ∈ V, x ≠ 1 →
        (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))) x ≠ x := he'.2
    let F' : Subgroup Alt7 := F.map
      (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom
    have hF'le : F' ≤ V := by
      change F.map (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom ≤ V
      rw [← heV]
      exact Subgroup.map_mono hFV'
    have hF'card : Nat.card F' = 2 := by
      change Nat.card (F.map
        (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom) = 2
      have hmapcard : Nat.card (F.map
          (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).toMonoidHom) = Nat.card F :=
        Subgroup.card_map_of_injective (K := F)
          (MulAut.conjNormal (H := Alt7) (e' : Perm (Fin 7))).injective
      rw [hmapcard, hFcard]
    have hF'ne : F' ≠ F := by
      exact map_conj_ne_of_card_two e' heV hefree hFV' hFcard
    have hsup_le : F ⊔ F' ≤ V := sup_le hFV' hF'le
    have hFne : F ≠ F ⊔ F' := by
      intro h
      have hle : F' ≤ F := by
        rw [h]
        exact le_sup_right
      have heq : F' = F := Subgroup.eq_of_le_of_card_ge hle (by rw [hF'card, hFcard])
      exact hF'ne heq
    have hlt : F < F ⊔ F' := lt_of_le_of_ne le_sup_left hFne
    let n : ℕ := Nat.card (F ⊔ F' : Subgroup Alt7)
    have hn : n = Nat.card (F ⊔ F' : Subgroup Alt7) := rfl
    have hcard_gt : 2 < n := by
      have h := Subgroup.card_lt_of_lt hlt
      rwa [hFcard, ← hn] at h
    have hdvd_sup : n ∣ 4 := by
      have h := Subgroup.card_dvd_of_le hsup_le
      rwa [card_conjugateKleinA7 g, ← hn] at h
    have hcard_sup : Nat.card (F ⊔ F' : Subgroup Alt7) = 4 := by
      have hle4 : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd_sup
      have hn4 : n = 4 := by
        interval_cases n
        · norm_num at hdvd_sup
        · rfl
      rw [← hn]
      exact hn4
    have hsup : F ⊔ F' = V :=
      Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hcard_sup, card_conjugateKleinA7 g])
    have hidxF' : (fixedSubgroup ρ F').index = (fixedSubgroup ρ F).index := by
      exact index_map_fixedSubgroup_conj ρ F e'
    have hCV : fixedSubgroup ρ V = fixedSubgroup ρ F ⊓ fixedSubgroup ρ F' := by
      rw [← hsup, ← fixedSubgroup_inf]
    rw [hCV]
    have hidx2 : (fixedSubgroup ρ F).index ≤ 2 := by
      rw [← hFcard]
      exact hidx
    calc
      (fixedSubgroup ρ F ⊓ fixedSubgroup ρ F').index
          ≤ (fixedSubgroup ρ F).index * (fixedSubgroup ρ F').index :=
            Subgroup.index_inf_le
      _ = (fixedSubgroup ρ F).index * (fixedSubgroup ρ F).index := by rw [hidxF']
      _ ≤ 2 * 2 := Nat.mul_le_mul hidx2 hidx2
      _ = 4 := by norm_num
  · have hFVeq : F = V :=
      Subgroup.eq_of_le_of_card_ge hFV' (by rw [hFcard, card_conjugateKleinA7 g])
    change (fixedSubgroup ρ V).index ≤ 4
    rw [← hFVeq]
    rw [hFcard] at hidx
    exact hidx


private theorem exists_h_generates_V1A :
    ∃ h : Alt7, V1A ⊔ V1A.map
      (MulAut.conjNormal (H := Alt7) (h : Perm (Fin 7))).toMonoidHom = ⊤ := by
  obtain ⟨g0, hg0⟩ := CFSG.CGT.PushingUpLit.CGT6X.End4.exists_gen_kleinA7
  let V0 := CFSG.CGT.PushingUpLit.CGT6X.End4.kleinA7
  have hg0' : V0 ⊔ V0.map
      (MulAut.conjNormal (H := Alt7) (g0 : Perm (Fin 7))).toMonoidHom = ⊤ := by
    simpa [V0, Subgroup.sup_eq_closure, MulAut.conjNormal_val] using hg0
  let h : Alt7 := sAlt7 * g0 * sAlt7⁻¹
  refine ⟨h, ?_⟩
  have hrange : (MulAut.conjNormal (H := Alt7) (sAlt7 : Perm (Fin 7))).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (MulAut.conjNormal (H := Alt7) (sAlt7 : Perm (Fin 7))).surjective
  have hsecond : (V0.map
      (MulAut.conjNormal (H := Alt7) (g0 : Perm (Fin 7))).toMonoidHom).map
        (MulAut.conjNormal (H := Alt7) (sAlt7 : Perm (Fin 7))).toMonoidHom =
      V1A.map (MulAut.conjNormal (H := Alt7) (h : Perm (Fin 7))).toMonoidHom := by
    rw [V1A_eq_map_kleinA7]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    subst h
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hmap := congrArg (Subgroup.map
    (MulAut.conjNormal (H := Alt7) (sAlt7 : Perm (Fin 7))).toMonoidHom) hg0'
  rw [Subgroup.map_sup, Subgroup.map_top, hrange, ← V1A_eq_map_kleinA7,
    hsecond] at hmap
  exact hmap

private theorem exists_conj_generates_conjugateKleinA7 (g : Perm (Fin 7)) :
    ∃ a : Alt7, conjugateKleinA7 g ⊔
      (conjugateKleinA7 g).map
        (MulAut.conjNormal (H := Alt7) (a : Perm (Fin 7))).toMonoidHom = ⊤ := by
  obtain ⟨h, hh⟩ := exists_h_generates_V1A
  let a : Alt7 := (MulAut.conjNormal (H := Alt7) g) h
  refine ⟨a, ?_⟩
  have hrange : (MulAut.conjNormal (H := Alt7) g).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulAut.conjNormal (H := Alt7) g).surjective
  have hcomp : (MulAut.conjNormal (H := Alt7) g).toMonoidHom.comp
      (MulAut.conjNormal (H := Alt7) (h : Perm (Fin 7))).toMonoidHom =
      (MulAut.conjNormal (H := Alt7) (a : Perm (Fin 7))).toMonoidHom.comp
        (MulAut.conjNormal (H := Alt7) g).toMonoidHom := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    subst a
    simp only [MulAut.conjNormal_apply]
    group
  have hsecond : (V1A.map
      (MulAut.conjNormal (H := Alt7) (h : Perm (Fin 7))).toMonoidHom).map
        (MulAut.conjNormal (H := Alt7) g).toMonoidHom =
      (V1A.map (MulAut.conjNormal (H := Alt7) g).toMonoidHom).map
        (MulAut.conjNormal (H := Alt7) (a : Perm (Fin 7))).toMonoidHom := by
    calc
      (V1A.map (MulAut.conjNormal (H := Alt7) (h : Perm (Fin 7))).toMonoidHom).map
          (MulAut.conjNormal (H := Alt7) g).toMonoidHom =
          V1A.map ((MulAut.conjNormal (H := Alt7) g).toMonoidHom.comp
            (MulAut.conjNormal (H := Alt7) (h : Perm (Fin 7))).toMonoidHom) := by
        rw [Subgroup.map_map]
      _ = V1A.map ((MulAut.conjNormal (H := Alt7) (a : Perm (Fin 7))).toMonoidHom.comp
            (MulAut.conjNormal (H := Alt7) g).toMonoidHom) := by
        rw [hcomp]
      _ = (V1A.map (MulAut.conjNormal (H := Alt7) g).toMonoidHom).map
            (MulAut.conjNormal (H := Alt7) (a : Perm (Fin 7))).toMonoidHom := by
        rw [Subgroup.map_map]
  have hmap := congrArg (Subgroup.map
    (MulAut.conjNormal (H := Alt7) g).toMonoidHom) hh
  rw [Subgroup.map_sup, Subgroup.map_top, hrange, hsecond,
    ← conjugateKleinA7_eq g] at hmap
  simpa [conjugateKleinA7_eq g] using hmap


private def u0 : Alt7 :=
  ⟨List.formPerm [0, 1, 2, 3, 4], by
    have hnd : ([0, 1, 2, 3, 4] : List (Fin 7)).Nodup := by decide
    have hcyc : (List.formPerm [0, 1, 2, 3, 4] : Perm (Fin 7)).IsCycle :=
      List.isCycle_formPerm hnd (by decide)
    have hsupp : (List.formPerm [0, 1, 2, 3, 4] : Perm (Fin 7)).support.card = 5 := by
      rw [List.support_formPerm_of_nodup _ hnd (by decide)]
      decide
    rw [Equiv.Perm.mem_alternatingGroup, hcyc.sign, hsupp]
    norm_num⟩

private theorem u0_orderOf : orderOf u0 = 5 := by
  let l : List (Fin 7) := [0, 1, 2, 3, 4]
  have hnd : l.Nodup := by decide
  have hcyc : (l.formPerm : Perm (Fin 7)).IsCycle := List.isCycle_formPerm hnd (by decide)
  have hsupp : (l.formPerm : Perm (Fin 7)).support.card = 5 := by
    rw [List.support_formPerm_of_nodup _ hnd (by decide)]
    decide
  have hordPerm : orderOf (u0 : Perm (Fin 7)) = 5 := by
    change orderOf (l.formPerm : Perm (Fin 7)) = 5
    rw [hcyc.orderOf, hsupp]
  rw [← Subgroup.orderOf_coe u0, hordPerm]


private theorem mem_fixedSubgroup_zpowers_of_fixed {M : Type*} [Group M]
    (ρ : Alt7 →* MulAut M) {x : Alt7} {m : M} (h : ρ x m = m) :
    m ∈ fixedSubgroup ρ (Subgroup.zpowers x) := by
  rw [show fixedSubgroup ρ (Subgroup.zpowers x) =
    CFSG.SL2MinimalFaithful.fixedPoints ρ (Subgroup.zpowers x) from rfl,
    CFSG.SL2MinimalFaithful.mem_fixedPoints]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have key : ∀ k : ℤ, ((ρ x) ^ k) m = m := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ j ih =>
      rw [zpow_add_one, MulAut.mul_apply, h]
      exact ih
    | pred j ih =>
      have h' : (ρ x)⁻¹ m = m := by
        conv_lhs => rw [← h]
        simp
      rw [zpow_sub_one, MulAut.mul_apply, h']
      exact ih
  rw [map_zpow]
  exact key n


private theorem exists_twoPart_odd_automorphism {M : Type*} [Group M] [Finite M]
    (ρ : Alt7 →* MulAut M) (hρinj : Function.Injective ρ)
    (σ : MulAut M) {π : Perm (Fin 7)} (hπ : π ∉ Alt7)
    (hσ : ∀ a : Alt7, σ * ρ a * σ⁻¹ =
      ρ ((MulAut.conjNormal (H := Alt7) π) a)) :
    ∃ z : MulAut M, z ≠ 1 ∧ (∃ a : ℕ, orderOf z = 2 ^ a) ∧
      Commute z (ρ u0) ∧
      (∀ x : Alt7, z * ρ x * z⁻¹ =
        ρ ((MulAut.conjNormal (H := Alt7) (swap (5 : Fin 7) 6)) x)) := by
  have hsignπ : Equiv.Perm.sign π = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · exact (hπ (Equiv.Perm.mem_alternatingGroup.mpr h)).elim
    · exact h
  let a0 : Alt7 :=
    ⟨swap (5 : Fin 7) 6 * π⁻¹, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
        hsignπ, Equiv.Perm.sign_swap (by decide)]
      norm_num⟩
  let φ : MulAut Alt7 := MulAut.conjNormal (H := Alt7) (swap (5 : Fin 7) 6)
  let w : MulAut M := ρ a0 * σ
  have hw : ∀ x : Alt7, w * ρ x * w⁻¹ = ρ (φ x) := by
    intro x
    have h1 := hσ x
    calc
      w * ρ x * w⁻¹ = ρ a0 * (σ * ρ x * σ⁻¹) * (ρ a0)⁻¹ := by simp only [w]; group
      _ = ρ a0 * ρ ((MulAut.conjNormal (H := Alt7) π) x) * (ρ a0)⁻¹ := by rw [h1]
      _ = ρ (a0 * ((MulAut.conjNormal (H := Alt7) π) x) * a0⁻¹) := by
        simp only [map_mul, map_inv]
      _ = ρ (φ x) := by
        congr 1
        apply Subtype.ext
        subst a0
        subst φ
        simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        group
  have hφ2 : φ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    rw [show (swap (5 : Fin 7) 6 : Perm (Fin 7)) * swap 5 6 = 1 by decide +kernel, map_one]
  have hwn : ∀ (n : ℕ) (x : Alt7),
      w ^ n * ρ x * (w ^ n)⁻¹ = ρ ((φ ^ n) x) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        w ^ (n + 1) * ρ x * (w ^ (n + 1))⁻¹ =
            w * (w ^ n * ρ x * (w ^ n)⁻¹) * w⁻¹ := by group
        _ = w * ρ ((φ ^ n) x) * w⁻¹ := by rw [ih]
        _ = ρ (φ ((φ ^ n) x)) := hw _
        _ = ρ ((φ ^ (n + 1)) x) := by rw [pow_succ']; rfl
  obtain ⟨a, m, hm_odd, hw_order⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hm_pos : 0 < m := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    exact Nat.not_odd_zero hm_odd
  let z : MulAut M := w ^ m
  have hzord : orderOf z = 2 ^ a :=
    CFSG.GH74.GLS.IVK.orderOf_pow_odd_part w hm_pos hw_order
  have hφm : φ ^ m = φ := by
    obtain ⟨k, hk⟩ := hm_odd
    rw [hk, pow_add, pow_mul, hφ2, one_pow, one_mul, pow_one]
  have hz_conj : ∀ x : Alt7, z * ρ x * z⁻¹ = ρ (φ x) := by
    intro x
    change w ^ m * ρ x * (w ^ m)⁻¹ = ρ (φ x)
    rw [hwn m x, hφm]
  have hswap_u : φ u0 = u0 := by
    apply Subtype.ext
    subst φ
    simp only [MulAut.conjNormal_apply, u0]
    ext i
    fin_cases i <;> decide +kernel
  have hz_u : z * ρ u0 * z⁻¹ = ρ u0 := by
    rw [hz_conj u0, hswap_u]
  have hcomm_z_u : Commute z (ρ u0) := (mul_inv_eq_iff_eq_mul).mp hz_u
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    have h2a : 2 ^ a = 1 := by
      have h := hzord
      rw [hz1, orderOf_one] at h
      exact h.symm
    have ha0 : a = 0 := by
      have hle : 2 ^ a ≤ 2 ^ 0 := by rw [h2a]; norm_num
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
      omega
    have hw_odd : Odd (orderOf w) := by
      rw [hw_order, ha0, pow_zero, one_mul]
      exact hm_odd
    have hw2_cent : ∀ x : Alt7, w ^ 2 * ρ x * (w ^ 2)⁻¹ = ρ x := by
      intro x
      rw [hwn 2 x, hφ2, MulAut.one_apply]
    have hw_mem : w ∈ Subgroup.zpowers (w ^ 2) := by
      obtain ⟨k, hk⟩ := hw_odd
      refine ⟨(k + 1 : ℕ), ?_⟩
      simp only [zpow_natCast]
      rw [← pow_mul, show 2 * (k + 1) = orderOf w + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hcentral : ∀ x : Alt7, w * ρ x * w⁻¹ = ρ x := by
      intro x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw_mem
      have hcomm2 : Commute (w ^ 2) (ρ x) := (mul_inv_eq_iff_eq_mul).mp (hw2_cent x)
      have hcommw : Commute w (ρ x) := by
        rw [← hk]
        exact hcomm2.zpow_left k
      rw [hcommw.eq, mul_assoc, mul_inv_cancel, mul_one]
    have hφall : ∀ x : Alt7, φ x = x := by
      intro x
      apply hρinj
      exact (hw x).symm.trans (hcentral x)
    let x0 : Alt7 := ⟨cTwo, eNine_le_alternatingGroup cTwo_mem_eNine⟩
    have hφne : φ x0 ≠ x0 := by
      intro h
      have h' : (swap (5 : Fin 7) 6 : Perm (Fin 7)) * cTwo * (swap 5 6)⁻¹ = cTwo := by
        simpa only [φ, x0, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply] using
          congrArg (fun y : Alt7 => (y : Perm (Fin 7))) h
      revert h'
      decide +kernel
    exact hφne (hφall x0)
  refine ⟨z, hz_ne_one, ⟨a, hzord⟩, hcomm_z_u, hz_conj⟩


private theorem false_of_odd_automorphism {M : Type*} [Group M] [Finite M] [Nontrivial M]
    (hM : IsPGroup 2 M) (ρ : Alt7 →* MulAut M) (hρinj : Function.Injective ρ)
    (hfix : ∀ m : M, (∀ a : Alt7, ρ a m = m) → m = 1)
    (hM16 : Nat.card M = 16)
    (hCu1 : Nat.card (fixedSubgroup ρ (Subgroup.zpowers u0)) = 1) :
    ∀ (σ : MulAut M) {π : Perm (Fin 7)}, π ∉ Alt7 →
      (∀ a : Alt7, σ * ρ a * σ⁻¹ =
        ρ ((MulAut.conjNormal (H := Alt7) π) a)) → False := by
  intro σ π hπ hσ
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨z, hz1, ⟨a, hzord⟩, hcomm_z_u, hz_conj⟩ :=
    exists_twoPart_odd_automorphism ρ hρinj σ hπ hσ
  let Pz : Subgroup (MulAut M) := Subgroup.zpowers z
  let P : Subgroup (MulAut M) := Subgroup.zpowers (ρ u0)
  let Cz : Subgroup M := CFSG.fixedPointSubgroup Pz M
  have hzord' : orderOf z = 2 ^ a := hzord
  have hPzcard : Nat.card Pz = 2 ^ a := by
    rw [Nat.card_zpowers, hzord']
  have hPzgroup : IsPGroup 2 Pz := IsPGroup.of_card (n := a) hPzcard
  have hCz_ne_top : Cz ≠ ⊤ := by
    intro htop
    apply hz1
    ext m
    have hm : m ∈ Cz := htop ▸ Subgroup.mem_top m
    have hmz : (⟨z, Subgroup.mem_zpowers z⟩ : Pz) • m = m :=
      (FixedPoints.mem_subgroup (M := Pz) (α := M) m).mp hm ⟨z, Subgroup.mem_zpowers z⟩
    simpa [MulAut.smul_def] using hmz
  have hCz_lt : Nat.card Cz < Nat.card M := by
    simpa using Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hCz_ne_top)
  have hfixCz : Nat.card (MulAction.fixedPoints Pz M) = Nat.card Cz := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro m
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hm
      exact (FixedPoints.mem_subgroup (M := Pz) (α := M) m).mpr hm
    · intro hm p
      exact (FixedPoints.mem_subgroup (M := Pz) (α := M) m).mp hm p
  have hCz_even : 2 ∣ Nat.card Cz := by
    have h1 : Nat.card M ≡ Nat.card Cz [MOD 2] := by
      simpa only [hfixCz] using hPzgroup.card_modEq_card_fixedPoints M
    have h2 : Nat.card Cz ≡ 0 [MOD 2] := by
      have h16 : Nat.card M ≡ 0 [MOD 2] := by
        rw [hM16]
        norm_num [Nat.ModEq]
      exact h1.symm.trans h16
    exact Nat.modEq_zero_iff_dvd.mp h2
  obtain ⟨k, hk⟩ := (hM.to_subgroup Cz).exists_card_eq
  have hklt : k < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp
    rw [← hk]
    simpa [hM16] using hCz_lt
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hk] at hCz_even
      simp at hCz_even
    · exact hk0
  have hPcard : Nat.card P = 5 := by
    rw [Nat.card_zpowers, (orderOf_injective ρ hρinj u0).trans u0_orderOf]
  have hPgroup : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hmCz : ∀ m : M, (z m = m) → m ∈ Cz := by
    intro m hm
    change m ∈ CFSG.fixedPointSubgroup Pz M
    rw [FixedPoints.mem_subgroup]
    intro p
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp p.2
    have key : ∀ n : ℤ, ((z ^ n) m = m) := by
      intro n
      induction n using Int.induction_on with
      | zero => simp
      | succ i ih =>
        rw [zpow_add_one, MulAut.mul_apply, hm]
        exact ih
      | pred i ih =>
        have h' : z⁻¹ m = m := by
          conv_lhs => rw [← hm]
          simp
        rw [zpow_sub_one, MulAut.mul_apply, h']
        exact ih
    change p.1 m = m
    rw [← hj]
    exact key j
  have hgen_mem : ∀ m ∈ Cz, ρ u0 m ∈ Cz := by
    intro m hm
    apply hmCz
    have hmz : z m = m :=
      (FixedPoints.mem_subgroup (M := Pz) (α := M) m).mp hm ⟨z, Subgroup.mem_zpowers z⟩
    have h := congrArg (fun f : MulAut M => f m) hcomm_z_u.eq
    simpa [MulAut.mul_apply, hmz] using h
  have hgen_inv_mem : ∀ m ∈ Cz, (ρ u0)⁻¹ m ∈ Cz := by
    intro m hm
    apply hmCz
    have hmz : z m = m :=
      (FixedPoints.mem_subgroup (M := Pz) (α := M) m).mp hm ⟨z, Subgroup.mem_zpowers z⟩
    have h := congrArg (fun f : MulAut M => f m) hcomm_z_u.inv_right.eq
    simpa [MulAut.mul_apply, hmz] using h
  have hzpow_mem : ∀ (n : ℤ) (m : M), m ∈ Cz → ((ρ u0) ^ n) m ∈ Cz := by
    intro n
    induction n using Int.induction_on with
    | zero => intro m hm; simpa using hm
    | succ i ih =>
      intro m hm
      rw [zpow_add_one, MulAut.mul_apply]
      exact ih _ (hgen_mem m hm)
    | pred i ih =>
      intro m hm
      rw [zpow_sub_one, MulAut.mul_apply]
      exact ih _ (hgen_inv_mem m hm)
  let S : SubMulAction P M :=
    { carrier := (Cz : Set M)
      smul_mem' := by
        intro p m hm
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp p.2
        change p.1 m ∈ Cz
        rw [← hn]
        exact hzpow_mem n m hm }
  have hCu_bot : fixedSubgroup ρ (Subgroup.zpowers u0) = ⊥ :=
    (Subgroup.card_eq_one).mp hCu1
  have hFixS : Nat.card (MulAction.fixedPoints P S) = 1 := by
    have hsub : Subsingleton (MulAction.fixedPoints P S) := by
      constructor
      intro u v
      apply Subtype.ext
      apply Subtype.ext
      have huCz : ((u : MulAction.fixedPoints P S) : S).1 ∈
          fixedSubgroup ρ (Subgroup.zpowers u0) := by
        have hu := (MulAction.mem_fixedPoints.mp u.2) ⟨ρ u0, Subgroup.mem_zpowers (ρ u0)⟩
        exact mem_fixedSubgroup_zpowers_of_fixed ρ
          (by simpa [MulAut.smul_def] using congrArg (fun y : S => (y : M)) hu)
      have hvCz : ((v : MulAction.fixedPoints P S) : S).1 ∈
          fixedSubgroup ρ (Subgroup.zpowers u0) := by
        have hv := (MulAction.mem_fixedPoints.mp v.2) ⟨ρ u0, Subgroup.mem_zpowers (ρ u0)⟩
        exact mem_fixedSubgroup_zpowers_of_fixed ρ
          (by simpa [MulAut.smul_def] using congrArg (fun y : S => (y : M)) hv)
      rw [hCu_bot] at huCz hvCz
      have hu1 : (((u : MulAction.fixedPoints P S) : S) : M) = 1 := Subgroup.mem_bot.mp huCz
      have hv1 : (((v : MulAction.fixedPoints P S) : S) : M) = 1 := Subgroup.mem_bot.mp hvCz
      exact hu1.trans hv1.symm
    let oneS : S := ⟨1, by
      change (1 : M) ∈ CFSG.fixedPointSubgroup Pz M
      rw [FixedPoints.mem_subgroup]
      intro p
      simpa [MulAut.smul_def] using map_one p.1⟩
    have hfixOne : oneS ∈ MulAction.fixedPoints P S := by
      rw [MulAction.mem_fixedPoints]
      intro p
      apply Subtype.ext
      change p.1 (1 : M) = 1
      exact map_one p.1
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨oneS, hfixOne⟩⟩⟩
  have hmod5S := hPgroup.card_modEq_card_fixedPoints S
  rw [hFixS] at hmod5S
  have hcardS : Nat.card S = Nat.card Cz := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  have hmod5Cz : Nat.card Cz ≡ 1 [MOD 5] := by
    rw [← hcardS]
    exact hmod5S
  have hkle : k ≤ 3 := by omega
  interval_cases k <;> norm_num [hk, Nat.ModEq] at hCz_even hmod5Cz

private theorem card_eq_sixteen_and_fixed_u_eq_one {M : Type*} [Group M] [Finite M]
    [Nontrivial M] (hM : IsPGroup 2 M) (ρ : Alt7 →* MulAut M)
    (hρinj : Function.Injective ρ) (hM16 : Nat.card M ≤ 16) :
    Nat.card M = 16 ∧ Nat.card (fixedSubgroup ρ (Subgroup.zpowers u0)) = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Subgroup (MulAut M) := Subgroup.zpowers (ρ u0)
  have horderρ : orderOf (ρ u0) = 5 :=
    (orderOf_injective ρ hρinj u0).trans u0_orderOf
  have hPcard : Nat.card P = 5 := by
    rw [Nat.card_zpowers, horderρ]
  have hPgroup : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hfixed_eq : Nat.card (MulAction.fixedPoints P M) =
      Nat.card (fixedSubgroup ρ (Subgroup.zpowers u0)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro m
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hm x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h1 : ρ u0 m = m := hm ⟨ρ u0, Subgroup.mem_zpowers (ρ u0)⟩
      have key : ∀ n : ℤ, ((ρ u0) ^ n) m = m := by
        intro n
        induction n using Int.induction_on with
        | zero => simp
        | succ j ih =>
          rw [zpow_add_one, MulAut.mul_apply, h1]
          exact ih
        | pred j ih =>
          have h' : (ρ u0)⁻¹ m = m := by
            conv_lhs => rw [← h1]
            simp
          rw [zpow_sub_one, MulAut.mul_apply, h']
          exact ih
      rw [map_zpow]
      exact key k
    · intro hm p
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp p.2
      have h1 : ρ u0 m = m := hm u0 (Subgroup.mem_zpowers u0)
      have key : ∀ n : ℤ, ((ρ u0) ^ n) m = m := by
        intro n
        induction n using Int.induction_on with
        | zero => simp
        | succ j ih =>
          rw [zpow_add_one, MulAut.mul_apply, h1]
          exact ih
        | pred j ih =>
          have h' : (ρ u0)⁻¹ m = m := by
            conv_lhs => rw [← h1]
            simp
          rw [zpow_sub_one, MulAut.mul_apply, h']
          exact ih
      change p.1 m = m
      rw [← hk]
      exact key k
  have hCu_ne_top : fixedSubgroup ρ (Subgroup.zpowers u0) ≠ ⊤ := by
    intro htop
    have hρu0 : ρ u0 = 1 := by
      ext m
      have hm : m ∈ fixedSubgroup ρ (Subgroup.zpowers u0) := htop ▸ Subgroup.mem_top m
      exact hm u0 (Subgroup.mem_zpowers u0)
    have hu0 : u0 = 1 := hρinj (hρu0.trans (map_one ρ).symm)
    exact (by decide +kernel : u0 ≠ 1) hu0
  let Cu : Subgroup M := fixedSubgroup ρ (Subgroup.zpowers u0)
  have hCu_lt : Nat.card Cu < Nat.card M := by
    simpa using Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hCu_ne_top)
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  obtain ⟨m, hm⟩ := (hM.to_subgroup Cu).exists_card_eq
  have hn4 : n ≤ 4 := by
    have hle : 2 ^ n ≤ 2 ^ 4 := by
      calc
        2 ^ n = Nat.card M := hn.symm
        _ ≤ 16 := hM16
        _ = 2 ^ 4 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hm_lt : m < n := by
    apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp
    rw [← hm, ← hn]
    exact hCu_lt
  have hmod : 2 ^ n ≡ 2 ^ m [MOD 5] := by
    have h := hPgroup.card_modEq_card_fixedPoints M
    simpa [P, hfixed_eq, hn, hm, Cu] using h
  have hnm : n = 4 ∧ m = 0 := by
    interval_cases n
    · omega
    · interval_cases m <;> norm_num [Nat.ModEq] at hmod
    · interval_cases m <;> norm_num [Nat.ModEq] at hmod
    · interval_cases m <;> norm_num [Nat.ModEq] at hmod
    · interval_cases m
      · norm_num
      · norm_num [Nat.ModEq] at hmod
      · norm_num [Nat.ModEq] at hmod
      · norm_num [Nat.ModEq] at hmod
  constructor
  · rw [hn, hnm.1]
    norm_num
  · rw [hm, hnm.2]
    norm_num

theorem card_mul_card_fixed_lt {M : Type*} [Group M] [Finite M] [Nontrivial M]
    (hM : IsPGroup 2 M) (ρ : alternatingGroup (Fin 7) →* MulAut M)
    (hfix : ∀ m : M, (∀ a, ρ a m = m) → m = 1)
    (σ : MulAut M) {π : Equiv.Perm (Fin 7)} (hπ : π ∉ alternatingGroup (Fin 7))
    (hσ : ∀ a, σ * ρ a * σ⁻¹ = ρ (MulAut.conjNormal π a))
    {F : Subgroup (alternatingGroup (Fin 7))} (hF : F ≠ ⊥) (g : Equiv.Perm (Fin 7))
    (hFV : F.map (alternatingGroup (Fin 7)).subtype ≤ vTwo.map (MulAut.conj g).toMonoidHom) :
    Nat.card F * Nat.card {m : M // ∀ a ∈ F, ρ a m = m} < Nat.card M := by
  by_contra hgoal
  have hle : Nat.card M ≤ Nat.card F *
      Nat.card {m : M // ∀ a ∈ F, ρ a m = m} := Nat.le_of_not_gt hgoal
  have hcardFix : Nat.card {m : M // ∀ a ∈ F, ρ a m = m} =
      Nat.card (fixedSubgroup ρ F) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun m => Iff.rfl)
  have hle' : Nat.card M ≤ Nat.card F * Nat.card (fixedSubgroup ρ F) := by
    simpa only [hcardFix] using hle
  have hidx : (fixedSubgroup ρ F).index ≤ Nat.card F := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.card_pos (α := fixedSubgroup ρ F))
    calc
      (fixedSubgroup ρ F).index * Nat.card (fixedSubgroup ρ F) = Nat.card M :=
        Subgroup.index_mul_card _
      _ ≤ Nat.card F * Nat.card (fixedSubgroup ρ F) := hle'
  let V : Subgroup Alt7 := conjugateKleinA7 g
  have hFV' : F ≤ V := by
    change F ≤ (vTwo.map (MulAut.conj g).toMonoidHom).comap Alt7.subtype
    exact (Subgroup.map_le_iff_le_comap).mp hFV
  have hidxV : (fixedSubgroup ρ V).index ≤ 4 :=
    index_conjugateKleinA7_le_four hM ρ hfix F hF g hFV hidx
  obtain ⟨a, hgen⟩ := exists_conj_generates_conjugateKleinA7 g
  let V' : Subgroup Alt7 := V.map
    (MulAut.conjNormal (H := Alt7) (a : Perm (Fin 7))).toMonoidHom
  have hV'index : (fixedSubgroup ρ V').index ≤ 4 := by
    have h := index_map_fixedSubgroup_conj ρ V a
    change (fixedSubgroup ρ (V.map
      (MulAut.conjNormal (H := Alt7) (a : Perm (Fin 7))).toMonoidHom)).index ≤ 4
    rw [MulAut.conjNormal_val]
    rw [h]
    exact hidxV
  have hCinf : fixedSubgroup ρ V ⊓ fixedSubgroup ρ V' = ⊥ := by
    rw [fixedSubgroup_inf, hgen, fixedSubgroup_top_eq_bot ρ hfix]
  have hM16le : Nat.card M ≤ 16 := by
    have h := Subgroup.index_inf_le (H := fixedSubgroup ρ V) (K := fixedSubgroup ρ V')
    calc
      Nat.card M = (fixedSubgroup ρ V ⊓ fixedSubgroup ρ V').index := by
        rw [hCinf, Subgroup.index_bot]
      _ ≤ (fixedSubgroup ρ V).index * (fixedSubgroup ρ V').index := h
      _ ≤ 4 * 4 := Nat.mul_le_mul hidxV hV'index
      _ = 16 := by norm_num
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI : IsSimpleGroup Alt7 := alternatingGroup.isSimpleGroup (by simp)
    have hker_ne_top : ρ.ker ≠ ⊤ := by
      intro htop
      have hAll : ∀ m : M, (∀ a : Alt7, ρ a m = m) := by
        intro m a
        have ha : a ∈ ρ.ker := htop ▸ Subgroup.mem_top a
        have h1 : ρ a = 1 := MonoidHom.mem_ker.mp ha
        simpa using congrArg (fun f : MulAut M => f m) h1
      obtain ⟨m, hm1⟩ := exists_ne (1 : M)
      exact hm1 (hfix m (hAll m))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hbot | htop
    · exact hbot
    · exact absurd htop hker_ne_top
  obtain ⟨hM16, hCu1⟩ := card_eq_sixteen_and_fixed_u_eq_one hM ρ hρinj hM16le
  exact false_of_odd_automorphism hM ρ hρinj hfix hM16 hCu1 σ hπ hσ



theorem card_map_mul_card_fixed_lt {X M : Type*} [Group X] [Group M] [Finite M] [Nontrivial M]
    (hM : IsPGroup 2 M) (ρ : X →* MulAut M) (ψ : X →* Equiv.Perm (Fin 7))
    (hψ : ψ.range = alternatingGroup (Fin 7)) (hker : ψ.ker ≤ ρ.ker)
    (hfix : ∀ m : M, (∀ x, ρ x m = m) → m = 1)
    (σ : MulAut M) {π : Equiv.Perm (Fin 7)} (hπ : π ∉ alternatingGroup (Fin 7))
    (hσ : ∀ x, ∃ x', ψ x' = π * ψ x * π⁻¹ ∧ σ * ρ x * σ⁻¹ = ρ x')
    {F : Subgroup X} (hF : F.map ψ ≠ ⊥) (g : Equiv.Perm (Fin 7))
    (hFV : F.map ψ ≤ vTwo.map (MulAut.conj g).toMonoidHom) :
    Nat.card (F.map ψ) * Nat.card {m : M // ∀ x ∈ F, ρ x m = m} < Nat.card M := by
  let ψr : X →* ψ.range := ψ.rangeRestrict
  have hψr : Function.Surjective ψr := MonoidHom.rangeRestrict_surjective ψ
  have hker' : ψr.ker ≤ ρ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let ρr : ψ.range →* MulAut M :=
    MonoidHom.liftOfSurjective ψr hψr ⟨ρ, hker'⟩
  have hρr : ∀ x : X, ρr (ψr x) = ρ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ψr _ _ ⟨ρ, hker'⟩ x
  let e : ψ.range ≃* Alt7 := MulEquiv.subgroupCongr hψ
  let ρbar : Alt7 →* MulAut M := ρr.comp e.symm.toMonoidHom
  let ψA : X → Alt7 := fun x => e (ψr x)
  have hρbar_ψA : ∀ x : X, ρbar (ψA x) = ρ x := by
    intro x
    change ρr (e.symm (e (ψr x))) = ρ x
    rw [MulEquiv.symm_apply_apply]
    exact hρr x
  have hfixbar : ∀ m : M, (∀ a : Alt7, ρbar a m = m) → m = 1 := by
    intro m hm
    apply hfix m
    intro x
    rw [← hρbar_ψA x]
    exact hm (ψA x)
  have hσbar : ∀ a : Alt7, σ * ρbar a * σ⁻¹ = ρbar (MulAut.conjNormal π a) := by
    intro a
    have harange : a.1 ∈ ψ.range := by rw [hψ]; exact a.2
    obtain ⟨x, hx⟩ := harange
    have ha : ψA x = a := Subtype.ext hx
    rw [← ha, hρbar_ψA x]
    obtain ⟨x', hx', hσx'⟩ := hσ x
    have hconj : ψA x' = MulAut.conjNormal (H := Alt7) π (ψA x) := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      change ψ x' = π * ψ x * π⁻¹
      rw [hx']
    rw [← hconj, hρbar_ψA x']
    exact hσx'
  let Fbar : Subgroup Alt7 := (F.map ψ).comap Alt7.subtype
  have hFbar_map : Fbar.map Alt7.subtype = F.map ψ := by
    refine Subgroup.map_comap_eq_self ?_
    rw [Subgroup.range_subtype]
    exact (Subgroup.map_le_range ψ F).trans (le_of_eq hψ)
  have hFbar_card : Nat.card Fbar = Nat.card (F.map ψ) := by
    rw [← hFbar_map, Subgroup.card_map_of_injective Alt7.subtype_injective]
  have hFbar_ne : Fbar ≠ ⊥ := by
    intro hbot
    apply hF
    rw [← hFbar_map, hbot, Subgroup.map_bot]
  have hFVbar : Fbar.map Alt7.subtype ≤ vTwo.map (MulAut.conj g).toMonoidHom := by
    rw [hFbar_map]
    exact hFV
  have hfixed_eq : Nat.card {m : M // ∀ x ∈ F, ρ x m = m} =
      Nat.card {m : M // ∀ a ∈ Fbar, ρbar a m = m} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro m
    constructor
    · intro hm a ha
      have ha' : a.1 ∈ F.map ψ := ha
      rcases ha' with ⟨x, hxF, hxa⟩
      have haeq : ψA x = a := Subtype.ext hxa
      rw [← haeq, hρbar_ψA x]
      exact hm x hxF
    · intro hm x hx
      have hψx : ψA x ∈ Fbar := by
        change ψA x ∈ (F.map ψ).comap Alt7.subtype
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_map_of_mem ψ hx
      have h1 := hm (ψA x) hψx
      rwa [hρbar_ψA x] at h1
  rw [hfixed_eq, ← hFbar_card]
  exact card_mul_card_fixed_lt hM ρbar hfixbar σ hπ hσbar hFbar_ne g hFVbar


end CFSG.RankThree.PartTwo.KFacts.KP2
