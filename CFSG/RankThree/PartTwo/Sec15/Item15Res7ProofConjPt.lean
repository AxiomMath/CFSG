module

import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec6.Item612Core
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.LBNatural
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofTools
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

namespace Proof15Res7

omit [Finite G] in
theorem exists_sylow_of_isZCentral {L : Subgroup G} {d : G} (h : IsZCentral L d) :
    ∃ hd : d ∈ L, ∃ S : Sylow 3 ↥L, (⟨d, hd⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hd⟩ : ↥L)} := by
  obtain ⟨S, ⟨Q, hQ⟩, hZ⟩ := h
  have hdS : d ∈ (Subgroup.center S).map S.subtype := hZ ▸ Subgroup.mem_zpowers d
  obtain ⟨s, hs, rfl⟩ := hdS
  have hsQ : (s : G) ∈ (Q : Subgroup ↥L).map L.subtype := hQ ▸ s.2
  obtain ⟨q, hq, hqs⟩ := hsQ
  have hdL : S.subtype s ∈ L := by
    change (s : G) ∈ L
    rw [← hqs]
    exact q.2
  refine ⟨hdL, Q, ?_, fun x hx => ?_⟩
  · have hq' : q = ⟨S.subtype s, hdL⟩ := Subtype.ext hqs
    rw [← hq']
    exact hq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hxS : (x : G) ∈ S := hQ ▸ ⟨x, hx, rfl⟩
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hs ⟨x, hxS⟩)
    apply Subtype.ext
    simp only [Subgroup.coe_mul] at hc ⊢
    exact hc

end Proof15Res7

open Proof15Res4 Proof15Res7

section Certificates


theorem Conf1515HJ.sec15R_conj (h : Conf1515HJ A c L Y) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) :
    Sec15R G A (w * c * w⁻¹) (L.map (MulAut.conj w).toMonoidHom) :=
  { h.sec15R with
    zpowers_mem_omegaA := by
      rw [← Proof15Res4.map_conj_zpowers]
      exact (map_conj_mem_omegaA_iff hwA).mpr h.sec13Data.zpowers_mem_omegaA
    mem_lA := (map_conj_mem_lA_iff hwA).mpr h.sec13Data.mem_lA }

theorem nonempty_j2_conj {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (w : G) :
    Nonempty (↥(L.map (MulAut.conj w).toMonoidHom) ⧸
      aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w).toMonoidHom) ≃*
        CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨e⟩ := hJ
  exact ⟨(thetaQuotEquiv (MulAut.conj w) L).symm.trans e⟩

theorem Conf1515HJ.zpowers_ne (h : Conf1515HJ A c L Y) {d : G} (hdL : d ∈ L) :
    Subgroup.zpowers c ≠ Subgroup.zpowers d := by
  intro heq
  apply h.not_mem_L
  have : c ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.mpr hdL) this

theorem Conf1515HJ.isHyperplane (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdL : d ∈ L) : IsHyperplane A (Subgroup.closure {c, d}) := by
  have hD := h.sec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  refine Main148.isHyperplane_closure_pair148 hA hD.mem_A hdA hD.ne_one fun hdc => ?_
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
  apply h.zpowers_ne hdL
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc) ?_).symm
  rw [Nat.card_zpowers, Nat.card_zpowers, hd3, hD.orderOf_eq]

theorem Conf1515HJ.isLBConfig (h : Conf1515HJ A c L Y) {d : G}
    (hdZ : IsZCentral L d) : IsLBConfig A (Subgroup.closure {c, d}) c d L := by
  have hD := h.sec13Data
  have hR := h.sec15R
  have hLc := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hR.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  have hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Sec12.gap128OTwoHJ ↥L (hR.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) h.j2
  exact ⟨rfl, hD.zpowers_mem_omegaA, lA_eq_singleton_of_j2_point hD h.j2, hJ2,
    exists_sylow_of_isZCentral hdZ⟩

omit [Finite G]
  in
theorem conj_mem_zpowers_of_mem_normalizer {d w : G}
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    w * d * w⁻¹ ∈ Subgroup.zpowers d :=
  (Subgroup.mem_normalizer_iff.mp hwd d).mp (Subgroup.mem_zpowers d)

theorem zpowers_conj_eq_of_mem_normalizer {d w : G}
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    Subgroup.zpowers (w * d * w⁻¹) = Subgroup.zpowers d := by
  refine Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr (conj_mem_zpowers_of_mem_normalizer hwd)) ?_
  rw [← Proof15Res4.map_conj_zpowers, Subgroup.card_map_of_injective (MulAut.conj w).injective]

theorem map_conj_closure_eq {d w : G}
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d}) :
    (Subgroup.closure {c, d}).map (MulAut.conj w).toMonoidHom = Subgroup.closure {c, d} := by
  have hdB : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, (rfl | rfl), rfl⟩
    · exact hwcB
    · exact (Subgroup.zpowers_le.mpr hdB) (conj_mem_zpowers_of_mem_normalizer hwd)
  · rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]

theorem Conf1515HJ.residual_eq_conj (h : Conf1515HJ A c L Y)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d}) :
    inSubgroup perfectResidual
        (L.map (MulAut.conj w).toMonoidHom ⊓ Subgroup.centralizer ({w * d * w⁻¹} : Set G)) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have hdL := mem_of_isZCentral hdZ
  have hc := h.isLBConfig hdZ
  have hc' := hc.map (MulAut.conj w)
  rw [map_conj_eq_self_of_mem_normalizer hwA, map_conj_closure_eq hwd hwcB] at hc'
  exact Item148HJ.residual_eq_of_isLBConfig h.sec15R.toSec14Std (h.isHyperplane hdA hd1 hdL) hc hc'

theorem Conf1515HJ.isLBConfig_conj (h : Conf1515HJ A c L Y)
    {d : G} (hdZ : IsZCentral L d) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d}) :
    IsLBConfig A (Subgroup.closure {c, d}) (w * c * w⁻¹) (w * d * w⁻¹)
      (L.map (MulAut.conj w).toMonoidHom) := by
  have hc' := (h.isLBConfig hdZ).map (MulAut.conj w)
  rw [map_conj_eq_self_of_mem_normalizer hwA, map_conj_closure_eq hwd hwcB] at hc'
  exact hc'

end Certificates

end CFSG.RankThree.PartTwo.Sec15
