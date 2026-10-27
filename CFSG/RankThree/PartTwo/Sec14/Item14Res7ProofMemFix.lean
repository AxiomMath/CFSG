module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Res7MemFix

variable {G : Type} [Group G] [Finite G]

theorem theta_le_of_mem {a : G} {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 a) :
    inSubgroup (aschbacherSolvableCore 3) X ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsIn (M := Subgroup.centralizer ({a} : Set G)) hX]
  exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf _)

theorem inf_centralizer_le_pPrimeCoreOf {a : G} {D : Subgroup G} (haD : a ∈ D) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ Subgroup.centralizer (D : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD)
  have hON : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  refine le_pPrimeCoreOf inf_le_right (fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hON (hCD hx), Subgroup.le_normalizer hx⟩) ?_
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    (coprime_card_pPrimeCoreOf 3 _)

theorem sup_le_of_eq_lB_sup {A B' X : Subgroup G} {a : G}
    (hθX : inSubgroup (aschbacherSolvableCore 3) X ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (hXeq : X = lB A B' ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A B' ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  conv_lhs => rw [hXeq]
  exact sup_le le_sup_right (sup_le le_sup_left (hθX.trans le_sup_right))

theorem inf_centralizer_le_of_le_sup {A D X : Subgroup G} {a : G} (haD : a ∈ D)
    (hOX : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :
    (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
        Subgroup.centralizer (D : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) ⊔ lB A D := by
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD)
  have hON : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hOD := inf_centralizer_le_pPrimeCoreOf (a := a) haD
  have hLD : lB A D ≤ Subgroup.centralizer (D : Set G) := lB_le_centralizer A D
  have hLN : lB A D ≤ Subgroup.normalizer (O : Set G) := (hLD.trans hCD).trans hON
  intro x ⟨hxOX, hxD⟩
  have hx' : x ∈ ((lB A D ⊔ O : Subgroup G) : Set G) := hOX hxOX
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hx'
  obtain ⟨l, hl, o, ho, rfl⟩ := Set.mem_mul.mp hx'
  have hoD : o ∈ Subgroup.centralizer (D : Set G) := by
    have : o = l⁻¹ * (l * o) := by group
    rw [this]
    exact mul_mem (inv_mem (hLD hl)) hxD
  exact mul_mem (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left (hOD ⟨ho, hoD⟩))

theorem commutator_le_of_le_sup {A B' X : Subgroup G} {a : G}
    (hB'a : B' ≤ Subgroup.centralizer ({a} : Set G)) (haB' : a ∈ B')
    (hOX : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A B' ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  have hON : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hLa : lB A B' ≤ Subgroup.centralizer ({a} : Set G) :=
    (lB_le_centralizer A B').trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB'))
  have hOmem : O ≤ commutatorInSubgroup B' O := by
    intro o ho
    refine mem_commutatorInSubgroup.mpr ⟨Subgroup.le_normalizer ho, fun q hq => ?_⟩
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hON (hB'a hq)) o).mp ho) (inv_mem ho)
  have hLmem : lB A B' ≤ commutatorInSubgroup B' O := by
    intro l hl
    refine mem_commutatorInSubgroup.mpr ⟨hON (hLa hl), fun q hq => ?_⟩
    have hql : q * l = l * q := Subgroup.mem_centralizer_iff.mp (lB_le_centralizer A B' hl) q hq
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hql]
    exact one_mem _
  have hOX' : O ⊔ X ≤ commutatorInSubgroup B' O := hOX.trans (sup_le hLmem hOmem)
  rw [Subgroup.commutator_le]
  intro g hg q hq
  rw [← commutatorElement_inv]
  exact inv_mem ((mem_commutatorInSubgroup.mp (hOX' hg)).2 q hq)

theorem le_qBound_of_commutator_le {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a : G}
    (ha : a ∈ A) {B' X D R : Subgroup G} (hB' : IsHyperplane A B') (hD : IsHyperplane A D)
    (haD : a ∈ D) (hDB : B' ≠ D)
    (hcomm : ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (hRN : R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
      Subgroup.centralizer (D : Set G))
    (hRR : R = ⁅R, A⁆) : R ≤ qBound A (lB A) D := by
  have hA := h.isE27'
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hx ha)
  have hON : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hB'D : ¬ B' ≤ D := by
    intro hle
    apply hDB
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := hB'.2
    have h2 := hD.2
    omega
  obtain ⟨b, hbB', hbD⟩ := Set.not_subset.mp hB'D
  have hbA : b ∈ A := hB'.1 hbB'
  have hAle : A ≤ D ⊔ Subgroup.zpowers b := le_sup_zpowers_of_not_mem hA hD hbA hbD
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.zpowers_le.mpr (hAa hbA)).trans hON
  have hAR : A ≤ commutatorInSubgroup R O := by
    refine hAle.trans (sup_le ?_ ?_)
    · intro δ hδ
      refine mem_commutatorInSubgroup.mpr ⟨hON (hAa (hD.1 hδ)), fun r hr => ?_⟩
      have hδr : δ * r = r * δ := Subgroup.mem_centralizer_iff.mp (hRN hr).2 δ hδ
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hδr.symm]
      exact one_mem _
    · intro q hq
      refine mem_commutatorInSubgroup.mpr ⟨hbN hq, fun r hr => ?_⟩
      exact hcomm (Subgroup.commutator_mem_commutator (hRN hr).1
        ((Subgroup.zpowers_le.mpr hbB') hq))
  have hRO : R ≤ O := by
    rw [hRR, Subgroup.commutator_le]
    intro r hr g hg
    exact (mem_commutatorInSubgroup.mp (hAR hg)).2 r hr
  have hRC : R ≤ O ⊓ Subgroup.centralizer (D : Set G) := le_inf hRO (hRN.trans inf_le_right)
  refine hRC.trans ((inf_centralizer_le_pPrimeCoreOf haD).trans ?_)
  rw [qBound]
  exact le_sup_left.trans le_sup_left

theorem le_qBound_of_le_sup {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a : G}
    (ha : a ∈ A) {B' X D R : Subgroup G} (hB' : IsHyperplane A B') (haB' : a ∈ B')
    (hOX : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A B' ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (hD : IsHyperplane A D) (haD : a ∈ D)
    (hRN : R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
      Subgroup.centralizer (D : Set G))
    (hRR : R = ⁅R, A⁆) : R ≤ qBound A (lB A) D := by
  by_cases hDB : B' = D
  · subst hDB
    refine hRN.trans ((inf_centralizer_le_of_le_sup haD hOX).trans ?_)
    rw [qBound]
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  · have hB'a : B' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute (hB'.1 hx) ha)
    exact le_qBound_of_commutator_le h ha hB' hD haD hDB (commutator_le_of_le_sup hB'a haB' hOX)
      hRN hRR

theorem isHyperplane_closure_of_omega {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a b' : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hb'Ω : Subgroup.zpowers b' ∈ omegaA A) :
    IsHyperplane A (Subgroup.closure {a, b'}) := by
  have hA := h.isE27'
  obtain ⟨hb'A, hb'3, -⟩ := zpowers_mem_omegaA_iff.mp hb'Ω
  have ha3 : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA.1.2 a ha) ha1
  refine Main148.isHyperplane_closure_pair148 hA ha hb'A ha1 fun hmem => hΩ ?_
  have heq : Subgroup.zpowers b' = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by rw [ha3, hb'3])
  exact heq ▸ hb'Ω

theorem alpha_or_beta_of_caseOne {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a b' : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hb'Ω : Subgroup.zpowers b' ∈ omegaA A) {X D : Subgroup G} (hXθ : X ∈ thetaComponentsAt 3 a)
    (hXeq : X = lB A (Subgroup.closure {a, b'}) ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    (∃ B' : Subgroup G, IsHyperplane A B' ∧ a ∈ B' ∧ B' ≠ D ∧
      ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) ∨
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
        lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have hB' := isHyperplane_closure_of_omega h ha ha1 hΩ hb'Ω
  have haB' : a ∈ Subgroup.closure {a, b'} := Subgroup.subset_closure (Set.mem_insert a _)
  have hOX := sup_le_of_eq_lB_sup (theta_le_of_mem hXθ) hXeq
  by_cases hB'D : Subgroup.closure {a, b'} = D
  · exact Or.inr (hB'D ▸ hOX)
  · have hB'a : Subgroup.closure {a, b'} ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute (hB'.1 hx) ha)
    exact Or.inl ⟨_, hB', haB', hB'D, commutator_le_of_le_sup hB'a haB' hOX⟩

end Res7MemFix

open Res7MemFix

end CFSG.RankThree.PartTwo.Sec14
