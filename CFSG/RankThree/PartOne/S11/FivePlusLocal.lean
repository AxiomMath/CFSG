module

public import CFSG.RankThree.PartOne.S11.FivePlusSelect
public import CFSG.RankThree.PartOne.S11.FivePlusInner
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.NormalPCoreTwoCommutatorThetaComponent
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem thetaQuotientConj_apply_ne_of_not_commute {p : ℕ} (hp : p.Prime) {L : Subgroup H}
    (hL : L ∈ thetaComponents p H) {g : H} (hg : g ∈ normalizer (L : Set H)) {l : L}
    (hne : QuotientGroup.mk' (aschbacherSolvableCore p H) (l : H) *
        QuotientGroup.mk' (aschbacherSolvableCore p H) g ≠
      QuotientGroup.mk' (aschbacherSolvableCore p H) g *
        QuotientGroup.mk' (aschbacherSolvableCore p H) (l : H)) :
    thetaQuotientConj p L ⟨g, hg⟩ (l : L ⧸ aschbacherSolvableCore p L) ≠
      (l : L ⧸ aschbacherSolvableCore p L) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNchar, -, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  have := hNchar
  have : (aschbacherSolvableCore p H).Normal := inferInstance
  set π := QuotientGroup.mk' (aschbacherSolvableCore p H) with hπ
  have hcore := solvable_prime_complement_core_subnormal_intersection hp hL.2.1
  intro h
  rw [thetaQuotientConj_mk, QuotientGroup.eq] at h
  have hmem : (((L.normalizerMonoidHom ⟨g, hg⟩ l : L))⁻¹ * l : L) ∈ aschbacherSolvableCore p L := h
  have hmemH : ((((L.normalizerMonoidHom ⟨g, hg⟩ l : L))⁻¹ * l : L) : H) ∈
      inSubgroup (aschbacherSolvableCore p) L := ⟨_, hmem, rfl⟩
  rw [hcore] at hmemH
  have h1 : π ((g * l * g⁻¹)⁻¹ * l) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmemH.2
  apply hne
  rw [map_mul, map_inv, map_mul, map_mul, map_inv, inv_mul_eq_one] at h1
  calc π l * π g = (π g * π l * (π g)⁻¹) * π g := by rw [h1]
    _ = π g * π l := by group

theorem exists_zero_thetaComponent_of_inner (hB5 : SelectedPrimeElementsNormalizeThetaComponents)
    (hK : CatalogPrimeTwoAutomorphismsInner) (he : CFSG.Assembly.evenRank H ≤ 3) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hcat : ∀ L ∈ thetaComponents p H, Catalog ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)))
    {A Q : Subgroup H} (hA : IsPGroup p A) (hQ2 : IsPGroup 2 Q)
    (hAQ : A ≤ normalizer (Q : Set H)) (hQA : ⁅Q, A⁆ = Q)
    (hQN : ⁅A, Q ⊓ aschbacherSolvableCore p H⁆ = ⊥)
    (hQO : ⁅Q.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
      pCore p (H ⧸ aschbacherSolvableCore p H)⁆ = ⊥)
    {a : H} (ha : a ∈ A) (hQa : ⁅Q, Subgroup.zpowers a⁆ ≠ ⊥) :
    ∃ L ∈ thetaComponents p H, A ≤ normalizer (L : Set H) ∧ ⁅L, Subgroup.zpowers a⁆ = L ∧
      ∃ T : Subgroup H, T ≤ L ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ normalizer (T : Set H) ∧
        ⁅T, A⁆ = T := by
  classical
  obtain ⟨J, hJ, hQJ, hAJ, hnc⟩ :=
    select_moved_component hB5 he hp hp3 hA hQ2 hAQ hQA hQN hQO ha hQa
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNchar, -, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set N := aschbacherSolvableCore p H with hN
  have := hNchar
  have : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨hLmem, hLJ⟩ := perfectResidual_comap_mem_thetaComponents hp hJ
  set L := inSubgroup perfectResidual (J.comap π) with hLdef
  have hAnorm : ∀ x ∈ A, x ∈ normalizer (L : Set H) := by
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨x, hx⟩
    exact hB5.1 H he p hp hp3 x ⟨k, (Subgroup.orderOf_coe (⟨x, hx⟩ : A)).trans hk⟩ L hLmem
  have hAL : A ≤ normalizer (L : Set H) := fun x hx => hAnorm x hx
  have hQL : Q ≤ normalizer (L : Set H) := by
    intro q hq
    apply SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual (J.comap π)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hQJ (Subgroup.mem_map_of_mem π hq)) (π h)
  have hzπ : Subgroup.zpowers (π a) ≤ normalizer (Q.map π : Set (H ⧸ N)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π (hAQ ha))
  have hQnc : ∃ q ∈ Q, ∃ j ∈ J, j * π q ≠ π q * j := by
    by_contra hcon
    push Not at hcon
    apply hnc
    refine (commutator_le_left_of_normalizes hzπ).trans ?_
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun j hj => hcon q hq j hj
  have hanc : ∃ j ∈ J, j * π a ≠ π a * j := by
    by_contra hcon
    push Not at hcon
    apply hnc
    exact commutator_le_centralizer_of_normalizes hQJ
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun j hj => hcon j hj))
  refine ⟨L, hLmem, hAL, ?_, ?_⟩
  ·
    obtain ⟨j, hjJ, hj⟩ := hanc
    rw [← hLJ] at hjJ
    obtain ⟨l, hlL, rfl⟩ := hjJ
    have hzL : Subgroup.zpowers a ≤ normalizer (L : Set H) :=
      Subgroup.zpowers_le.mpr (hAL ha)
    let _ : MulDistribMulAction (Subgroup.zpowers a) L := conjActionOn hzL
    have hnt := thetaQuotientConj_apply_ne_of_not_commute hp hLmem (hAL ha) (l := ⟨l, hlL⟩) hj
    have hA1 := actionCommutator_top_eq_top_of_moving_theta_quotient hp hLmem.1 hLmem.2.2
      (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) (⟨l, hlL⟩ : L) hnt
    have h := SteinbergBM.map_actionCommutator_conj hzL (⊤ : Subgroup L)
    have hTopL : (⊤ : Subgroup L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hA1, hTopL] at h
    exact h.symm
  ·
    obtain ⟨q, hq, j, hjJ, hj⟩ := hQnc
    rw [← hLJ] at hjJ
    obtain ⟨l, hlL, rfl⟩ := hjJ
    have hmoved := thetaQuotientConj_apply_ne_of_not_commute hp hLmem (hQL hq) (l := ⟨l, hlL⟩) hj
    refine exists_two_commutator_in_thetaComponent hp hp3 hK hAL hQL hA hQ2 hAQ hQA hLmem.2.2
      (hcat L hLmem) ⟨⟨q, hq⟩, fun h1 => hmoved ?_⟩
    have h2 : thetaQuotientAction p hQL ⟨q, hq⟩ ((⟨l, hlL⟩ : L) : L ⧸ aschbacherSolvableCore p L) =
        ((⟨l, hlL⟩ : L) : L ⧸ aschbacherSolvableCore p L) := by
      rw [h1]
      rfl
    exact h2

end CFSG.RankThree.PartOne
