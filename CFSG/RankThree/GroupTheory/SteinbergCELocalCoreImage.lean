module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers

universe u v

variable {p : ℕ}

theorem map_thetaCoreOf_centralizer_le_of_normal_pGroup {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (M : Subgroup G) [M.Normal] (hM : IsPGroup p M) {A : Subgroup G}
    (hA : IsPGroup p A) :
    (thetaCoreOf p (Subgroup.centralizer (A : Set G))).map (QuotientGroup.mk' M) ≤
      thetaCoreOf p (Subgroup.centralizer (A.map (QuotientGroup.mk' M) : Set (G ⧸ M))) := by
  set π := QuotientGroup.mk' M
  set C := Subgroup.centralizer (A : Set G)
  set S := thetaCoreOf p C
  set D := (Subgroup.centralizer (A.map π : Set (G ⧸ M))).comap π
  set T := Subgroup.centralizer (M : Set G) ⊓ C
  have hSC : S ≤ C := thetaCoreOf_le p C
  have hSnormalC : (S.subgroupOf C).Normal := by
    rw [thetaCoreOf_subgroupOf p hp C C le_rfl]
    exact thetaCoreOf_normal_of_normal p hp _ (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hSp : ¬p ∣ Nat.card S := thetaCoreOf_prime_complement p hp C
  have hSsol : Group.IsSolvable S := thetaCoreOf_solvable p hp C
  have hSM : ⁅S, M⁆ = ⊥ :=
    local_prime_complement_centralizes_normal_prime_group hp hM hA hSC hSnormalC hSp
  have hST : S ≤ T := le_inf (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSM) hSC
  have hTC : T ≤ C := inf_le_right
  have hTnormalC : (T.subgroupOf C).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hTC).mpr fun t c ht hc => ⟨?_, ?_⟩
    · exact (Subgroup.normal_centralizer (H := M)).conj_mem t ht.1 c
    · exact C.mul_mem (C.mul_mem hc ht.2) (C.inv_mem hc)
  have hθT : thetaCoreOf p T = S := by
    rw [thetaCoreOf_normal_intersection p hp T C hTC hTnormalC]
    exact inf_eq_right.mpr hST
  have hCD : C ≤ D := by
    intro c hc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hc) a ha]
  have hTD : T ≤ D := hTC.trans hCD
  have hTnormalD : (T.subgroupOf D).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hTD).mpr fun t d ht hd => ⟨?_, ?_⟩
    · exact (Subgroup.normal_centralizer (H := M)).conj_mem t ht.1 d
    · change d * t * d⁻¹ ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hcomm : π a * π d = π d * π a :=
        Subgroup.mem_centralizer_iff.mp hd (π a) (Subgroup.mem_map_of_mem π ha)
      have hm : a⁻¹ * d⁻¹ * a * d ∈ M := by
        rw [← QuotientGroup.eq_one_iff]
        change π (a⁻¹ * d⁻¹ * a * d) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (π a), hcomm]
        group
      have hta : a * t = t * a := Subgroup.mem_centralizer_iff.mp ht.2 a ha
      have htm : (a⁻¹ * d⁻¹ * a * d) * t = t * (a⁻¹ * d⁻¹ * a * d) :=
        Subgroup.mem_centralizer_iff.mp ht.1 _ hm
      have key : (d⁻¹ * a * d) * t = t * (d⁻¹ * a * d) := by
        have h1 : d⁻¹ * a * d = a * (a⁻¹ * d⁻¹ * a * d) := by group
        rw [h1, mul_assoc, htm, ← mul_assoc, hta, mul_assoc]
      calc a * (d * t * d⁻¹) = d * ((d⁻¹ * a * d) * t) * d⁻¹ := by group
        _ = d * (t * (d⁻¹ * a * d)) * d⁻¹ := by rw [key]
        _ = d * t * d⁻¹ * a := by group
  have hSD : S ≤ D := hSC.trans hCD
  have hSnormalD : (S.subgroupOf D).Normal := by
    rw [← hθT, thetaCoreOf_subgroupOf p hp T D hTD]
    exact thetaCoreOf_normal_of_normal p hp _ hTnormalD
  have hle : S.map π ≤ Subgroup.centralizer (A.map π : Set (G ⧸ M)) :=
    Subgroup.map_le_iff_le_comap.mpr hSD
  apply normal_solvable_primeComplement_le_thetaCoreOf p _ _ hle
  · refine (Subgroup.normal_subgroupOf_iff hle).mpr fun x y hx hy => ?_
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M y
    have hg : g ∈ D := hy
    refine ⟨g * s * g⁻¹, (Subgroup.normal_subgroupOf_iff hSD).mp hSnormalD s g hs hg, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  · exact Group.isSolvable_of_surjective (π.subgroupMap_surjective S)
  · exact fun h => hSp (h.trans (Subgroup.card_map_dvd S π))

theorem local_solvable_core_image_under_solvable_quotient_aux (hp : p.Prime) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n →
    ∀ (Q : Type v) [Group Q] [Finite Q] (φ : G →* Q), Function.Surjective φ →
      Group.IsSolvable φ.ker → ∀ A : Subgroup G, IsPGroup p A →
        (thetaCoreOf p (Subgroup.centralizer (A : Set G))).map φ ≤
          thetaCoreOf p (Subgroup.centralizer (A.map φ : Set Q)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hcard Q _ _ φ hφ hN A hA
  by_cases hNp : p ∣ Nat.card φ.ker
  swap
  · exact (thetaCoreOf_centralizer_map_eq_of_pGroup_solvable_prime_complement_kernel p hp φ hφ hN
      hNp A hA).le
  have hNne : φ.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hNp
    exact hp.one_lt.ne' (Nat.dvd_one.mp hNp)
  obtain ⟨M, hMN, hMmin⟩ := Finite.exists_le_minimal
    (p := fun X : Subgroup G => X.Normal ∧ X ≠ ⊥) (a := φ.ker) ⟨inferInstance, hNne⟩
  have : M.Normal := hMmin.1.1
  have hMsol : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMN)
  obtain ⟨r, hr, -, d, -, hMcard⟩ := minimal_normal_solvable_elementary M hMmin hMsol
  set π := QuotientGroup.mk' M
  set φ' := QuotientGroup.lift M φ hMN
  have hcomp : φ'.comp π = φ := MonoidHom.ext fun g => QuotientGroup.lift_mk' M hMN g
  have hφ' : Function.Surjective φ' := by
    intro y
    obtain ⟨g, rfl⟩ := hφ y
    exact ⟨π g, QuotientGroup.lift_mk' M hMN g⟩
  have hker' : Group.IsSolvable φ'.ker := by
    rw [QuotientGroup.ker_lift]
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective φ.ker)
  have hlt : Nat.card (G ⧸ M) < n := by
    have hMone : 1 < Nat.card M := (Subgroup.one_lt_card_iff_ne_bot M).mpr hMmin.1.2
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup M
    have hpos : 0 < Nat.card (G ⧸ M) := Nat.card_pos
    rw [← hcard, hmul]
    exact lt_mul_of_one_lt_right hpos hMone
  have hstep : (thetaCoreOf p (Subgroup.centralizer (A : Set G))).map π ≤
      thetaCoreOf p (Subgroup.centralizer (A.map π : Set (G ⧸ M))) := by
    by_cases hrp : r = p
    · subst hrp
      exact map_thetaCoreOf_centralizer_le_of_normal_pGroup hp M (IsPGroup.of_card hMcard) hA
    · have hMp : ¬p ∣ Nat.card M := by
        rw [hMcard]
        intro h
        exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)).symm
      exact (thetaCoreOf_centralizer_map_eq_of_pGroup_solvable_prime_complement_kernel p hp π
        (QuotientGroup.mk'_surjective M) (by rw [QuotientGroup.ker_mk']; exact hMsol)
        (by rw [QuotientGroup.ker_mk']; exact hMp) A hA).le
  have hIH := ih _ hlt (G ⧸ M) rfl Q φ' hφ' hker' (A.map π) (hA.map π)
  rw [Subgroup.map_map, hcomp] at hIH
  calc (thetaCoreOf p (Subgroup.centralizer (A : Set G))).map φ =
        ((thetaCoreOf p (Subgroup.centralizer (A : Set G))).map π).map φ' := by
          rw [Subgroup.map_map, hcomp]
    _ ≤ (thetaCoreOf p (Subgroup.centralizer (A.map π : Set (G ⧸ M)))).map φ' :=
          Subgroup.map_mono hstep
    _ ≤ _ := hIH

theorem local_solvable_core_image_under_solvable_quotient {G Q : Type*} [Group G] [Group Q]
    [Finite G] [Finite Q] (hp : p.Prime) (φ : G →* Q) (hφ : Function.Surjective φ)
    (hN : Group.IsSolvable φ.ker) {A : Subgroup G} (hA : IsPGroup p A) :
    (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer (A : Set G))).map φ ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer (A.map φ : Set Q)) := by
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
    inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  exact local_solvable_core_image_under_solvable_quotient_aux hp _ G rfl Q φ hφ hN A hA

end CFSG.RankThree.GroupTheory
