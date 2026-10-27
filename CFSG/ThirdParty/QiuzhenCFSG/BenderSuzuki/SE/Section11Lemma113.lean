module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Arithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Burnside
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Disjoint

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.3

The Mersenne number attached to the Lemma 10.1 prime is not prime.  The proof
assembles the checked Proposition 10.2 support/Sylow data, the two intersection
branches, and the implication-shaped earlier-book callbacks without assuming
the conclusion of this lemma (or any later theorem).
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Source Lemma 11.3. -/
public theorem lemma_11_3
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (h97 : Lemma97Conclusion M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    : Lemma113Conclusion d := by
  apply lemma113Conclusion_of_mersenne_not_prime d
  intro hq
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let e := h102.exponent
  have hspec := lemma113_mersenne_prime_specialization d e hq
  have hHp : IsPGroup e.r H := by
    apply lemma113_isPGroup_of_prime_support e.r_prime (n := e.a + 1)
    intro q
    rw [h102.support_iff, hspec.2]
  have hHsylX : ∃ S : Sylow e.r X, (S : Subgroup X) = H :=
    lemma113_sylow_of_hall_and_support e.r_prime h102.derived_hall
      hHp e.r_dvd_derived_card
  have hHD : H ≤ D := by
    exact (Subgroup.map_subtype_le (derivedSubgroup E)).trans inf_le_right
  have hHM : H ≤ M := hHD.trans inf_le_left
  have hHW : H ≤ W := by
    exact (Subgroup.map_subtype_le (derivedSubgroup E)).trans inf_le_left
  have hHsylM : theorem4bIsSylowSubgroupOf e.r H M := by
    letI : Fact e.r.Prime := ⟨e.r_prime⟩
    rcases hHsylX with ⟨S, hS⟩
    have hSM : (S : Subgroup X) ≤ M := by simpa [hS] using hHM
    let T : Sylow e.r M := S.subtype hSM
    refine ⟨T, ?_⟩
    change H = (S.comapOfInjective M.subtype _ _ : Subgroup M).map M.subtype
    rw [← hS]
    change (S : Subgroup X) = Subgroup.map M.subtype (S.comap M.subtype)
    exact (Subgroup.map_comap_eq_self (H := (S : Subgroup X)) (f := M.subtype) (by
      intro x hx
      exact ⟨⟨x, hSM hx⟩, rfl⟩)).symm
  have hCnormal :
      ((involutionCoreIn M).subgroupOf M).Normal := by
    rw [involutionCoreIn, subgroupOf_map_subtype_eq]
    exact involutionCore_normal
  have hHnormC : H ≤ Subgroup.normalizer
      ((involutionCoreIn M : Subgroup X) : Set X) := by
    exact hHM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (involutionCoreIn_le M)).mp hCnormal)
  have hcore : involutionCoreIn M = W := by
    by_cases hR : involutionCoreIn M ⊓ H = ⊥
    · obtain ⟨b, _hb, _hCcard, hIcard⟩ :=
        lemma113_disjoint_branch_endpoint hM ht htM e.r_prime hHM hHsylM
          hCnormal hR hHnormC hrank
          (by simpa [H, D, E] using h102.kset_subset_derived)
      have heq : e.r ^ (e.a + 1) = 2 ^ b - 1 := by
        calc
          e.r ^ (e.a + 1) =
              Nat.card {k : X // k ∈ peterfalviKSet D t} := by
            simpa [D] using hspec.2.symm
          _ = 2 ^ b - 1 := hIcard
      have hr2 : e.r ≠ 2 := by
        intro hre
        have hsub : 2 = 2 ^ d.choice.p - 1 := hre.symm.trans hspec.1
        have hpow : 2 ^ d.choice.p = 3 := by
          have hpos : 0 < 2 ^ d.choice.p := pow_pos (by norm_num) _
          omega
        have hEven : Even (2 ^ d.choice.p) :=
          Nat.even_pow.mpr ⟨even_two, d.choice.p_prime.ne_zero⟩
        rw [hpow] at hEven
        rcases hEven with ⟨k, hk⟩
        omega
      have ha0 : e.a = 0 :=
        lemma113_prime_power_successor_forces_exponent_zero
          e.r_prime hr2 heq
      exact ((Nat.ne_of_gt e.a_pos) ha0).elim
    · have hDodd : Odd (Nat.card D) := by
        simpa [D] using hM.inf_rightConjugate_card_odd htM
      have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
        simpa [D] using
          inf_rightConjugate_mem_normalizer_of_isInvolution M ht
      exact lemma113_involutionCoreIn_eq_W_of_nontrivial_intersection
        e.r_prime ht htM d83 (D := D) rfl hDodd hDnorm hW hHD hHsylM
        (by simpa [H, D, E] using h102.derived_normal_D) hR
        (by simpa [D] using h97.peterfalvi_centralizer_eq_bot)
  have hZne : (involutionsInSet M).Nonempty :=
    ⟨d83.u, d83.u_mem_M, d83.u_involution⟩
  have hclass : ∀ x : X, x ∈ involutionsInSet M →
      ∀ y : X, y ∈ involutionsInSet M →
        ∃ w : X, w ∈ W ∧ y = rightConjugateElem x w := by
    intro x hx y hy
    obtain ⟨kx, hkx, hux⟩ :=
      hM.exists_mem_peterfalviKSet_of_involution_mem
        d83.u_mem_M d83.u_involution ht htM hx.1 hx.2
    obtain ⟨ky, hky, huy⟩ :=
      hM.exists_mem_peterfalviKSet_of_involution_mem
        d83.u_mem_M d83.u_involution ht htM hy.1 hy.2
    let w : X := kx⁻¹ * ky
    have hkxH : kx ∈ H := by
      simpa [H, D, E] using h102.kset_subset_derived hkx
    have hkyH : ky ∈ H := by
      simpa [H, D, E] using h102.kset_subset_derived hky
    have hwW : w ∈ W := hHW (H.mul_mem (H.inv_mem hkxH) hkyH)
    refine ⟨w, hwW, ?_⟩
    calc
      y = rightConjugateElem d83.u ky := huy.symm
      _ = rightConjugateElem d83.u (kx * w) := by simp [w]
      _ = rightConjugateElem (rightConjugateElem d83.u kx) w := by
        rw [rightConjugateElem_comp]
      _ = rightConjugateElem x w := by rw [hux]
  have hZcard : Nat.card (involutionsInSet M) = e.r ^ (e.a + 1) := by
    calc
      Nat.card (involutionsInSet M) =
          Nat.card {k : X // k ∈ peterfalviKSet D t} := by
        symm
        simpa [D] using
          lemma113_peterfalviKSet_card_eq_involutionsInSet
            hM d83.u_mem_M d83.u_involution ht htM
      _ = e.r ^ (e.a + 1) := by simpa [D] using hspec.2
  exact lemma113_burnside_prime_power_involution_class_false
    hrank hcore hZne hclass e.r_prime hZcard

end CFSG.BenderSuzuki
