module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_9_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# corollary_12_10_b
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_ambientDerivedSubgroup_sigma_compl
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    IsPiSubgroup (section10SigmaPrimes M)ᶜ (ambientDerivedSubgroup E) := by
  classical
  intro p hpD
  rw [Set.mem_compl_iff]
  have hD_le_E : ambientDerivedSubgroup E ≤ E := section12_ambientDerivedSubgroup_le
  have hpE : p ∈ subgroupPrimeSet E :=
    by
      have hcard :
          Nat.card ((ambientDerivedSubgroup E).subgroupOf E) =
            Nat.card (ambientDerivedSubgroup E) :=
        section12_card_subgroupOf_eq hD_le_E
      have hpDsub : p.val ∣ Nat.card ((ambientDerivedSubgroup E).subgroupOf E) := by
        rwa [hcard]
      exact hpDsub.trans
        (Subgroup.card_subgroup_dvd_card ((ambientDerivedSubgroup E).subgroupOf E))
  have hpτ :
      p ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
    section12_prime_mem_tau_union_of_mem_E hM hcomp hpE
  rcases hpτ with hpτ12 | hpτ3
  · rcases hpτ12 with hpτ1 | hpτ2
    · exact hpτ1.1
    · exact hpτ2.1
  · exact hpτ3.1

private theorem CFSG.section12_ambientDerivedSubgroup_commutative
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    IsMulCommutative (ambientDerivedSubgroup E) := by
  classical
  exact corollary_12_10_a
    (G := G) (M := M) (K := ambientDerivedSubgroup E) hM
    (section12_ambientDerivedSubgroup_le.trans hE.1.2.1)
    (section12_ambientDerivedSubgroup_sigma_compl hM hE.1)
    (lemma_12_1_a (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) hM hE)

private theorem CFSG.section12_E2_commutative
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    IsMulCommutative E₂ := by
  classical
  by_cases hτ2empty : section12Tau2Primes M = ∅
  · have hE2HallIn :
        section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
      section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
    rcases hE2HallIn with ⟨hE2E, hHallE2⟩
    have hE2bot : E₂ = ⊥ := by
      apply Subgroup.card_eq_one.mp
      apply section12_card_eq_one_of_no_prime_dvd
      intro q hqdiv
      have hqdiv_sub : q.val ∣ Nat.card (E₂.subgroupOf E) := by
        simpa [section12_card_subgroupOf_eq hE2E] using hqdiv
      have hqτ2 : q ∈ section12Tau2Primes M :=
        hHallE2.p_in_pi_of_p_dvd_card q hqdiv_sub
      exact (show q ∉ section12Tau2Primes M from by simp [hτ2empty]) hqτ2
    subst E₂
    infer_instance
  · have hτ2nonempty : (section12Tau2Primes M).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hτ2empty
    rcases hτ2nonempty with ⟨p, hp⟩
    obtain ⟨A, hA⟩ := section12_exists_rankTwo_in_E_of_tau2 hM hE hp
    have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
      section12_rankTwo_of_EData hE hA
    have hA_p : IsPGroup p.val A := by
      have hElem := (section12_rankTwo_elementary hA).2
      haveI : IsElementaryAbelian p.val A := hElem
      exact IsElementaryAbelian.isPGroup p.val A
    obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hA_p
    by_cases hScomm : IsMulCommutative (S : Subgroup G)
    · exact (lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm).1
    · have hτ2_single : section12Tau2Primes M = {p} :=
        theorem_12_7_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA ⟨S, hScomm⟩
      have hE2HallIn :
          section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
        section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
      rcases hE2HallIn with ⟨hE2E, hHallE2⟩
      have hE2_p : IsPGroup p.val E₂ := by
        apply section12_isPGroup_of_isPiSubgroup_singleton
        intro q hqdiv
        have hqdiv_sub : q.val ∣ Nat.card (E₂.subgroupOf E) := by
          simpa [section12_card_subgroupOf_eq hE2E] using hqdiv
        have hqτ2 : q ∈ section12Tau2Primes M :=
          hHallE2.p_in_pi_of_p_dvd_card q hqdiv_sub
        have hq_single : q ∈ ({p} : Set Nat.Primes) := by
          simpa [hτ2_single] using hqτ2
        simpa using hq_single
      let E₂sub : Subgroup M := E₂.subgroupOf M
      have hE2_le_M : E₂ ≤ M := hE2E.trans hE.1.2.1
      have hE2sub_p : IsPGroup p.val E₂sub :=
        hE2_p.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := M) hE2_le_M).symm
      obtain ⟨T, hE2sub_le_T⟩ :=
        IsPGroup.exists_le_sylow (G := M) (p := p.val) hE2sub_p
      have hTcomm : IsMulCommutative (T : Subgroup M) :=
        (theorem_12_5_b hM hp hA_M).1 T
      have hTamb_comm : IsMulCommutative (section10AmbientSylowSubgroup M T) := by
        letI : IsMulCommutative (T : Subgroup M) := hTcomm
        change IsMulCommutative ((T : Subgroup M).map M.subtype)
        exact Subgroup.map_isMulCommutative (f := M.subtype) (H := (T : Subgroup M))
      have hE2_amb_le_T : E₂ ≤ section10AmbientSylowSubgroup M T := by
        intro x hx
        exact Subgroup.mem_map.mpr
          ⟨⟨x, hE2_le_M hx⟩,
            hE2sub_le_T (by simpa [E₂sub, Subgroup.mem_subgroupOf] using hx), rfl⟩
      refine ⟨⟨fun x y => ?_⟩⟩
      exact Subtype.ext <|
        setLike_mul_comm
          (s := section10AmbientSylowSubgroup M T)
          (hE2_amb_le_T x.property) (hE2_amb_le_T y.property)

/-- Corollary 12.10(b). -/
public theorem CFSG.corollary_12_10_b
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    IsMulCommutative E₂ ∧ IsMulCommutative (ambientDerivedSubgroup E) := by
  exact ⟨section12_E2_commutative hM hE,
    section12_ambientDerivedSubgroup_commutative hM hE⟩

end Section12
