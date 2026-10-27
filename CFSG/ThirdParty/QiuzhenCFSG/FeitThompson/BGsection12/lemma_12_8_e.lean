module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_10_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_8_e
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.8(e). -/
public theorem CFSG.lemma_12_8_e
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups E₁ →
      subgroupCentralizerIn (section10Msigma M) X = ⊥ →
        X ≤ centerIn (G := G) E := by
  classical
  intro X hX hCXbot
  let N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let K : Subgroup G := E₂ ⊔ E₃
  rcases hX with ⟨hXE1, q, hXcard⟩
  have hEeq : E = E₁ ⊔ E₂ ⊔ E₃ :=
    (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hE1cyc : IsCyclic E₁ :=
    (lemma_12_1_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hKnormE : section10NormalIn K E := by
    simpa [K] using
      (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2.2.1
  have hE1E12 : E₁ ≤ E₁₂ := hE.2.2.1.1
  have hE12E : E₁₂ ≤ E := hE.2.1.1
  have hXE : X ≤ E := hXE1.trans (hE1E12.trans hE12E)
  have hXM : X ≤ M := hXE.trans hE.1.2.1
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn q E₁ := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXE1, hXcard⟩
  have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot hXprime
  have hqτ1 : q ∈ section12Tau1Primes M := by
    rcases hE.2.2.1 with ⟨_hE1E12, hHallE1⟩
    have hqX : q.val ∣ Nat.card E₁ := by
      exact (by rw [hXcard] : q.val ∣ Nat.card X).trans
        (Subgroup.card_dvd_of_le hXE1)
    exact hHallE1.p_in_pi_of_p_dvd_card q
      (by simpa [section12_card_subgroupOf_eq hE1E12] using hqX)
  have h8c :=
    lemma_12_8_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have h8a :=
    lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have h8d :=
    lemma_12_8_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have hNS_eq_NK : N = Subgroup.normalizer (K : Set G) := by
    calc
      N = Subgroup.normalizer ((S : Subgroup G) : Set G) := rfl
      _ = Subgroup.normalizer (E₂ : Set G) := h8d.2.1
      _ = Subgroup.normalizer (K : Set G) := h8d.2.2.1
  have hX_le_N : X ≤ N := by
    have hE_norm_K : E ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKnormE.1).1 hKnormE.2
    rw [hNS_eq_NK]
    exact hXE.trans hE_norm_K
  have hKleM : K ≤ M :=
    ((lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2.2.1.1).trans hE.1.2.1
  have hKσcompl : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K :=
    section12_subgroup_of_complement_is_sigma_compl
      (G := G) (M := M) (E := E) (K := K) hM hE.1
      ((lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2.2.1.1)
  have hFcomm : IsMulCommutative (section8FittingSubgroup E) := by
    exact corollary_12_10_a
      (G := G) (M := M) (K := section8FittingSubgroup E) hM
      ((section8FittingSubgroup_le E).trans hE.1.2.1)
      (section12_fitting_sigma_compl (G := G) (M := M) (E := E) hM hE.1)
      (by simpa using section8FittingSubgroup_isNilpotent E)
  have hKleF : K ≤ section8FittingSubgroup E := by
    have hE2_le_F : E₂ ≤ section8FittingSubgroup E := by
      letI : IsMulCommutative E₂ := h8a.1
      letI : CommGroup E₂ := IsMulCommutative.instCommGroup
      have hE2nil : Group.IsNilpotent E₂ := by infer_instance
      simpa [section8FittingSubgroup] using
        section12_le_fittingSubgroupOf_of_normalIn_nilpotent
          (G := G) (H := E) (N := E₂)
          h8a.2.1 h8a.2.2 hE2nil
    have hE3_le_F : E₃ ≤ section8FittingSubgroup E := by
      have hDerNorm : section10NormalIn (ambientDerivedSubgroup E) E :=
        section12_normalIn_ambientDerivedSubgroup (G := G) (E := E)
      have hDer_le_F : ambientDerivedSubgroup E ≤ section8FittingSubgroup E := by
        simpa [section8FittingSubgroup] using
          section12_le_fittingSubgroupOf_of_normalIn_nilpotent
            (G := G) (H := E) (N := ambientDerivedSubgroup E)
            hDerNorm.1 hDerNorm.2
            (lemma_12_1_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
              (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE)
      exact (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1.trans hDer_le_F
    simpa [K] using sup_le hE2_le_F hE3_le_F
  have hKcomm : IsMulCommutative K := by
    refine ⟨⟨fun x y => ?_⟩⟩
    exact Subtype.ext <|
      setLike_mul_comm
        (s := section8FittingSubgroup E) (hKleF x.property) (hKleF y.property)
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet q) K := by
    intro r hrK
    have hrKτ :
        r ∈ section12Tau2Primes M ∪ section12Tau3Primes M := by
      have hKHallIn :
          section12HallSubgroupIn
            (section12Tau2Primes M ∪ section12Tau3Primes M) K E := by
        simpa [K] using section12_E2_sup_E3_hall_in_E
          (M := M) (E := E) (E₁₂ := E₁₂) (E₂ := E₂) (E₃ := E₃)
          hE.2.1 hE.2.2.2.1 hE.2.2.2.2
          ((lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2)
      rcases hKHallIn with ⟨hKE, hHallK⟩
      exact hHallK.p_in_pi_of_p_dvd_card r
        (by simpa [section12_card_subgroupOf_eq hKE] using hrK)
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hrq
    rcases hrKτ with hr2 | hr3
    · have h2 : primeRank r.val M = 2 := hr2.2
      have h1 : primeRank q.val M = 1 := hqτ1.2.2
      subst hrq
      omega
    · have hq_not_der : q ∉ subgroupPrimeSet (derivedSubgroup M) := hqτ1.2.1
      subst hrq
      exact hq_not_der hr3.2.1
  have hComm :=
    proposition_10_11_d (G := G) (M := M) (K := K) (P := X) (p := q)
      hM hKleM hKσcompl hqτ1.1
      (by
        intro x hx
        exact ⟨by
          rw [← hNS_eq_NK]
          exact hX_le_N hx, hXM hx⟩)
      hXcard hCXbot hKcomm hKp'
  have hDcentK : ambientDerivedSubgroup N ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hxF : x ∈ section8FittingSubgroup E := h8c.2.1 hx
    exact (setLike_mul_comm
      (s := section8FittingSubgroup E) hxF (hKleF hk)).symm
  have hKXnormN : section10NormalIn (⁅K, X⁆) N :=
    section12_commutator_normal_of_normal_and_derived_le_centralizer
      (G := G) (N := N) (K := K) (X := X) (by
        have hKN : K ≤ N := by
          rw [hNS_eq_NK]
          exact Subgroup.le_normalizer
        refine ⟨hKN, ?_⟩
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).2
          (by simp [hNS_eq_NK]))
      hX_le_N hDcentK
  have hKXbot : ⁅K, X⁆ = ⊥ := by
    by_contra hne
    let C : Subgroup G := ⁅K, X⁆
    have hCnormN : section10NormalIn C N := by simpa [C] using hKXnormN
    have hCnormM : section10NormalIn C M := by simpa [C] using hComm.2.1
    let CM : Subgroup M := C.subgroupOf M
    have hCM_ne_bot : CM ≠ ⊥ := by
      intro hbot
      apply hne
      have hmap_bot : (CM.map M.subtype : Subgroup G) = ⊥ := by
        simpa using congrArg (fun H : Subgroup M => (H.map M.subtype : Subgroup G)) hbot
      have hmap_eq : (CM.map M.subtype : Subgroup G) = C := by
        simpa [CM] using Subgroup.map_subgroupOf_eq_of_le hCnormM.1
      simpa [C, hmap_eq] using hmap_bot
    have hM8 : M ∈ section8MaximalSubgroups G := by
      simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
    have hnorm_eq_M : Subgroup.normalizer (C : Set G) = M := by
      simpa [CM, C, section8SubgroupInAmbient, Subgroup.map_subgroupOf_eq_of_le hCnormM.1] using
        section8_normalizer_subgroupInAmbient_eq_of_nontrivial_normal_in_maximal
          (G := G) (M := M) hM8 hCM_ne_bot hCnormM.2
    have hnotN : ¬ N ≤ M := by
      have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
        section12_rankTwo_of_EData hE hA
      have hSleE : (S : Subgroup G) ≤ E :=
        h8c.1.trans (h8c.2.1.trans (h8c.2.2.1.trans h8c.2.2.2))
      have hSleM : (S : Subgroup G) ≤ M := hSleE.trans hE.1.2.1
      let SM : Sylow p.val M := S.subtype hSleM
      have hSM_eq : section10AmbientSylowSubgroup M SM = (S : Subgroup G) := by
        simpa [SM, section10AmbientSylowSubgroup] using
          (Subgroup.map_subgroupOf_eq_of_le
            (G := G) (H := (S : Subgroup G)) (K := M) hSleM)
      have hSM_not :
          ¬ Subgroup.normalizer
              ((section10AmbientSylowSubgroup M SM : Subgroup G) : Set G) ≤ M :=
        ((theorem_12_5_b (G := G) (M := M) (A := A) (p := p)
          hM hp hA_M).2 SM
          (by simpa [hSM_eq] using hAS)).2
      simpa [N, hSM_eq] using hSM_not
    have hN_le_M : N ≤ M := by
      have hN_le_normC : N ≤ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCnormN.1).1 hCnormN.2
      simpa [hnorm_eq_M] using hN_le_normC
    exact hnotN hN_le_M
  have hK_le_centX : K ≤ Subgroup.centralizer (X : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := X)).mp hKXbot
  have hE1_centX : E₁ ≤ Subgroup.centralizer (X : Set G) := by
    letI : IsCyclic E₁ := hE1cyc
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (setLike_mul_comm (s := E₁) hy (hXE1 hx)).symm
  have hE1supK_centX : E₁ ⊔ K ≤ Subgroup.centralizer (X : Set G) := by
    exact sup_le hE1_centX hK_le_centX
  have hE_centX : E ≤ Subgroup.centralizer (X : Set G) := by
    rw [hEeq]
    simpa [K, sup_assoc] using hE1supK_centX
  have hX_centE : X ≤ Subgroup.centralizer (E : Set G) :=
    (Subgroup.le_centralizer_iff (H := E) (K := X)).mp hE_centX
  intro x hx
  exact ⟨hXE hx, hX_centE hx⟩

end Section12
