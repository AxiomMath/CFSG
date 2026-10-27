module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma101
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.2

This module proves that the Lemma 10.1 subgroup `P` is maximal among the
`N_M(P)`-invariant subgroups of `V`.  The proof restricts the checked
Proposition 8.4 normalizer factor to `N_M(P)` and invokes the existing Sylow
transfer through its normal `2`-factor.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

public theorem lemma112_decompose_Y
    {X : Type u} [Group X]
    {V A P Y : Subgroup X}
    (hV : (V : Set X) = (A : Set X) * (P : Set X))
    (hPY : P ≤ Y) (hYV : Y ≤ V) :
    (Y : Set X) = ((Y ⊓ A : Subgroup X) : Set X) * (P : Set X) := by
  ext x
  constructor
  · intro hxY
    have hxV : x ∈ V := hYV hxY
    change x ∈ (V : Set X) at hxV
    rw [hV] at hxV
    rcases Set.mem_mul.mp hxV with ⟨a, haA, p, hpP, hap⟩
    have hpY : p ∈ Y := hPY hpP
    have haY : a ∈ Y := by
      have haEq : a = x * p⁻¹ := by
        rw [← hap]
        simp
      rw [haEq]
      exact Y.mul_mem hxY (Y.inv_mem hpY)
    exact Set.mem_mul.mpr ⟨a, ⟨haY, haA⟩, p, hpP, hap⟩
  · rintro ⟨a, ha, p, hp, rfl⟩
    exact Y.mul_mem ha.1 (hPY hp)

public theorem lemma112_restrict_normalizer_factor
    {X : Type u} [Group X]
    {M D P Y S : Subgroup X}
    (hDM : D ≤ M)
    (hPY : P ≤ Y)
    (hNnormY : normalizerIn M P ≤ Subgroup.normalizer (Y : Set X))
    (hS : Proposition84NormalizerFactor M D Y S) :
    S ≤ normalizerIn M P ∧
      (S.subgroupOf (normalizerIn M P)).Normal ∧
      ((normalizerIn M P : Subgroup X) : Set X) =
        (S : Set X) * (normalizerIn D P : Set X) := by
  let N : Subgroup X := normalizerIn M P
  let NY : Subgroup X := normalizerIn M Y
  let NDP : Subgroup X := normalizerIn D P
  have hNleNY : N ≤ NY := by
    intro x hx
    exact ⟨hx.1, hNnormY hx⟩
  have hScentralP : S ≤ Subgroup.centralizer (P : Set X) := by
    exact hS.le_centralizer.trans (Subgroup.centralizer_le hPY)
  have hSleN : S ≤ N := by
    intro x hx
    exact ⟨hS.le_M hx, centralizer_le_normalizer P (hScentralP hx)⟩
  have hNnormalS : N ≤ Subgroup.normalizer (S : Set X) := by
    have hNYnormalS : NY ≤ Subgroup.normalizer (S : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hS.le_normalizerIn).mp
        hS.normal_in_normalizerIn
    exact hNleNY.trans hNYnormalS
  have hSnormalN : (S.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSleN).mpr hNnormalS
  refine ⟨hSleN, hSnormalN, ?_⟩
  ext x
  constructor
  · intro hxN
    have hxNY : x ∈ NY := hNleNY hxN
    have hxy : x ∈ (S : Set X) * (normalizerIn D Y : Set X) := by
      have hxNY' : x ∈ (normalizerIn M Y : Set X) := hxNY
      change x ∈ ((M ⊓ Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) at hxNY'
      rw [hS.normalizerIn_eq_mul] at hxNY'
      simpa [normalizerIn] using hxNY'
    rcases Set.mem_mul.mp hxy with ⟨s, hsS, d, hdDY, hsd⟩
    have hsNormP : s ∈ Subgroup.normalizer (P : Set X) :=
      centralizer_le_normalizer P (hScentralP hsS)
    have hdNormP : d ∈ Subgroup.normalizer (P : Set X) := by
      have hdEq : d = s⁻¹ * x := by
        calc
          d = s⁻¹ * (s * d) := by simp
          _ = s⁻¹ * x := by rw [hsd]
      rw [hdEq]
      exact (Subgroup.normalizer (P : Set X)).mul_mem
        ((Subgroup.normalizer (P : Set X)).inv_mem hsNormP) hxN.2
    exact Set.mem_mul.mpr ⟨s, hsS, d, ⟨hdDY.1, hdNormP⟩, hsd⟩
  · rintro ⟨s, hsS, d, hdNDP, rfl⟩
    exact N.mul_mem (hSleN hsS) ⟨hDM hdNDP.1, hdNDP.2⟩

public theorem lemma_11_2
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (_ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t) :
    ∀ Y : Subgroup X,
      d.choice.P ≤ Y →
      Y ≤ peterfalviV (M ⊓ rightConjugate M t) t →
      normalizerIn M d.choice.P ≤ Subgroup.normalizer (Y : Set X) →
      Y = d.choice.P := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let P : Subgroup X := d.choice.P
  let A : Subgroup X := d.choice.initial.A1
  let N : Subgroup X := normalizerIn M P
  intro Y hPY hYV hNnormY
  by_contra hYneP
  have hPYlt : P < Y := lt_of_le_of_ne hPY (Ne.symm hYneP)
  let B : Subgroup X := Y ⊓ A
  have hYprod : (Y : Set X) = (B : Set X) * (P : Set X) := by
    simpa [B, V, A, P] using
      lemma112_decompose_Y d.V_eq_mul hPY hYV
  have hBne : B ≠ ⊥ := by
    intro hBbot
    have hYP : Y = P := by
      apply SetLike.coe_injective
      simpa [hBbot] using hYprod
    exact hYneP hYP
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hYnormA : Y ≤ Subgroup.normalizer (A : Set X) := by
    exact hYV.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAV).mp
        d.choice.initial.A1_normal_V)
  have hYnormB : Y ≤ Subgroup.normalizer (B : Set X) := by
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, hYnormA hy⟩
  have hBnormalY : (B.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hYnormB
  have hBA : B ≤ A := inf_le_right
  obtain ⟨j, hjI, hjCY0, hjne⟩ := d.choice.Y_nontrivial_centralizer
  have hjJ : j ∈ d.choice.initial.J := by
    change j ∈ (d.choice.initial.J : Set X)
    rw [d.choice.initial.J_eq_centralizer]
    exact ⟨hjI, hjCY0⟩
  have hjCB : j ∈ Subgroup.centralizer (B : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hbB
    have hbA : b ∈ A := hBA hbB
    change b ∈ d.choice.initial.A1 at hbA
    rw [d.choice.initial.A1_eq] at hbA
    exact (Subgroup.mem_centralizer_iff.mp hbA.2 j hjJ).symm
  have hIB : HasNontrivialPeterfalviNormalizer D t B :=
    ⟨j, by simpa [D] using hjI, centralizer_le_normalizer B hjCB, hjne⟩
  have hYVsource : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    simpa [V, D, peterfalviV] using hYV
  obtain ⟨S, hS⟩ := h84.exists_factor_of_normal d83
    (by simpa [D] using hYVsource) hBne inf_le_left hBnormalY
    (by simpa [D] using hIB)
  have hNnormY' : normalizerIn M P ≤ Subgroup.normalizer (Y : Set X) := by
    simpa [P, N] using hNnormY
  obtain ⟨hSleN, hSnormalN, hNfactor⟩ :=
    lemma112_restrict_normalizer_factor (M := M) (D := D)
      (P := P) (Y := Y) (S := S) inf_le_left hPY hNnormY' hS
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hPD : P ≤ D := by
    exact d.choice.P_le_V.trans (show V ≤ D from inf_le_left)
  have hpodd : Odd d.choice.p := by
    apply hDodd.of_dvd_nat
    rw [← d.P_card]
    exact Subgroup.card_dvd_of_le hPD
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  obtain ⟨PD, hPDmap⟩ := d.P_sylow_D
  obtain ⟨PM, hPMmap⟩ := exists_sylow_of_two_factor
    hpodd (show D ≤ M from inf_le_left) hPD hDodd
    (by simpa [P, N] using hSleN) hS.isPGroup_two
    (by simpa [P, N] using hSnormalN)
    (by simpa [P, N] using hNfactor) PD hPDmap.symm
  have hPsylM : theorem4bIsSylowSubgroupOf d.choice.p P M :=
    ⟨PM, hPMmap.symm⟩
  have hPcomm : P ≤ Subgroup.centralizer (P : Set X) := by
    letI : IsMulCommutative P :=
      (isCyclic_of_prime_card (by simpa [P] using d.P_card)).commutative
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := P)).comm
        (⟨x, hx⟩ : P) (⟨y, hy⟩ : P)).symm
  have hNDPcentral : normalizerIn D P ≤
      Subgroup.centralizer (P : Set X) := by
    rw [d.normalizer_factorization.1]
    exact sup_le inf_le_right hPcomm
  have hScentralP : S ≤ Subgroup.centralizer (P : Set X) :=
    hS.le_centralizer.trans (Subgroup.centralizer_le hPY)
  have hNcentral : N ≤ Subgroup.centralizer (P : Set X) := by
    intro x hxN
    have hxProd : x ∈ (S : Set X) * (normalizerIn D P : Set X) := by
      rw [← hNfactor]
      simpa [N] using hxN
    rcases Set.mem_mul.mp hxProd with ⟨s, hs, q, hq, hsq⟩
    rw [← hsq]
    exact (Subgroup.centralizer (P : Set X)).mul_mem
      (hScentralP hs) (hNDPcentral hq)
  have hNeqC : N = M ⊓ Subgroup.centralizer (P : Set X) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hNcentral hx⟩
    · intro x hx
      exact ⟨hx.1, centralizer_le_normalizer P hx.2⟩
  have hgrowth := d.normalizer_growth_if_sylow_M hPsylM
  change M ⊓ Subgroup.centralizer (P : Set X) < N at hgrowth
  rw [← hNeqC] at hgrowth
  exact (lt_irrefl N) hgrowth

end CFSG.BenderSuzuki
