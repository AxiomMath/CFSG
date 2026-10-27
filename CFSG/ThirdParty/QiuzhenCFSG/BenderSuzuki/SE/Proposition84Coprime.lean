module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Coprime-action infrastructure for Proposition 8.4

The proper-predecessor branch uses the odd-order decomposition
`R = [R,A] C_R(A)` for the involution group `A = <t>`.  This file proves that
decomposition independently from the Proposition 8.4 assembly.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise

open PFAppendixIII PFchapter1section1

universe u

/-- If a subgroup `A` of order two normalizes an odd-order subgroup `R`, then
`R` is the product of its action commutator with its `A`-centralizer.

Solvability of `R` is supplied by the Feit--Thompson odd-order theorem; the
fixed-point/commutator decomposition is the standard coprime-action theorem.
-/
public theorem odd_subgroup_eq_commutator_mul_centralizer
    {X : Type u} [Group X] [Finite X]
    (R A : Subgroup X)
    (hA_norm_R : A ≤ Subgroup.normalizer (R : Set X))
    (hAcard : Nat.card A = 2) (hRodd : Odd (Nat.card R)) :
    (R : Set X) =
      (⁅R, A⁆ : Subgroup X) *
        ((R ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
  letI : Subgroup.Normalizes A R := ⟨hA_norm_R⟩
  let Cfix : Subgroup R := fixedPointSubgroup A R
  let Ccomm : Subgroup R := commutatorAction (A := A) (G := R)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    rw [hAcard]
    exact hRodd.coprime_two_left
  have hsup : Cfix ⊔ Ccomm = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (odd_order_theorem R hRodd) hcop
  have hcommMap : Ccomm.map R.subtype = ⁅R, A⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator R A hA_norm_R
  have hfixEq :
      Cfix =
        ((R ⊓ Subgroup.centralizer (A : Set X)).subgroupOf R) := by
    simpa [subgroupCentralizerIn] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
        R A hA_norm_R
  haveI : Ccomm.Normal :=
    (commutatorAction_normal_and_invariant (A := A) (G := R)).1
  apply Set.Subset.antisymm
  · intro x hxR
    let xR : R := ⟨x, hxR⟩
    have hxTop : xR ∈ Ccomm ⊔ Cfix := by
      rw [sup_comm, hsup]
      exact Subgroup.mem_top xR
    rcases (Subgroup.mem_sup_of_normal_left.mp hxTop) with
      ⟨k, hk, c, hc, hkc⟩
    rw [Set.mem_mul]
    refine ⟨(k : X), ?_, (c : X), ?_, ?_⟩
    · rw [← hcommMap]
      exact ⟨k, hk, rfl⟩
    · rw [hfixEq] at hc
      exact hc
    · exact congrArg Subtype.val hkc
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨k, hk, c, hc, rfl⟩
    have hkR : k ∈ R := by
      rw [← hcommMap] at hk
      exact Subgroup.map_subtype_le Ccomm hk
    exact R.mul_mem hkR hc.1

/-- In the proper-predecessor branch of Proposition 8.4, the normalizer of
`Y` inside `D = M ∩ M^t` is contained in the product of the centralizer of the
two-prime residual of `Y` and the normalizer of `Y` inside
`V = D ∩ C_X(u)`.

This is the coprime-action transfer used after the induction hypothesis has
identified the residual of `Y`: decompose the odd-order subgroup `N_D(Y)`
under the action of `⟨t⟩`, put the action commutator in the residual
centralizer, and put the fixed-point factor in `N_V(Y)`.
-/
public theorem normalizerIn_le_centralizerResidual_mul_normalizerIn
    {X : Type*} [Group X] [Finite X] {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M) (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) {Y : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X)) :
    ((normalizerIn (M ⊓ rightConjugate M t) Y : Subgroup X) : Set X) ⊆
      (centralizerTwoPrimeResidual Y : Set X) *
        (normalizerIn
          ((M ⊓ rightConjugate M t) ⊓
            Subgroup.centralizer ({d83.u} : Set X)) Y : Set X) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := D ⊓ Subgroup.centralizer ({d83.u} : Set X)
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let F : Subgroup X := centralizerTwoPrimeResidual Y
  let R : Subgroup X := normalizerIn D Y
  let A : Subgroup X := Subgroup.zpowers t
  have hYVt : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    dsimp [D]
    rw [d83.centralizer_eq]
    exact hYV
  have htC : t ∈ Subgroup.centralizer (Y : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyY
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYVt hyY).2
  have htN : t ∈ N := centralizer_le_normalizer Y htC
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    exact inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have htNormN : t ∈ Subgroup.normalizer (N : Set X) := N.le_normalizer htN
  have htNormR : t ∈ Subgroup.normalizer (R : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at htNormD htNormN ⊢
    intro r
    change (r ∈ D ∧ r ∈ N) ↔
      (t * r * t⁻¹ ∈ D ∧ t * r * t⁻¹ ∈ N)
    exact and_congr (htNormD r) (htNormN r)
  have hA_norm_R : A ≤ Subgroup.normalizer (R : Set X) := by
    rw [Subgroup.zpowers_le]
    exact htNormR
  have hAcard : Nat.card A = 2 := by
    have horder : orderOf t = 2 :=
      (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
    simp [A, Nat.card_zpowers, horder]
  have hRodd : Odd (Nat.card R) := by
    apply odd_of_card_dvd (hM.inf_rightConjugate_card_odd htM)
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdecomp :
      (R : Set X) = (⁅R, A⁆ : Subgroup X) *
        ((R ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) :=
    odd_subgroup_eq_commutator_mul_centralizer R A
      hA_norm_R hAcard hRodd
  have hA_le_F : A ≤ F := by
    exact zpowers_le_centralizerTwoPrimeResidual_of_isInvolution Y ht htC
  have hF_le_N : F ≤ N :=
    (centralizerTwoPrimeResidual_le_ambientCentralizer Y).trans
      (centralizer_le_normalizer Y)
  have hFnormal : (F.subgroupOf N).Normal := by
    exact centralizerTwoPrimeResidual_normal_in_normalizer Y
  have hcomm_le_F : ⁅R, A⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro r hr a ha
    have hrN : r ∈ N := hr.2
    have haF : a ∈ F := hA_le_F ha
    have hconj : r * a * r⁻¹ ∈ F := by
      have h := (Subgroup.normal_subgroupOf_iff hF_le_N).mp hFnormal
        a r haF hrN
      simpa using h
    simpa [commutatorElement_def, mul_assoc] using
      F.mul_mem hconj (F.inv_mem haF)
  have hcentral_le_NV :
      R ⊓ Subgroup.centralizer (A : Set X) ≤ normalizerIn V Y := by
    intro c hc
    have hcCentT : c ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hc.2)
        t (Subgroup.mem_zpowers t)).symm
    have hcV : c ∈ V := by
      have hcDt : c ∈ D ⊓ Subgroup.centralizer ({t} : Set X) :=
        ⟨hc.1.1, hcCentT⟩
      rw [d83.centralizer_eq] at hcDt
      exact hcDt
    exact ⟨hcV, hc.1.2⟩
  intro x hxR
  have hx : x ∈
      (⁅R, A⁆ : Subgroup X) *
        ((R ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
    rw [← hdecomp]
    exact hxR
  rw [Set.mem_mul] at hx ⊢
  rcases hx with ⟨k, hk, c, hc, rfl⟩
  exact ⟨k, hcomm_le_F hk, c, hcentral_le_NV hc, rfl⟩

end CFSG.BenderSuzuki
