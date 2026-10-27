module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2: ambient Sylow support

This module isolates the Corollary 7.12 endpoint used in the prime-support
half of Proposition 10.2.  A prime dividing the Peterfalvi anti-fixed set
forces every local Sylow subgroup at that prime to fix exactly the two base
cosets; the checked two-fixed-point Witt adapter then promotes it to an
ambient Sylow subgroup.  No conclusion of Proposition 10.2 is used here.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Conjugation preserves the cardinality of a finite subgroup. -/
public theorem proposition102_natCard_rightConjugate
    {X : Type u} [Group X] (Y : Subgroup X) (g : X) :
    Nat.card (rightConjugate Y g) = Nat.card Y := by
  rw [rightConjugate, Subgroup.conjBy]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective Y
      (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.toEquiv

/-- The relative index of `V = C_D(t)` is the Peterfalvi anti-fixed-set
cardinality. -/
public theorem proposition102_peterfalviV_index_eq_kset_card
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    ((peterfalviV D t).subgroupOf D).index =
      Nat.card {x : X // x ∈ peterfalviKSet D t} := by
  have hcard := (PFchapter1section1.lemma_a t D ht hDodd hDnorm).2.2
  have hVD : peterfalviV D t ≤ D := inf_le_left
  have hpos : 0 < Nat.card (peterfalviV D t) := Nat.card_pos
  apply Nat.mul_left_cancel hpos
  calc
    Nat.card (peterfalviV D t) *
        ((peterfalviV D t).subgroupOf D).index =
        Nat.card D := by
      rw [← natCard_subgroupOf_eq (peterfalviV D t) D hVD]
      exact ((peterfalviV D t).subgroupOf D).card_mul_index
    _ = Nat.card (peterfalviV D t) *
        Nat.card (peterfalviKSet D t) := by
      simpa [peterfalviV, peterfalviKSet] using hcard

/-- If a prime divides the relative index of `V` in `D`, a local Sylow
subgroup of `D` at that prime cannot be contained in `V`. -/
public theorem proposition102_no_sylow_le_of_prime_index
    {X : Type u} [Group X] [Finite X]
    {D V R : Subgroup X} {q : ℕ}
    (hq : q.Prime)
    (hRsyl : theorem4bIsSylowSubgroupOf q R D)
    (hRV : R ≤ V)
    (hqidx : q ∣ (V.subgroupOf D).index) :
    False := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  rcases hRsyl with ⟨S, hS⟩
  have hRD : R ≤ D := by
    rw [hS]
    exact Subgroup.map_subtype_le (S : Subgroup D)
  let RD : Subgroup D := R.subgroupOf D
  have hRDmap : RD.map D.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRD]
  have hRDS : RD = (S : Subgroup D) := by
    apply Subgroup.map_injective D.subtype_injective
    rw [hRDmap, hS]
  have hRVd : RD ≤ V.subgroupOf D := by
    intro x hx
    change (x : X) ∈ V
    exact hRV hx
  have hindexdvd : (V.subgroupOf D).index ∣ RD.index :=
    Subgroup.index_dvd_of_le hRVd
  have hqRDnot : ¬ q ∣ RD.index := by
    rw [hRDS]
    exact S.not_dvd_index
  exact hqRDnot (hqidx.trans hindexdvd)

/-- A prime dividing the Peterfalvi anti-fixed set occurs in an ambient Sylow
subgroup of `X` contained in the two-point stabilizer `D`. -/
public theorem proposition102_ambient_sylow_of_prime_dvd_kset
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    {q : ℕ} (hq : q.Prime)
    (hqI : q ∣ Nat.card {x : X //
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t}) :
    ∃ Q : Sylow q X,
      (Q : Subgroup X) ≤ M ⊓ rightConjugate M t := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hindex : (V.subgroupOf D).index =
      Nat.card {x : X // x ∈ peterfalviKSet D t} := by
    simpa [V] using
      proposition102_peterfalviV_index_eq_kset_card ht hDodd htNormD
  have hqidx : q ∣ (V.subgroupOf D).index := by
    rw [hindex]
    simpa [D] using hqI
  have hqD : q ∣ Nat.card D := by
    exact hqidx.trans (V.subgroupOf D).index_dvd_card
  have hqOdd : Odd q := hDodd.of_dvd_nat hqD
  letI : Fact q.Prime := ⟨hq⟩
  let S : Sylow q D := Sylow.nonempty.some
  let P : Subgroup X := (S : Subgroup D).map D.subtype
  have hPD : P ≤ D := Subgroup.map_subtype_le (S : Subgroup D)
  have hPsyl : theorem4bIsSylowSubgroupOf q P D := ⟨S, rfl⟩
  have hPp : IsPGroup q P := S.isPGroup'.map D.subtype
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hab : alpha ≠ beta := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h
  have hPalpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    theorem4b_baseCoset_mem_fixedPoints (hPD.trans inf_le_left)
  have hPbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
    intro x hx
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hPD.trans inf_le_right hx
  have htwo : 2 ≤ Nat.card (theorem4bFixedPoints M P) := by
    let p0 : theorem4bFixedPoints M P := ⟨alpha, hPalpha⟩
    let p1 : theorem4bFixedPoints M P := ⟨beta, hPbeta⟩
    let f : Bool → theorem4bFixedPoints M P :=
      fun b => if b then p1 else p0
    have hf : Function.Injective f := by
      intro a b hf
      cases a <;> cases b
      · rfl
      · exact (hab (congrArg Subtype.val hf)).elim
      · exact (hab (congrArg Subtype.val hf).symm).elim
      · rfl
    simpa using Nat.card_le_card_of_injective f hf
  have hcard : Nat.card (theorem4bFixedPoints M P) = 2 := by
    by_contra hne
    have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M P) := by omega
    obtain ⟨d, hdD, hPdV⟩ := d83.conjugate_le P
      (by simpa [D] using hPD) hthree
    have hPdV' : rightConjugate P d ≤ V := by
      simpa [D, V, peterfalviV] using hPdV
    have hcardPd : Nat.card (rightConjugate P d) =
        Nat.card (S : Subgroup D) := by
      calc
        Nat.card (rightConjugate P d) = Nat.card P :=
          proposition102_natCard_rightConjugate P d
        _ = Nat.card (S : Subgroup D) := by
          exact Subgroup.card_map_of_injective D.subtype_injective
    have hcardSdV : Nat.card (S : Subgroup D) ∣ Nat.card V := by
      rw [← hcardPd]
      exact Subgroup.card_dvd_of_le hPdV'
    obtain ⟨k, hk⟩ := hcardSdV
    have hindexEq : S.index = k * (V.subgroupOf D).index := by
      have hSpos : 0 < Nat.card (S : Subgroup D) := Nat.card_pos
      apply Nat.mul_left_cancel hSpos
      calc
        Nat.card (S : Subgroup D) * S.index = Nat.card D :=
          S.1.card_mul_index
        _ = Nat.card V * (V.subgroupOf D).index := by
          calc
            Nat.card D = Nat.card (V.subgroupOf D) *
                (V.subgroupOf D).index :=
              (V.subgroupOf D).card_mul_index.symm
            _ = Nat.card V * (V.subgroupOf D).index := by
              rw [natCard_subgroupOf_eq V D inf_le_left]
        _ = (Nat.card (S : Subgroup D) * k) *
            (V.subgroupOf D).index := by rw [hk]
        _ = Nat.card (S : Subgroup D) *
            (k * (V.subgroupOf D).index) := by
          simp [Nat.mul_assoc]
    apply S.not_dvd_index
    rw [hindexEq]
    exact dvd_mul_of_dvd_right hqidx k
  have hPsylPair : theorem4bIsSylowSubgroupOf q P
      (MulAction.stabilizer X alpha ⊓ MulAction.stabilizer X beta) := by
    rw [show MulAction.stabilizer X alpha = M by
      simpa [alpha] using baseCoset_stabilizer M]
    rw [show MulAction.stabilizer X beta = rightConjugate M t by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
    simpa [D] using hPsyl
  obtain ⟨Q, hQP⟩ := chapter1_two_fixed_local_sylow_is_ambient
    hq hqOdd hPp hab hPalpha hPbeta hcard hPsylPair
  refine ⟨Q, ?_⟩
  rw [hQP]
  simpa [D] using hPD

end CFSG.BenderSuzuki
