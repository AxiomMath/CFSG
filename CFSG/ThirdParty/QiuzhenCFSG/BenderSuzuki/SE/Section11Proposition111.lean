module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111FixedProduct
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111Normalization

namespace CFSG
end CFSG
open CFSG

noncomputable section

/-!
# Section 11, Proposition 11.1

This is the numbered assembly of the Lemma 11.5 product, fixed-point, and
Fitting-normalization endpoints.
-/

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Proposition 11.1: the selected normalizer normalizes `F(V)`. -/
public theorem proposition_11_1
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h113 : Lemma113Conclusion d)
    (h114 : Lemma114Conclusion d83 d) :
    normalizerIn M d.choice.P ≤
      Subgroup.normalizer
        (fittingSubgroupOf
          (peterfalviV (M ⊓ rightConjugate M t) t) : Set X) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let V : Subgroup X := peterfalviV D t
  let F : Subgroup X := fittingSubgroupOf V
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let B : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  let f : ℕ := orderOf (t * d83.u)
  let B1 : Subgroup X := lemma115BOne B f
  let P : Subgroup X := d.choice.P
  let N : Subgroup X := normalizerIn M P
  let H : Subgroup X := F ⊔ B1
  have h115 : Lemma115Conclusion d83 d B f := by
    simpa [C, B, f] using
      lemma_11_5 hM ht htM d83 h84 h42 htwo d h102 h113 h114
  have hB1leB : B1 ≤ B := by
    simpa [B1] using lemma115_BOne_le B f
  have hVleC : V ≤ C := by
    have hVC : V ≤ B ⊔ V := le_sup_right
    rw [h115.normal_complement.sup_eq] at hVC
    exact hVC
  have hCnormB : C ≤ Subgroup.normalizer (B : Set X) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      h115.normal_complement.le_M).mp h115.normal_complement.normal_in_M
  have hVnormB : V ≤ Subgroup.normalizer (B : Set X) :=
    hVleC.trans hCnormB
  have hVnormB1 : V ≤ Subgroup.normalizer (B1 : Set X) := by
    simpa [B1] using lemma115_BOne_normalized (f := f) hVnormB
  have hFnormB1 : F ≤ Subgroup.normalizer (B1 : Set X) :=
    (fittingSubgroupOf_le V).trans hVnormB1
  have hPnormB1 : P ≤ Subgroup.normalizer (B1 : Set X) := by
    have hPV : P ≤ V := by simpa [P, V, D] using d.choice.P_le_V
    exact hPV.trans hVnormB1
  have hVnormF : V ≤ Subgroup.normalizer (F : Set X) := by
    letI : (fittingSubgroup V).Characteristic := fittingSubgroup_characteristic
    have hnorm :=
      proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        V (fittingSubgroup V)
    exact V.le_normalizer.trans (by simpa [F, fittingSubgroupOf] using hnorm)
  have hPnormF : P ≤ Subgroup.normalizer (F : Set X) := by
    have hPV : P ≤ V := by simpa [P, V, D] using d.choice.P_le_V
    exact hPV.trans hVnormF
  have hPnormH : P ≤ Subgroup.normalizer (H : Set X) := by
    intro x hx
    exact mem_normalizer_sup_of_mem_normalizers
      (hPnormF hx) (hPnormB1 hx)
  have hHmul : (H : Set X) = (F : Set X) * (B1 : Set X) := by
    simpa [H] using
      (Subgroup.coe_mul_of_left_le_normalizer_right F B1 hFnormB1)
  have hB1cardDvd : Nat.card B1 ∣ Nat.card B :=
    Subgroup.card_dvd_of_le hB1leB
  have hFB1cop : Nat.Coprime (Nat.card F) (Nat.card B1) := by
    exact Nat.Coprime.of_dvd_right hB1cardDvd
      (by simpa [F, V, D] using h115.B_coprime_fitting.symm)
  have hFB1disj : Disjoint F B1 := by
    rw [disjoint_iff]
    exact Subgroup.inf_eq_bot_of_coprime hFB1cop
  have hPprime : Nat.Prime (Nat.card P) := by
    rw [show Nat.card P = d.choice.p by simpa [P] using d.P_card]
    exact d.choice.p_prime
  have hFCentP : subgroupCentralizerIn F P = ⊥ := by
    simpa [F, P, V, D] using h102.fitting_centralizer_P
  have hB1CentP : subgroupCentralizerIn B1 P = ⊥ := by
    simpa [subgroupCentralizerIn, B1, P] using
      h115.BOne_inf_centralizer_eq_bot
  have hHnil : Group.IsNilpotent H :=
    proposition111_fixed_product_nilpotent
      hHmul hFB1disj hPnormH hPnormF hPnormB1 hPprime hFCentP hB1CentP
  have hFleH : F ≤ H := le_sup_left
  have hB1leH : B1 ≤ H := le_sup_right
  have hHnormB1 : H ≤ Subgroup.normalizer (B1 : Set X) := by
    exact sup_le hFnormB1 Subgroup.le_normalizer
  have hB1normalH : (B1.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB1leH).mpr hHnormB1
  have hFp : IsPGroup h102.exponent.r F := by
    rw [show F =
        (derivedSubgroup E).map E.subtype ⊓ V by
      simpa [F, V, D, E] using h102.fitting_eq_derived_inf]
    simpa [V, D, E] using h102.derived_inf_isPGroup
  have hrdvdF : h102.exponent.r ∣ Nat.card F := by
    simpa [F, V, D, E, h102.fitting_eq_derived_inf] using
      h102.exponent.r_dvd_derived_inf_card
  have hrB1cop : Nat.Coprime h102.exponent.r (Nat.card B1) := by
    apply Nat.Coprime.of_dvd_right hB1cardDvd
    apply Nat.Coprime.of_dvd_left hrdvdF
    simpa [F, V, D] using h115.B_coprime_fitting.symm
  have hFHp : IsPGroup h102.exponent.r (F.subgroupOf H) :=
    hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hFleH).symm
  obtain ⟨S, hFS⟩ := hFHp.exists_le_sylow
  let R : Subgroup X := (S : Subgroup H).map H.subtype
  have hRH : R ≤ H := Subgroup.map_subtype_le (S : Subgroup H)
  have hRsyl : theorem4bIsSylowSubgroupOf h102.exponent.r R H := ⟨S, rfl⟩
  have hFleR : F ≤ R := by
    intro x hxF
    let xH : H := ⟨x, hFleH hxF⟩
    have hxFH : xH ∈ F.subgroupOf H := hxF
    exact ⟨xH, hFS hxFH, rfl⟩
  have hRcentB1 : R ≤ Subgroup.centralizer (B1 : Set X) :=
    proposition111_nilpotent_normal_coprime_core_commute
      h102.exponent.r_prime hRH hB1leH hRsyl hB1normalH hrB1cop hHnil
  have hFcentB1 : F ≤ Subgroup.centralizer (B1 : Set X) :=
    hFleR.trans hRcentB1
  let Y : Subgroup X := subgroupCentralizerIn M B1
  have hVM : V ≤ M :=
    (show V ≤ D from inf_le_left).trans (show D ≤ M from inf_le_left)
  have hFM : F ≤ M := (fittingSubgroupOf_le V).trans hVM
  have hFleY : F ≤ Y := by
    intro x hxF
    exact ⟨hFM hxF, hFcentB1 hxF⟩
  have hfixB1 : ∀ x : X, x ∈ B1 → x ≠ 1 →
      fixedPointsOfSubgroup X (conjugateCosetSpace M)
        (Subgroup.zpowers x) = ∅ := by
    intro x hxB1 hxne
    exact h115.nonidentity_fixedPoints_eq_empty x (hB1leB hxB1) hxne
  have hB1cardFixed : Nat.card B1 ≤
      Nat.card (theorem4bFixedPoints M Y) := by
    simpa [Y] using
      proposition111_card_le_fixedPoints_subgroupCentralizerIn M B1 hfixB1
  have hB1odd : Odd (Nat.card B1) :=
    h115.B_card_odd.of_dvd_nat hB1cardDvd
  have hB1oneLt : 1 < Nat.card B1 :=
    (Subgroup.one_lt_card_iff_ne_bot B1).mpr (by simpa [B1] using h115.BOne_ne_bot)
  have hB1three : 3 ≤ Nat.card B1 := by
    rcases hB1odd with ⟨k, hk⟩
    omega
  have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y) :=
    hB1three.trans hB1cardFixed
  have hNnormM : N ≤ Subgroup.normalizer (M : Set X) :=
    (inf_le_left : N ≤ M).trans Subgroup.le_normalizer
  have hNnormCentB1 : N ≤
      Subgroup.normalizer (Subgroup.centralizer (B1 : Set X) : Set X) := by
    exact le_normalizer_centralizer_of_le_normalizer
      (by simpa [N, P, B1] using h115.normalizerIn_normalizes_BOne)
  have hNnormY : N ≤ Subgroup.normalizer (Y : Set X) := by
    simpa [Y, subgroupCentralizerIn] using
      Subgroup.le_normalizer_inf hNnormM hNnormCentB1
  have hYM : Y ≤ M := by
    intro x hx
    exact hx.1
  have hresult := proposition111_normalizes_fitting_of_fixedPoints
    (Y := Y) (N := N) ht htM htwo d83 d h102
      hYM
      (by simpa [F, V, D] using hFleY)
      hthree
      hNnormY
  simpa [N, P, F, V, D] using hresult

end CFSG.BenderSuzuki
