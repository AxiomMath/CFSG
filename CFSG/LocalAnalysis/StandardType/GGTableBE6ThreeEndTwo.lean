module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBF4EndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.CentralCover TableBExc.E6Three

namespace E6ThreeEnd

local instance e6ThreeEndTwoNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem uvSL_mul_uSL {K : Type} [Field K] (h2 : (2 : K) = 0) :
    (uSL (1 : K) * vSL 1) * uSL 1 = vSL 1 * (uSL 1 * vSL 1) := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [← Matrix.SpecialLinearGroup.coe_mul (uSL 1) (vSL 1), coe_uvSL h2]
  simp only [uSL, vSL, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11]

@[expose] def perpB0 : Set (Fin Tag.E6.rank → ℤ) := {γ | IsRoot .E6 γ ∧ iform γ (bE6 0) = 0}

section Perp


theorem iform_self_E6 {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have hs : ∀ j : Fin Tag.E6.rank, Tag.symmetrizer .E6 j j = 1 := by decide
  rw [hj, hs j, mul_one]

theorem not_isRoot_add_of_iform_eq_zero {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (hβ : IsRoot .E6 β) (h0 : iform α β = 0) : ¬ IsRoot .E6 (α + β) := by
  intro h
  have h1 := iform_self_E6 h
  rw [iform_add_left, iform_add_right, iform_add_right, iform_self_E6 hα, iform_self_E6 hβ,
    h0, iform_comm, h0] at h1
  norm_num at h1

theorem bE6_mem_perpB0 {k : Fin 4} (hk : k ≠ 0) : bE6 k ∈ perpB0 :=
  ⟨isRoot_bE6 k, (iform_bE6 k 0 hk).1⟩

end Perp

section Levi

variable (K : Type) [Field K]

@[expose] noncomputable def leviB0 : Subgroup (adjointGroup .E6 K) :=
  (rootSpan .E6 K perpB0).subgroupOf (adjointGroup .E6 K)

end Levi

section Inputs


@[expose] def GGE6TwoToralInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (h2 : (2 : K) = 0), Nat.card K = 2 →
    ∀ A : Subgroup (adjointGroup .E6 K), IsElemAbelian 3 A → 3 ^ 4 ≤ Nat.card A →
      ∃ e : adjointGroup .E6 K ≃* adjointGroup .E6 K,
        A.map e.toMonoidHom = (torusE6Two (K := K) h2).range

@[expose] def GGE6TwoLayerInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    LargeEvenLayer (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K))) = leviB0 K ∧
      IsComponentOf (leviB0 K) (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)))

end Inputs

section EndNode

variable {K : Type} [Field K]

theorem commute_pinnedX_b0 {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ perpB0) (c d : K) :
    Commute (pinnedX .E6 K (bE6 0) c) (pinnedX .E6 K γ d) ∧
      Commute (pinnedX .E6 K (-bE6 0) c) (pinnedX .E6 K γ d) := by
  obtain ⟨hγr, hγ0⟩ := hγ
  have h1 : iform (bE6 0) γ = 0 := by
    rw [iform_comm]
    exact hγ0
  have h2 : iform (-bE6 0) γ = 0 := by rw [iform_neg_left, h1, neg_zero]
  exact ⟨pinnedX_commute_of_iform_eq_zero K (isRoot_bE6 0) hγr h1
      (not_isRoot_add_of_iform_eq_zero (isRoot_bE6 0) hγr h1) c d,
    pinnedX_commute_of_iform_eq_zero K (isRoot_neg_bE6 0) hγr h2
      (not_isRoot_add_of_iform_eq_zero (isRoot_neg_bE6 0) hγr h2) c d⟩

theorem rootSpan_perpB0_le_centralizer :
    rootSpan .E6 K perpB0 ≤ Subgroup.centralizer
      ({((uE6Two 0 : adjointGroup .E6 K) : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨d, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨h1, h2⟩ := commute_pinnedX_b0 hγ (1 : K) d
  exact (h1.mul_left h2).eq.symm

theorem uE6Two_zero_comm_of_mem_leviB0 {j : adjointGroup .E6 K} (hj : j ∈ leviB0 K) :
    uE6Two 0 * j = j * uE6Two 0 := by
  rw [leviB0, Subgroup.mem_subgroupOf] at hj
  exact Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.mp (rootSpan_perpB0_le_centralizer hj)).symm

theorem uE6Two_conj_pinnedX (h2 : (2 : K) = 0) (k : Fin 4) :
    ((uE6Two (K := K) k : adjointGroup .E6 K) : ModGL .E6 K) * pinnedX .E6 K (bE6 k) 1 *
      ((uE6Two k : adjointGroup .E6 K) : ModGL .E6 K)⁻¹ = pinnedX .E6 K (-bE6 k) 1 := by
  have e : (uSL (1 : K) * vSL 1) * uSL 1 * (uSL 1 * vSL 1)⁻¹ = vSL 1 := by
    rw [uvSL_mul_uSL h2, mul_inv_cancel_right]
  have h := congrArg (rootSL2 .E6 K (bE6 k)) e
  rw [map_mul, map_mul, map_inv] at h
  rw [coe_uE6Two_eq h2, ← rootSL2_uSL_of_two h2 (bE6 k) 1,
    ← rootSL2_vSL_of_two h2 (isRoot_bE6 k) 1]
  exact h

theorem uE6Two_not_comm (h2 : (2 : K) = 0) (k : Fin 4) :
    ((uE6Two (K := K) k : adjointGroup .E6 K) : ModGL .E6 K) * pinnedX .E6 K (bE6 k) 1 ≠
      pinnedX .E6 K (bE6 k) 1 * ((uE6Two k : adjointGroup .E6 K) : ModGL .E6 K) := by
  intro h
  have h1 := uE6Two_conj_pinnedX h2 k
  rw [h, mul_inv_cancel_right] at h1
  exact neg_bE6_ne k (CFSG.SeitzReduction.EPilot.eq_of_pinnedX_eq_pinnedX_of_pos
    (isRoot_neg_bE6 k) (isRoot_bE6 k) (height_bE6_pos k) one_ne_zero h1.symm)

theorem torusE6Two_mem_of_coord_zero (h2 : (2 : K) = 0) {H : Subgroup (adjointGroup .E6 K)}
    (k : Fin 4) (huH : ∀ i : Fin 4, i ≠ k → uE6Two (K := K) i ∈ H)
    (w' : Multiplicative (Fin 4 → ZMod 3)) (hw' : Multiplicative.toAdd w' k = 0) :
    torusE6Two h2 w' ∈ H := by
  have hw'H : w' ∈ H.comap (torusE6Two h2) := by
    rw [TableBExc.Three.eq_prod_single w']
    refine Subgroup.prod_mem _ fun i _ => ?_
    change torusE6Two h2 (.ofAdd (Pi.single i (Multiplicative.toAdd w' i))) ∈ H
    rw [torusE6Two_single]
    by_cases hik : i = k
    · rw [hik, hw', ofAdd_zero, map_one]
      exact H.one_mem
    · rw [zmodPowHom_apply]
      exact pow_mem (huH i hik) _
  exact hw'H

theorem mem_zpowers_of_comm_leviB0 (h2 : (2 : K) = 0) {s : adjointGroup .E6 K}
    (hs : s ∈ (torusE6Two (K := K) h2).range) (hc : ∀ j ∈ leviB0 K, s * j = j * s) :
    s ∈ Subgroup.zpowers (uE6Two 0) := by
  obtain ⟨w, rfl⟩ := hs
  set v := Multiplicative.toAdd w with hv
  have hvk : ∀ k : Fin 4, k ≠ 0 → v k = 0 := by
    intro k hk
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x : adjointGroup .E6 K, (x : ModGL .E6 K) = pinnedX .E6 K (bE6 k) 1 :=
      ⟨⟨_, pinnedX_mem_adjointGroup _ _⟩, rfl⟩
    have hxL : x ∈ leviB0 K := by
      rw [leviB0, Subgroup.mem_subgroupOf, hx]
      exact pinnedX_mem_rootSpan (bE6_mem_perpB0 hk) 1
    obtain ⟨H, hH⟩ : ∃ H : Subgroup (adjointGroup .E6 K),
        H = Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) := ⟨_, rfl⟩
    have hsH : torusE6Two h2 w ∈ H := by
      rw [hH]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hc x hxL)
    have huH : ∀ i : Fin 4, i ≠ k → uE6Two (K := K) i ∈ H := by
      intro i hik
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨c1, -, c3, -⟩ := commute_pinnedX_bE6 (K := K) hik 1 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hx]
      exact (c1.mul_left c3).eq
    have hw0 : torusE6Two h2 (.ofAdd (v - Pi.single k (v k))) ∈ H := by
      refine torusE6Two_mem_of_coord_zero h2 k huH _ ?_
      have e : (v - Pi.single k (v k) : Fin 4 → ZMod 3) k = v k - v k := by
        simp only [Pi.sub_apply, Pi.single_eq_same]
      change (v - Pi.single k (v k) : Fin 4 → ZMod 3) k = 0
      exact e.trans (sub_self _)
    have hdec : w = Multiplicative.ofAdd (Pi.single k (v k)) *
        Multiplicative.ofAdd (v - Pi.single k (v k)) := by
      rw [← ofAdd_add]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have hukH : uE6Two (K := K) k ^ (v k).val ∈ H := by
      have h1 : torusE6Two h2 w * (torusE6Two h2 (.ofAdd (v - Pi.single k (v k))))⁻¹ ∈ H :=
        mul_mem hsH (inv_mem hw0)
      rw [hdec, map_mul, mul_inv_cancel_right, torusE6Two_single, zmodPowHom_apply] at h1
      exact h1
    have hukH' : uE6Two (K := K) k ∈ H := by
      have h12 : ∀ a : ZMod 3, a ≠ 0 → a.val = 1 ∨ a.val = 2 := by decide
      rcases h12 _ hne with h | h
      · rw [h, pow_one] at hukH
        exact hukH
      · rw [h] at hukH
        have e : uE6Two (K := K) k = (uE6Two k ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, uE6Two_pow_three h2, one_mul]
        rw [e]
        exact pow_mem hukH 2
    rw [hH, Subgroup.mem_centralizer_singleton_iff] at hukH'
    have hcomm := congrArg Subtype.val hukH'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx] at hcomm
    exact uE6Two_not_comm h2 k hcomm
  have hw : w = Multiplicative.ofAdd (Pi.single 0 (v 0)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    funext i
    by_cases hi : i = 0
    · rw [hi, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hi]
      exact hvk i hi
  rw [hw, torusE6Two_single, zmodPowHom_apply]
  exact Subgroup.npow_mem_zpowers _ _

theorem endNodeAt_torusE6Two_of_layer (h2 : (2 : K) = 0)
    (hL : LargeEvenLayer (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K))) =
        leviB0 K ∧
      IsComponentOf (leviB0 K) (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)))) :
    TableBF4.EndNodeAt (torusE6Two (K := K) h2).range (uE6Two 0) := by
  obtain ⟨hlay, hcomp⟩ := hL
  refine ⟨⟨.ofAdd (Pi.single 0 1), ?_⟩, uE6Two_ne_one 0, by rw [hlay]; exact hcomp, ?_⟩
  · rw [torusE6Two_single, zmodPowHom_apply, ZMod.val_one, pow_one]
  · intro s hs
    rw [hlay]
    constructor
    · exact mem_zpowers_of_comm_leviB0 h2 hs
    · intro hmem j hj
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact (Commute.zpow_left (uE6Two_zero_comm_of_mem_leviB0 hj) m).eq

theorem ggE6TwoEndNodeInput_of_inputs (hT : GGE6TwoToralInput) (hL : GGE6TwoLayerInput) :
    GGE6TwoEndNodeInput := by
  intro K _ _ hK
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  exact TableBF4.ggEndNodeElt_of_endNodeAt (V := (torusE6Two (K := K) h2).range)
    (fun A hA hr => hT K h2 hK A hA hr) (endNodeAt_torusE6Two_of_layer h2 (hL K hK))

end EndNode

end E6ThreeEnd

end CFSG.StandardType
