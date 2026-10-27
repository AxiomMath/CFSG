module

public import CFSG.Monster.Existence.BabyAmbient
public import CFSG.Monster.Existence.BabyTableIVCore
public import CFSG.Monster.Existence.BabyTableIVLabels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS CFSG.Blueprint

@[expose] noncomputable def babyToShat :
    NativeSporadic.B ≃* Shat :=
  CTIB.iotaEquiv.trans CTIB.sEquiv

theorem isConj_babyToShat_iff
    {a b : NativeSporadic.B} :
    IsConj (babyToShat a) (babyToShat b) ↔ IsConj a b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨babyToShat.symm c, babyToShat.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨babyToShat c, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hc]

theorem babyToShat_babyRep
    (i : ℕ) : babyToShat (babyRep i) = CTIB.sEquiv (CTIB.rs i) := by
  rw [babyToShat, MulEquiv.trans_apply, babyRep, MulEquiv.apply_symm_apply]

theorem babyToShat_babyRep_zero :
    babyToShat (babyRep 0) = CTIB.xhatS := by
  rw [babyToShat_babyRep, CTIB.rs0_eq, CTIB.sEquiv_xs]

theorem orderOf_babyRep
    {i : ℕ} (hi : i < 14) : orderOf (babyRep i) = 2 := by
  rw [babyRep, MulEquiv.orderOf_eq]
  exact CTIB.orderOf_two_iff.2 ⟨CTIB.rs_mul_self hi, CTIB.rs_ne_one hi⟩

theorem babyInv_zero_babyRep_one :
    BabyInv 0 (babyRep 1) :=
  ⟨orderOf_babyRep (by norm_num), natCard_centralizer_rep_one⟩

theorem babyInv_one_babyRep_zero :
    BabyInv 1 (babyRep 0) :=
  ⟨orderOf_babyRep (by norm_num), natCard_centralizer_rep_zero⟩

theorem babyInv_three_babyRep_five :
    BabyInv 3 (babyRep 5) :=
  ⟨orderOf_babyRep (by norm_num), natCard_centralizer_rep_five⟩

theorem isConj_clabelS_babyToShat_babyRep_one
    (v : CVert) :
    IsConj (clabelS v) (babyToShat (babyRep 1)) := by
  have h1 : IsConj (CTIB.sEquiv (CTIB.rs 1)) (CTIB.sEquiv CTIB.labelS) :=
    CTIB.sEquiv.toMonoidHom.map_isConj (CTIB.isConj_labelS_of_rank
      (CTIB.orderOf_two_iff.2 ⟨CTIB.rs_mul_self (by norm_num), CTIB.rs_ne_one (by norm_num)⟩)
      CTIB.rank_four.1)
  rw [CTIB.sEquiv_labelS, CTIB.cS_inv] at h1
  have h2 : CTIB.cS = clabelS cv0 := Subtype.ext clabel_cv0.symm
  rw [babyToShat_babyRep]
  exact (CTIB.isConj_clabelS v cv0).trans (by rw [← h2]; exact h1.symm)

theorem babyInv_zero_iff_clabelS
    (hcls : ∀ t : NativeSporadic.B, BabyInv 0 t → IsConj t (babyRep 1)) (t : NativeSporadic.B) :
    BabyInv 0 t ↔ ∃ v, clabelS v = babyToShat t := by
  constructor
  · intro ht
    have h1 : IsConj (babyToShat t) (babyToShat (babyRep 1)) :=
      isConj_babyToShat_iff.2 (hcls t ht)
    exact CTIB.exists_clabelS_eq_of_isConj ((isConj_clabelS_babyToShat_babyRep_one cv0).trans
      h1.symm)
  · rintro ⟨v, hv⟩
    have h1 : IsConj (babyToShat (babyRep 1)) (babyToShat t) := by
      rw [← hv]
      exact (isConj_clabelS_babyToShat_babyRep_one v).symm
    exact babyInv_zero_babyRep_one.of_isConj (isConj_babyToShat_iff.1 h1)

theorem isConj_babyRep_one_of_babyInv_zero
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0)
    {t : NativeSporadic.B} (ht : BabyInv 0 t) : IsConj t (babyRep 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -⟩ := CTIB.native_four_involution_classes
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB t ht.1
  have hcard := natCard_centralizer_eq_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hc
  · exact absurd (BabyInv.unique ht ⟨ht.1, hcard.trans natCard_centralizer_rep_zero⟩) (by decide)
  · exact absurd (BabyInv.unique ht ⟨ht.1, hcard.trans natCard_centralizer_rep_five⟩) (by decide)
  · exact absurd (hcard.symm.trans ht.2) h3

theorem babyTableIV_of_ne_rep_three
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0) :
    BabyTableIV :=
  babyTableIV_of_labels babyToShat clabelS labelSphere (babyRep 0) (babyRep 5)
    babyInv_one_babyRep_zero babyInv_three_babyRep_five
    (babyInv_zero_iff_clabelS fun _ => isConj_babyRep_one_of_babyInv_zero h3) clabelS_injective
    labelSphere_cover (fun _ _ _ _ hu hu' => labelSphere_trans hu hu') labelSphere_ncard
    (fun _ _ hu => by
      rw [babyToShat_babyRep_zero]
      exact isConj_clabelS_mul_of_mem_zero hu)
    (fun _ _ hu => by
      rw [babyToShat_babyRep]
      exact isConj_clabelS_mul_of_mem_one hu)
    (fun _ _ hu => orderOf_clabelS_mul_of_mem_two hu)
    (fun _ _ hu => ⟨orderOf_clabelS_mul_of_mem_three hu, by
      rw [babyToShat_babyRep_zero]
      exact isConj_sq_clabelS_mul_of_mem_three hu⟩)

theorem natCard_centralizer_rep_three_ne_of_babyTableIII
    (hT3 : BabyTableIII) :
    Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0 := by
  intro h
  have hc : IsConj (babyRep 3) (babyRep 1) :=
    hT3.2 0 _ _ ⟨orderOf_babyRep (by norm_num), h⟩ babyInv_zero_babyRep_one
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, b1, -, -, b3⟩ := CTIB.native_four_involution_classes
  have hr : ((CTIB.iotaEquiv.symm (CTIB.rs 3)).val.val - 1).rank =
      ((CTIB.iotaEquiv.symm (CTIB.rs 1)).val.val - 1).rank := rank_sub_one_of_isConj hc
  rw [b1, b3] at hr
  exact absurd hr (by norm_num)

theorem babyTableIV_of
    (hT3 : BabyTableIII) : BabyTableIV :=
  babyTableIV_of_ne_rep_three (natCard_centralizer_rep_three_ne_of_babyTableIII hT3)

theorem babyTableIV_of_rep_three
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) = babyCentOrder 2) :
    BabyTableIV :=
  babyTableIV_of_ne_rep_three (by rw [h3]; decide)

end CFSG.Monster.Existence
