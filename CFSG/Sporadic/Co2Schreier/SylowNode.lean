module

public import CFSG.Sporadic.Co2Schreier.Sylow
public import CFSG.Sporadic.Co2Schreier.Cores

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier

theorem mem_zpowers_of_sq_eq_one {G : Type*} [Group G] {z y : G} (hz : z ^ 2 = 1) :
    y ∈ Subgroup.zpowers z ↔ y = 1 ∨ y = z := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hk : z ^ k = z ^ (k % 2) := by
      have := zpow_eq_zpow_emod' k hz
      rwa [Nat.cast_ofNat] at this
    rw [hk]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_centerIn_S_iff
    (x : Equiv.Perm (Fin 2300)) :
    x ∈ CFSG.centerIn locS ↔ x = 1 ∨ x = locZ := by
  constructor
  · intro hx
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxQ : x ∈ CFSG.centerIn locQ := by
      rw [← locC_inf_centralizer_Q]
      refine Subgroup.mem_inf.2 ⟨locS_le_C hxS, ?_⟩
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 locQ_le_S) hxc
    obtain ⟨k, hk, rfl⟩ := enumQ_facts.exists_elt repTuple_q (Subgroup.mem_inf.1 hxQ).1
    have hkc := (enumQ_facts.mem_centerIn_iff repTuple_q hk).1 hxQ
    rw [(coreOK_spec coreQ_check.1).2.2] at hkc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkc
    rcases hkc with rfl | rfl
    · exact Or.inl enumQ_facts.elt_zero
    · exact Or.inr eltE_Q_z
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · refine (mem_center_closure_iff locZ_mem_S).2 fun g hg => ?_
      obtain ⟨j, hj, hgj⟩ := (mem_iff_exists_getD (d := 1)).1 hg
      rw [sTuple_length] at hj
      rw [← hgj]
      exact (commA_iff rep_z (sTuple_getD hj)).1 (fratFacts.commZ j hj)

theorem center_locS :
    (Subgroup.center locS).map locS.subtype = Subgroup.zpowers locZ := by
  rw [← CFSG.centerIn_eq_map_center]
  ext x
  rw [mem_centerIn_S_iff, mem_zpowers_of_sq_eq_one locZ_sq]

theorem mem_center_locS_iff
    (y : locS) :
    y ∈ Subgroup.center locS ↔ (y : Equiv.Perm (Fin 2300)) = 1 ∨
      (y : Equiv.Perm (Fin 2300)) = locZ := by
  rw [← mem_centerIn_S_iff, CFSG.centerIn_eq_map_center]
  exact (Subgroup.mem_map_iff_mem locS.subtype_injective).symm

theorem mem_cosetY_iff
    (w : ℕ) (x : locS) :
    (x : locS ⧸ frattini locS) = cosetY w ↔
      (yPerm w)⁻¹ * (x : Equiv.Perm (Fin 2300)) ∈ locF := by
  rw [cosetY, eq_comm, QuotientGroup.eq, frattini_locS, Subgroup.mem_subgroupOf]
  rfl

theorem card_coset_eq
    (w : ℕ) (P : Equiv.Perm (Fin 2300) → Prop) :
    Nat.card {x : locS // (x : locS ⧸ frattini locS) = cosetY w ∧ P x} =
      Nat.card {f : locF // P (yPerm w * f)} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨(yPerm w)⁻¹ * x.1, (mem_cosetY_iff w x.1).1 x.2.1⟩, by
        simpa only [mul_inv_cancel_left] using x.2.2⟩
      invFun := fun f => ⟨⟨yPerm w * f.1, locS.mul_mem (yPerm_mem w) (locF_le_S f.1.2)⟩, by
        refine ⟨(mem_cosetY_iff w _).2 ?_, f.2⟩
        simpa only [inv_mul_cancel_left] using f.1.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [mul_inv_cancel_left]
      right_inv := fun f => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [inv_mul_cancel_left] }

theorem card_F_of_key
    {key : Array ℕ → ℕ} {P : Equiv.Perm (Fin 2300) → Prop} {c : ℕ}
    (hp : ∀ t g, Rep 2300 t g → (key t = c ↔ P g)) :
    Nat.card {f : locF // P f} = (keys2 fratLevels key).count c := by
  rw [← count2_eq_count_keys2, ← fratChain_original]
  exact chain_card_of_count2 fratChain_arrays (by norm_num) fratFacts.chain rfl
    fun t g ht => by rw [beq_iff_eq]; exact hp t g ht

theorem profile_facts {w : ℕ} (hw : w < 32) {e : ℕ} (he : e < 6) :
    ((keys2 fratLevels fun t => profKey zArr (compA 2300 (yArr w) t)).map (· / 8)).count e =
        (profTable.getD w []).getD (6 + e) 0 ∧
      ((keys2 fratLevels fun t => profKey zArr (compA 2300 (yArr w) t)).map (· % 8)).count e =
        (profTable.getD w []).getD e 0 := by
  have h := allLt_spec (allLt_spec profile_check hw) he
  simpa only [Bool.and_eq_true, beq_iff_eq] using h

theorem card_coset_orderOf
    {w : ℕ} (hw : w < 32) {e : ℕ} (he : e < 6) :
    Nat.card {x : locS // (x : locS ⧸ frattini locS) = cosetY w ∧ orderOf x = 2 ^ e} =
      (profTable.getD w []).getD (6 + e) 0 := by
  have h1 := card_coset_eq w (fun g => orderOf g = 2 ^ e)
  simp only [Subgroup.orderOf_coe] at h1
  rw [h1, ← (profile_facts hw he).1, keys2_map]
  refine card_F_of_key (P := fun g => orderOf (yPerm w * g) = 2 ^ e) fun t g ht => ?_
  rw [profKey_div]
  exact ordCode_eq_iff (rep_compA (rep_yArr w) ht) he

@[expose] def FirstZ (e : ℕ) (h : Equiv.Perm (Fin 2300)) : Prop :=
  (h ^ 2 ^ e = 1 ∨ h ^ 2 ^ e = locZ) ∧ ∀ i < e, ¬ (h ^ 2 ^ i = 1 ∨ h ^ 2 ^ i = locZ)

theorem orderOf_quot_center_iff
    (x : locS) (e : ℕ) :
    orderOf (x : locS ⧸ Subgroup.center locS) = 2 ^ e ↔ FirstZ e x := by
  have key : ∀ n : ℕ, (x : locS ⧸ Subgroup.center locS) ^ n = 1 ↔
      ((x : Equiv.Perm (Fin 2300)) ^ n = 1 ∨ (x : Equiv.Perm (Fin 2300)) ^ n = locZ) := by
    intro n
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_locS_iff,
      Subgroup.coe_pow]
  rw [orderOf_eq_two_pow_iff, FirstZ, key]
  exact and_congr_right fun _ => forall₂_congr fun i _ => by rw [key]

theorem card_coset_orderOf_quot
    {w : ℕ} (hw : w < 32) {e : ℕ} (he : e < 6) :
    Nat.card {x : locS // (x : locS ⧸ frattini locS) = cosetY w ∧
        orderOf (x : locS ⧸ Subgroup.center locS) = 2 ^ e} =
      (profTable.getD w []).getD e 0 := by
  have h0 : Nat.card {x : locS // (x : locS ⧸ frattini locS) = cosetY w ∧
      orderOf (x : locS ⧸ Subgroup.center locS) = 2 ^ e} =
      Nat.card {x : locS // (x : locS ⧸ frattini locS) = cosetY w ∧ FirstZ e x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [orderOf_quot_center_iff])
  rw [h0, card_coset_eq w (FirstZ e), ← (profile_facts hw he).2, keys2_map]
  refine card_F_of_key (P := fun g => FirstZ e (yPerm w * g)) fun t g ht => ?_
  rw [profKey_mod, ordZCode]
  refine firstIdx_sqChain_eq_iff (P := fun g => g = 1 ∨ g = locZ) (fun t g ht => ?_)
    (rep_compA (rep_yArr w) ht) he
  rw [Bool.or_eq_true, eqA_iff ht rep_idA, eqA_iff ht rep_z]

end CFSG.Sporadic.Co2Schreier
