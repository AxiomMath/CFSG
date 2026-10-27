module

public import CFSG.Sporadic.Co2Smith.Generators

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Certificates.ExtraspecialNF
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] def bitVec (v : ℕ) : Fin 8 → ZMod 2 := fun i => if v.testBit i then 1 else 0

theorem exists_bitVec (u : Fin 8 → ZMod 2) : ∃ v < 256, u = bitVec v := by
  revert u
  decide +kernel

theorem rowsMatrix_ite_mulRows (b : Bool) (X Y : Array ℕ) :
    rowsMatrix 22 (if b = true then mulRows 22 X Y else Y) =
      (if b = true then rowsMatrix 22 X else 1) * rowsMatrix 22 Y := by
  split_ifs <;> simp [rowsMatrix_mulRows]

theorem hE_pow_bitVec (v : ℕ) (i : Fin 8) :
    (hE i ^ (bitVec v i).val).val.val =
      if v.testBit i = true then rowsMatrix 22 hR[(i : ℕ)]! else 1 := by
  rw [bitVec]
  split_ifs
  · rw [ZMod.val_one, pow_one, hE_val]
  · rw [ZMod.val_zero, pow_zero]
    rfl

theorem mon_val (v : ℕ) :
    (mon hE (bitVec v)).val.val = rowsMatrix 22 ((List.range 8).foldr
      (fun i acc => if v.testBit i = true then mulRows 22 hR[i]! acc else acc) (idRows 22)) := by
  simp only [mon, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, val_val_mul,
    mul_one]
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldr_cons, List.foldr_nil, rowsMatrix_ite_mulRows, rowsMatrix_idRows, mul_one]
  rw [hE_pow_bitVec, hE_pow_bitVec, hE_pow_bitVec, hE_pow_bitVec, hE_pow_bitVec, hE_pow_bitVec,
    hE_pow_bitVec, hE_pow_bitVec]
  rfl

theorem pow_val_z0 (σ : ZMod 2) :
    (z0 ^ σ.val).val.val = if σ.val = 1 then rowsMatrix 22 co2RowsA else 1 := by
  rcases zmod_two_cases σ with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, zero_ne_one, ite_false]
    rfl
  · simp only [ZMod.val_one, pow_one, ite_true, z0_val]

theorem nf_val (σ : ZMod 2) (v : ℕ) :
    (nf z0 hE σ (bitVec v)).val.val = rowsMatrix 22 (Native.nfRows seedRowsArr hR σ.val v) := by
  rw [nf, val_val_mul, mon_val, pow_val_z0, Native.nfRows]
  rcases zmod_two_cases σ with rfl | rfl
  · simp only [ZMod.val_zero, zero_ne_one, ite_false, one_mul]
    rfl
  · simp only [ZMod.val_one, beq_self_eq_true, ite_true, rowsMatrix_mulRows]
    rfl

theorem colAct_lt (R : Array ℕ) (v : ℕ) : Native.colAct R v < 2 ^ 22 := by
  rw [Native.colAct, vecMulN]
  have key : ∀ (L : List ℕ) (acc : ℕ), acc < 2 ^ 22 →
      L.foldl (fun acc j => if v.testBit j then acc ^^^ ((transposeRows 22 R)[j]?.getD 0) else acc)
        acc < 2 ^ 22 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons j L ih =>
      intro acc h
      apply ih
      dsimp only
      split_ifs
      · refine Nat.xor_lt_two_pow h ?_
        cases hj : (transposeRows 22 R)[j]? with
        | none => simp
        | some x =>
          rw [Option.getD_some]
          rw [transposeRows, Array.getElem?_ofFn] at hj
          split_ifs at hj with hlt
          · simp only [Option.some.injEq] at hj
            rw [← hj]
            exact ofBits_lt 22 _
      · exact h
  exact key _ 0 (by norm_num)

theorem nf_moves
    (σ : ZMod 2) {u : Fin 8 → ZMod 2} (hu : u ≠ 0) :
    (nf z0 hE σ u).val.val *ᵥ vec Native.wFix ≠ vec Native.wFix := by
  obtain ⟨v, hv, rfl⟩ := exists_bitVec u
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hu (funext fun i => by simp [bitVec])
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
  rw [nf_val, rowsMatrix_mulVec_vec]
  intro h
  have := vec_injective (colAct_lt _ _) (by rw [Native.wFix]; norm_num) h
  exact elements_spec.2.2.2.2.2.2.2.2 σ.val (ZMod.val_lt σ) w (by omega) this

theorem z0_ne_one : z0 ≠ 1 := by
  intro h
  have h1 := ncard_conjClass_z0
  have : MulAction.orbit (ConjAct K) z0 = {z0} := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      show k • z0 = z0
      rw [ConjAct.smul_def, h, mul_one, mul_inv_cancel]
    · rintro rfl
      exact MulAction.mem_orbit_self z0
  rw [this, Set.ncard_singleton] at h1
  exact absurd h1 (by norm_num)

theorem nf_eq_one
    {σ : ZMod 2} {u : Fin 8 → ZMod 2} (h : nf z0 hE σ u = 1) : σ = 0 ∧ u = 0 := by
  by_cases hu : u = 0
  · subst hu
    refine ⟨?_, rfl⟩
    rw [nf_zero_vec] at h
    rcases zmod_two_cases σ with rfl | rfl
    · rfl
    · exact absurd (by simpa only [ZMod.val_one, pow_one] using h) z0_ne_one
  · exact absurd (by rw [h, val_val_one, Matrix.one_mulVec]) (nf_moves σ hu)

theorem nf_injective :
    Function.Injective (Function.uncurry (nf z0 hE)) := by
  rintro ⟨s, v⟩ ⟨t, w⟩ h
  simp only [Function.uncurry_apply_pair] at h
  set c := collect hypMat w w
  have h2 : nf z0 hE s v * nf z0 hE (t + c) w = 1 := by
    rw [h, nf_mul_nf hE_rel]
    have hw : w + w = 0 := funext fun i => CharTwo.add_self_eq_zero (w i)
    have ht : t + (t + c) + c = 0 := by
      linear_combination CharTwo.add_self_eq_zero t + CharTwo.add_self_eq_zero c
    rw [hw, ht, nf_zero_zero]
  rw [nf_mul_nf hE_rel] at h2
  obtain ⟨h3, h4⟩ := nf_eq_one h2
  have hvw : v = w := by
    funext i
    have h5 := congrFun h4 i
    simp only [Pi.add_apply, Pi.zero_apply] at h5
    linear_combination h5 - CharTwo.add_self_eq_zero (w i)
  subst hvw
  refine Prod.ext ?_ rfl
  show s = t
  linear_combination h3 - CharTwo.add_self_eq_zero (collect hypMat v v) -
    CharTwo.add_self_eq_zero t

abbrev Qsub :
    Subgroup K := Subgroup.closure (insert z0 (Set.range hE))

theorem natCard_Q :
    Nat.card Qsub = 2 ^ 9 := card_closure hE_rel nf_injective

end CFSG.Sporadic.Co2Smith
