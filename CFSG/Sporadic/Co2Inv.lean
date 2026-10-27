module

public import CFSG.Sporadic.Co2InvCheck
public import CFSG.Sporadic.Co2Cert.Order

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Inv

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  Matrix
open scoped Matrix Pointwise

@[expose] def Co2InvolutionInput : Prop :=
  ∃ z t u : NativeSporadic.Co2, z * z = 1 ∧ z ≠ 1 ∧ t * t = 1 ∧ t ≠ 1 ∧ u * u = 1 ∧ u ≠ 1 ∧
    (z.val.val - 1).rank = 6 ∧ (t.val.val - 1).rank = 8 ∧ (u.val.val - 1).rank = 10 ∧
    ∀ P : NativeSporadic.Co2, P * P = 1 → P ≠ 1 → IsConj P z ∨ IsConj P t ∨ IsConj P u

theorem isConj_of_odd_pow {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    {m : ℕ} (hm : Odd m) (hc : (x * y) ^ m = 1) : IsConj x y := by
  obtain ⟨k, rfl⟩ := hm
  rw [isConj_iff]
  set r := x * y with hr_def
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hr : x * r * x⁻¹ = r⁻¹ := by
    rw [hr_def, _root_.mul_inv_rev, hxi, hyi, ← mul_assoc, hx, one_mul]
  set A := r ^ k with hA_def
  have hA : x * A * x⁻¹ = A⁻¹ := by
    rw [hA_def, ← conj_pow, hr, inv_pow]
  have h1 : x * A⁻¹ * x⁻¹ = A := by
    calc x * A⁻¹ * x⁻¹ = (x * A * x⁻¹)⁻¹ := by group
      _ = A := by rw [hA, inv_inv]
  have hA' : x * A⁻¹ = A * x := by
    calc x * A⁻¹ = x * A⁻¹ * x⁻¹ * x := by group
      _ = A * x := by rw [h1]
  have hr2 : r ^ (2 * k) = r⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hc]
  refine ⟨A, ?_⟩
  calc A * x * A⁻¹ = A * (x * A⁻¹) := by group
    _ = A * (A * x) := by rw [hA']
    _ = r ^ (2 * k) * x := by rw [hA_def, ← mul_assoc, ← pow_add, two_mul]
    _ = r⁻¹ * x := by rw [hr2]
    _ = y := by rw [hr_def, _root_.mul_inv_rev, hxi, hyi, mul_assoc, hx, mul_one]

theorem val_val_mul (u v : NativeSporadic.Co2) : (u * v).val.val = u.val.val * v.val.val := rfl

theorem val_val_one : (1 : NativeSporadic.Co2).val.val = 1 := rfl

theorem val_val_pow (u : NativeSporadic.Co2) (e : ℕ) : (u ^ e).val.val = u.val.val ^ e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [pow_succ, val_val_mul, ih, pow_succ]

theorem eq_of_val_val {u v : NativeSporadic.Co2} (h : u.val.val = v.val.val) : u = v :=
  Units.ext (Subtype.ext h)

theorem val_val_inv {u : NativeSporadic.Co2} {N : Matrix (Fin 22) (Fin 22) (ZMod 2)}
    (h : u.val.val * N = 1) : (u⁻¹).val.val = N := by
  have h1 : (u⁻¹).val.val * u.val.val = 1 := by rw [← val_val_mul, inv_mul_cancel]; rfl
  calc (u⁻¹).val.val = (u⁻¹).val.val * (u.val.val * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

instance finite_Co2 :
    Finite NativeSporadic.Co2 :=
  Nat.finite_of_card_ne_zero (by rw [natCard_Co2]; norm_num)

theorem getElem!_eq_getD_zero (A : Array ℕ) (i : ℕ) : A[i]! = A[i]?.getD 0 := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rfl

theorem wfRows_spec {A : Array ℕ} (h : wfRows A = true) :
    A.size = 22 ∧ ∀ i < 22, A[i]! < 2 ^ 22 := by
  simp only [wfRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have hi' : i < A.size := h.1 ▸ hi
  rw [getElem!_pos A i hi']
  exact h.2 i hi'

theorem eq_of_rowsMatrix_eq {A B : Array ℕ} (hA : wfRows A = true) (hB : wfRows B = true)
    (h : rowsMatrix 22 A = rowsMatrix 22 B) : A = B := by
  obtain ⟨hAs, hAl⟩ := wfRows_spec hA
  obtain ⟨hBs, hBl⟩ := wfRows_spec hB
  apply Array.ext (hAs.trans hBs.symm)
  intro i hiA hiB
  have hi : i < 22 := hAs ▸ hiA
  have hrow : toVecD 22 A[i]! = toVecD 22 B[i]! := by
    funext j
    have := congrFun (congrFun h ⟨i, hi⟩) j
    rwa [rowsMatrix_apply, rowsMatrix_apply, ← getElem!_eq_getD_zero,
      ← getElem!_eq_getD_zero] at this
  have he := toVecD_injective (hAl i hi) (hBl i hi) hrow
  rwa [getElem!_pos A i hiA, getElem!_pos B i hiB] at he

theorem foldl_xor_lt (R : Array ℕ) (v : ℕ) (hR : ∀ j < 22, R[j]?.getD 0 < 2 ^ 22) :
    ∀ (l : List ℕ), (∀ j ∈ l, j < 22) → ∀ acc < 2 ^ 22,
      l.foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) acc < 2 ^ 22
  | [], _, acc, hacc => hacc
  | j :: l, hl, acc, hacc => by
    rw [List.foldl_cons]
    refine foldl_xor_lt R v hR l (fun j' h' => hl j' (List.mem_cons_of_mem _ h')) _ ?_
    split_ifs
    · exact Nat.xor_lt_two_pow hacc (hR j (hl j List.mem_cons_self))
    · exact hacc

theorem vecMulN_lt {R : Array ℕ} (hR : wfRows R = true) (v : ℕ) : vecMulN 22 R v < 2 ^ 22 := by
  obtain ⟨hs, hl⟩ := wfRows_spec hR
  refine foldl_xor_lt R v (fun j hj => ?_) (List.range 22) (fun j hj => List.mem_range.1 hj) 0
    (by norm_num)
  rw [← getElem!_eq_getD_zero]
  exact hl j hj

theorem wfRows_mulRows {X Y : Array ℕ} (hX : wfRows X = true) (hY : wfRows Y = true) :
    wfRows (mulRows 22 X Y) = true := by
  have hXs := (wfRows_spec hX).1
  unfold wfRows
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by simp [mulRows, hXs], fun i hi => ?_⟩
  simp only [mulRows, Array.getElem_map, decide_eq_true_eq]
  exact vecMulN_lt hY _

theorem wfRows_idRows : wfRows (idRows 22) = true := by
  unfold wfRows
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by simp [idRows], fun i hi => ?_⟩
  simp only [idRows, Array.getElem_ofFn, decide_eq_true_eq]
  rw [Nat.one_shiftLeft]
  have hi' : i < 22 := by simpa [idRows] using hi
  exact Nat.pow_lt_pow_right (by norm_num) hi'

theorem firstIdPow_spec (Q : Array ℕ) : ∀ (fuel : ℕ) (P : Array ℕ) (e e' : ℕ),
    P = powRows 22 Q e → firstIdPow Q fuel P e = some e' → powRows 22 Q e' = idRows 22
  | 0, _, _, _, _, h => by simp [firstIdPow] at h
  | fuel + 1, P, e, e', hP, h => by
    rw [firstIdPow] at h
    split_ifs at h with hid
    · cases h
      rw [← hP]
      exact beq_iff_eq.1 hid
    · exact firstIdPow_spec Q fuel _ (e + 1) e' (by rw [hP]; rfl) h

theorem oddPowOK_spec {Q : Array ℕ} (h : oddPowOK Q = true) :
    ∃ e, Odd e ∧ powRows 22 Q e = idRows 22 := by
  unfold oddPowOK at h
  split at h
  · rename_i e he
    exact ⟨e, Nat.odd_iff.2 (by simpa using h), firstIdPow_spec Q 64 _ 1 e rfl he⟩
  · cases h

theorem matrix_eq_of_vecs
    {M N : Matrix (Fin 22) (Fin 22) (ZMod 2)}
    (h : ∀ i : Fin 2300, M *ᵥ co2Vec i = N *ᵥ co2Vec i) : M = N := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on co2X_span
  rintro _ ⟨i, hi, rfl⟩
  simpa [Matrix.toLin'_apply] using h ⟨i, hi⟩

abbrev genPerm (j : ℕ) : Array ℕ := genPermWith co2PosTable j

structure GenFacts (j : ℕ) : Prop where
  wf : wfRows co2InvGens[j]! = true
  size : (genPerm j).size = 2300
  inv : isInvA 2300 (genPerm j) (invCand 2300 (genPerm j)) = true
  img : ∀ i < 2300, co2PackedVecs[(genPerm j)[i]!]! =
    vecMulN 22 (transposeRows 22 co2InvGens[j]!) co2PackedVecs[i]!
  sift : siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 (genPerm j) = true

theorem genFacts {j : ℕ} (hj : j < 5) : GenFacts j := by
  have h := gens_check
  simp only [gensCheck, Bool.and_eq_true, beq_iff_eq] at h
  have hj' := allLt_spec h.2 hj
  simp only [genCheckOne, Bool.and_eq_true, beq_iff_eq] at hj'
  obtain ⟨⟨⟨⟨hwf, hsz⟩, hinv⟩, himg⟩, hsift⟩ := hj'
  exact ⟨hwf, hsz, hinv, fun i hi => by simpa using allLt_spec himg hi, hsift⟩

theorem rep_genPerm
    {j : ℕ} (hj : j < 5) : Rep 2300 (genPerm j) (permOfArr 2300 (genPerm j)) :=
  (rep_permOfArr (genFacts hj).inv).1

theorem genPerm_mem
    {j : ℕ} (hj : j < 5) : permOfArr 2300 (genPerm j) ∈ co2P := by
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
    (rep_genPerm hj)).1 (genFacts hj).sift

@[expose] noncomputable def genCo2
    (j : ℕ) : NativeSporadic.Co2 :=
  if h : j < 5 then co2PermEquiv.symm ⟨permOfArr 2300 (genPerm j), genPerm_mem h⟩ else 1

theorem genCo2_val
    {j : ℕ} (hj : j < 5) :
    (genCo2 j).val.val = rowsMatrix 22 co2InvGens[j]! := by
  apply matrix_eq_of_vecs
  intro i
  have hp := co2Vec_permEquiv (genCo2 j) i
  have he : (co2PermEquiv (genCo2 j) : Equiv.Perm (Fin 2300)) =
      permOfArr 2300 (genPerm j) := by
    rw [genCo2, dite_eq_left hj, MulEquiv.apply_symm_apply]
  rw [he] at hp
  rw [← hp, co2Vec_eq i.2, rowsMatrix_mulVec, ← (genFacts hj).img i i.2,
    rep_genPerm hj i, ← co2Vec_eq (permOfArr 2300 (genPerm j) i).2]

@[expose] noncomputable def sylowS :
    Subgroup NativeSporadic.Co2 :=
  Subgroup.closure (Set.range fun j : Fin 5 => genCo2 j)

theorem genCo2_mem
    (j : ℕ) : genCo2 j ∈ sylowS := by
  by_cases hj : j < 5
  · exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩
  · rw [genCo2, dite_eq_right hj]
    exact one_mem _

abbrev sPar (k : ℕ) : ℕ := enumS.par[k]!

abbrev sLab (k : ℕ) : ℕ := enumS.lab[k]!

abbrev sElem (k : ℕ) : Array ℕ := enumS.elems[k]!

abbrev sTbl (k j : ℕ) : ℕ := (enumS.tbl[k]!)[j]!

abbrev sPos (A : Array ℕ) : ℕ := enumS.pos.getD A 0

structure EnumFacts : Prop where
  zero : sElem 0 = idRows 22
  wf : ∀ k < sOrder, wfRows (sElem k) = true
  step : ∀ k < sOrder, k ≠ 0 →
    sPar k < k ∧ sLab k < 5 ∧ sElem k = mulRows 22 (sElem (sPar k)) co2InvGens[sLab k]!
  tbl : ∀ k < sOrder, ∀ j < 5,
    sTbl k j < sOrder ∧ sElem (sTbl k j) = mulRows 22 (sElem k) co2InvGens[j]!
  pos : ∀ k < sOrder, sPos (sElem k) = k
  fuse : ∀ k < sOrder, isInvolRows (sElem k) = true → fuseOK candYs (sElem k) = true
  reps : ∀ r < 3, sPos co2InvReps[r]! < sOrder ∧ sElem (sPos co2InvReps[r]!) = co2InvReps[r]!

theorem enumFacts : EnumFacts := by
  have h := enum_check
  simp only [enumCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h2, fun k hk => allLt_spec h3 hk, fun k hk hk0 => ?_, fun k hk j hj => ?_,
    fun k hk => ?_, fun k hk hinv => ?_, fun r hr => ?_⟩
  · have := allLt_spec h4 hk
    simp only [Bool.or_eq_true, beq_iff_eq, hk0, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allLt_spec (allLt_spec h5 hk) hj
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  · simpa only [beq_iff_eq] using allLt_spec h6 hk
  · have := allLt_spec h7 hk
    simpa [hinv] using this
  · have := allLt_spec h8 hr
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

@[expose] noncomputable def eltS :
    ℕ → NativeSporadic.Co2
  | 0 => 1
  | k + 1 => if _h : sPar (k + 1) < k + 1 then eltS (sPar (k + 1)) * genCo2 (sLab (k + 1))
      else 1
termination_by k => k
decreasing_by assumption

theorem eltS_zero :
    eltS 0 = 1 := by
  rw [eltS]

theorem eltS_step
    {k : ℕ} (hp : sPar (k + 1) < k + 1) :
    eltS (k + 1) = eltS (sPar (k + 1)) * genCo2 (sLab (k + 1)) := by
  rw [eltS, dite_eq_left hp]

theorem eltS_mem
    (k : ℕ) : eltS k ∈ sylowS := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [eltS_zero]
      exact one_mem _
    · by_cases h' : sPar (k + 1) < k + 1
      · rw [eltS_step h']
        exact mul_mem (ih _ h') (genCo2_mem _)
      · rw [eltS, dite_eq_right h']
        exact one_mem _

theorem eltS_val :
    ∀ k < sOrder, (eltS k).val.val = rowsMatrix 22 (sElem k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · rw [eltS_zero, enumFacts.zero, rowsMatrix_idRows]
      rfl
    · obtain ⟨hp, hl, he⟩ := enumFacts.step (k + 1) hk (Nat.succ_ne_zero k)
      rw [eltS_step hp, val_val_mul, ih _ hp (hp.trans hk), genCo2_val hl, he,
        rowsMatrix_mulRows]

theorem exists_eltS_of_mem
    {x : NativeSporadic.Co2} (hx : x ∈ sylowS) :
    ∃ k < sOrder, eltS k = x := by
  have hx' : x ∈ sylowS.toSubmonoid := hx
  rw [sylowS, Subgroup.closure_toSubmonoid_of_finite] at hx'
  clear hx
  induction hx' using Submonoid.closure_induction_right with
  | one => exact ⟨0, by norm_num [sOrder], eltS_zero⟩
  | mul_right x _ y hy ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨ht, hte⟩ := enumFacts.tbl k hk j j.2
    refine ⟨sTbl k j, ht, eq_of_val_val ?_⟩
    rw [eltS_val _ ht, val_val_mul, eltS_val _ hk, genCo2_val j.2, hte, rowsMatrix_mulRows]

theorem eltS_injective
    {i j : ℕ} (hi : i < sOrder) (hj : j < sOrder) (h : eltS i = eltS j) :
    i = j := by
  have hm : (eltS i).val.val = (eltS j).val.val := by rw [h]
  rw [eltS_val i hi, eltS_val j hj] at hm
  have he := eq_of_rowsMatrix_eq (enumFacts.wf i hi) (enumFacts.wf j hj) hm
  rw [← enumFacts.pos i hi, ← enumFacts.pos j hj, he]

theorem card_sylowS :
    Nat.card sylowS = 262144 := by
  have hbij : Function.Bijective fun k : Fin sOrder => (⟨eltS k, eltS_mem k⟩ : sylowS) := by
    refine ⟨fun a b h => Fin.ext (eltS_injective a.2 b.2 (congrArg Subtype.val h)), fun x => ?_⟩
    obtain ⟨k, hk, hx⟩ := exists_eltS_of_mem x.2
    exact ⟨⟨k, hk⟩, Subtype.ext hx⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem isPGroup_sylowS :
    IsPGroup 2 sylowS :=
  IsPGroup.of_card (n := 18) (by rw [card_sylowS]; norm_num)

theorem index_sylowS :
    sylowS.index = 161382375 := by
  have h := sylowS.index_mul_card
  rw [card_sylowS, natCard_Co2] at h
  have h' : sylowS.index * 262144 = 161382375 * 262144 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

@[expose] noncomputable def sylowS' :
    Sylow 2 NativeSporadic.Co2 :=
  isPGroup_sylowS.toSylow (by rw [index_sylowS]; decide)

theorem coe_sylowS' :
    (sylowS' : Subgroup NativeSporadic.Co2) = sylowS := rfl

theorem exists_conj_mem_sylowS
    (x : NativeSporadic.Co2) (hx : IsPGroup 2 (Subgroup.zpowers x)) :
    ∃ g : NativeSporadic.Co2, g * x * g⁻¹ ∈ sylowS := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq NativeSporadic.Co2 Q sylowS'
  refine ⟨g, ?_⟩
  rw [← coe_sylowS', ← hg, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup NativeSporadic.Co2)
    (hQ (Subgroup.mem_zpowers x))

theorem isPGroup_zpowers_of_invol
    {x : NativeSporadic.Co2} (hx : x * x = 1) (hx1 : x ≠ 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have ho : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])

structure RepFacts (r : ℕ) : Prop where
  wf : wfRows co2InvReps[r]! = true
  sq : mulRows 22 co2InvReps[r]! co2InvReps[r]! = idRows 22
  ne : co2InvReps[r]! ≠ idRows 22
  hP : mulRows 22 co2InvRankP[r]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankP[r]!) = idRows 22
  hQ : mulRows 22 co2InvRankQ[r]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankQ[r]!) = idRows 22
  hD : mulRows 22 (mulRows 22 co2InvRankP[r]! (addId co2InvReps[r]!)) co2InvRankQ[r]! =
    truncId (6 + 2 * r)

theorem repFacts {r : ℕ} (hr : r < 3) : RepFacts r := by
  have h := rank_check
  simp only [rankCheck, Bool.and_eq_true, beq_iff_eq] at h
  have hr' := allLt_spec h.2 hr
  simp only [isInvolRows, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hr'
  obtain ⟨⟨⟨⟨hwf, hsq, hne⟩, hP⟩, hQ⟩, hD⟩ := hr'
  exact ⟨hwf, hsq, hne, hP, hQ, hD⟩

abbrev repIdx (r : ℕ) : ℕ := sPos co2InvReps[r]!

@[expose] noncomputable def repCo2
    (r : ℕ) : NativeSporadic.Co2 := eltS (repIdx r)

theorem repCo2_val
    {r : ℕ} (hr : r < 3) : (repCo2 r).val.val = rowsMatrix 22 co2InvReps[r]! := by
  rw [repCo2, eltS_val _ (enumFacts.reps r hr).1, (enumFacts.reps r hr).2]

theorem repCo2_sq
    {r : ℕ} (hr : r < 3) : repCo2 r * repCo2 r = 1 := by
  apply eq_of_val_val
  rw [val_val_mul, repCo2_val hr, ← rowsMatrix_mulRows, (repFacts hr).sq, rowsMatrix_idRows]
  rfl

theorem repCo2_ne_one
    {r : ℕ} (hr : r < 3) : repCo2 r ≠ 1 := by
  intro h
  have hm : rowsMatrix 22 co2InvReps[r]! = rowsMatrix 22 (idRows 22) := by
    rw [← repCo2_val hr, h, rowsMatrix_idRows]
    rfl
  exact (repFacts hr).ne (eq_of_rowsMatrix_eq (repFacts hr).wf wfRows_idRows hm)

theorem sub_one_eq_add_one (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) : M - 1 = M + 1 := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  generalize M i j = a
  generalize (1 : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j = b
  revert a b
  decide

theorem rowsMatrix_addId (X : Array ℕ) : rowsMatrix 22 (addId X) = rowsMatrix 22 X + 1 := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, ← rowsMatrix_idRows 22,
    rowsMatrix_apply]
  unfold addId idRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor, Pi.add_apply, getElem!_eq_getD_zero]

theorem rowsMatrix_truncId (r : ℕ) :
    rowsMatrix 22 (truncId r) =
      Matrix.diagonal fun i : Fin 22 => if (i : ℕ) < r then (1 : ZMod 2) else 0 := by
  ext i j
  rw [rowsMatrix_apply, Matrix.diagonal_apply]
  unfold truncId
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  by_cases hr : (i : ℕ) < r
  · rw [ite_eq_left hr, toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : i = j
    · subst h
      simp [hr]
    · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
      simp [h, h']
  · rw [ite_eq_right hr, toVecD_zero]
    by_cases h : i = j
    · subst h
      simp [hr]
    · simp [h]

theorem rank_rowsMatrix_cert {A P Q D : Matrix (Fin 22) (Fin 22) (ZMod 2)}
    {Pi Qi : Matrix (Fin 22) (Fin 22) (ZMod 2)} (hP : P * Pi = 1) (hQ : Q * Qi = 1)
    (hD : P * A * Q = D) : A.rank = D.rank := by
  rw [← hD, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hQ),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hP)]

theorem rank_repCo2
    {r : ℕ} (hr : r < 3) :
    ((repCo2 r).val.val - 1).rank =
      Fintype.card {i : Fin 22 // (if (i : ℕ) < 6 + 2 * r then (1 : ZMod 2) else 0) ≠ 0} := by
  have F := repFacts hr
  have hP := congrArg (rowsMatrix 22) F.hP
  have hQ := congrArg (rowsMatrix 22) F.hQ
  have hD := congrArg (rowsMatrix 22) F.hD
  rw [rowsMatrix_mulRows, rowsMatrix_idRows] at hP hQ
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_addId, rowsMatrix_truncId] at hD
  rw [repCo2_val hr, sub_one_eq_add_one, rank_rowsMatrix_cert hP hQ hD, Matrix.rank_diagonal]

theorem rank_repCo2_zero :
    ((repCo2 0).val.val - 1).rank = 6 := by
  rw [rank_repCo2 (by norm_num)]
  decide

theorem rank_repCo2_one :
    ((repCo2 1).val.val - 1).rank = 8 := by
  rw [rank_repCo2 (by norm_num)]
  decide

theorem rank_repCo2_two :
    ((repCo2 2).val.val - 1).rank = 10 := by
  rw [rank_repCo2 (by norm_num)]
  decide

@[expose] noncomputable def seedCo2 (l : ℕ) : NativeSporadic.Co2 :=
  if l = 0 then co2SeedA else co2SeedB

@[expose] noncomputable def seedWordCo2 : List ℕ → NativeSporadic.Co2
  | [] => 1
  | l :: w => seedCo2 l * seedWordCo2 w

theorem seedCo2_val
    (l : ℕ) : (seedCo2 l).val.val = rowsMatrix 22 (seedRows l) := by
  unfold seedCo2 seedRows
  split_ifs
  · rw [co2SeedA_val, rowsMatrix_co2RowsA]
  · rw [co2SeedB_val, rowsMatrix_co2RowsB]

theorem seedWordCo2_val : ∀ w : List ℕ,
    (seedWordCo2 w).val.val = rowsMatrix 22 (wordRowsSeed w)
  | [] => by
    rw [seedWordCo2, wordRowsSeed, rowsMatrix_idRows]
    rfl
  | l :: w => by
    rw [seedWordCo2, wordRowsSeed, val_val_mul, seedCo2_val, seedWordCo2_val w,
      rowsMatrix_mulRows]

structure CandFacts (c : ℕ) : Prop where
  rep : (co2InvCands[c]!).1 < 3
  inv : mulRows 22 (candW c) (CFSG.Monster.B.Max2.Native.inv22 (candW c)) = idRows 22

theorem candFacts {c : ℕ} (hc : c < 54) : CandFacts c := by
  have h := cand_check
  simp only [candCheck, Bool.and_eq_true, beq_iff_eq] at h
  have hc' := allLt_spec h.2 hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc'
  exact ⟨hc'.1, hc'.2⟩

@[expose] noncomputable def candCo2
    (c : ℕ) : NativeSporadic.Co2 :=
  seedWordCo2 (co2InvCands[c]!).2 * repCo2 (co2InvCands[c]!).1 *
    (seedWordCo2 (co2InvCands[c]!).2)⁻¹

theorem candCo2_val
    {c : ℕ} (hc : c < 54) : (candCo2 c).val.val = rowsMatrix 22 (candY c) := by
  have F := candFacts hc
  have hW : (seedWordCo2 (co2InvCands[c]!).2).val.val = rowsMatrix 22 (candW c) :=
    seedWordCo2_val _
  have hWi : ((seedWordCo2 (co2InvCands[c]!).2)⁻¹).val.val =
      rowsMatrix 22 (CFSG.Monster.B.Max2.Native.inv22 (candW c)) := by
    apply val_val_inv
    rw [hW, ← rowsMatrix_mulRows, F.inv, rowsMatrix_idRows]
  rw [candCo2, val_val_mul, val_val_mul, hW, hWi, repCo2_val F.rep, candY, rowsMatrix_mulRows,
    rowsMatrix_mulRows]

theorem candCo2_sq
    {c : ℕ} (hc : c < 54) : candCo2 c * candCo2 c = 1 := by
  have h := repCo2_sq (candFacts hc).rep
  rw [candCo2]
  calc _ = seedWordCo2 (co2InvCands[c]!).2 * (repCo2 (co2InvCands[c]!).1 *
        repCo2 (co2InvCands[c]!).1) * (seedWordCo2 (co2InvCands[c]!).2)⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem isConj_candCo2
    (c : ℕ) : IsConj (candCo2 c) (repCo2 (co2InvCands[c]!).1) :=
  (isConj_iff.2 ⟨seedWordCo2 (co2InvCands[c]!).2, rfl⟩).symm

theorem candYs_get {c : ℕ} (hc : c < 54) : candYs[c]! = candY c := by
  rw [candYs, getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem isInvolRows_of_invol
    {k : ℕ} (hk : k < sOrder) (h2 : eltS k * eltS k = 1)
    (h1 : eltS k ≠ 1) : isInvolRows (sElem k) = true := by
  have hwf := enumFacts.wf k hk
  have hsq : mulRows 22 (sElem k) (sElem k) = idRows 22 := by
    apply eq_of_rowsMatrix_eq (wfRows_mulRows hwf hwf) wfRows_idRows
    rw [rowsMatrix_mulRows, ← eltS_val k hk, ← val_val_mul, h2, rowsMatrix_idRows]
    rfl
  have hne : sElem k ≠ idRows 22 := by
    intro he
    apply h1
    apply eq_of_val_val
    rw [eltS_val k hk, he, rowsMatrix_idRows]
    rfl
  simp only [isInvolRows, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨hsq, hne⟩

theorem exists_rep_of_invol
    {k : ℕ} (hk : k < sOrder) (h2 : eltS k * eltS k = 1)
    (h1 : eltS k ≠ 1) : ∃ r < 3, IsConj (eltS k) (repCo2 r) := by
  have hf := enumFacts.fuse k hk (isInvolRows_of_invol hk h2 h1)
  unfold fuseOK at hf
  rw [List.any_eq_true] at hf
  obtain ⟨c, hc, hodd⟩ := hf
  have hsz : candYs.size = 54 := by rw [candYs, Array.size_ofFn]
  have hc' : c < 54 := by
    rw [List.mem_range, hsz] at hc
    exact hc
  rw [candYs_get hc'] at hodd
  obtain ⟨e, he, hpow⟩ := oddPowOK_spec hodd
  refine ⟨(co2InvCands[c]!).1, (candFacts hc').rep, ?_⟩
  have hpow' : (eltS k * candCo2 c) ^ e = 1 := by
    apply eq_of_val_val
    rw [val_val_pow, val_val_mul, eltS_val k hk, candCo2_val hc', ← rowsMatrix_mulRows,
      ← rowsMatrix_powRows, hpow, rowsMatrix_idRows]
    rfl
  have hsq : candCo2 c * candCo2 c = 1 := candCo2_sq hc'
  have hconj : IsConj (eltS k) (candCo2 c) := isConj_of_odd_pow h2 hsq he hpow'
  exact hconj.trans (isConj_candCo2 c)

theorem co2_involution_input :
    Co2InvolutionInput := by
  refine ⟨repCo2 0, repCo2 1, repCo2 2, repCo2_sq (by norm_num), repCo2_ne_one (by norm_num),
    repCo2_sq (by norm_num), repCo2_ne_one (by norm_num), repCo2_sq (by norm_num),
    repCo2_ne_one (by norm_num), rank_repCo2_zero, rank_repCo2_one, rank_repCo2_two, ?_⟩
  intro P hP hP1
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowS P (isPGroup_zpowers_of_invol hP hP1)
  obtain ⟨k, hk, hke⟩ := exists_eltS_of_mem hg
  have h2 : eltS k * eltS k = 1 := by
    rw [hke]
    calc g * P * g⁻¹ * (g * P * g⁻¹) = g * (P * P) * g⁻¹ := by group
      _ = 1 := by rw [hP, mul_one, mul_inv_cancel]
  have h1 : eltS k ≠ 1 := by
    rw [hke]
    intro h
    apply hP1
    calc P = g⁻¹ * (g * P * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  obtain ⟨r, hr, hconj⟩ := exists_rep_of_invol hk h2 h1
  have hPk : IsConj P (eltS k) := by
    rw [hke]
    exact isConj_iff.2 ⟨g, rfl⟩
  have hP' := hPk.trans hconj
  interval_cases r
  · exact Or.inl hP'
  · exact Or.inr (Or.inl hP')
  · exact Or.inr (Or.inr hP')

end CFSG.Sporadic.Co2Inv
