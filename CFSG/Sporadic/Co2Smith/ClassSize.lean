module

public import CFSG.Sporadic.Co2Smith.Elements
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.Co2Smith.Check

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

theorem validM_spec {X : Array ℕ} (h : Native.validM X = true) :
    X.size = 22 ∧ ∀ t < 22, X[t]! < 2 ^ 22 := by
  simp only [Native.validM, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true,
    decide_eq_true_eq] at h
  refine ⟨h.1, fun t ht => ?_⟩
  have ht' : t < X.size := h.1 ▸ ht
  rw [getElem!_pos X t ht']
  exact h.2 t ht'

theorem eq_of_rowsMatrix_eq {X Y : Array ℕ} (hX : Native.validM X = true)
    (hY : Native.validM Y = true) (h : rowsMatrix 22 X = rowsMatrix 22 Y) : X = Y := by
  obtain ⟨hXs, hXb⟩ := validM_spec hX
  obtain ⟨hYs, hYb⟩ := validM_spec hY
  refine Array.ext (hXs.trans hYs.symm) fun t htX htY => ?_
  have ht : t < 22 := hXs ▸ htX
  have hrow : toVecD 22 (X[t]?.getD 0) = toVecD 22 (Y[t]?.getD 0) := by
    funext j
    have := congrFun (congrFun h ⟨t, ht⟩) j
    rwa [rowsMatrix_apply, rowsMatrix_apply] at this
  rw [Array.getElem?_eq_getElem htX, Array.getElem?_eq_getElem htY, Option.getD_some,
    Option.getD_some] at hrow
  have h1 := hXb t ht
  have h2 := hYb t ht
  rw [getElem!_pos X t htX] at h1
  rw [getElem!_pos Y t htY] at h2
  exact toVecD_injective h1 h2 hrow

theorem seedA_mul_self : co2SeedA * co2SeedA = 1 :=
  eq_of_val_eq (by rw [val_val_mul, co2SeedA_val, co2A1_sq]; rfl)

theorem seedA_inv :
    co2SeedA⁻¹ = co2SeedA := inv_eq_of_mul_eq_one_right seedA_mul_self

theorem seedB_pow_five : co2SeedB ^ 5 = 1 := by
  apply eq_of_val_eq
  have : (co2SeedB ^ 5).val.val = co2SeedB.val.val ^ 5 := rfl
  rw [this, co2SeedB_val, co2A2_pow]
  rfl

theorem seedB_inv : co2SeedB⁻¹ = co2SeedB ^ 4 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', seedB_pow_five]

theorem seedRowsArr_zero : seedRowsArr[0]! = co2RowsA := rfl

theorem seedRowsArr_one : seedRowsArr[1]! = co2RowsB := rfl

theorem rowsMatrix_conjSeed_zero (X : Array ℕ) :
    rowsMatrix 22 (Native.conjSeed seedRowsArr 0 X) = co2A1 * rowsMatrix 22 X * co2A1 := by
  change rowsMatrix 22 (mulRows 22 (mulRows 22 seedRowsArr[0]! X) seedRowsArr[0]!) = _
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, seedRowsArr_zero, rowsMatrix_co2RowsA]

theorem rowsMatrix_conjSeed_one (X : Array ℕ) :
    rowsMatrix 22 (Native.conjSeed seedRowsArr 1 X) = co2A2 * rowsMatrix 22 X * co2A2 ^ 4 := by
  change rowsMatrix 22 (mulRows 22 (mulRows 22 seedRowsArr[1]! X) (powRows 22 seedRowsArr[1]! 4)) =
    _
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRows, seedRowsArr_one,
    rowsMatrix_co2RowsB]

theorem val_conj_seed
    {u : K} {X : Array ℕ} (hu : u.val.val = rowsMatrix 22 X) {l : ℕ}
    (hl : l < 2) :
    ((if l = 0 then co2SeedA else co2SeedB) * u * (if l = 0 then co2SeedA else co2SeedB)⁻¹).val.val
      = rowsMatrix 22 (Native.conjSeed seedRowsArr l X) := by
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · change (co2SeedA * u * co2SeedA⁻¹).val.val = _
    rw [seedA_inv, val_val_mul, val_val_mul, co2SeedA_val, hu, rowsMatrix_conjSeed_zero]
  · change (co2SeedB * u * co2SeedB⁻¹).val.val = _
    rw [seedB_inv, val_val_mul, val_val_mul, rowsMatrix_conjSeed_one, hu, ← co2SeedB_val]
    rfl

theorem co2_closure_seeds :
    Subgroup.closure ({co2SeedA, co2SeedB} : Set K) = ⊤ := by
  have hpre : ((↑) : co2J → GL (Fin 22) (ZMod 2)) ⁻¹' {co2GL1, co2GL2} =
      {⟨co2GL1, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
        ⟨co2GL2, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have htop := Subgroup.closure_closure_coe_preimage (k := ({co2GL1, co2GL2} :
    Set (GL (Fin 22) (ZMod 2))))
  rw [hpre] at htop
  have hmap := congrArg (Subgroup.map (co2MatEquiv.symm : co2J →* K)) htop
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ co2MatEquiv.symm.surjective,
    Set.image_insert_eq, Set.image_singleton] at hmap
  exact hmap

@[expose] def classRec : Array (Array ℕ) × Array ℕ × Array ℕ :=
  Native.classBFS seedRowsArr seedRowsArr[0]! 60000

@[expose] def classPos (X : Array ℕ) : ℕ :=
  (Native.posMap classRec.1).getD (Native.encM X) classRec.1.size

theorem classRec_spec :
    classRec.1[0]! = co2RowsA ∧
    ∀ i < 56925, Native.validM classRec.1[i]! = true ∧ classPos classRec.1[i]! = i ∧
      (i = 0 ∨ (classRec.2.1[i]! < i ∧ classRec.2.2[i]! < 2 ∧
        classRec.1[i]! =
          Native.conjSeed seedRowsArr classRec.2.2[i]! classRec.1[classRec.2.1[i]!]!))
      ∧ ∀ l < 2, classPos (Native.conjSeed seedRowsArr l classRec.1[i]!) < 56925 ∧
        classRec.1[classPos (Native.conjSeed seedRowsArr l classRec.1[i]!)]! =
          Native.conjSeed seedRowsArr l classRec.1[i]! := by
  have h := class_check
  simp only [Native.classOK, Native.classCertOK, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, h0, h⟩ := h
  exact ⟨h0, fun i hi => h i hi⟩

theorem exists_conj_of_lt :
    ∀ i < 56925, ∃ k : K, (k * z0 * k⁻¹).val.val = rowsMatrix 22 classRec.1[i]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨h0, h⟩ := classRec_spec
    obtain ⟨-, -, ht, -⟩ := h i hi
    rcases ht with rfl | ⟨hp, hl, heq⟩
    · exact ⟨1, by rw [one_mul, inv_one, mul_one, h0, z0_val]⟩
    · obtain ⟨k, hk⟩ := ih _ hp (hp.trans hi)
      refine ⟨(if classRec.2.2[i]! = 0 then co2SeedA else co2SeedB) * k, ?_⟩
      rw [heq, ← val_conj_seed hk hl, _root_.mul_inv_rev]
      simp only [mul_assoc]

@[expose] def classSet : Set K := {u | ∃ i < 56925, u.val.val = rowsMatrix 22 classRec.1[i]!}

theorem conj_seed_mem_classSet
    {u : K} (hu : u ∈ classSet) {l : ℕ} (hl : l < 2) :
    (if l = 0 then co2SeedA else co2SeedB) * u * (if l = 0 then co2SeedA else co2SeedB)⁻¹ ∈
      classSet := by
  obtain ⟨i, hi, hui⟩ := hu
  obtain ⟨-, -, -, hc⟩ := classRec_spec.2 i hi
  obtain ⟨hpos, heq⟩ := hc l hl
  exact ⟨_, hpos, by rw [val_conj_seed hui hl, heq]⟩

theorem conj_mem_classSet
    (k : K) {u : K} (hu : u ∈ classSet) : k * u * k⁻¹ ∈ classSet := by
  have hfin : classSet.Finite := Set.toFinite _
  have hk : k ∈ Subgroup.closure ({co2SeedA, co2SeedB} : Set K) := by
    rw [co2_closure_seeds]; exact Subgroup.mem_top k
  induction hk using Subgroup.closure_induction generalizing u with
  | mem x hx =>
    rcases hx with rfl | rfl
    · simpa using conj_seed_mem_classSet hu (l := 0) (by norm_num)
    · simpa using conj_seed_mem_classSet hu (l := 1) (by norm_num)
  | one => simpa using hu
  | mul x y _ _ hx hy =>
    have := hx (hy hu)
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have hmaps : Set.MapsTo (fun v => x * v * x⁻¹) classSet classSet := fun v hv => hx hv
    have hinj : Set.InjOn (fun v => x * v * x⁻¹) classSet := fun v _ w _ h => by
      simpa using h
    obtain ⟨v, hv, hvu⟩ := ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj).surjOn hu
    have : x⁻¹ * u * x⁻¹⁻¹ = v := by rw [← hvu]; group
    rw [this]; exact hv

@[expose] noncomputable def classElt
    (i : Fin 56925) : K :=
  (exists_conj_of_lt i i.2).choose * z0 * (exists_conj_of_lt i i.2).choose⁻¹

theorem classElt_val
    (i : Fin 56925) : (classElt i).val.val = rowsMatrix 22 classRec.1[(i : ℕ)]! :=
  (exists_conj_of_lt i i.2).choose_spec

theorem classElt_injective :
    Function.Injective classElt := by
  intro i j hij
  have hv := (classElt_val i).symm.trans ((congrArg (fun u : K => u.val.val) hij).trans
    (classElt_val j))
  have hi := classRec_spec.2 i i.2
  have hj := classRec_spec.2 j j.2
  have heq := eq_of_rowsMatrix_eq hi.1 hj.1 hv
  apply Fin.ext
  rw [← hi.2.1, ← hj.2.1, heq]

theorem classSet_eq_range :
    classSet = Set.range classElt := by
  ext u
  constructor
  · rintro ⟨i, hi, hu⟩
    exact ⟨⟨i, hi⟩, eq_of_val_eq ((classElt_val ⟨i, hi⟩).trans hu.symm)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, classElt_val i⟩

theorem z0_mem_classSet :
    z0 ∈ classSet :=
  ⟨0, by norm_num, by rw [classRec_spec.1, z0_val]⟩

theorem orbit_z0_eq :
    MulAction.orbit (ConjAct K) z0 = classSet := by
  ext u
  constructor
  · rintro ⟨k, rfl⟩
    show k • z0 ∈ classSet
    rw [ConjAct.smul_def]
    exact conj_mem_classSet _ z0_mem_classSet
  · intro hu
    rw [classSet_eq_range] at hu
    obtain ⟨i, rfl⟩ := hu
    refine ⟨ConjAct.toConjAct (exists_conj_of_lt i i.2).choose, ?_⟩
    show ConjAct.toConjAct (exists_conj_of_lt i i.2).choose • z0 = classElt i
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    rfl

theorem ncard_conjClass_z0 :
    (MulAction.orbit (ConjAct K) z0).ncard = 56925 := by
  rw [orbit_z0_eq, classSet_eq_range, Set.ncard_range_of_injective classElt_injective,
    Nat.card_fin]

theorem natCard_centralizer_z0 :
    Nat.card (Subgroup.centralizer ({z0} : Set K)) = 743178240 := by
  have h1 := Subgroup.nat_card_centralizer_nat_card_stabilizer z0
  have h2 := (MulAction.stabilizer (ConjAct K) z0).card_mul_index
  rw [MulAction.index_stabilizer, ncard_conjClass_z0] at h2
  have h3 : Nat.card (ConjAct K) = 42305421312000 := by
    rw [← CFSG.Sporadic.Co2.card_Co2]
    rfl
  rw [h3, show (42305421312000 : ℕ) = 743178240 * 56925 by norm_num] at h2
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

end CFSG.Sporadic.Co2Smith
