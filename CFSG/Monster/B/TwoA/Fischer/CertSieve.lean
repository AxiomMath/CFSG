module

public import CFSG.Monster.B.TwoA.Fischer.CertFixed
public meta import CFSG.Monster.B.TwoA.Fischer.CertFixed
public meta import Certificates.Data.CFSGNative.MonsterB.BinaryRank
public import CFSG.Monster.B.TwoA.Fischer.CertSieveInputs
public import Certificates.Certificate3067
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate16010
public import Certificates.Certificate16023

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary CFSG.Monster.B.Binary.Native
open scoped Matrix

theorem tableCheck_eq_true : tableCheck = true :=
  Certificates.certificate3067.1

theorem tableEntry_spec {i j : ℕ} (hi : i < 78) (hj : j < 78) :
    bTable i j = if (jLabelArr (labelWord i))[basisPt j]! = basisPt j then 0
      else labelCoord (basisPt i) ^^^ labelCoord (basisPt j) ^^^
        labelCoord (jLabelArr (labelWord i))[basisPt j]! := by
  have h := tableCheck_eq_true
  rw [tableCheck, Bool.and_eq_true] at h
  have hrow : tableRowOK i = true := List.all_eq_true.1 h.2 i (List.mem_range.2 hi)
  have hrow' : ((List.range 78).all fun j => tableEntryOK (jLabelArr (labelWord i)) i j) = true :=
    hrow
  exact beq_iff_eq.1 (List.all_eq_true.1 hrow' j (List.mem_range.2 hj))

theorem table_binding
    {i j : ℕ} (hi : i < 78) (hj : j < 78) (y : Y)
    (hy : (ι y : ℕ) = basisPt j) :
    (jLabel (labelWord i) y = y → toVecD 78 (bTable i j) = 0) ∧
    (jLabel (labelWord i) y ≠ y → toVecD 78 (bTable i j) =
      toVecD 78 (labelCoord (basisPt i)) + toVecD 78 (labelCoord (basisPt j)) +
        toVecD 78 (labelCoord (ι (jLabel (labelWord i) y)))) := by
  have hrep := repY_label hi y
  rw [hy] at hrep
  rw [tableEntry_spec hi hj, hrep]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, ← hy, ite_eq_left rfl, toVecD_zero]
  · have hne : (ι (jLabel (labelWord i) y) : ℕ) ≠ basisPt j := fun e =>
      h (ι_bijective.1 (Fin.ext (e.trans hy.symm)))
    rw [ite_eq_right hne, toVecD_xor, toVecD_xor]

@[expose] def adMat (x : Fin 78 → ZMod 2) : Matrix (Fin 78) (Fin 78) (ZMod 2) :=
  Matrix.of fun r c => ∑ i : Fin 78, x i * toVecD 78 (bTable i c) r

@[expose] def tableBracket (x y : Fin 78 → ZMod 2) : Fin 78 → ZMod 2 := adMat x *ᵥ y

theorem tableBracket_single (i j : Fin 78) :
    tableBracket (Pi.single i 1) (Pi.single j 1) = toVecD 78 (bTable i j) := by
  rw [tableBracket, Matrix.mulVec_single_one]
  funext r
  rw [Matrix.col_apply, adMat, Matrix.of_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem adCols_size (m : ℕ) : (adCols m).size = 78 := Array.size_ofFn

theorem adMat_toVecD (m : ℕ) : adMat (toVecD 78 m) = (rowsMatrix 78 (adCols m))ᵀ := by
  ext r c
  rw [Matrix.transpose_apply, rowsMatrix_apply, adCols, Array.getElem?_ofFn, dite_eq_left_of_eq_true
    (eq_true c.2), Option.getD_some, toVecD_vecMulN, Matrix.vecMul, dotProduct, adMat,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowsMatrix_apply, tableCol, Array.getElem?_ofFn, dite_eq_left_of_eq_true (eq_true i.2),
    Option.getD_some]

theorem tableBracket_toVecD (m x : ℕ) :
    tableBracket (toVecD 78 m) (toVecD 78 x) = toVecD 78 (vecMulN 78 (adCols m) x) := by
  rw [tableBracket, adMat_toVecD, transpose_mulVec]

theorem rank_adMat (m : ℕ) :
    (adMat (toVecD 78 m)).rank = Module.finrank (ZMod 2) (listSpan 78 (adCols m).toList) := by
  rw [adMat_toVecD, rank_transpose_rowsMatrix (adCols_size m)]

@[expose] noncomputable def cliqueSpan : Submodule (ZMod 2) (Fin 78 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun c : Fin 22 => toVecD 78 (labelCoord c))

theorem radicalCheck_eq_true : radicalCheck = true :=
  Certificates.certificate3067.2.1

theorem rRank_check :
    spanRankIs 78 (subOneRows transIdx) 67 = true :=
  Certificates.certificate3067.2.2.1

theorem rFree_check :
    freeIs 78 (subOneRows transIdx) (List.range 11) = true :=
  Certificates.certificate3067.2.2.2.1

theorem radicalCheck_spec :
    (∀ c < 22, labelCoord c < 2 ^ 11) ∧ (∀ q < 11, basisPt q < 22) ∧
      (∀ k ∈ transIdx, ∀ m < 2048, vecMulN 78 (fColArr[k]!) m = m) ∧
      ∀ k ∈ transIdx, ∀ q < 11, fCol k q = 2 ^ q := by
  have h := radicalCheck_eq_true
  simp only [radicalCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem mem_transIdx {k : ℕ} : k ∈ transIdx ↔ 2 ≤ k ∧ k < 12 := by
  rw [transIdx, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have := List.mem_range.1 ht
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨k - 2, List.mem_range.2 (by omega), by omega⟩

theorem toVecD_two_pow (q : Fin 78) : toVecD 78 (2 ^ (q : ℕ)) = Pi.single q 1 := by
  rw [← Nat.one_shiftLeft, toVecD_one_shiftLeft]

theorem mem_cliqueSpan
    (v : Fin 78 → ZMod 2) :
    v ∈ cliqueSpan ↔ ∀ j : Fin 78, 11 ≤ (j : ℕ) → v j = 0 := by
  constructor
  · intro hv
    refine Submodule.span_induction (p := fun v _ => ∀ j : Fin 78, 11 ≤ (j : ℕ) → v j = 0)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨c, rfl⟩ j hj
      exact toVecD_of_lt (radicalCheck_spec.1 c c.2) j hj
    · intro j _
      rfl
    · intro a b _ _ ha hb j hj
      rw [Pi.add_apply, ha j hj, hb j hj, add_zero]
    · intro c a _ ha j hj
      rw [Pi.smul_apply, ha j hj, smul_zero]
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun q _ => ?_
    by_cases hq : (q : ℕ) < 11
    · have hc : basisPt q < 22 := radicalCheck_spec.2.1 q hq
      have he : toVecD 78 (labelCoord (⟨basisPt q, hc⟩ : Fin 22)) = Pi.single q 1 := by
        rw [← toVecD_two_pow q]
        exact congrArg (toVecD 78) (fischer_label_coordinates_certificate.1 q q.2)
      rw [← mul_one (v q), ← smul_eq_mul, Pi.single_smul, ← he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [hv q (by omega), Pi.single_zero]
      exact Submodule.zero_mem _

theorem mem_cliqueSpan_iff_exists
    (v : Fin 78 → ZMod 2) :
    v ∈ cliqueSpan ↔ ∃ m < 2048, v = toVecD 78 m := by
  rw [mem_cliqueSpan, exists_toVecD_iff (k := 11)]
  norm_num

theorem radical_fixed_iff
    (v : Fin 78 → ZMod 2) :
    (∀ k, 2 ≤ k → k < 12 → fMat k *ᵥ v = v) ↔ v ∈ cliqueSpan := by
  constructor
  · intro hv
    obtain ⟨hrs, T, hT, hfree⟩ := freeIs_spec rFree_check
    have hunit : ∀ p : Fin 78, (p : ℕ) < 11 → ∀ k ∈ transIdx, fMat k *ᵥ Pi.single p 1 =
        Pi.single p 1 := fun p hp k hk => by
      have hk' := mem_transIdx.1 hk
      rw [fMat_col (by omega), fCol, ← toVecD_two_pow]
      exact congrArg (toVecD 78) (radicalCheck_spec.2.2.2 k hk p hp)
    have key := eq_sum_of_table hrs hT (fun p => Pi.single p 1) (fun p hp => by
        have hp' : (p : ℕ) < 11 := List.mem_range.1 ((hfree p p.2).1 hp)
        refine ⟨dotProduct_subOneRows (hunit p hp'), fun p' _ => ?_⟩
        rw [Pi.single_apply])
      (dotProduct_subOneRows fun k hk => hv k (mem_transIdx.1 hk).1 (mem_transIdx.1 hk).2)
    rw [mem_cliqueSpan]
    intro j hj
    rw [key, Finset.sum_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : T[(p : ℕ)]! = 0
    · have hp' : (p : ℕ) < 11 := List.mem_range.1 ((hfree p p.2).1 hp)
      have hpj : j ≠ p := fun e => by rw [e] at hj; omega
      rw [ite_eq_left hp, Pi.smul_apply, Pi.single_eq_of_ne hpj, smul_zero]
    · rw [ite_eq_right hp]
      rfl
  · intro hv k hk2 hk12
    obtain ⟨m, hm, rfl⟩ := (mem_cliqueSpan_iff_exists v).1 hv
    rw [fMat_mulVec, radicalCheck_spec.2.2.1 k (mem_transIdx.2 ⟨hk2, hk12⟩) m hm]

theorem radical_rank :
    (stackSubOne fun t : Fin 10 => fMat ((t : ℕ) + 2)).rank = 67 := by
  rw [rank_eq_finrank_listSpan _ (subOneRows transIdx)
    (range_stack_row transIdx (fun t : Fin 10 => (t : ℕ) + 2) fun k => by
      rw [mem_transIdx]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨k - 2, by omega⟩, by simp only; omega⟩
      · rintro ⟨t, rfl⟩
        exact ⟨by omega, by omega⟩)]
  exact finrank_listSpan rRank_check

theorem orbitCheck_eq_true : orbitCheck = true :=
  Certificates.certificate3067.2.2.2.2.1

theorem orbit_card : ∀ t < 8,
    ((Finset.range 2048).filter fun m => orbIdx m = t).card = orbLen t :=
  Certificates.certificate3067.2.2.2.2.2.1

inductive FReach (u : Fin 78 → ZMod 2) : (Fin 78 → ZMod 2) → Prop
  | refl : FReach u u
  | step {v : Fin 78 → ZMod 2} (k : ℕ) (hk : k < 12) : FReach u v → FReach u (fMat k *ᵥ v)

@[expose] def orbSet (t : ℕ) : Set (Fin 78 → ZMod 2) :=
  {v | ∃ m < 2048, orbIdx m = t ∧ v = toVecD 78 m}

theorem orbitEntry_spec {m : ℕ} (hm : m < 2048) :
    orbIdx m < 8 ∧
      (∀ k < 12, vecMulN 78 (fColArr[k]!) m < 2048 ∧
        orbIdx (vecMulN 78 (fColArr[k]!) m) = orbIdx m) ∧
      (orbDist m = 0 → m = orbRep (orbIdx m)) ∧
      (orbDist m ≠ 0 → orbPar m < 2048 ∧ orbIdx (orbPar m) = orbIdx m ∧
        orbDist (orbPar m) + 1 = orbDist m ∧ orbGen m < 2 ∧
        vecMulN 78 (fColArr[orbGen m]!) (orbPar m) = m) ∧
      spanRankIs 78 (adCols m).toList (orbRank (orbIdx m)) = true := by
  have h := orbitCheck_eq_true
  rw [orbitCheck, Bool.and_eq_true, Bool.and_eq_true] at h
  have he : orbitEntryOK m = true := List.all_eq_true.1 h.1.1 m (List.mem_range.2 hm)
  rw [orbitEntryOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at he
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := he
  refine ⟨of_decide_eq_true h1, fun k hk => ?_, fun hd => ?_, fun hd => ?_, h4⟩
  · have := List.all_eq_true.1 h2 k (List.mem_range.2 hk)
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  · rw [ite_eq_left hd, beq_iff_eq] at h3
    exact h3
  · rw [ite_eq_right hd] at h3
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    exact ⟨h3.1.1.1.1, h3.1.1.1.2, h3.1.1.2, h3.1.2, h3.2⟩

theorem orbitRep_spec {t : ℕ} (ht : t < 8) : orbIdx (orbRep t) = t ∧
    orbRep t < 2048 := by
  have h := orbitCheck_eq_true
  rw [orbitCheck, Bool.and_eq_true, Bool.and_eq_true] at h
  have := List.all_eq_true.1 h.1.2 t (List.mem_range.2 ht)
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this

theorem orbitIdent_spec {m : ℕ} (hm : m < 2048) :
    (orbIdx m = 0 ↔ m = 0) ∧ (orbIdx m = 7 ↔ m = 949) ∧
      (orbIdx m = 1 ↔ ∃ c < 22, labelCoord c = m) ∧
      (orbIdx m = 6 ↔ ∃ c < 22, 949 ^^^ labelCoord c = m) := by
  have h := orbitCheck_eq_true
  rw [orbitCheck, Bool.and_eq_true, Bool.and_eq_true] at h
  have hm' := List.all_eq_true.1 h.2 m (List.mem_range.2 hm)
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hm'
  obtain ⟨⟨⟨h0, h7⟩, h1⟩, h6⟩ := hm'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← beq_iff_eq, beq_iff_eq.1 h0, beq_iff_eq]
  · rw [← beq_iff_eq, beq_iff_eq.1 h7, beq_iff_eq]
  · rw [← beq_iff_eq, beq_iff_eq.1 h1, List.contains_iff_mem, List.mem_map]
    simp only [List.mem_range]
  · rw [← beq_iff_eq, beq_iff_eq.1 h6, List.contains_iff_mem, List.mem_map]
    simp only [List.mem_range]

theorem toVecD_lt_injective {m m' : ℕ} (hm : m < 2048) (hm' : m' < 2048)
    (h : toVecD 78 m = toVecD 78 m') : m = m' :=
  toVecD_injective (lt_trans hm (by norm_num)) (lt_trans hm' (by norm_num)) h

theorem mem_orbSet {t : ℕ} {m : ℕ} (hm : m < 2048) : toVecD 78 m ∈ orbSet t ↔ orbIdx m = t := by
  constructor
  · rintro ⟨m', hm', ht, he⟩
    rw [toVecD_lt_injective hm hm' he]
    exact ht
  · intro ht
    exact ⟨m, hm, ht, rfl⟩

theorem freach_iff {t : ℕ} (ht : t < 8) (v : Fin 78 → ZMod 2) :
    FReach (toVecD 78 (orbRep t)) v ↔ v ∈ orbSet t := by
  constructor
  · intro hv
    induction hv with
    | refl => exact ⟨orbRep t, (orbitRep_spec ht).2, (orbitRep_spec ht).1, rfl⟩
    | step k hk _ ih =>
      obtain ⟨m, hm, hmt, rfl⟩ := ih
      obtain ⟨hx, hxi⟩ := (orbitEntry_spec hm).2.1 k hk
      exact ⟨_, hx, hxi.trans hmt, fMat_mulVec k m⟩
  · rintro ⟨m, hm, hmt, rfl⟩
    have key : ∀ n, ∀ m < 2048, orbDist m = n → orbIdx m = t →
        FReach (toVecD 78 (orbRep t)) (toVecD 78 m) := by
      intro n
      induction n with
      | zero =>
        intro m hm hd hmt
        rw [(orbitEntry_spec hm).2.2.1 hd, hmt]
        exact FReach.refl
      | succ n ih =>
        intro m hm hd hmt
        obtain ⟨hp, hpi, hpd, hg, hpm⟩ := (orbitEntry_spec hm).2.2.2.1 (by omega)
        have hr := ih (orbPar m) hp (by omega) (hpi.trans hmt)
        have := FReach.step (orbGen m) (by omega) hr
        rw [fMat_mulVec, hpm] at this
        exact this
    exact key _ m hm rfl hmt

theorem orbSet_disjoint {t t' : ℕ} (h : t ≠ t') : Disjoint (orbSet t) (orbSet t') := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, hm, hmt, rfl⟩ hv
  exact h (hmt.symm.trans ((mem_orbSet hm).1 hv))

theorem mem_cliqueSpan_iff_orbSet
    (v : Fin 78 → ZMod 2) :
    v ∈ cliqueSpan ↔ ∃ t < 8, v ∈ orbSet t := by
  rw [mem_cliqueSpan_iff_exists]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨orbIdx m, (orbitEntry_spec hm).1, m, hm, rfl, rfl⟩
  · rintro ⟨t, -, m, hm, -, rfl⟩
    exact ⟨m, hm, rfl⟩

theorem ncard_cliqueSpan :
    (cliqueSpan : Set (Fin 78 → ZMod 2)).ncard
    = 2048 := by
  have hset : (cliqueSpan : Set (Fin 78 → ZMod 2)) = toVecD 78 '' (Finset.range 2048 : Set ℕ) := by
    ext v
    rw [SetLike.mem_coe, mem_cliqueSpan_iff_exists]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, Finset.mem_coe.2 (Finset.mem_range.2 hm), rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, Finset.mem_range.1 (Finset.mem_coe.1 hm), rfl⟩
  have hinj : Set.InjOn (toVecD 78) (Finset.range 2048 : Set ℕ) := fun m hm m' hm' e =>
    toVecD_lt_injective (Finset.mem_range.1 hm) (Finset.mem_range.1 hm') e
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]

theorem orbSet_eq_image (t : ℕ) :
    orbSet t = toVecD 78 '' {m | m < 2048 ∧ orbIdx m = t} := by
  ext v
  constructor
  · rintro ⟨m, hm, hmt, rfl⟩
    exact ⟨m, ⟨hm, hmt⟩, rfl⟩
  · rintro ⟨m, ⟨hm, hmt⟩, rfl⟩
    exact ⟨m, hm, hmt, rfl⟩

theorem ncard_orbSet {t : ℕ} (ht : t < 8) : (orbSet t).ncard = orbLen
    t := by
  have hinj : Set.InjOn (toVecD 78) {m | m < 2048 ∧ orbIdx m = t} := fun m hm m' hm' e =>
    toVecD_lt_injective hm.1 hm'.1 e
  rw [orbSet_eq_image, hinj.ncard_image, ← orbit_card t ht, ← Set.ncard_coe_finset]
  congr 1
  ext m
  simp

theorem rank_orbSet {t : ℕ} {v : Fin 78 → ZMod 2} (hv : v ∈ orbSet t)
    :
    (adMat v).rank = orbRank t := by
  obtain ⟨m, hm, rfl, rfl⟩ := hv
  rw [rank_adMat]
  exact finrank_listSpan (orbitEntry_spec hm).2.2.2.2

theorem orbSet_zero : orbSet 0 = {0} := by
  ext v
  constructor
  · rintro ⟨m, hm, hmt, rfl⟩
    rw [(orbitIdent_spec hm).1.1 hmt, toVecD_zero]
    rfl
  · intro hv
    rw [Set.mem_singleton_iff.1 hv, ← toVecD_zero 78]
    exact ⟨0, by norm_num, (orbitIdent_spec (by norm_num)).1.2 rfl, rfl⟩

theorem orbSet_seven : orbSet 7 = {toVecD 78 949} := by
  ext v
  constructor
  · rintro ⟨m, hm, hmt, rfl⟩
    rw [(orbitIdent_spec hm).2.1.1 hmt]
    rfl
  · intro hv
    rw [Set.mem_singleton_iff.1 hv]
    exact ⟨949, by norm_num, (orbitIdent_spec (by norm_num)).2.1.2 rfl, rfl⟩

theorem orbSet_one : orbSet 1 = Set.range fun c : Fin 22 => toVecD 78
    (labelCoord c) := by
  ext v
  constructor
  · rintro ⟨m, hm, hmt, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (orbitIdent_spec hm).2.2.1.1 hmt
    exact ⟨⟨c, hc⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    have hm : labelCoord c < 2048 := radicalCheck_spec.1 c c.2
    exact ⟨_, hm, (orbitIdent_spec hm).2.2.1.2 ⟨c, c.2, rfl⟩, rfl⟩

theorem orbSet_six :
    orbSet 6 = Set.range fun c : Fin 22 => toVecD 78 949 + toVecD 78 (labelCoord c) := by
  ext v
  constructor
  · rintro ⟨m, hm, hmt, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (orbitIdent_spec hm).2.2.2.1 hmt
    exact ⟨⟨c, hc⟩, (toVecD_xor 78 949 (labelCoord c)).symm⟩
  · rintro ⟨c, rfl⟩
    have hm : 949 ^^^ labelCoord c < 2048 :=
      Nat.xor_lt_two_pow (n := 11) (by norm_num) (radicalCheck_spec.1 c c.2)
    exact ⟨_, hm, (orbitIdent_spec hm).2.2.2.2 ⟨c, c.2, rfl⟩,
      (toVecD_xor 78 949 (labelCoord c)).symm⟩

theorem zeroSetCheck_eq_true : zeroSetCheck = true :=
  Certificates.certificate3067.2.2.2.2.2.2

theorem zeroSet_spec
    {u : ℕ} (h : zeroSetOK u = true) (y : Y) :
    tableBracket (toVecD 78 u) (toVecD 78 (labelCoord (ι y))) = 0 ↔ (ι y : ℕ) < 22 := by
  have h' : ((List.range 3510).all fun q =>
      decide (vecMulN 78 (adCols u) (labelCoord q) < 2 ^ 78) &&
        (vecMulN 78 (adCols u) (labelCoord q) == 0) == decide (q < 22)) = true := h
  have hq := List.all_eq_true.1 h' (ι y) (List.mem_range.2 (ι y).2)
  rw [Bool.and_eq_true, decide_eq_true_eq, Bool.beq_eq_decide_eq, decide_eq_true_eq] at hq
  rw [tableBracket_toVecD, toVecD_eq_zero_iff hq.1, ← beq_iff_eq, hq.2, decide_eq_true_eq]

theorem zeroSet_clique
    (y : Y) :
    tableBracket (toVecD 78 949) (toVecD 78 (labelCoord (ι y))) = 0 ↔ (ι y : ℕ) < 22 := by
  have h := zeroSetCheck_eq_true
  rw [zeroSetCheck, Bool.and_eq_true] at h
  exact zeroSet_spec h.1 y

theorem zeroSet_clique_add
    {c : ℕ} (hc : c < 22) (y : Y) :
    tableBracket (toVecD 78 949 + toVecD 78 (labelCoord c)) (toVecD 78 (labelCoord (ι y))) = 0 ↔
      (ι y : ℕ) < 22 := by
  have h := zeroSetCheck_eq_true
  rw [zeroSetCheck, Bool.and_eq_true] at h
  rw [← toVecD_xor]
  exact zeroSet_spec (List.all_eq_true.1 h.2 c (List.mem_range.2 hc)) y

theorem fischer_radical_sieve_certificate :
    (∀ i < 78, ∀ j < 78, ∀ y : Y, (ι y : ℕ) = basisPt j →
      (jLabel (labelWord i) y = y → toVecD 78 (bTable i j) = 0) ∧
      (jLabel (labelWord i) y ≠ y → toVecD 78 (bTable i j) =
        toVecD 78 (labelCoord (basisPt i)) + toVecD 78 (labelCoord (basisPt j)) +
          toVecD 78 (labelCoord (ι (jLabel (labelWord i) y))))) ∧
    (∀ i j : Fin 78, tableBracket (Pi.single i 1) (Pi.single j 1) = toVecD 78 (bTable i j)) ∧
    (stackSubOne fun t : Fin 10 => fMat ((t : ℕ) + 2)).rank = 67 ∧
    (∀ v : Fin 78 → ZMod 2, (∀ k, 2 ≤ k → k < 12 → fMat k *ᵥ v = v) ↔ v ∈ cliqueSpan) ∧
    (cliqueSpan : Set (Fin 78 → ZMod 2)).ncard = 2048 ∧
    (∀ t < 8, ∀ v, FReach (toVecD 78 (orbRep t)) v ↔ v ∈ orbSet t) ∧
    (∀ t t' : ℕ, t ≠ t' → Disjoint (orbSet t) (orbSet t')) ∧
    (∀ v, v ∈ cliqueSpan ↔ ∃ t < 8, v ∈ orbSet t) ∧
    (List.range 8).map orbRep = [0, 1, 3, 7, 39, 117, 437, 949] ∧
    (∀ t < 8, (orbSet t).ncard = orbLen t) ∧
    (List.range 8).map orbLen = [1, 22, 231, 770, 770, 231, 22, 1] ∧
    (∀ t, ∀ v ∈ orbSet t, (adMat v).rank = orbRank t) ∧
    (List.range 8).map orbRank = [0, 22, 32, 38, 38, 32, 22, 22] ∧
    orbSet 0 = {0} ∧ orbSet 7 = {toVecD 78 949} ∧
    orbSet 1 = Set.range (fun c : Fin 22 => toVecD 78 (labelCoord c)) ∧
    orbSet 6 = Set.range (fun c : Fin 22 => toVecD 78 949 + toVecD 78 (labelCoord c)) ∧
    (∀ y : Y, tableBracket (toVecD 78 949) (toVecD 78 (labelCoord (ι y))) = 0 ↔ (ι y : ℕ) < 22) ∧
    ∀ c < 22, ∀ y : Y,
      tableBracket (toVecD 78 949 + toVecD 78 (labelCoord c)) (toVecD 78 (labelCoord (ι y))) = 0 ↔
        (ι y : ℕ) < 22 :=
  ⟨fun _ hi _ hj y hy => table_binding hi hj y hy, tableBracket_single, radical_rank,
    radical_fixed_iff, ncard_cliqueSpan, fun _ ht v => freach_iff ht v,
    fun _ _ h => orbSet_disjoint h,
    mem_cliqueSpan_iff_orbSet, by decide, fun _ ht => ncard_orbSet ht, by decide,
    fun _ _ hv => rank_orbSet hv, by decide, orbSet_zero, orbSet_seven, orbSet_one, orbSet_six,
    zeroSet_clique, fun _ hc y => zeroSet_clique_add hc y⟩

end CFSG.Monster.B.TwoA.Fischer.Cert
