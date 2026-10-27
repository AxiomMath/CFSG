module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.LocalAnalysis.StandardType.GGA11CohAutSL6

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

private def blkI (l m : Fin 4) : Fin 4 :=
  if l ≠ 0 ∧ m ≠ 0 then 0 else if l ≠ 1 ∧ m ≠ 1 then 1 else if l ≠ 2 ∧ m ≠ 2 then 2 else 3

private def blkJ (l m : Fin 4) : Fin 4 :=
  if l ≠ 3 ∧ m ≠ 3 then 3 else if l ≠ 2 ∧ m ≠ 2 then 2 else if l ≠ 1 ∧ m ≠ 1 then 1 else 0

private lemma blkI_ne_left : ∀ l m : Fin 4, l ≠ m → blkI l m ≠ l := by decide

private lemma blkI_ne_right : ∀ l m : Fin 4, l ≠ m → blkI l m ≠ m := by decide

private lemma blkJ_ne_left : ∀ l m : Fin 4, l ≠ m → blkJ l m ≠ l := by decide

private lemma blkJ_ne_right : ∀ l m : Fin 4, l ≠ m → blkJ l m ≠ m := by decide

private def posOf (l m : Fin 4) (p : Fin 6) : Fin 12 :=
  if h : p.val < 3 then pos (blkI l m) ⟨p.val, h⟩
  else pos (blkJ l m) ⟨p.val - 3, by omega⟩

private lemma posOf_blk_ne_left : ∀ (l m : Fin 4), l ≠ m → ∀ p : Fin 6, blk (posOf l m p) ≠ l := by
  decide

private lemma posOf_blk_ne_right : ∀ (l m : Fin 4), l ≠ m → ∀ p : Fin 6, blk (posOf l m p) ≠ m := by
  decide

private lemma swapBlocks_pos_lt9 : ∀ (l b : Fin 4), b ≠ l → ∀ k : Fin 3,
    (swapBlocks l (pos b k)).val < 9 := by decide

private lemma swapBlocks_posOf_lt9 : ∀ (l m : Fin 4), l ≠ m → ∀ p : Fin 6,
    (swapBlocks l (posOf l m p)).val < 9 := by decide

private def to9 (x : Fin 12) (h : x.val < 9) : Fin 9 := ⟨x.val, h⟩

private lemma to9_inj : ∀ (x y : Fin 12) (hx : x.val < 9) (hy : y.val < 9),
    to9 x hx = to9 y hy → x = y := by
  intro x y hx hy h
  exact Fin.ext (by simpa [to9] using congrArg Fin.val h)

private def Qfun (l m : Fin 4) (h : l ≠ m) (p : Fin 6) : Fin 9 :=
  to9 (swapBlocks l (posOf l m p)) (swapBlocks_posOf_lt9 l m h p)

private def Q'fun (l m : Fin 4) (h : l ≠ m) (q : Fin 3) : Fin 9 :=
  to9 (swapBlocks l (pos m q)) (swapBlocks_pos_lt9 l m (Ne.symm h) q)

private def einv (l m : Fin 4) (h : l ≠ m) (x : Fin 9) : Fin 6 ⊕ Fin 3 :=
  if blk (Fin.castLE (by omega : 9 ≤ 12) x) = Equiv.swap l 3 (blkI l m) then
    Sum.inl ⟨(idxIn (Fin.castLE (by omega : 9 ≤ 12) x)).val, by omega⟩
  else if blk (Fin.castLE (by omega : 9 ≤ 12) x) = Equiv.swap l 3 (blkJ l m) then
    Sum.inl ⟨3 + (idxIn (Fin.castLE (by omega : 9 ≤ 12) x)).val, by omega⟩
  else
    Sum.inr ⟨(idxIn (Fin.castLE (by omega : 9 ≤ 12) x)).val, by omega⟩

private noncomputable def eEquiv (l m : Fin 4) (h : l ≠ m) : Fin 6 ⊕ Fin 3 ≃ Fin 9 :=
  Equiv.mk
    (fun x => match x with | Sum.inl p => Qfun l m h p | Sum.inr q => Q'fun l m h q)
    (einv l m h)
    (by rintro (p | q) <;> decide +revert)
    (by intro x <;> decide +revert)

@[simp] private lemma eEquiv_inl (l m : Fin 4) (h : l ≠ m) (p : Fin 6) :
    eEquiv l m h (Sum.inl p) = Qfun l m h p := rfl

private noncomputable def blockMat (e : Fin 6 ⊕ Fin 3 ≃ Fin 9) (A : Matrix (Fin 6) (Fin 6) F2) :
    Matrix (Fin 9) (Fin 9) F2 :=
  (Matrix.reindexAlgEquiv F2 F2 e) (Matrix.fromBlocks A 0 0 1)

private noncomputable def blockEmb (e : Fin 6 ⊕ Fin 3 ≃ Fin 9) : SL 6 →* SL 9 where
  toFun A := ⟨blockMat e (A : Matrix (Fin 6) (Fin 6) F2), by
    rw [blockMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
      mul_one]
    exact A.2⟩
  map_one' := Subtype.ext (by
    show blockMat e ((1 : SL 6) : Matrix (Fin 6) (Fin 6) F2) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, blockMat, Matrix.fromBlocks_one, map_one])
  map_mul' A B := Subtype.ext (by
    show blockMat e ((A * B : SL 6) : Matrix (Fin 6) (Fin 6) F2) =
      blockMat e (A : Matrix (Fin 6) (Fin 6) F2) * blockMat e (B : Matrix (Fin 6) (Fin 6) F2)
    rw [Matrix.SpecialLinearGroup.coe_mul, blockMat, blockMat, blockMat, ← map_mul,
      Matrix.fromBlocks_multiply]
    simp)

private lemma fromBlocks_transvection {p q : Fin 6} (hpq : p ≠ q) (c : F2) :
    Matrix.fromBlocks (SpecialLinearGroup.transvection hpq c) 0 0 (1 : Matrix (Fin 3) (Fin 3) F2) =
      ((SpecialLinearGroup.transvection (Sum.inl_injective.ne hpq) c :
        SpecialLinearGroup (Fin 6 ⊕ Fin 3) F2) :
        Matrix (Fin 6 ⊕ Fin 3) (Fin 6 ⊕ Fin 3) F2) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.fromBlocks, SpecialLinearGroup.transvection_coe, Matrix.one_apply,
      Matrix.single_apply]

private lemma reindex_transvection (e : Fin 6 ⊕ Fin 3 ≃ Fin 9)
    {a b : Fin 6 ⊕ Fin 3} (hab : a ≠ b) (c : F2) :
    (Matrix.reindexAlgEquiv F2 F2 e)
        ((SpecialLinearGroup.transvection hab c : SpecialLinearGroup (Fin 6 ⊕ Fin 3) F2) :
          Matrix (Fin 6 ⊕ Fin 3) (Fin 6 ⊕ Fin 3) F2) =
      ((SpecialLinearGroup.transvection (e.injective.ne hab) c : SL 9) :
        Matrix (Fin 9) (Fin 9) F2) := by
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, map_add, map_one,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv]
  simp

private lemma blockEmb_transvection (e : Fin 6 ⊕ Fin 3 ≃ Fin 9)
    {p q : Fin 6} (hpq : p ≠ q) (c : F2) :
    blockEmb e (SpecialLinearGroup.transvection hpq c) =
      SpecialLinearGroup.transvection (e.injective.ne (Sum.inl_injective.ne hpq)) c := by
  apply Subtype.ext
  show blockMat e (SpecialLinearGroup.transvection hpq c) = _
  rw [blockMat, fromBlocks_transvection, reindex_transvection]

private lemma posOf_injective : ∀ (l m : Fin 4) (h : l ≠ m), Function.Injective (posOf l m) := by
  decide

private lemma tv9_eq_to9 (a b : Fin 12) (ha : a.val < 9) (hb : b.val < 9) (hab : a ≠ b) :
    tv9 a b = SpecialLinearGroup.transvection
      (i := to9 a ha) (j := to9 b hb) (fun hh => hab (to9_inj a b ha hb hh)) 1 := by
  unfold tv9
  rw [dif_pos ⟨ha, hb, hab⟩]
  rfl

private noncomputable def psiFun {G : Type} [Group G] (l m : Fin 4) (h : l ≠ m)
    (φ₃ : SL 9 →* G) (n : Fin 4 → G) : SL 6 →* G :=
  (MulAut.conj (n l)).toMonoidHom.comp (φ₃.comp (blockEmb (eEquiv l m h)))

private lemma psiFun_transvection {G : Type} [Group G] (l m : Fin 4) (h : l ≠ m)
    (φ₃ : SL 9 →* G) (n : Fin 4 → G) {p q : Fin 6} (hpq : p ≠ q) :
    psiFun l m h φ₃ n (SpecialLinearGroup.transvection hpq 1) =
      Xe φ₃ n l (posOf l m p) (posOf l m q) := by
  rw [psiFun, MonoidHom.comp_apply, MonoidHom.comp_apply, blockEmb_transvection]
  simp only [MulAut.conj_apply, eEquiv_inl, Qfun]
  rw [← tv9_eq_to9 (swapBlocks l (posOf l m p)) (swapBlocks l (posOf l m q))
      (swapBlocks_posOf_lt9 l m h p) (swapBlocks_posOf_lt9 l m h q) (by
        intro hh
        exact hpq (posOf_injective l m h ((swapBlocks l).injective hh)))]
  rw [Xe, tvAt]
  rfl

private lemma blkI_lt_three : ∀ l m : Fin 4, l ≠ m → (blkI l m).val < 3 := by decide

private lemma swap_blkJ_lt_three : ∀ l m : Fin 4, l ≠ m → (Equiv.swap l 3 (blkJ l m)).val < 3 := by
  decide

private noncomputable def OmZ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private noncomputable def T6matZ (b : Fin 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun a c =>
    if a.val / 3 = b.val ∧ c.val / 3 = b.val
    then OmZ ⟨a.val % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨c.val % 3, Nat.mod_lt _ (by norm_num)⟩
    else if a = c then 1 else 0

private noncomputable def T9matZ (i : Fin 3) : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  Matrix.of fun a c =>
    if blk (Fin.castLE (by omega) a) = (i.castSucc : Fin 4) ∧
        blk (Fin.castLE (by omega) c) = i.castSucc
    then OmZ (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) c))
    else if a = c then 1 else 0

private noncomputable def blockMatZ (e : Fin 6 ⊕ Fin 3 ≃ Fin 9)
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  (Matrix.fromBlocks A 0 0 1).submatrix e.symm e.symm

private noncomputable def e2 : ZMod 2 ≃+* F2 := by
  letI : Fintype F2 := Fintype.ofFinite _
  have h2 : Fintype.card F2 = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 1 (by omega)
  exact FiniteField.ringEquivOfCardEq (by
    rw [show Fintype.card (ZMod 2) = 2 by simp, h2])

@[simp] private lemma e2_ite (P : Prop) [Decidable P] (x y : ZMod 2) :
    e2 (if P then x else y) = if P then e2 x else e2 y := by
  split_ifs <;> rfl

private lemma map_T6matZ (b : Fin 2) :
    Matrix.map (T6matZ b) (e2 : ZMod 2 →+* F2) = T6mat b := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [T6matZ, T6mat, Matrix.map_apply, Matrix.of_apply, e2_ite, OmZ, Om, map_zero, map_one]

private lemma map_T9matZ (k : Fin 3) :
    Matrix.map (T9matZ k) (e2 : ZMod 2 →+* F2) = T9mat k := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [T9matZ, T9mat, Matrix.map_apply, Matrix.of_apply, e2_ite, OmZ, Om, idxIn, blk,
      map_zero, map_one]

private lemma map_blockMatZ (e : Fin 6 ⊕ Fin 3 ≃ Fin 9)
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Matrix.map (blockMatZ e A) (e2 : ZMod 2 →+* F2) =
      blockMat e (Matrix.map A (e2 : ZMod 2 →+* F2)) := by
  rw [blockMatZ, blockMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  ext i c
  rcases hi : e.symm i with a | q <;> rcases hc : e.symm c with d | r <;>
    simp [Matrix.map_apply, Matrix.submatrix_apply, Matrix.reindex_apply, hi, hc,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, e2_ite, OmZ, Om,
      map_zero, map_one]

private lemma blockMat_T6 (l m : Fin 4) (h : l ≠ m) (b : Fin 2) :
    blockMat (eEquiv l m h) (T6mat b) =
      T9mat (if b = 0 then ⟨(blkI l m).val, blkI_lt_three l m h⟩
        else ⟨(Equiv.swap l 3 (blkJ l m)).val, swap_blkJ_lt_three l m h⟩) := by
  have hZ : blockMatZ (eEquiv l m h) (T6matZ b) =
      T9matZ (if b = 0 then ⟨(blkI l m).val, blkI_lt_three l m h⟩
        else ⟨(Equiv.swap l 3 (blkJ l m)).val, swap_blkJ_lt_three l m h⟩) := by
    fin_cases l <;> fin_cases m <;> (first | (exfalso; exact h rfl) | fin_cases b <;> decide +revert)
  have := congrArg (fun M => Matrix.map M (e2 : ZMod 2 →+* F2)) hZ
  rw [map_blockMatZ, map_T6matZ, map_T9matZ] at this
  exact this

private lemma castSucc_blkI (l m : Fin 4) (h : l ≠ m) :
    (⟨(blkI l m).val, blkI_lt_three l m h⟩ : Fin 3).castSucc = blkI l m := by
  ext; rfl

private lemma castSucc_swap_blkJ (l m : Fin 4) (h : l ≠ m) :
    (⟨(Equiv.swap l 3 (blkJ l m)).val, swap_blkJ_lt_three l m h⟩ : Fin 3).castSucc =
      Equiv.swap l 3 (blkJ l m) := by
  ext; rfl

private lemma swap_l3_blkI : ∀ l m : Fin 4, l ≠ m → Equiv.swap l 3 (blkI l m) = blkI l m := by
  decide

private lemma swap_l3_swap_blkJ : ∀ l m : Fin 4, l ≠ m →
    Equiv.swap l 3 (Equiv.swap l 3 (blkJ l m)) = blkJ l m := by
  decide

private lemma blockMat_T6_zero (l m : Fin 4) (h : l ≠ m) :
    blockMat (eEquiv l m h) (T6mat 0) = T9mat ⟨(blkI l m).val, blkI_lt_three l m h⟩ := by
  simpa using blockMat_T6 l m h 0

private lemma blockMat_T6_one (l m : Fin 4) (h : l ≠ m) :
    blockMat (eEquiv l m h) (T6mat 1) =
      T9mat ⟨(Equiv.swap l 3 (blkJ l m)).val, swap_blkJ_lt_three l m h⟩ := by
  simpa using blockMat_T6 l m h 1

private lemma psiFun_T6 {G : Type} [Group G] (l m : Fin 4) (h : l ≠ m)
    (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (hglue : A11GlueHyp φ₃ f n) (b : Fin 2) :
    psiFun l m h φ₃ n (T6 b) = f (if b = 0 then blkI l m else blkJ l m) := by
  obtain ⟨-, hT9, -, -, -, -, hn, -⟩ := hglue
  fin_cases b
  · change n l * φ₃ (blockEmb (eEquiv l m h) (T6 0)) * (n l)⁻¹ = f (blkI l m)
    have hbe : blockEmb (eEquiv l m h) (T6 0) =
        T9 ⟨(blkI l m).val, blkI_lt_three l m h⟩ := by
      apply Subtype.ext; exact blockMat_T6_zero l m h
    rw [hbe, ← hT9 ⟨(blkI l m).val, blkI_lt_three l m h⟩, castSucc_blkI l m h,
      hn l (blkI l m), swap_l3_blkI l m h]
  · change n l * φ₃ (blockEmb (eEquiv l m h) (T6 1)) * (n l)⁻¹ = f (blkJ l m)
    have hbe : blockEmb (eEquiv l m h) (T6 1) =
        T9 ⟨(Equiv.swap l 3 (blkJ l m)).val, swap_blkJ_lt_three l m h⟩ := by
      apply Subtype.ext; exact blockMat_T6_one l m h
    rw [hbe, ← hT9 ⟨(Equiv.swap l 3 (blkJ l m)).val, swap_blkJ_lt_three l m h⟩,
      castSucc_swap_blkJ l m h, hn l (Equiv.swap l 3 (blkJ l m)), swap_l3_swap_blkJ l m h]

private def pidx (l m : Fin 4) (a : Fin 12) : Fin 6 :=
  if blk a = blkI l m then ⟨(idxIn a).val, by omega⟩
  else ⟨3 + (idxIn a).val, by omega⟩

private lemma posOf_pidx : ∀ (l m : Fin 4), l ≠ m → ∀ a : Fin 12,
    blk a ≠ l → blk a ≠ m → posOf l m (pidx l m a) = a := by decide

private lemma pidx_ne : ∀ (l m : Fin 4), l ≠ m → ∀ a b : Fin 12,
    blk a ≠ l → blk a ≠ m → blk b ≠ l → blk b ≠ m → a ≠ b →
      pidx l m a ≠ pidx l m b := by
  intro l m h a b hal ham hbl hbm hab hEq
  exact hab (by rw [← posOf_pidx l m h a hal ham, ← posOf_pidx l m h b hbl hbm, hEq])

private lemma F2_eq_zero_or_one (c : F2) : c = 0 ∨ c = 1 := by
  classical
  haveI : Fintype F2 := Fintype.ofFinite F2
  have hcard : Fintype.card F2 ≤ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact le_of_eq (GaloisField.card 2 1 (by omega))
  have h : (Finset.univ : Finset F2) = {0, 1} := Finset.univ_of_card_le_two hcard
  have hc : c ∈ (Finset.univ : Finset F2) := Finset.mem_univ c
  rw [h] at hc
  simpa [Finset.mem_insert, Finset.mem_singleton] using hc

private lemma psiFun_range {G : Type} [Group G] (l m : Fin 4) (h : l ≠ m)
    (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (hglue : A11GlueHyp φ₃ f n) :
    (psiFun l m h φ₃ n).range = Ovl φ₃ n l m := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map,
      show (⊤ : Subgroup (SL 6)) = Subgroup.closure {x : SL 6 |
        ∃ (p q : Fin 6) (hpq : p ≠ q) (c : F2), x = SpecialLinearGroup.transvection hpq c} from by
        rw [CFSG.ClassicalGroups.SpecialLinear.closure_transvection_eq_top],
      Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro x ⟨p, q, hpq, c, rfl⟩
    show psiFun l m h φ₃ n (SpecialLinearGroup.transvection hpq c) ∈ Ovl φ₃ n l m
    rcases F2_eq_zero_or_one c with hc | hc
    · subst hc
      rw [show SpecialLinearGroup.transvection hpq (0 : F2) = 1 from by
        ext i j; simp [SpecialLinearGroup.transvection_coe], map_one]
      exact Subgroup.one_mem (Ovl φ₃ n l m)
    · subst hc
      rw [psiFun_transvection l m h φ₃ n hpq]
      exact Subgroup.subset_closure ⟨posOf l m p, posOf l m q,
        fun hh => hpq (posOf_injective l m h hh),
        posOf_blk_ne_left l m h p, posOf_blk_ne_left l m h q,
        posOf_blk_ne_right l m h p, posOf_blk_ne_right l m h q, rfl⟩
  · rw [Ovl, Subgroup.closure_le]
    rintro g ⟨a, b, hab, hal, hbl, ham, hbm, rfl⟩
    rw [← posOf_pidx l m h a hal ham, ← posOf_pidx l m h b hbl hbm,
      ← psiFun_transvection l m h φ₃ n
        (pidx_ne l m h a b hal ham hbl hbm hab)]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

private lemma blkI_comm : ∀ l m : Fin 4, blkI l m = blkI m l := by decide

private lemma blkJ_comm : ∀ l m : Fin 4, blkJ l m = blkJ m l := by decide

private lemma pidx_comm : ∀ (l m : Fin 4), l ≠ m → ∀ a : Fin 12, pidx l m a = pidx m l a := by
  intro l m h a; simp [pidx, blkI_comm, blkJ_comm]

private lemma blockEmb_injective (e : Fin 6 ⊕ Fin 3 ≃ Fin 9) : Function.Injective (blockEmb e) := by
  intro A B hAB
  have h : blockMat e (A : Matrix (Fin 6) (Fin 6) F2) = blockMat e (B : Matrix (Fin 6) (Fin 6) F2) :=
    congrArg (fun x : SL 9 => (x : Matrix (Fin 9) (Fin 9) F2)) hAB
  have h2 : Matrix.fromBlocks (A : Matrix (Fin 6) (Fin 6) F2) 0 0 (1 : Matrix (Fin 3) (Fin 3) F2) =
      Matrix.fromBlocks (B : Matrix (Fin 6) (Fin 6) F2) 0 0 (1 : Matrix (Fin 3) (Fin 3) F2) := by
    have hh := (Matrix.reindexAlgEquiv F2 F2 e).injective h
    simpa [blockMat] using hh
  exact Subtype.ext (Matrix.fromBlocks_inj.mp h2).1

private lemma psiFun_injective {G : Type} [Group G] (l m : Fin 4) (h : l ≠ m)
    (φ₃ : SL 9 →* G) (n : Fin 4 → G) (hφ : Function.Injective φ₃) :
    Function.Injective (psiFun l m h φ₃ n) := by
  intro x y hxy
  apply blockEmb_injective (eEquiv l m h)
  apply hφ
  exact (MulAut.conj (n l)).injective hxy

private noncomputable def psiEquiv {G : Type} [Group G] (l m : Fin 4) (h : l ≠ m)
    (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (hφ : Function.Injective φ₃)
    (hglue : A11GlueHyp φ₃ f n) : SL 6 ≃* Ovl φ₃ n l m :=
  (MonoidHom.ofInjective (f := psiFun l m h φ₃ n) (psiFun_injective l m h φ₃ n hφ)).trans
    (MulEquiv.subgroupCongr (psiFun_range l m h φ₃ f n hglue))

theorem a11OverlapAutInput_holds :
    ∀ (G : Type) [Group G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G), A11GlueHyp φ₃ f n →
      ∀ l m : Fin 4, l ≠ m → Ovl φ₃ n l m = Ovl φ₃ n m l →
        ∃ u ∈ OvlTorus f l m, ∀ a b : Fin 12, a ≠ b → blk a ≠ l → blk b ≠ l → blk a ≠ m → blk b ≠ m →
          Xe φ₃ n l a b = u * Xe φ₃ n m a b * u⁻¹ := by
  intro G _ φ₃ f n hglue l m hlm hEq
  have hglue0 : A11GlueHyp φ₃ f n := hglue
  obtain ⟨hφ, hT9, -, -, -, -, hn, -⟩ := hglue
  let el : SL 6 ≃* Ovl φ₃ n l m := psiEquiv l m hlm φ₃ f n hφ hglue0
  let em0 : SL 6 ≃* Ovl φ₃ n m l := psiEquiv m l (Ne.symm hlm) φ₃ f n hφ hglue0
  let em : SL 6 ≃* Ovl φ₃ n l m := em0.trans (MulEquiv.subgroupCongr hEq.symm)
  let α : MulAut (SL 6) := el.trans em.symm
  have hval_l : ∀ g, ((el g : Ovl φ₃ n l m) : G) = psiFun l m hlm φ₃ n g := by
    intro g; rfl
  have hval_m : ∀ g, ((em g : Ovl φ₃ n l m) : G) = psiFun m l (Ne.symm hlm) φ₃ n g := by
    intro g; rfl
  have hα0 : α (T6 0) = T6 0 := by
    have h1 : em (α (T6 0)) = el (T6 0) := by
      rw [show α (T6 0) = em.symm (el (T6 0)) from rfl, MulEquiv.apply_symm_apply]
    have h2 : el (T6 0) = em (T6 0) := by
      apply Subtype.ext
      rw [hval_l, hval_m, psiFun_T6 l m hlm φ₃ f n hglue0 0,
        psiFun_T6 m l (Ne.symm hlm) φ₃ f n hglue0 0]
      simp [blkI_comm]
    exact em.injective (h1.trans h2)
  have hα1 : α (T6 1) = T6 1 := by
    have h1 : em (α (T6 1)) = el (T6 1) := by
      rw [show α (T6 1) = em.symm (el (T6 1)) from rfl, MulEquiv.apply_symm_apply]
    have h2 : el (T6 1) = em (T6 1) := by
      apply Subtype.ext
      rw [hval_l, hval_m, psiFun_T6 l m hlm φ₃ f n hglue0 1,
        psiFun_T6 m l (Ne.symm hlm) φ₃ f n hglue0 1]
      simp [blkJ_comm]
    exact em.injective (h1.trans h2)
  obtain ⟨a, b, hab⟩ := a11AutSL6Input_holds α hα0 hα1
  refine ⟨f (blkI l m) ^ a * f (blkJ l m) ^ b, ?_, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ a) (Subgroup.pow_mem _ ?_ b)
    · exact Subgroup.subset_closure ⟨blkI l m, blkI_ne_left l m hlm, blkI_ne_right l m hlm, rfl⟩
    · exact Subgroup.subset_closure ⟨blkJ l m, blkJ_ne_left l m hlm, blkJ_ne_right l m hlm, rfl⟩
  · intro a' b' hab' hal hbl ham hbm
    have hpq : pidx l m a' ≠ pidx l m b' := pidx_ne l m hlm a' b' hal ham hbl hbm hab'
    have hp : posOf l m (pidx l m a') = a' := posOf_pidx l m hlm a' hal ham
    have hq : posOf l m (pidx l m b') = b' := posOf_pidx l m hlm b' hbl hbm
    have hp' : posOf m l (pidx l m a') = a' := by
      rw [show pidx l m a' = pidx m l a' from pidx_comm l m hlm a']
      exact posOf_pidx m l (Ne.symm hlm) a' ham hal
    have hq' : posOf m l (pidx l m b') = b' := by
      rw [show pidx l m b' = pidx m l b' from pidx_comm l m hlm b']
      exact posOf_pidx m l (Ne.symm hlm) b' hbm hbl
    have he_l : Xe φ₃ n l a' b' =
        psiFun l m hlm φ₃ n (SpecialLinearGroup.transvection hpq 1) := by
      rw [psiFun_transvection l m hlm φ₃ n hpq, hp, hq]
    have he_m : Xe φ₃ n m a' b' =
        psiFun m l (Ne.symm hlm) φ₃ n (SpecialLinearGroup.transvection hpq 1) := by
      rw [psiFun_transvection m l (Ne.symm hlm) φ₃ n hpq, hp', hq']
    have hcomp : el (SpecialLinearGroup.transvection hpq 1) =
        em (α (SpecialLinearGroup.transvection hpq 1)) := by
      rw [show α (SpecialLinearGroup.transvection hpq 1) =
        em.symm (el (SpecialLinearGroup.transvection hpq 1)) from rfl, MulEquiv.apply_symm_apply]
    calc Xe φ₃ n l a' b'
        = psiFun l m hlm φ₃ n (SpecialLinearGroup.transvection hpq 1) := he_l
      _ = (el (SpecialLinearGroup.transvection hpq 1) : G) := (hval_l _).symm
      _ = (em (α (SpecialLinearGroup.transvection hpq 1)) : G) := by rw [hcomp]
      _ = psiFun m l (Ne.symm hlm) φ₃ n (α (SpecialLinearGroup.transvection hpq 1)) := hval_m _
      _ = psiFun m l (Ne.symm hlm) φ₃ n
            ((T6 0 ^ a * T6 1 ^ b) * SpecialLinearGroup.transvection hpq 1 * (T6 0 ^ a * T6 1 ^ b)⁻¹) := by
          rw [hab]
      _ = psiFun m l (Ne.symm hlm) φ₃ n (T6 0 ^ a * T6 1 ^ b) *
            psiFun m l (Ne.symm hlm) φ₃ n (SpecialLinearGroup.transvection hpq 1) *
            (psiFun m l (Ne.symm hlm) φ₃ n (T6 0 ^ a * T6 1 ^ b))⁻¹ := by
          simp only [map_mul, map_inv]
      _ = (f (blkI l m) ^ a * f (blkJ l m) ^ b) * Xe φ₃ n m a' b' *
            (f (blkI l m) ^ a * f (blkJ l m) ^ b)⁻¹ := by
          rw [map_mul, map_pow, map_pow, psiFun_T6 m l (Ne.symm hlm) φ₃ f n hglue0 0,
            psiFun_T6 m l (Ne.symm hlm) φ₃ f n hglue0 1, he_m]
          simp [blkI_comm, blkJ_comm]

end CFSG.StandardType.A11

end
