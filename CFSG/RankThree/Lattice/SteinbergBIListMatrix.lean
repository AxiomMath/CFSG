module

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley

@[expose] def lget (A : List (List ℤ)) (i j : ℕ) : ℤ := (A.getD i []).getD j 0

@[expose] def vget (v : List ℤ) (i : ℕ) : ℤ := v.getD i 0

@[expose] def toMat (n : ℕ) (A : List (List ℤ)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => lget A i j

@[expose] def toVec (n : ℕ) (v : List ℤ) : Fin n → ℤ := fun i => vget v i

@[expose] def lofFn (n : ℕ) (f : Fin n → Fin n → ℤ) : List (List ℤ) :=
  List.ofFn fun i => List.ofFn fun j => f i j

@[expose] def vofFn (n : ℕ) (f : Fin n → ℤ) : List ℤ := List.ofFn f

theorem lget_lofFn {n : ℕ} (f : Fin n → Fin n → ℤ) (i j : Fin n) :
    lget (lofFn n f) i j = f i j := by
  simp [lget, lofFn]

theorem vget_vofFn {n : ℕ} (f : Fin n → ℤ) (i : Fin n) : vget (vofFn n f) i = f i := by
  simp [vget, vofFn]

theorem toMat_lofFn {n : ℕ} (f : Fin n → Fin n → ℤ) : toMat n (lofFn n f) = Matrix.of f := by
  ext i j
  exact lget_lofFn f i j

theorem toVec_vofFn {n : ℕ} (f : Fin n → ℤ) : toVec n (vofFn n f) = f := by
  funext i
  exact vget_vofFn f i

@[expose] def lmul (n : ℕ) (A B : List (List ℤ)) : List (List ℤ) :=
  lofFn n fun i j => (List.ofFn fun k : Fin n => lget A i k * lget B k j).sum

@[expose] def lmulVec (n : ℕ) (A : List (List ℤ)) (v : List ℤ) : List ℤ :=
  vofFn n fun i => (List.ofFn fun k : Fin n => lget A i k * vget v k).sum

@[expose] def lmulVecT (n : ℕ) (A : List (List ℤ)) (v : List ℤ) : List ℤ :=
  vofFn n fun i => (List.ofFn fun k : Fin n => lget A k i * vget v k).sum

@[expose] def lid (n : ℕ) : List (List ℤ) := lofFn n fun i j => if i = j then 1 else 0

@[expose] def ladd (n : ℕ) (A B : List (List ℤ)) : List (List ℤ) :=
  lofFn n fun i j => lget A i j + lget B i j

@[expose] def lsmul (n : ℕ) (c : ℤ) (A : List (List ℤ)) : List (List ℤ) :=
  lofFn n fun i j => c * lget A i j

@[expose] def lpow (n : ℕ) (A : List (List ℤ)) : ℕ → List (List ℤ)
  | 0 => lid n
  | k + 1 => lmul n A (lpow n A k)

@[expose] def vadd (n : ℕ) (u v : List ℤ) : List ℤ := vofFn n fun i => vget u i + vget v i

@[expose] def vsmul (n : ℕ) (c : ℤ) (v : List ℤ) : List ℤ := vofFn n fun i => c * vget v i

@[expose] def lcols (n : ℕ) (cs : List (List ℤ)) : List (List ℤ) :=
  lofFn n fun i j => vget (cs.getD j []) i

theorem toMat_lmul (n : ℕ) (A B : List (List ℤ)) :
    toMat n (lmul n A B) = toMat n A * toMat n B := by
  ext i j
  simp only [lmul, toMat_lofFn, Matrix.of_apply, Matrix.mul_apply, List.sum_ofFn]
  rfl

theorem toVec_lmulVec (n : ℕ) (A : List (List ℤ)) (v : List ℤ) :
    toVec n (lmulVec n A v) = (toMat n A).mulVec (toVec n v) := by
  funext i
  simp only [lmulVec, toVec_vofFn, Matrix.mulVec, dotProduct, List.sum_ofFn]
  rfl

theorem toVec_lmulVecT (n : ℕ) (A : List (List ℤ)) (v : List ℤ) :
    toVec n (lmulVecT n A v) = (toMat n A).transpose.mulVec (toVec n v) := by
  funext i
  simp only [lmulVecT, toVec_vofFn, Matrix.mulVec, dotProduct, List.sum_ofFn]
  rfl

theorem toMat_lid (n : ℕ) : toMat n (lid n) = 1 := by
  ext i j
  simp only [lid, toMat_lofFn, Matrix.of_apply, Matrix.one_apply]

theorem toMat_ladd (n : ℕ) (A B : List (List ℤ)) :
    toMat n (ladd n A B) = toMat n A + toMat n B := by
  ext i j
  simp only [ladd, toMat_lofFn, Matrix.of_apply, Matrix.add_apply]
  rfl

theorem toMat_lsmul (n : ℕ) (c : ℤ) (A : List (List ℤ)) :
    toMat n (lsmul n c A) = c • toMat n A := by
  ext i j
  simp only [lsmul, toMat_lofFn, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

theorem toMat_lpow (n : ℕ) (A : List (List ℤ)) (k : ℕ) :
    toMat n (lpow n A k) = toMat n A ^ k := by
  induction k with
  | zero => rw [lpow, toMat_lid, pow_zero]
  | succ k ih => rw [lpow, toMat_lmul, ih, pow_succ']

theorem toVec_vadd (n : ℕ) (u v : List ℤ) : toVec n (vadd n u v) = toVec n u + toVec n v := by
  funext i
  simp only [vadd, toVec_vofFn, Pi.add_apply]
  rfl

theorem toVec_vsmul (n : ℕ) (c : ℤ) (v : List ℤ) : toVec n (vsmul n c v) = c • toVec n v := by
  funext i
  simp only [vsmul, toVec_vofFn, Pi.smul_apply, smul_eq_mul]
  rfl

theorem toMat_lcols (n : ℕ) (cs : List (List ℤ)) :
    toMat n (lcols n cs) = Matrix.of fun (i j : Fin n) => toVec n (cs.getD (j : ℕ) []) i := by
  rw [lcols, toMat_lofFn]
  rfl

instance Tag.neZero_rank (τ : Tag) : NeZero τ.rank := ⟨by cases τ <;> decide⟩

@[expose] def reflMat (τ : Tag) (i : Fin τ.rank) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  Matrix.of fun a b => (if a = b then 1 else 0) - if a = i then τ.cartan i b else 0

theorem reflMat_mulVec (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    (reflMat τ i).mulVec v = reflect τ i v := by
  funext a
  simp only [reflMat, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · simp
  · by_cases h : a = i
    · subst h
      simp
    · simp [h]

@[expose] def wordMat (τ : Tag) (l : List (Fin τ.rank)) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  (l.map (reflMat τ)).prod

theorem wordMat_nil (τ : Tag) : wordMat τ [] = 1 := rfl

theorem wordMat_cons (τ : Tag) (i : Fin τ.rank) (l : List (Fin τ.rank)) :
    wordMat τ (i :: l) = reflMat τ i * wordMat τ l := by
  rw [wordMat, List.map_cons, List.prod_cons]
  rfl

theorem wordMat_append (τ : Tag) (l l' : List (Fin τ.rank)) :
    wordMat τ (l ++ l') = wordMat τ l * wordMat τ l' := by
  rw [wordMat, List.map_append, List.prod_append]
  rfl

@[expose] def cartanList (τ : Tag) : List (List ℤ) := lofFn τ.rank fun i j => τ.cartan i j

theorem toMat_cartanList (τ : Tag) : toMat τ.rank (cartanList τ) = τ.cartan := by
  rw [cartanList, toMat_lofFn]
  rfl

@[expose] def lrefl (n : ℕ) (C : List (List ℤ)) (i : ℕ) : List (List ℤ) :=
  lofFn n fun a b => (if a = b then 1 else 0) - if (a : ℕ) = i then lget C i b else 0

@[expose] def lword (n : ℕ) (C : List (List ℤ)) (l : List ℕ) : List (List ℤ) :=
  l.foldr (fun i M => lmul n (lrefl n C i) M) (lid n)

theorem toMat_lrefl (τ : Tag) {C : List (List ℤ)} (hC : toMat τ.rank C = τ.cartan)
    (i : Fin τ.rank) : toMat τ.rank (lrefl τ.rank C i) = reflMat τ i := by
  rw [lrefl, toMat_lofFn]
  ext a b
  simp only [Matrix.of_apply, reflMat, Fin.val_eq_val]
  congr 1
  split_ifs with h
  · subst h
    rw [← hC]
    rfl
  · rfl

theorem toMat_lword (τ : Tag) {C : List (List ℤ)} (hC : toMat τ.rank C = τ.cartan)
    (l : List (Fin τ.rank)) : toMat τ.rank (lword τ.rank C (l.map Fin.val)) = wordMat τ l := by
  induction l with
  | nil => rw [List.map_nil, lword, List.foldr_nil, toMat_lid, wordMat_nil]
  | cons i l ih =>
    rw [List.map_cons, lword, List.foldr_cons, toMat_lmul, toMat_lrefl τ hC, ← lword, ih,
      wordMat_cons]

end CFSG.RankThree.Lattice
