module

public import CFSG.Quasithin.Background.SmithB45HM22Comp
public import CFSG.Quasithin.Background.SmithB45MatRep
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.B45Mat CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier Matrix
open scoped Kronecker

@[expose] def gmat (g : ↥hatM22Γ₀) : Matrix (Fin 6) (Fin 6) FieldFour :=
  ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)

theorem gmat_mul (g h : ↥hatM22Γ₀) : gmat (g * h) = gmat g * gmat h := rfl

theorem gmat_one : gmat 1 = 1 := rfl

@[expose] def g1 : ↥hatM22Γ₀ := ⟨hatM22G1, hatM22G1_mem⟩

@[expose] def g2 : ↥hatM22Γ₀ := ⟨hatM22G2, hatM22G2_mem⟩

theorem g1_mul_self : g1 * g1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact hatM22N1_mul_self

@[expose] def genΓ (z : ℤ) : ↥hatM22Γ₀ := if z = 2 then g2 else if z = -2 then g2⁻¹ else g1

@[expose] def wordΓ : List ℤ → ↥hatM22Γ₀
  | [] => 1
  | z :: w => genΓ z * wordΓ w

theorem wordΓ_append (w w' : List ℤ) : wordΓ (w ++ w') = wordΓ w * wordΓ w' := by
  induction w with
  | nil => simp [wordΓ]
  | cons z w ih => rw [List.cons_append, wordΓ, wordΓ, ih, mul_assoc]

theorem genΓ_neg_mul (z : ℤ) : genΓ (-z) = (genΓ z)⁻¹ := by
  have hg1 : g1⁻¹ = g1 := inv_eq_of_mul_eq_one_left g1_mul_self
  unfold genΓ
  by_cases h2 : z = 2
  · subst h2
    norm_num
  · by_cases hm2 : z = -2
    · subst hm2
      norm_num
    · have h2' : -z ≠ 2 := fun h => hm2 (by omega)
      have hm2' : -z ≠ -2 := fun h => h2 (by omega)
      rw [ite_eq_right h2', ite_eq_right hm2', ite_eq_right h2, ite_eq_right hm2, hg1]

theorem wordΓ_invW (w : List ℤ) : wordΓ (invW w) = (wordΓ w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordΓ]
  | cons z w ih =>
    have e : invW (z :: w) = invW w ++ [-z] := by simp [invW]
    rw [e, wordΓ_append, ih, wordΓ, wordΓ, wordΓ, mul_one, genΓ_neg_mul, _root_.mul_inv_rev]

theorem length_n2P : n2P.length = 6 := PM.length_ofMat _

theorem n2iP_eq : PM.toMat 6 6 n2iP = hatM22N2Inv := by
  rw [n2iP, PM.toMat_mul _ _ length_n2P (by rw [PM.length_mul]; exact length_n2P),
    PM.toMat_mul _ _ length_n2P length_n2P, n2P, PM.toMat_ofMat, hatM22N2Inv, Matrix.mul_assoc]

theorem length_pGen (z : ℤ) : (pGen z).length = 6 := by
  unfold pGen
  split_ifs
  · exact length_n2P
  · rw [n2iP, PM.length_mul, PM.length_mul]; exact length_n2P
  · exact PM.length_ofMat _

theorem length_pWord (w : List ℤ) : (pWord w).length = 6 := by
  cases w with
  | nil => simp [pWord, PM.idm]
  | cons z w => rw [pWord, PM.length_mul]; exact length_pWord w

theorem toMat_pGen (z : ℤ) : PM.toMat 6 6 (pGen z) = gmat (genΓ z) := by
  unfold pGen genΓ
  split_ifs
  · rw [n2P, PM.toMat_ofMat]; rfl
  · rw [n2iP_eq]; rfl
  · rw [n1P, PM.toMat_ofMat]; rfl

theorem gmat_wordΓ (w : List ℤ) : gmat (wordΓ w) = PM.toMat 6 6 (pWord w) := by
  induction w with
  | nil => rw [wordΓ, pWord, PM.toMat_idm]; rfl
  | cons z w ih =>
    rw [wordΓ, pWord, gmat_mul, ih, PM.toMat_mul _ _ (length_pGen z) (length_pWord w),
      toMat_pGen]

@[expose] def IsLetters (w : List ℤ) : Prop := ∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2

theorem hatM22Act_g1' : hatM22Act g1 = m22gA := hatM22Act_g1

theorem hatM22Act_g2' : hatM22Act g2 = m22gB := hatM22Act_g2

theorem hatM22Act_genΓ {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    hatM22Act (genΓ z) = evalCodes [m22gA, m22gB] [z] := by
  rcases hz with rfl | rfl | rfl | rfl
  · rw [genΓ, ite_eq_right (by decide), ite_eq_right (by decide), hatM22Act_g1']
    decide
  · rw [genΓ, ite_eq_right (by decide), ite_eq_right (by decide), hatM22Act_g1']
    decide
  · rw [genΓ, ite_eq_left rfl, hatM22Act_g2']
    decide
  · rw [genΓ, ite_eq_right (by decide), ite_eq_left rfl, map_inv, hatM22Act_g2']
    decide

theorem hatM22Act_wordΓ {w : List ℤ} (hw : IsLetters w) :
    hatM22Act (wordΓ w) = evalCodes [m22gA, m22gB] w := by
  induction w with
  | nil => simp [wordΓ, evalCodes]
  | cons z w ih =>
    rw [wordΓ, map_mul, ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)),
      hatM22Act_genΓ (hw z List.mem_cons_self)]
    simp [evalCodes]

@[expose] def hatH : Subgroup ↥hatM22Γ₀ where
  carrier := {g | hatM22Act g 0 = 0}
  mul_mem' := fun {a b} (ha : hatM22Act a 0 = 0) (hb : hatM22Act b 0 = 0) => by
    change hatM22Act (a * b) 0 = 0
    rw [map_mul, Equiv.Perm.mul_apply, hb, ha]
  one_mem' := by
    change hatM22Act 1 0 = 0
    rw [map_one]
    rfl
  inv_mem' := fun {a} (ha : hatM22Act a 0 = 0) => by
    change hatM22Act a⁻¹ 0 = 0
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, ha]

theorem mem_hatH {g : ↥hatM22Γ₀} : g ∈ hatH ↔ hatM22Act g 0 = 0 := Iff.rfl

theorem hatM22Z_mem_hatH : hatM22Z ∈ hatH := by
  rw [mem_hatH]
  have h : hatM22Z ∈ hatM22Act.ker := (mem_ker_hatM22Act_iff _).2 (Or.inr (Or.inl rfl))
  rw [MonoidHom.mem_ker.1 h]
  rfl

@[expose] def zH : ↥hatH := ⟨hatM22Z, hatM22Z_mem_hatH⟩

theorem hatM22L0_mul_B0 : hatM22L 0 * hatM22B 0 = 1 := by decide +kernel

theorem hatM22F0_mul_B0 : hatM22F 0 * hatM22B 0 = 0 := hatM22F_mul_B 0

theorem hatM22F0_mul_R0 : hatM22F 0 * hatM22R0 = 1 := by decide +kernel

theorem hatM22B0L0_add_R0F0 : hatM22B 0 * hatM22L 0 + hatM22R0 * hatM22F 0 = 1 := by
  decide +kernel

theorem mul_B0_of_mem {g : ↥hatM22Γ₀} (hg : g ∈ hatH) :
    gmat g * hatM22B 0 = hatM22B 0 * (hatM22L 0 * gmat g * hatM22B 0) := by
  have hmov := moves_hatM22Act g 0
  rw [mem_hatH.1 hg] at hmov
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hx : Matrix.toLin' (gmat g) (Matrix.toLin' (hatM22B 0) x) ∈ hatM22U 0 := by
    rw [← hmov]
    exact ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := hx
  simp only [Matrix.toLin'_mul, LinearMap.comp_apply]
  change Matrix.toLin' (gmat g) (Matrix.toLin' (hatM22B 0) x) =
    Matrix.toLin' (hatM22B 0) (Matrix.toLin' (hatM22L 0) (Matrix.toLin' (gmat g)
      (Matrix.toLin' (hatM22B 0) x)))
  rw [← hy, ← LinearMap.comp_apply (Matrix.toLin' (hatM22L 0)), ← Matrix.toLin'_mul,
    hatM22L0_mul_B0, Matrix.toLin'_one, LinearMap.id_apply]

theorem F0_mul_of_mem {g : ↥hatM22Γ₀} (hg : g ∈ hatH) :
    hatM22F 0 * gmat g = hatM22F 0 * gmat g * hatM22R0 * hatM22F 0 := by
  have h1 : hatM22F 0 * gmat g * hatM22B 0 = 0 := by
    rw [Matrix.mul_assoc, mul_B0_of_mem hg, ← Matrix.mul_assoc, hatM22F0_mul_B0,
      Matrix.zero_mul]
  calc hatM22F 0 * gmat g = hatM22F 0 * gmat g * (hatM22B 0 * hatM22L 0 + hatM22R0 * hatM22F 0) :=
        by rw [hatM22B0L0_add_R0F0, Matrix.mul_one]
    _ = hatM22F 0 * gmat g * hatM22B 0 * hatM22L 0 + hatM22F 0 * gmat g * hatM22R0 * hatM22F 0 :=
        by simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = hatM22F 0 * gmat g * hatM22R0 * hatM22F 0 := by rw [h1, Matrix.zero_mul, zero_add]

@[expose] noncomputable def rep3a : ↥hatH →* Matrix (Fin 3) (Fin 3) FieldFour where
  toFun h := hatM22L 0 * gmat h * hatM22B 0
  map_one' := by
    change hatM22L 0 * 1 * hatM22B 0 = 1
    rw [Matrix.mul_one, hatM22L0_mul_B0]
  map_mul' g h := by
    change hatM22L 0 * (gmat g * gmat h) * hatM22B 0 =
      hatM22L 0 * gmat g * hatM22B 0 * (hatM22L 0 * gmat h * hatM22B 0)
    rw [Matrix.mul_assoc (hatM22L 0), Matrix.mul_assoc (gmat g), mul_B0_of_mem h.2]
    simp only [Matrix.mul_assoc]

theorem rep3a_apply (h : ↥hatH) : rep3a h = hatM22L 0 * gmat h * hatM22B 0 := rfl

@[expose] noncomputable def rep3b : ↥hatH →* Matrix (Fin 3) (Fin 3) FieldFour where
  toFun h := hatM22F 0 * gmat h * hatM22R0
  map_one' := by
    change hatM22F 0 * 1 * hatM22R0 = 1
    rw [Matrix.mul_one, hatM22F0_mul_R0]
  map_mul' g h := by
    change hatM22F 0 * (gmat g * gmat h) * hatM22R0 =
      hatM22F 0 * gmat g * hatM22R0 * (hatM22F 0 * gmat h * hatM22R0)
    calc hatM22F 0 * (gmat g * gmat h) * hatM22R0 = hatM22F 0 * gmat g * gmat h * hatM22R0 := by
          simp only [Matrix.mul_assoc]
      _ = hatM22F 0 * gmat g * hatM22R0 * hatM22F 0 * gmat h * hatM22R0 := by
          rw [← F0_mul_of_mem g.2]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem rep3b_apply (h : ↥hatH) : rep3b h = hatM22F 0 * gmat h * hatM22R0 := rfl

section General

variable {G : Type*} [Group G] {n : ℕ}

@[expose] noncomputable def dualRep (M : G →* Matrix (Fin n) (Fin n) FieldFour) :
    G →* Matrix (Fin n) (Fin n) FieldFour where
  toFun g := (M g⁻¹).transpose
  map_one' := by rw [inv_one, map_one, Matrix.transpose_one]
  map_mul' g h := by rw [_root_.mul_inv_rev, map_mul, Matrix.transpose_mul]

@[expose] noncomputable def frobRep (M : G →* Matrix (Fin n) (Fin n) FieldFour) :
    G →* Matrix (Fin n) (Fin n) FieldFour :=
  (FieldFour.frob.mapMatrix : Matrix (Fin n) (Fin n) FieldFour →+*
    Matrix (Fin n) (Fin n) FieldFour).toMonoidHom.comp M

theorem dualRep_apply (M : G →* Matrix (Fin n) (Fin n) FieldFour) (g : G) :
    dualRep M g = (M g⁻¹).transpose := rfl

theorem frobRep_apply (M : G →* Matrix (Fin n) (Fin n) FieldFour) (g : G) :
    frobRep M g = (M g).map FieldFour.frob := rfl

end General

@[expose] def trV : Fin 9 → FieldFour := ![1, 0, 0, 0, 1, 0, 0, 0, 1]

theorem trV_apply (i j : Fin 3) :
    trV (finProdFinEquiv (i, j)) = if i = j then 1 else 0 := by
  revert i j
  decide

theorem trV_vecMul_kron {A B : Matrix (Fin 3) (Fin 3) FieldFour} (h : A.transpose * B = 1) :
    trV ᵥ* Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) = trV := by
  funext x
  obtain ⟨⟨k, l⟩, rfl⟩ := finProdFinEquiv.surjective x
  have hsum : (trV ᵥ* Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B))
      (finProdFinEquiv (k, l)) = ∑ p : Fin 3 × Fin 3,
        trV (finProdFinEquiv p) * (A p.1 k * B p.2 l) := by
    rw [Matrix.vecMul, dotProduct]
    exact (Fintype.sum_equiv finProdFinEquiv
      (fun p => trV (finProdFinEquiv p) * (A p.1 k * B p.2 l))
      (fun y => trV y * Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) y
        (finProdFinEquiv (k, l)))
      (fun p => by simp [Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply])).symm
  rw [hsum, Fintype.sum_prod_type]
  simp only [trV_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  have := congrFun (congrFun h k) l
  rw [Matrix.mul_apply] at this
  simp only [Matrix.transpose_apply] at this
  rw [this, Matrix.one_apply]

theorem hatM22B8_mul_P8 :
    hatM22B8 * hatM22P8 = 1 + Matrix.vecMulVec (Pi.single 0 1) trV := by decide +kernel

theorem trV_vecMul_B8 : trV ᵥ* hatM22B8 = 0 := by decide +kernel

theorem hatM22P8_mul_B8 : hatM22P8 * hatM22B8 = 1 := by decide +kernel

@[expose] noncomputable def rep33 : ↥hatH →* Matrix (Fin (3 * 3)) (Fin (3 * 3)) FieldFour :=
  kronRep rep3a (dualRep rep3a)

theorem rep33_inv (g : ↥hatH) :
    rep33 g * hatM22B8 = hatM22B8 * (hatM22P8 * rep33 g * hatM22B8) := by
  have htr : trV ᵥ* rep33 g = trV := by
    apply trV_vecMul_kron
    rw [dualRep_apply, ← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.transpose_one]
  have h0 : Matrix.vecMulVec (Pi.single (0 : Fin 9) (1 : FieldFour)) trV *
      (rep33 g * hatM22B8) = 0 := by
    rw [Matrix.vecMulVec_mul, ← Matrix.vecMul_vecMul, htr, trV_vecMul_B8]
    funext i j
    simp [Matrix.vecMulVec]
  calc rep33 g * hatM22B8
      = (1 + Matrix.vecMulVec (Pi.single 0 1) trV) * (rep33 g * hatM22B8) := by
        rw [Matrix.add_mul, h0, add_zero, Matrix.one_mul]
    _ = hatM22B8 * (hatM22P8 * rep33 g * hatM22B8) := by
        rw [← hatM22B8_mul_P8]
        simp only [Matrix.mul_assoc]

@[expose] noncomputable def rep8 : ↥hatH →* Matrix (Fin 8) (Fin 8) FieldFour :=
  subRep rep33 hatM22B8 hatM22P8 hatM22P8_mul_B8 rep33_inv

@[expose] noncomputable def rep9 : ↥hatH →* Matrix (Fin (3 * 3)) (Fin (3 * 3)) FieldFour :=
  kronRep (dualRep rep3a) (frobRep rep3a)

@[expose] noncomputable def rep24a : ↥hatH →* Matrix (Fin (8 * 3)) (Fin (8 * 3)) FieldFour :=
  kronRep rep8 (frobRep (dualRep rep3a))

@[expose] noncomputable def rep24b : ↥hatH →* Matrix (Fin (3 * 8)) (Fin (3 * 8)) FieldFour :=
  kronRep rep3a (frobRep rep8)

namespace Blk

theorem length_blk3a (w : List ℤ) : (blk3a w).length = 3 := by
  rw [blk3a, PM.length_mul, PM.length_ofMat]

theorem length_blk8 (w : List ℤ) : (blk8 w).length = 8 := by
  rw [blk8, PM.length_mul, PM.length_ofMat]

theorem wordΓ_invW_mem {w : List ℤ} (hw : wordΓ w ∈ hatH) : wordΓ (invW w) ∈ hatH := by
  rw [wordΓ_invW]
  exact hatH.inv_mem hw

@[expose] def hOf {w : List ℤ} (hw : wordΓ w ∈ hatH) : ↥hatH := ⟨wordΓ w, hw⟩

theorem hOf_invW {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    hOf (wordΓ_invW_mem hw) = (hOf hw)⁻¹ := Subtype.ext (wordΓ_invW w)

theorem toMat_blk3a {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat 3 3 (blk3a w) = rep3a (hOf hw) := by
  rw [blk3a, PM.toMat_mul (n := 6) _ _ (by rw [PM.length_mul]; exact length_pWord w)
      (PM.length_ofMat _),
    PM.toMat_mul (n := 6) _ _ (PM.length_ofMat _) (length_pWord w), PM.toMat_ofMat,
    PM.toMat_ofMat, ← gmat_wordΓ, rep3a_apply]
  rfl

theorem toMat_blk3b {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat 3 3 (blk3b w) = rep3b (hOf hw) := by
  rw [blk3b, PM.toMat_mul (n := 6) _ _ (by rw [PM.length_mul]; exact length_pWord w)
      (PM.length_ofMat _),
    PM.toMat_mul (n := 6) _ _ (PM.length_ofMat _) (length_pWord w), PM.toMat_ofMat,
    PM.toMat_ofMat, ← gmat_wordΓ, rep3b_apply]
  rfl

theorem toMat_dual3a {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat 3 3 (PM.transp 3 (blk3a (invW w))) = dualRep rep3a (hOf hw) := by
  rw [PM.toMat_transp _ (length_blk3a _), toMat_blk3a (wordΓ_invW_mem hw), hOf_invW,
    dualRep_apply]

theorem toMat_blk9 {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat (3 * 3) (3 * 3) (blk9 w) = rep9 (hOf hw) := by
  rw [blk9, PM.toMat_kron _ _ (PM.length_transp _ _)
      (by rw [PM.frob, List.length_map, length_blk3a]),
    toMat_dual3a hw, PM.toMat_frob _ (length_blk3a w), toMat_blk3a hw]
  rfl

theorem toMat_rep33 {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat (3 * 3) (3 * 3) (PM.kron 3 3 (blk3a w) (PM.transp 3 (blk3a (invW w)))) =
      rep33 (hOf hw) := by
  rw [PM.toMat_kron _ _ (length_blk3a w) (PM.length_transp _ _), toMat_dual3a hw,
    toMat_blk3a hw]
  rfl

theorem toMat_blk8 {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat 8 8 (blk8 w) = rep8 (hOf hw) := by
  rw [blk8, PM.toMat_mul (n := 9) _ _ (by
      rw [PM.length_mul, PM.length_kron, length_blk3a, PM.length_transp]) (PM.length_ofMat _),
    PM.toMat_mul (n := 9) _ _ (PM.length_ofMat _) (by
      rw [PM.length_kron, length_blk3a, PM.length_transp]),
    PM.toMat_ofMat, PM.toMat_ofMat]
  have h := toMat_rep33 hw
  change hatM22P8 * PM.toMat (3 * 3) (3 * 3) _ * hatM22B8 = _
  rw [h]
  rfl

theorem toMat_blk24a {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat (8 * 3) (8 * 3) (blk24a w) = rep24a (hOf hw) := by
  rw [blk24a, PM.toMat_kron _ _ (length_blk8 w)
      (by rw [PM.frob, List.length_map, PM.length_transp]),
    toMat_blk8 hw, PM.toMat_frob _ (PM.length_transp _ _), toMat_dual3a hw]
  rfl

theorem toMat_blk24b {w : List ℤ} (hw : wordΓ w ∈ hatH) :
    PM.toMat (3 * 8) (3 * 8) (blk24b w) = rep24b (hOf hw) := by
  rw [blk24b, PM.toMat_kron _ _ (length_blk3a w) (by rw [PM.frob, List.length_map, length_blk8]),
    toMat_blk3a hw, PM.toMat_frob _ (length_blk8 w), toMat_blk8 hw]
  rfl

end Blk

end CFSG.Quasithin.HM22
