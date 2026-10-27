module

public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K) {r : ℕ}

theorem oddUni_mul (x x' : Fin r → K) (C C' : Matrix (Fin r) (Fin r) K) :
    oddUni hK x C * oddUni hK x' C' =
      oddUni hK (x + x') (C + C' - vecMulVec x fun j => hK.bar (x' j)) := by
  rw [oddUni, oddUni, oddUni, blk3_mul]
  congr 1
  · simp
  · ext i k
    simp [add_comm]
  · ext i j
    simp [vecMulVec, mul_apply, sub_eq_add_neg, add_comm]
    ring
  · simp
  · ext k j
    simp [add_comm]
  · simp

theorem blk3_one : (blk3 (1 : Matrix (Fin r) (Fin r) K) (0 : Matrix (Fin r) (Fin 1) K)
    (0 : Matrix (Fin r) (Fin r) K) (1 : Matrix (Fin 1) (Fin 1) K)
    (0 : Matrix (Fin 1) (Fin r) K) (1 : Matrix (Fin r) (Fin r) K)) = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp [one_apply]

theorem oddUni_zero : oddUni hK (0 : Fin r → K) 0 = 1 := by
  rw [oddUni, ← blk3_one]
  congr 1
  ext i k; simp

theorem oddDiag_mul (A A' : Matrix (Fin r) (Fin r) K) (d d' : K) :
    oddDiag hK A d * oddDiag hK A' d' = oddDiag hK (A * A') (d * d') := by
  rw [oddDiag, oddDiag, oddDiag, blk3_mul, barInvT_mul]
  congr 1
  all_goals first | rfl | simp | (ext k l; simp [mul_apply])
end CFSG.RankThree.PartOne.U5K.Hyp

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K) {r : ℕ}

theorem barInvT_one : barInvT hK (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [barInvT, Matrix.map_one _ (map_zero _) (map_one _), inv_one, transpose_one]

theorem oddDiag_one : oddDiag hK (1 : Matrix (Fin r) (Fin r) K) 1 = 1 := by
  rw [oddDiag, barInvT_one, ← blk3_one]
  congr 1
  ext k l; simp [one_apply, Subsingleton.elim k l]

theorem oddDiag_mul_oddUni_comm {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) {d : K}
    (hd : hK.bar d * d = 1) (x : Fin r → K) (C : Matrix (Fin r) (Fin r) K) :
    oddDiag hK A d * oddUni hK x C =
      oddUni hK (d⁻¹ • (A *ᵥ x)) (A * C * (A.map hK.bar)ᵀ) * oddDiag hK A d := by
  have hd0 : d ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have hAD := conjTranspose_mul_barInvT (h := hK) hA
  rw [oddDiag_mul_oddUni, oddUni, oddDiag, blk3_mul]
  congr 1
  · simp
  · ext i k
    simp [mul_apply, mulVec, dotProduct]
    field_simp
  · ext i j
    simp
    rw [Matrix.mul_assoc, hAD, Matrix.mul_one]
  · simp
  · ext k j
    have hent : ∀ k j, ∑ i, hK.bar (A i k) * barInvT hK A i j = if k = j then 1 else 0 := by
      intro k j
      have := congrFun (congrFun hAD k) j
      simpa [mul_apply, one_apply] using this
    have hbd : (hK.bar d)⁻¹ = d := inv_eq_of_mul_eq_one_right hd
    simp [mul_apply, mulVec, dotProduct]
    have hL : d * hK.bar (x j) = (hK.bar d)⁻¹ * hK.bar (x j) := by rw [hbd]
    rw [hL]
    calc (hK.bar d)⁻¹ * hK.bar (x j)
        = (hK.bar d)⁻¹ * ∑ k, hK.bar (x k) * (if k = j then 1 else 0) := by simp
      _ = (hK.bar d)⁻¹ * ∑ k, hK.bar (x k) * ∑ i, hK.bar (A i k) * barInvT hK A i j := by
          simp_rw [hent]
      _ = ∑ i, ((hK.bar d)⁻¹ * ∑ k, hK.bar (A i k) * hK.bar (x k)) * barInvT hK A i j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  · simp


section Subgroups

variable {hK}

@[expose] def mat (g : hypSU hK 2 1) : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
  ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K)

theorem mat_mul (g g' : hypSU hK 2 1) : mat (g * g') = mat g * mat g' := rfl

theorem mat_one : mat (1 : hypSU hK 2 1) = 1 := rfl

theorem mat_injective : Function.Injective (mat : hypSU hK 2 1 → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem mat_inv_eq {g : hypSU hK 2 1} {M : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (h : M * mat g = 1) : mat g⁻¹ = M := by
  have h1 : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  exact (left_inv_eq_right_inv h h1).symm

variable (hK)

@[expose] def Ssub : Subgroup (hypSU hK 2 1) where
  carrier := {g | g ∈ hypUnitriangular hK 2 1 ∧
    ∃ (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K), mat g = oddUni hK x C}
  mul_mem' := by
    rintro g g' ⟨hg, x, C, hgC⟩ ⟨hg', x', C', hgC'⟩
    exact ⟨mul_mem hg hg', x + x', C + C' - vecMulVec x fun j => hK.bar (x' j),
      by rw [mat_mul, hgC, hgC', oddUni_mul]⟩
  one_mem' := ⟨one_mem _, 0, 0, by rw [mat_one, oddUni_zero]⟩
  inv_mem' := by
    rintro g ⟨hg, x, C, hgC⟩
    refine ⟨inv_mem hg, -x, -C - vecMulVec x (fun j => hK.bar (x j)), mat_inv_eq ?_⟩
    rw [hgC, oddUni_mul]
    have : (-C - vecMulVec x (fun j => hK.bar (x j)) + C -
        vecMulVec (-x) fun j => hK.bar (x j)) = 0 := by
      ext i j; simp [vecMulVec]; ring
    rw [this, neg_add_cancel, oddUni_zero]

@[expose] def Vsub : Subgroup (hypSU hK 2 1) where
  carrier := {g | g ∈ hypUnitriangular hK 2 1 ∧
    ∃ Y : Matrix (Fin 2) (Fin 2) K, mat g = oddUni hK 0 Y}
  mul_mem' := by
    rintro g g' ⟨hg, Y, hgC⟩ ⟨hg', Y', hgC'⟩
    refine ⟨mul_mem hg hg', Y + Y', ?_⟩
    rw [mat_mul, hgC, hgC', oddUni_mul]
    simp
  one_mem' := ⟨one_mem _, 0, by rw [mat_one, oddUni_zero]⟩
  inv_mem' := by
    rintro g ⟨hg, Y, hgC⟩
    refine ⟨inv_mem hg, -Y, mat_inv_eq ?_⟩
    rw [hgC, oddUni_mul]
    simp [oddUni_zero]

end Subgroups


section Coordinates

variable {hK}

theorem oddUni_apply_ee (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    oddUni hK x C (.inl i) (.inl j) = (1 : Matrix (Fin 2) (Fin 2) K) i j := rfl

theorem oddUni_apply_ez (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    oddUni hK x C (.inl i) (.inr (.inl 0)) = x i := by
  simp [oddUni]

theorem oddUni_apply_ef (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    oddUni hK x C (.inl i) (.inr (.inr j)) = C i j := rfl

theorem oddUni_inj {x x' : Fin 2 → K} {C C' : Matrix (Fin 2) (Fin 2) K}
    (h : oddUni hK x C = oddUni hK x' C') : x = x' ∧ C = C' := by
  refine ⟨funext fun i => ?_, Matrix.ext fun i j => ?_⟩
  · rw [← oddUni_apply_ez (hK := hK) x C i, h, oddUni_apply_ez]
  · rw [← oddUni_apply_ef (hK := hK) x C i j, h, oddUni_apply_ef]

theorem exists_coord {g : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1) :
    ∃ (a : K) (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K),
      C + (C.map hK.bar)ᵀ = -vecMulVec x (fun j => hK.bar (x j)) ∧
      mat g = oddDiag hK !![1, a; 0, 1] 1 * oddUni hK x C := by
  obtain ⟨A, C, x, hA, hC, hg'⟩ :=
    (exists_mem_hypUnitriangular_odd_iff (h := hK) (r := 2) (mat g)).1 ⟨g, hg, rfl⟩
  have hA10 : A 1 0 = 0 := hA.1 (show (0 : Fin 2) < 1 by decide)
  obtain ⟨a, hAeq⟩ : ∃ a : K, A = !![1, a; 0, 1] := by
    refine ⟨A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA10, hA.2 0, hA.2 1]
  exact ⟨a, x, C, hC, by rw [hg', hAeq]⟩

theorem U_lower {g : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1) {a b : HypIndex 2 1}
    (hab : fullPos b < fullPos a) : mat g a b = 0 :=
  (mem_hypUnitriangular.mp hg).1 hab

theorem U_diag {g : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1) (a : HypIndex 2 1) :
    mat g a a = 1 :=
  (mem_hypUnitriangular.mp hg).2 a

@[expose] def aOf (g : hypSU hK 2 1) : K := mat g (.inl 0) (.inl 1)

theorem aOf_mul {g g' : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1)
    (hg' : g' ∈ hypUnitriangular hK 2 1) : aOf (g * g') = aOf g + aOf g' := by
  have h1 : mat g' (.inr (.inl 0)) (.inl 1) = 0 := U_lower hg' (by simp)
  have h2 : mat g' (.inr (.inr 0)) (.inl 1) = 0 := U_lower hg' (by simp)
  have h3 : mat g' (.inr (.inr 1)) (.inl 1) = 0 := U_lower hg' (by simp)
  have d0 := U_diag hg (.inl 0)
  have d1 := U_diag hg' (.inl 1)
  unfold aOf
  rw [mat_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [Fin.sum_univ_two, h1, h2, h3, d0, d1]
  ring

theorem mem_Ssub_iff {g : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1) :
    g ∈ Ssub hK ↔ aOf g = 0 := by
  constructor
  · rintro ⟨-, x, C, hgC⟩
    unfold aOf
    rw [hgC, oddUni_apply_ee]
    simp
  · intro ha
    obtain ⟨a, x, C, -, hg'⟩ := exists_coord hg
    have : a = 0 := by
      have h1 : aOf g = a := by
        unfold aOf
        rw [hg', oddDiag_mul_oddUni]
        simp
      rw [← h1, ha]
    subst this
    refine ⟨hg, x, C, ?_⟩
    rw [hg']
    have : (!![1, (0 : K); 0, 1] : Matrix (Fin 2) (Fin 2) K) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this, oddDiag_one, one_mul]

end Coordinates


section Basic

variable {hK}

theorem Vsub_le_Ssub : Vsub hK ≤ Ssub hK := by
  rintro g ⟨hg, Y, hY⟩
  exact ⟨hg, 0, Y, hY⟩

theorem Ssub_le_Usub : Ssub hK ≤ hypUnitriangular hK 2 1 := fun _ hg => hg.1

theorem mem_Vsub_iff {g : hypSU hK 2 1} (hg : g ∈ Ssub hK) :
    g ∈ Vsub hK ↔ ∀ i, mat g (.inl i) (.inr (.inl 0)) = 0 := by
  constructor
  · rintro ⟨-, Y, hY⟩ i
    rw [hY, oddUni_apply_ez]
    rfl
  · intro h0
    obtain ⟨hgU, x, C, hgC⟩ := hg
    refine ⟨hgU, C, ?_⟩
    have : x = 0 := funext fun i => by
      rw [← oddUni_apply_ez (hK := hK) x C i, ← hgC, h0 i]
      rfl
    rw [hgC, this]

theorem oddUni_mul_self (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) :
    oddUni hK x C * oddUni hK x C = oddUni hK 0 (vecMulVec x fun j => hK.bar (x j)) := by
  have := hK.charP
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  rw [oddUni_mul]
  congr 1
  · funext i; simp [h2]
  · ext i j; simp [h2, vecMulVec, CharTwo.neg_eq]

theorem oddUni_sq_eq_one_iff (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) :
    oddUni hK x C * oddUni hK x C = 1 ↔ x = 0 := by
  rw [oddUni_mul_self, ← oddUni_zero hK (r := 2)]
  constructor
  · intro h
    have h1 := (oddUni_inj h).2
    funext i
    have h2 := congrFun (congrFun h1 i) i
    simpa [vecMulVec] using h2
  · rintro rfl
    simp

theorem oddUni_comm_zero (x : Fin 2 → K) (C Y : Matrix (Fin 2) (Fin 2) K) :
    oddUni hK x C * oddUni hK 0 Y = oddUni hK 0 Y * oddUni hK x C := by
  rw [oddUni_mul, oddUni_mul]
  congr 1
  · simp
  · ext i j; simp [vecMulVec, add_comm]

theorem oddDiag_mul_oddUni_zero {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det) {d : K}
    (hd : hK.bar d * d = 1) (Y : Matrix (Fin 2) (Fin 2) K) :
    oddDiag hK A d * oddUni hK 0 Y = oddUni hK 0 (A * Y * (A.map hK.bar)ᵀ) * oddDiag hK A d := by
  have := oddDiag_mul_oddUni_comm hK hA hd (0 : Fin 2 → K) Y
  simpa using this

end Basic


section Herm

variable {hK}

theorem trace_surj {a : K} (ha : hK.bar a = a) : ∃ c : K, c + hK.bar c = a := by
  have : Finite K := hK.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hK.charP
  have hbar : ∀ c, hK.bar c = CFSG.LieType.BorelTits.unitaryInvolution K 2 f c := fun c => by
    rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  obtain ⟨c, hc⟩ := CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq (p := 2) (f := f)
    hK.card_eq_sq (a := a) (by rw [← hbar]; exact ha)
  exact ⟨c, by rw [hbar]; exact hc⟩

variable (hK)

@[expose] def IsHerm (Y : Matrix (Fin 2) (Fin 2) K) : Prop := Y + (Y.map hK.bar)ᵀ = 0

variable {hK}

theorem isHerm_iff {Y : Matrix (Fin 2) (Fin 2) K} :
    IsHerm hK Y ↔ hK.bar (Y 0 0) = Y 0 0 ∧ hK.bar (Y 1 1) = Y 1 1 ∧ Y 1 0 = hK.bar (Y 0 1) := by
  have := hK.charP
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  unfold IsHerm
  constructor
  · intro h
    have e00 := congrFun (congrFun h 0) 0
    have e11 := congrFun (congrFun h 1) 1
    have e01 := congrFun (congrFun h 0) 1
    simp at e00 e11 e01
    refine ⟨?_, ?_, ?_⟩
    · linear_combination e00 - h2 (Y 0 0)
    · linear_combination e11 - h2 (Y 1 1)
    · have : hK.bar (Y 1 0) = Y 0 1 := by linear_combination e01 - h2 (Y 0 1)
      rw [← this, hK.bar_bar]
  · rintro ⟨h00, h11, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h10, hK.bar_bar, h2]

theorem constraint_of_oddUni {g : hypSU hK 2 1} {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K}
    (hg : mat g = oddUni hK x C) :
    C + (C.map hK.bar)ᵀ = -vecMulVec x fun j => hK.bar (x j) := by
  have hgram := (mem_hypSU.mp g.2).1
  change ((mat g).map hK.bar)ᵀ * hypGram 2 1 K * mat g = hypGram 2 1 K at hgram
  rw [hg, oddUni] at hgram
  obtain ⟨-, -, -, h4⟩ := (blk3_gram_iff hK _ _ _ _ _ _).mp hgram
  ext i j
  have := congrFun (congrFun h4 i) j
  simp [Matrix.mul_apply, replicateRow, vecMulVec, hK.bar_bar] at this ⊢
  linear_combination this

theorem exists_mem_Ssub {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K}
    (hC : C + (C.map hK.bar)ᵀ = -vecMulVec x fun j => hK.bar (x j)) :
    ∃ g ∈ Ssub hK, mat g = oddUni hK x C := by
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_odd_iff (h := hK) (r := 2)
    (oddUni hK x C)).2 ⟨1, C, x, ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij),
        fun i => Matrix.one_apply_eq i⟩, hC, by
      rw [oddDiag_one, one_mul]⟩
  exact ⟨g, ⟨hg, x, C, hgm⟩, hgm⟩

theorem exists_mem_Vsub {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm hK Y) :
    ∃ g ∈ Vsub hK, mat g = oddUni hK 0 Y := by
  obtain ⟨g, hg, hgm⟩ := exists_mem_Ssub (hK := hK) (x := 0) (C := Y) (by
    have : vecMulVec (0 : Fin 2 → K) (fun j => hK.bar ((0 : Fin 2 → K) j)) = 0 := by
      ext i j; simp [vecMulVec]
    rw [this, neg_zero]; exact hY)
  exact ⟨g, ⟨hg.1, Y, hgm⟩, hgm⟩

theorem herm_of_mem_Vsub {g : hypSU hK 2 1} {Y : Matrix (Fin 2) (Fin 2) K}
    (hg : mat g = oddUni hK 0 Y) : IsHerm hK Y := by
  have := constraint_of_oddUni hg
  have h0 : vecMulVec (0 : Fin 2 → K) (fun j => hK.bar ((0 : Fin 2 → K) j)) = 0 := by
    ext i j; simp [vecMulVec]
  rw [h0, neg_zero] at this
  exact this

theorem card_herm : Nat.card {Y : Matrix (Fin 2) (Fin 2) K // IsHerm hK Y} = (2 ^ f) ^ 4 := by
  have h := card_matrix_of_upper K (r := 2) (fun _ => (hK.fixedField : Set K))
    (fun _ _ => hK.bar)
  have e : {Y : Matrix (Fin 2) (Fin 2) K // IsHerm hK Y} ≃
      {C : Matrix (Fin 2) (Fin 2) K // (∀ i, C i i ∈ (fun _ => (hK.fixedField : Set K)) i) ∧
        ∀ i j, j < i → C i j = (fun _ _ => hK.bar) i j (C j i)} :=
    Equiv.subtypeEquivRight fun Y => by
      rw [isHerm_iff]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨fun i => ?_, fun i j hji => ?_⟩
        · fin_cases i
          · exact h0
          · exact h1
        · fin_cases i <;> fin_cases j <;> simp at hji ⊢
          exact h2
      · rintro ⟨hd, hl⟩
        exact ⟨hd 0, hd 1, hl 1 0 (by decide)⟩
  rw [Nat.card_congr e, h]
  simp only [SetLike.coe_sort_coe, hK.card_fixedField, Fin.prod_univ_two, hK.card_eq_sq]
  norm_num [Nat.choose_two_right]
  ring

@[expose] def Yof (g : hypSU hK 2 1) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => mat g (.inl i) (.inr (.inr j))

theorem Yof_eq {g : hypSU hK 2 1} {Y : Matrix (Fin 2) (Fin 2) K} (h : mat g = oddUni hK 0 Y) :
    Yof g = Y := by
  ext i j
  simp only [Yof, Matrix.of_apply]
  rw [h, oddUni_apply_ef]

theorem card_Vsub : Nat.card (Vsub hK) = (2 ^ f) ^ 4 := by
  rw [← card_herm (hK := hK)]
  have hh : ∀ g : Vsub hK, IsHerm hK (Yof g.1) := by
    rintro ⟨g, hg, Y, hY⟩
    rw [Yof_eq hY]
    exact herm_of_mem_Vsub hY
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨Yof g.1, hh g⟩) ⟨?_, ?_⟩)
  · rintro ⟨g, hg, Y, hY⟩ ⟨g', hg', Y', hY'⟩ h
    have h1 : Yof g = Yof g' := congrArg Subtype.val h
    rw [Yof_eq hY, Yof_eq hY'] at h1
    subst h1
    exact Subtype.ext (mat_injective (hY.trans hY'.symm))
  · rintro ⟨Y, hY⟩
    obtain ⟨g, hg, hgm⟩ := exists_mem_Vsub hY
    exact ⟨⟨g, hg⟩, Subtype.ext (Yof_eq hgm)⟩

end Herm


section Levi

variable {hK}

theorem oddUni_blockTriangular (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) :
    (oddUni hK x C).BlockTriangular fullPos :=
  blockTriangular_blk3 (fun i j hij => Matrix.one_apply_ne (ne_of_gt hij))
    (fun k l hkl => by
      exfalso
      have := Subsingleton.elim k l
      subst this
      exact lt_irrefl _ hkl)
    (fun i j hij => Matrix.one_apply_ne (ne_of_lt (OrderDual.toDual_lt_toDual.mp hij))) _ _ _

theorem oddUni_diag (x : Fin 2 → K) (C : Matrix (Fin 2) (Fin 2) K) (a : HypIndex 2 1) :
    oddUni hK x C a a = 1 := by
  rcases a with i | k | i
  · simp [oddUni]
  · fin_cases k
    simp [oddUni]
  · simp [oddUni]

theorem mem_U_of_oddUni {g : hypSU hK 2 1} {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K}
    (h : mat g = oddUni hK x C) : g ∈ hypUnitriangular hK 2 1 := by
  rw [mem_hypUnitriangular]
  refine ⟨?_, fun a => ?_⟩
  · have h' : (mat g).BlockTriangular fullPos := by rw [h]; exact oddUni_blockTriangular x C
    exact h'
  · have := oddUni_diag (hK := hK) x C a
    rw [← h] at this
    exact this

theorem mem_Ssub_of_mat {g : hypSU hK 2 1} {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K}
    (h : mat g = oddUni hK x C) : g ∈ Ssub hK := ⟨mem_U_of_oddUni h, x, C, h⟩

theorem mem_Vsub_of_mat {g : hypSU hK 2 1} {Y : Matrix (Fin 2) (Fin 2) K}
    (h : mat g = oddUni hK 0 Y) : g ∈ Vsub hK := ⟨mem_U_of_oddUni h, Y, h⟩

@[expose] noncomputable def lev (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) : hypSU hK 2 1 :=
  mkHypSU hK (oddDiag hK A (hK.bar A.det / A.det))
    (by
      have := oddProd_gram (h := hK) (C := (0 : Matrix (Fin 2) (Fin 2) K))
        (x := (0 : Fin 2 → K)) hA (bar_mul_self_of_eq_div hA rfl) (by ext i j; simp [vecMulVec])
      rwa [oddUni_zero, mul_one] at this)
    (by
      have := det_oddProd (h := hK) hA (hK.bar A.det / A.det) (0 : Fin 2 → K)
        (0 : Matrix (Fin 2) (Fin 2) K)
      rw [oddUni_zero, mul_one] at this
      rw [this]
      have h0 : A.det ≠ 0 := hA.ne_zero
      have h0' : hK.bar A.det ≠ 0 := (map_ne_zero hK.bar).mpr h0
      field_simp)

theorem mat_lev (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    mat (lev A hA : hypSU hK 2 1) = oddDiag hK A (hK.bar A.det / A.det) := rfl

theorem lev_conj (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) {g : hypSU hK 2 1}
    {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K} (hg : mat g = oddUni hK x C) :
    mat (lev A hA * g * (lev A hA)⁻¹) = oddUni hK ((hK.bar A.det / A.det)⁻¹ • (A *ᵥ x))
      (A * C * (A.map hK.bar)ᵀ) := by
  have h1 := oddDiag_mul_oddUni_comm hK hA (bar_mul_self_of_eq_div hA rfl) x C
  have h2 : mat (lev A hA : hypSU hK 2 1) * mat g = oddUni hK ((hK.bar A.det / A.det)⁻¹ •
      (A *ᵥ x)) (A * C * (A.map hK.bar)ᵀ) * mat (lev A hA : hypSU hK 2 1) := by
    rw [mat_lev, hg]; exact h1
  have h3 : mat (lev A hA : hypSU hK 2 1) * mat (lev A hA : hypSU hK 2 1)⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [mat_mul, mat_mul, h2, Matrix.mul_assoc, h3, Matrix.mul_one]

theorem lev_conj_mem_Ssub (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) {g : hypSU hK 2 1}
    (hg : g ∈ Ssub hK) : lev A hA * g * (lev A hA)⁻¹ ∈ Ssub hK := by
  obtain ⟨-, x, C, hgC⟩ := hg
  exact mem_Ssub_of_mat (lev_conj A hA hgC)

theorem lev_conj_mem_Vsub (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) {g : hypSU hK 2 1}
    (hg : g ∈ Vsub hK) : lev A hA * g * (lev A hA)⁻¹ ∈ Vsub hK := by
  obtain ⟨-, Y, hY⟩ := hg
  have := lev_conj A hA hY
  simp only [mulVec_zero, smul_zero] at this
  exact mem_Vsub_of_mat this

theorem U_conj_V {u v : hypSU hK 2 1} {a : K} {x : Fin 2 → K} {C Y : Matrix (Fin 2) (Fin 2) K}
    (hu : mat u = oddDiag hK !![1, a; 0, 1] 1 * oddUni hK x C) (hv : mat v = oddUni hK 0 Y) :
    mat (u * v * u⁻¹) = oddUni hK 0 (!![1, a; 0, 1] * Y * ((!![1, a; 0, 1]).map hK.bar)ᵀ) := by
  have hA : IsUnit (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) K).det := by
    simp [Matrix.det_fin_two]
  have h1 : mat u * mat v = oddUni hK 0 (!![1, a; 0, 1] * Y * ((!![1, a; 0, 1]).map hK.bar)ᵀ) *
      mat u := by
    rw [hu, hv, Matrix.mul_assoc, oddUni_comm_zero, ← Matrix.mul_assoc,
      oddDiag_mul_oddUni_zero hA (by simp), Matrix.mul_assoc]
  have h3 : mat u * mat u⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [mat_mul, mat_mul, h1, Matrix.mul_assoc, h3, Matrix.mul_one]

theorem aOf_one : aOf (1 : hypSU hK 2 1) = 0 := by
  simp [aOf, mat_one]

theorem aOf_inv {g : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1) : aOf g⁻¹ = -aOf g := by
  have h := aOf_mul hg (inv_mem hg)
  rw [mul_inv_cancel, aOf_one] at h
  linear_combination -h

theorem conj_mem_Ssub {u s : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1) (hs : s ∈ Ssub hK) :
    u * s * u⁻¹ ∈ Ssub hK := by
  have hs' := Ssub_le_Usub hs
  have hmem : u * s * u⁻¹ ∈ hypUnitriangular hK 2 1 := mul_mem (mul_mem hu hs') (inv_mem hu)
  rw [mem_Ssub_iff hmem, aOf_mul (mul_mem hu hs') (inv_mem hu), aOf_mul hu hs', aOf_inv hu,
    (mem_Ssub_iff hs').1 hs]
  ring

theorem conj_mem_Vsub {u v : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1)
    (hv : v ∈ Vsub hK) : u * v * u⁻¹ ∈ Vsub hK := by
  obtain ⟨a, x, C, -, hu'⟩ := exists_coord hu
  obtain ⟨-, Y, hY⟩ := hv
  exact mem_Vsub_of_mat (U_conj_V hu' hY)

theorem Vsub_comm {v v' : hypSU hK 2 1} (hv : v ∈ Vsub hK) (hv' : v' ∈ Vsub hK) :
    v * v' = v' * v := by
  obtain ⟨-, Y, hY⟩ := hv
  obtain ⟨-, Y', hY'⟩ := hv'
  apply mat_injective
  rw [mat_mul, mat_mul, hY, hY', oddUni_mul, oddUni_mul]
  have : Y + Y' = Y' + Y := add_comm _ _
  simp [this]

theorem Vsub_sq {v : hypSU hK 2 1} (hv : v ∈ Vsub hK) : v * v = 1 := by
  obtain ⟨-, Y, hY⟩ := hv
  apply mat_injective
  have h0 : vecMulVec (0 : Fin 2 → K) (fun j => hK.bar ((0 : Fin 2 → K) j)) = 0 := by
    ext i j; simp [vecMulVec]
  rw [mat_mul, hY, oddUni_mul_self, h0, mat_one, oddUni_zero]

theorem mem_Vsub_of_sq {g : hypSU hK 2 1} (hg : g ∈ Ssub hK) (h : g * g = 1) : g ∈ Vsub hK := by
  obtain ⟨hgU, x, C, hgC⟩ := hg
  have h1 : mat (g * g) = 1 := by rw [h, mat_one]
  rw [mat_mul, hgC] at h1
  have := (oddUni_sq_eq_one_iff (hK := hK) x C).1 h1
  subst this
  exact ⟨hgU, C, hgC⟩

theorem commute_Vsub_iff {u : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1) :
    (∀ v ∈ Vsub hK, u * v = v * u) ↔ u ∈ Ssub hK := by
  constructor
  · intro h
    obtain ⟨a, x, C, -, hu'⟩ := exists_coord hu
    obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub (hK := hK) (Y := !![0, 0; 0, 1]) (by
      rw [isHerm_iff]; simp)
    have h1 := U_conj_V hu' hvm
    have h2 : u * v * u⁻¹ = v := by rw [h v hv, mul_inv_cancel_right]
    rw [h2, hvm] at h1
    have h3 := (oddUni_inj h1).2
    have h4 := congrFun (congrFun h3 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h4
    rw [mem_Ssub_iff hu]
    have h5 : aOf u = a := by
      unfold aOf
      rw [hu', oddDiag_mul_oddUni]
      simp
    rw [h5]
    exact h4.symm
  · intro hs v hv
    obtain ⟨-, x, C, hx⟩ := hs
    obtain ⟨-, Y, hY⟩ := hv
    apply mat_injective
    rw [mat_mul, mat_mul, hx, hY, oddUni_comm_zero]

end Levi


section ElemAb

variable {hK}

theorem herm_Yof {g : hypSU hK 2 1} (hg : g ∈ Vsub hK) : IsHerm hK (Yof g) := by
  obtain ⟨-, Y, hY⟩ := hg
  rw [Yof_eq hY]
  exact herm_of_mem_Vsub hY

theorem aOf_eq_of_coord {u : hypSU hK 2 1} {a : K} {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K}
    (hu : mat u = oddDiag hK !![1, a; 0, 1] 1 * oddUni hK x C) : aOf u = a := by
  unfold aOf
  rw [hu, oddDiag_mul_oddUni]
  simp

theorem commute_Vsub_entries {u v : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1)
    (hv : v ∈ Vsub hK) (h : u * v = v * u) :
    aOf u * Yof v 1 1 = 0 ∧
      aOf u * Yof v 1 0 + Yof v 0 1 * hK.bar (aOf u) + aOf u * Yof v 1 1 * hK.bar (aOf u) = 0 := by
  obtain ⟨a, x, C, -, hu'⟩ := exists_coord hu
  obtain ⟨-, Y, hY⟩ := hv
  have h1 := U_conj_V hu' hY
  have h2 : u * v * u⁻¹ = v := by rw [h, mul_inv_cancel_right]
  rw [h2, hY] at h1
  have h3 := (oddUni_inj h1).2
  rw [aOf_eq_of_coord hu', Yof_eq hY]
  have e01 := congrFun (congrFun h3 0) 1
  have e00 := congrFun (congrFun h3 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e01 e00
  constructor
  · rcases e01 with h0 | h0 <;> simp [h0]
  · linear_combination (-1 : K) * e00

theorem Yof_ext {g g' : hypSU hK 2 1} (hg : g ∈ Vsub hK) (hg' : g' ∈ Vsub hK)
    (h00 : Yof g 0 0 = Yof g' 0 0) (h01 : Yof g 0 1 = Yof g' 0 1)
    (h11 : Yof g 1 1 = Yof g' 1 1) : g = g' := by
  have e1 := (isHerm_iff.1 (herm_Yof hg)).2.2
  have e2 := (isHerm_iff.1 (herm_Yof hg')).2.2
  obtain ⟨-, Y, hY⟩ := hg
  obtain ⟨-, Y', hY'⟩ := hg'
  have : Yof g = Yof g' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h11, e1, e2]
  apply mat_injective
  rw [hY, hY', ← Yof_eq hY, ← Yof_eq hY', this]

@[expose] noncomputable def aHom (F : Subgroup (hypSU hK 2 1))
    (hFU : F ≤ hypUnitriangular hK 2 1) : F →* Multiplicative K where
  toFun g := Multiplicative.ofAdd (aOf (g : hypSU hK 2 1))
  map_one' := by simp [aOf_one]
  map_mul' g g' := by
    simp only [Subgroup.coe_mul]
    rw [aOf_mul (hFU g.2) (hFU g'.2), ofAdd_add]

theorem aOf_eq_zero_of_mem_ker {F : Subgroup (hypSU hK 2 1)} {hFU : F ≤ hypUnitriangular hK 2 1}
    (k : (aHom F hFU).ker) : aOf (k.1 : hypSU hK 2 1) = 0 := by
  have h := k.2
  rw [MonoidHom.mem_ker] at h
  exact ofAdd_eq_one.mp h

theorem elemAb_card_le {F : Subgroup (hypSU hK 2 1)} (hFU : F ≤ hypUnitriangular hK 2 1)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hsq : ∀ x ∈ F, x * x = 1)
    {u₀ : hypSU hK 2 1} (hu₀ : u₀ ∈ F) (hα : aOf u₀ ≠ 0) : Nat.card F ≤ (2 ^ f) ^ 3 := by
  classical
  have : Finite K := hK.finite
  have hchar : CharP K 2 := hK.charP
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  set α₀ : K := aOf u₀ with hα₀
  have hα' : hK.bar α₀ ≠ 0 := (map_ne_zero hK.bar).mpr hα
  have hcard := Subgroup.card_ker_mul_card_range (aHom F hFU)
  have hkd : ∀ g ∈ F, aOf g = 0 → g ∈ Vsub hK ∧ Yof g 1 1 = 0 ∧
      hK.bar (Yof g 0 1) * α₀ = Yof g 0 1 * hK.bar α₀ := by
    intro g hg hga
    have hgV : g ∈ Vsub hK := mem_Vsub_of_sq ((mem_Ssub_iff (hFU hg)).2 hga) (hsq g hg)
    obtain ⟨e1, e2⟩ := commute_Vsub_entries (hFU hu₀) hgV (hcomm u₀ hu₀ g hg)
    have hY11 : Yof g 1 1 = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · exact absurd h hα
      · exact h
    have hh := (isHerm_iff.1 (herm_Yof hgV)).2.2
    refine ⟨hgV, hY11, ?_⟩
    rw [hY11, hh] at e2
    linear_combination e2 - h2 (Yof g 0 1 * hK.bar α₀)
  have hk0 : ∀ k : (aHom F hFU).ker, Yof (k.1 : hypSU hK 2 1) 0 0 ∈ hK.fixedField := fun k =>
    (isHerm_iff.1 (herm_Yof (hkd _ k.1.2 (aOf_eq_zero_of_mem_ker k)).1)).1
  by_cases hi : ∀ g ∈ F, hK.bar (aOf g / α₀) = aOf g / α₀
  · have hk1 : ∀ k : (aHom F hFU).ker, Yof (k.1 : hypSU hK 2 1) 0 1 / α₀ ∈ hK.fixedField := by
      intro k
      obtain ⟨-, -, e⟩ := hkd _ k.1.2 (aOf_eq_zero_of_mem_ker k)
      refine hK.mem_fixedField.mpr ?_
      rw [map_div₀, div_eq_div_iff hα' hα]
      exact e
    have hker : Nat.card (aHom F hFU).ker ≤ (2 ^ f) ^ 2 := by
      let φ : (aHom F hFU).ker → hK.fixedField × hK.fixedField := fun k =>
        (⟨Yof (k.1 : hypSU hK 2 1) 0 0, hk0 k⟩, ⟨Yof (k.1 : hypSU hK 2 1) 0 1 / α₀, hk1 k⟩)
      have hinj : Function.Injective φ := by
        intro k k' h
        have h1 := congrArg (fun p => (p.1 : K)) h
        have h2' := congrArg (fun p => (p.2 : K)) h
        simp only [φ] at h1 h2'
        obtain ⟨hV, hY, -⟩ := hkd _ k.1.2 (aOf_eq_zero_of_mem_ker k)
        obtain ⟨hV', hY', -⟩ := hkd _ k'.1.2 (aOf_eq_zero_of_mem_ker k')
        exact Subtype.ext (Subtype.ext (Yof_ext hV hV' h1 ((div_left_inj' hα).1 h2')
          (by rw [hY, hY'])))
      calc Nat.card (aHom F hFU).ker ≤ Nat.card (hK.fixedField × hK.fixedField) :=
            Nat.card_le_card_of_injective φ hinj
        _ = (2 ^ f) ^ 2 := by rw [Nat.card_prod, hK.card_fixedField]; ring
    have hrange : Nat.card (aHom F hFU).range ≤ 2 ^ f := by
      let ψ : (aHom F hFU).range → hK.fixedField := fun r => ⟨Multiplicative.toAdd r.1 / α₀, by
        obtain ⟨g, hg⟩ := r.2
        have : Multiplicative.toAdd r.1 = aOf (g : hypSU hK 2 1) := by rw [← hg]; rfl
        rw [this]
        exact hi g g.2⟩
      have hinj : Function.Injective ψ := by
        intro r r' h
        have h3 := (div_left_inj' hα).1 (congrArg Subtype.val h)
        exact Subtype.ext (Multiplicative.toAdd.injective h3)
      calc Nat.card (aHom F hFU).range ≤ Nat.card hK.fixedField :=
            Nat.card_le_card_of_injective ψ hinj
        _ = 2 ^ f := hK.card_fixedField
    calc Nat.card F = Nat.card (aHom F hFU).ker * Nat.card (aHom F hFU).range := hcard.symm
      _ ≤ (2 ^ f) ^ 2 * 2 ^ f := Nat.mul_le_mul hker hrange
      _ = (2 ^ f) ^ 3 := by ring
  · push Not at hi
    obtain ⟨u₁, hu₁, hne⟩ := hi
    have hb0 : ∀ g ∈ F, aOf g = 0 → Yof g 0 1 = 0 := by
      intro g hg hga
      obtain ⟨hgV, hY11, E0⟩ := hkd g hg hga
      obtain ⟨-, e2'⟩ := commute_Vsub_entries (hFU hu₁) hgV (hcomm u₁ hu₁ g hg)
      have hh := (isHerm_iff.1 (herm_Yof hgV)).2.2
      rw [hY11, hh] at e2'
      set α₁ := aOf u₁
      have E1 : α₁ * hK.bar (Yof g 0 1) = Yof g 0 1 * hK.bar α₁ := by
        linear_combination e2' - h2 (Yof g 0 1 * hK.bar α₁)
      by_contra hb
      apply hne
      have : Yof g 0 1 * (hK.bar α₁ * α₀) = Yof g 0 1 * (α₁ * hK.bar α₀) := by
        linear_combination (-α₀) * E1 + α₁ * E0
      have h5 := mul_left_cancel₀ hb this
      rw [map_div₀, div_eq_div_iff hα' hα]
      exact h5
    have hker : Nat.card (aHom F hFU).ker ≤ 2 ^ f := by
      let φ : (aHom F hFU).ker → hK.fixedField := fun k =>
        ⟨Yof (k.1 : hypSU hK 2 1) 0 0, hk0 k⟩
      have hinj : Function.Injective φ := by
        intro k k' h
        have h1 := congrArg (fun p : hK.fixedField => (p : K)) h
        simp only [φ] at h1
        obtain ⟨hV, hY, -⟩ := hkd _ k.1.2 (aOf_eq_zero_of_mem_ker k)
        obtain ⟨hV', hY', -⟩ := hkd _ k'.1.2 (aOf_eq_zero_of_mem_ker k')
        exact Subtype.ext (Subtype.ext (Yof_ext hV hV' h1
          (by rw [hb0 _ k.1.2 (aOf_eq_zero_of_mem_ker k),
            hb0 _ k'.1.2 (aOf_eq_zero_of_mem_ker k')]) (by rw [hY, hY'])))
      calc Nat.card (aHom F hFU).ker ≤ Nat.card hK.fixedField :=
            Nat.card_le_card_of_injective φ hinj
        _ = 2 ^ f := hK.card_fixedField
    have hrange : Nat.card (aHom F hFU).range ≤ (2 ^ f) ^ 2 := by
      calc Nat.card (aHom F hFU).range ≤ Nat.card (Multiplicative K) :=
            Subgroup.card_le_card_group _
        _ = (2 ^ f) ^ 2 := by rw [Nat.card_congr Multiplicative.toAdd, hK.card_eq_sq]
    calc Nat.card F = Nat.card (aHom F hFU).ker * Nat.card (aHom F hFU).range := hcard.symm
      _ ≤ 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_le_mul hker hrange
      _ = (2 ^ f) ^ 3 := by ring

theorem elemAb_le_Vsub_or_card_le {F : Subgroup (hypSU hK 2 1)}
    (hFU : F ≤ hypUnitriangular hK 2 1) (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hsq : ∀ x ∈ F, x * x = 1) : F ≤ Vsub hK ∨ Nat.card F ≤ (2 ^ f) ^ 3 := by
  by_cases hall : ∀ g ∈ F, aOf g = 0
  · left
    intro g hg
    exact mem_Vsub_of_sq ((mem_Ssub_iff (hFU hg)).2 (hall g hg)) (hsq g hg)
  · right
    push Not at hall
    obtain ⟨u₀, hu₀, hne⟩ := hall
    exact elemAb_card_le hFU hcomm hsq hu₀ hne

end ElemAb

end CFSG.RankThree.PartOne.U5K.Hyp
