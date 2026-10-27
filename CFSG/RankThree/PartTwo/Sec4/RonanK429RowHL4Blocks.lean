module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHSL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHBlock
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open Matrix

theorem l4_map_eq_one_of_isPerfect {X A : Type*} [Group X] [CommGroup A] [Group.IsPerfect X]
    (φ : X →* A) (x : X) : φ x = 1 := by
  have h : commutator X ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.IsPerfect.commutator_eq_top] at h
  exact h (Subgroup.mem_top x)

section Blocks

variable {K : Type} [Field K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

theorem l4_submatrix_mul {A B : Matrix ι ι K} (f : κ → ι) (hf : Function.Injective f)
    (hA : ∀ i k, (∀ l, f l ≠ k) → A (f i) k = 0) :
    (A * B).submatrix f f = A.submatrix f f * B.submatrix f f := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  exact (Fintype.sum_of_injective f hf (fun l => A (f i) (f l) * B (f l) (f j))
    (fun k => A (f i) k * B k (f j))
    (fun k hk => by rw [hA i k (fun l hl => hk ⟨l, hl⟩), zero_mul]) (fun l => rfl)).symm

@[expose] noncomputable def l4BlockHom (H : Subgroup (GL ι K)) (f : κ → ι)
    (hf : Function.Injective f)
    (hH : ∀ M ∈ H, ∀ i k, (∀ l, f l ≠ k) → (M : Matrix ι ι K) (f i) k = 0) : H →* GL κ K :=
  MonoidHom.toHomUnits
    { toFun := fun M => ((M : GL ι K) : Matrix ι ι K).submatrix f f
      map_one' := by
        show (1 : Matrix ι ι K).submatrix f f = 1
        exact submatrix_one f hf
      map_mul' := fun M N => by
        show (((M : GL ι K) : Matrix ι ι K) * ((N : GL ι K) : Matrix ι ι K)).submatrix f f = _
        exact l4_submatrix_mul f hf (hH M M.2) }

theorem l4_entry_eq_zero {D : GL ι K} {d : ι → K} (hD : (D : Matrix ι ι K) = diagonal d)
    {M : GL ι K} (hM : M ∈ Subgroup.centralizer ({D} : Set (GL ι K))) {i k : ι}
    (h : d i ≠ d k) : (M : Matrix ι ι K) i k = 0 := by
  have hc : M * D = D * M := Subgroup.mem_centralizer_singleton_iff.mp hM
  have hc' : (M : Matrix ι ι K) * diagonal d = diagonal d * (M : Matrix ι ι K) := by
    rw [← hD, ← Units.val_mul, hc, Units.val_mul]
  exact Sec21.Tables.isBlockDiag_of_commute hc' i k h

theorem l4_det_eq_one_of_isPerfect {X : Type*} [Group X] [Group.IsPerfect X] (φ : X →* GL κ K)
    (x : X) : ((φ x : GL κ K) : Matrix κ κ K).det = 1 := by
  have h := congrArg Units.val
    (l4_map_eq_one_of_isPerfect ((GeneralLinearGroup.det : GL κ K →* Kˣ).comp φ) x)
  rwa [MonoidHom.comp_apply, GeneralLinearGroup.val_det_apply, Units.val_one] at h

@[expose] noncomputable def l4ToSL {X : Type} [Group X] [Group.IsPerfect X]
    (φ : X →* GL κ K) : X →* SpecialLinearGroup κ K where
  toFun x := ⟨(φ x : Matrix κ κ K), l4_det_eq_one_of_isPerfect φ x⟩
  map_one' := by
    apply Subtype.ext
    show ((φ 1 : GL κ K) : Matrix κ κ K) = 1
    rw [map_one, Units.val_one]
  map_mul' x y := by
    apply Subtype.ext
    show ((φ (x * y) : GL κ K) : Matrix κ κ K) = (φ x : Matrix κ κ K) * (φ y : Matrix κ κ K)
    rw [map_mul, Units.val_mul]

theorem l4ToSL_eq_one_iff {X : Type} [Group X] [Group.IsPerfect X] (φ : X →* GL κ K) (x : X) :
    l4ToSL φ x = 1 ↔ ((φ x : GL κ K) : Matrix κ κ K) = 1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Blocks

section Blk3

variable {K : Type} [Field K]

@[expose] def l4Blk3 (B : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 4) (Fin 4) K :=
  !![B 0 0, B 0 1, B 0 2, 0; B 1 0, B 1 1, B 1 2, 0; B 2 0, B 2 1, B 2 2, 0; 0, 0, 0, 1]

theorem l4Blk3_one : l4Blk3 (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Blk3]

theorem l4Blk3_mul (X Y : Matrix (Fin 3) (Fin 3) K) : l4Blk3 (X * Y) = l4Blk3 X * l4Blk3 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Blk3, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four]

theorem det_l4Blk3 (X : Matrix (Fin 3) (Fin 3) K) : (l4Blk3 X).det = X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, l4Blk3, Fin.succAbove]

theorem l4Blk3_submatrix (X : Matrix (Fin 3) (Fin 3) K) :
    (l4Blk3 X).submatrix Fin.castSucc Fin.castSucc = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Blk3]

@[expose] noncomputable def l4BlkGL3 : GL (Fin 3) K →* GL (Fin 4) K where
  toFun X :=
    { val := l4Blk3 (X : Matrix (Fin 3) (Fin 3) K)
      inv := l4Blk3 ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      val_inv := by
        rw [← l4Blk3_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, l4Blk3_one]
      inv_val := by
        rw [← l4Blk3_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, l4Blk3_one] }
  map_one' := Units.ext (by simp [l4Blk3_one])
  map_mul' X Y := Units.ext (by simp [l4Blk3_mul])

theorem coe_l4BlkGL3 (X : GL (Fin 3) K) :
    ((l4BlkGL3 X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      l4Blk3 (X : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem l4BlkGL3_mem_centralizer {D : GL (Fin 4) K} {d : Fin 4 → K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d) (h01 : d 0 = d 1) (h12 : d 1 = d 2)
    (B : GL (Fin 3) K) : l4BlkGL3 B ∈ Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD, coe_l4BlkGL3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Blk3, mul_diagonal, diagonal_mul, h01, h12, mul_comm]

end Blk3

section Cases

variable
  {K : Type} [Field K]

theorem l4_not_isType429_two_blocks [Finite K] (h3 : (3 : K) ≠ 0) {D : GL (Fin 4) K}
    {d : Fin 4 → K} (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d) (h02 : d 0 ≠ d 2)
    (h03 : d 0 ≠ d 3) (h12 : d 1 ≠ d 2) (h13 : d 1 ≠ d 3) {L : Subgroup (GL (Fin 4) K)}
    (hL : L ≤ Subgroup.centralizer ({D} : Set (GL (Fin 4) K))) [Group.IsPerfect L] :
    ¬ IsType429 (L ⧸ CFSG.pCore 2 L) := by
  set H := Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) with hH
  have hr₁ : ∀ k : Fin 4, (∀ l : Fin 2, (![0, 1] : Fin 2 → Fin 4) l ≠ k) → k = 2 ∨ k = 3 := by
    decide
  have hr₂ : ∀ k : Fin 4, (∀ l : Fin 2, (![2, 3] : Fin 2 → Fin 4) l ≠ k) → k = 0 ∨ k = 1 := by
    decide
  have hv₁ : ∀ i k, (∀ l, (![0, 1] : Fin 2 → Fin 4) l ≠ k) → d (![0, 1] i) ≠ d k := by
    intro i k hk
    rcases hr₁ k hk with rfl | rfl <;> fin_cases i
    · exact h02
    · exact h12
    · exact h03
    · exact h13
  have hv₂ : ∀ i k, (∀ l, (![2, 3] : Fin 2 → Fin 4) l ≠ k) → d (![2, 3] i) ≠ d k := by
    intro i k hk
    rcases hr₂ k hk with rfl | rfl <;> fin_cases i
    · exact h02.symm
    · exact h03.symm
    · exact h12.symm
    · exact h13.symm
  have hf₁ : Function.Injective (![0, 1] : Fin 2 → Fin 4) := by decide
  have hf₂ : Function.Injective (![2, 3] : Fin 2 → Fin 4) := by decide
  set b₁ := l4BlockHom H ![0, 1] hf₁ (fun M hM i k hk => l4_entry_eq_zero hD hM (hv₁ i k hk))
  set b₂ := l4BlockHom H ![2, 3] hf₂ (fun M hM i k hk => l4_entry_eq_zero hD hM (hv₂ i k hk))
  refine not_isType429_of_two_homs (rank3LeOne_SL2 h3) (rank3LeOne_SL2 h3)
    (l4ToSL (b₁.comp (Subgroup.inclusion hL))) (l4ToSL (b₂.comp (Subgroup.inclusion hL))) ?_
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker, l4ToSL_eq_one_iff,
    l4ToSL_eq_one_iff] at hx
  obtain ⟨e₁, e₂⟩ := hx
  have e₁' : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1] = 1 := e₁
  have e₂' : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3] = 1 := e₂
  have hxC : (x : GL (Fin 4) K) ∈ H := hL x.2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using congrFun (congrFun e₁' 0) 0
  · simpa using congrFun (congrFun e₁' 0) 1
  · simpa using l4_entry_eq_zero hD hxC h02
  · simpa using l4_entry_eq_zero hD hxC h03
  · simpa using congrFun (congrFun e₁' 1) 0
  · simpa using congrFun (congrFun e₁' 1) 1
  · simpa using l4_entry_eq_zero hD hxC h12
  · simpa using l4_entry_eq_zero hD hxC h13
  · simpa using l4_entry_eq_zero hD hxC h02.symm
  · simpa using l4_entry_eq_zero hD hxC h12.symm
  · simpa using congrFun (congrFun e₂' 0) 0
  · simpa using congrFun (congrFun e₂' 0) 1
  · simpa using l4_entry_eq_zero hD hxC h03.symm
  · simpa using l4_entry_eq_zero hD hxC h13.symm
  · simpa using congrFun (congrFun e₂' 1) 0
  · simpa using congrFun (congrFun e₂' 1) 1

theorem l4_good429_three_one [Finite K] {G : Subgroup (GL (Fin 4) K)}
    {Q : Subgroup (GL (Fin 3) K)} (hQ : IsQuasisimple Q) (hE : ∀ B ∈ Q, l4BlkGL3 B ∈ G)
    (hβ : ∀ M ∈ G, ∀ B : GL (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc →
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
        (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0) →
      (B : Matrix (Fin 3) (Fin 3) K).det = 1 → B ∈ Q)
    {D : GL (Fin 4) K} (hDG : D ∈ G) {d : Fin 4 → K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d) (h01 : d 0 = d 1) (h12 : d 1 = d 2)
    (h23 : d 2 ≠ d 3) (hdet : (D : Matrix (Fin 4) (Fin 4) K).det = 1) (hD3 : D ^ 3 = 1) :
    Good429 (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
  intro L hLC hLp hLs
  haveI := hLp
  set H := Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) with hH
  set C := H ⊓ G with hC
  have hd : ∀ i : Fin 3, d (Fin.castSucc i) = d 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
  have hd3 : d 3 ≠ d 0 := fun h => h23 ((h01.trans h12).symm.trans h.symm)
  have hcs : ∀ k : Fin 4, (∀ l : Fin 3, (Fin.castSucc l : Fin 4) ≠ k) → k = 3 := by decide
  have hv : ∀ i k, (∀ l, (Fin.castSucc l : Fin 4) ≠ k) → d (Fin.castSucc i) ≠ d k := by
    intro i k hk
    rw [hcs k hk, hd i]
    exact hd3.symm
  have hv3 : ∀ i k, (∀ l, (![3] : Fin 1 → Fin 4) l ≠ k) → d (![3] i) ≠ d k := by
    intro i k hk
    fin_cases i
    fin_cases k
    · exact hd3
    · show d 3 ≠ d 1
      rw [← h01]; exact hd3
    · show d 3 ≠ d 2
      rw [← h12, ← h01]; exact hd3
    · exact absurd rfl (hk 0)
  have hinj3 : Function.Injective (![3] : Fin 1 → Fin 4) := by decide
  set b : H →* GL (Fin 3) K := l4BlockHom H Fin.castSucc (Fin.castSucc_injective 3)
    (fun M hM i k hk => l4_entry_eq_zero hD hM (hv i k hk)) with hb
  set b3 : H →* GL (Fin 1) K := l4BlockHom H ![3] hinj3
    (fun M hM i k hk => l4_entry_eq_zero hD hM (hv3 i k hk)) with hb3
  set β : C →* GL (Fin 3) K := b.comp (Subgroup.inclusion inf_le_left) with hβdef
  have hβc : ∀ c : C, ((β c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc :=
    fun c => rfl
  have hz3 : ∀ M ∈ H, ∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
      (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0 := fun M hM i =>
    ⟨l4_entry_eq_zero hD hM (by rw [hd i]; exact hd3.symm),
      l4_entry_eq_zero hD hM (by rw [hd i]; exact hd3)⟩
  have hDH : D ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set Dc : C := ⟨D, hDH, hDG⟩ with hDc
  set z : GL (Fin 3) K := β Dc with hz
  have hzmat : (z : Matrix (Fin 3) (Fin 3) K) = diagonal (fun _ => d 0) := by
    rw [hz, hβc, show ((Dc : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal d from hD,
      submatrix_diagonal _ _ (Fin.castSucc_injective 3)]
    congr 1
    funext i
    exact hd i
  have hμ3 : d 0 ^ 3 = 1 := by
    have hm : (D : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hD3, Units.val_one]
    rw [hD, diagonal_pow] at hm
    have := congrFun (congrFun hm 0) 0
    simpa [diagonal_apply_eq] using this
  have hlam : d 3 = 1 := by
    have e1 : d 1 = d 0 := h01.symm
    have e2 : d 2 = d 0 := (h01.trans h12).symm
    rw [hD, det_diagonal, Fin.prod_univ_four, e1, e2] at hdet
    have h' : d 0 ^ 3 * d 3 = 1 := by rw [← hdet]; ring
    rwa [hμ3, one_mul] at h'
  have hμ1 : d 0 ≠ 1 := fun h => hd3 (hlam.trans h.symm)
  have hzQ : z ∈ Q := by
    refine hβ D hDG z (hβc Dc) (hz3 D hDH) ?_
    rw [hzmat, det_diagonal, Fin.prod_univ_three, ← hμ3]
    ring
  have hzc : ∀ q ∈ Q, q * z = z * q := by
    intro q _
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hzmat]
    ext i j
    simp [mul_diagonal, diagonal_mul, mul_comm]
  have hzo : orderOf z = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply orderOf_eq_prime
    · have hD3' : Dc ^ 3 = 1 := Subtype.ext hD3
      rw [hz, ← map_pow, hD3', map_one]
    · intro h1
      have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
      simp only [hzmat, diagonal_apply_eq, Units.val_one, one_apply_eq] at h00
      exact hμ1 h00
  have hLH : L ≤ H := hLC.trans inf_le_left
  have hβinj : Function.Injective (β.comp (Subgroup.inclusion hLC)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have e : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc
        Fin.castSucc = 1 := congrArg Units.val hx
    have e3 : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
      have h1 := l4_det_eq_one_of_isPerfect (b3.comp (Subgroup.inclusion hLH)) x
      rw [Matrix.det_fin_one] at h1
      exact h1
    have hxH : (x : GL (Fin 4) K) ∈ H := hLH x.2
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using congrFun (congrFun e 0) 0
    · simpa using congrFun (congrFun e 0) 1
    · simpa using congrFun (congrFun e 0) 2
    · simpa using (hz3 _ hxH 0).1
    · simpa using congrFun (congrFun e 1) 0
    · simpa using congrFun (congrFun e 1) 1
    · simpa using congrFun (congrFun e 1) 2
    · simpa using (hz3 _ hxH 1).1
    · simpa using congrFun (congrFun e 2) 0
    · simpa using congrFun (congrFun e 2) 1
    · simpa using congrFun (congrFun e 2) 2
    · simpa using (hz3 _ hxH 2).1
    · simpa using (hz3 _ hxH 0).2
    · simpa using (hz3 _ hxH 1).2
    · simpa using (hz3 _ hxH 2).2
    · simpa using e3
  have hKQ : ∀ k : L, β (Subgroup.inclusion hLC k) ∈ Q := by
    intro k
    have hkC : (k : GL (Fin 4) K) ∈ C := hLC k.2
    exact hβ k hkC.2 _ rfl (hz3 k hkC.1)
      (l4_det_eq_one_of_isPerfect (β.comp (Subgroup.inclusion hLC)) k)
  have hQC : Q ≤ β.range := by
    intro B hB
    refine ⟨⟨l4BlkGL3 B, l4BlkGL3_mem_centralizer hD h01 h12 B, hE B hB⟩, ?_⟩
    apply Units.ext
    rw [hβc]
    exact l4Blk3_submatrix _
  exact not_isType429_of_quasisimple_block_on hLC hLs β hβinj hQC hKQ hQ hzQ hzc hzo

end Cases

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
