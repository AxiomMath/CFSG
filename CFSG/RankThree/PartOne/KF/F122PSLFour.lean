module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.RankThree.PartOne.KF.ClsSULift
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups

abbrev I4 : Type := Fin 2 × Fin 2

section Blocks

variable {K : Type} [Field K]

@[expose] def yMat₂ (X : Matrix (Fin 2) (Fin 2) K) : Matrix I4 I4 K :=
  Matrix.of fun ib jb => if ib.2 = 0 ∧ jb.2 = 1 then X ib.1 jb.1 else 0

theorem yMat₂_mul_yMat₂ (X X' : Matrix (Fin 2) (Fin 2) K) : yMat₂ X * yMat₂ X' = 0 := by
  ext ib jb
  simp only [mul_apply, yMat₂, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun kc _ => ?_
  by_cases h : kc.2 = 1
  · have : ¬ (kc.2 = 0 ∧ jb.2 = 1) := fun h' => by rw [h] at h'; exact absurd h'.1 (by decide)
    rw [ite_eq_right this, mul_zero]
  · have : ¬ (ib.2 = 0 ∧ kc.2 = 1) := fun h' => h h'.2
    rw [ite_eq_right this, zero_mul]

theorem yMat₂_zero : yMat₂ (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext ib jb
  simp [yMat₂]

theorem yMat₂_add (X X' : Matrix (Fin 2) (Fin 2) K) : yMat₂ (X + X') = yMat₂ X + yMat₂ X' := by
  ext ib jb
  simp only [yMat₂, of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem one_add_yMat₂_mul (X X' : Matrix (Fin 2) (Fin 2) K) :
    (1 + yMat₂ X) * (1 + yMat₂ X') = 1 + yMat₂ (X + X') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, yMat₂_mul_yMat₂, add_zero, yMat₂_add]
  abel

@[expose] def bdMat (A B : Matrix (Fin 2) (Fin 2) K) : Matrix I4 I4 K := blockDiagonal ![A, B]

theorem bdMat_mul (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    bdMat A B * bdMat A' B' = bdMat (A * A') (B * B') := by
  rw [bdMat, bdMat, bdMat, ← blockDiagonal_mul]
  congr 1
  funext b
  fin_cases b <;> simp

theorem det_bdMat (A B : Matrix (Fin 2) (Fin 2) K) : (bdMat A B).det = A.det * B.det := by
  rw [bdMat, det_blockDiagonal, Fin.prod_univ_two]
  simp

theorem bdMat_one : bdMat (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [bdMat, ← blockDiagonal_one]
  congr 1
  funext b
  fin_cases b <;> rfl

theorem bdMat_mul_yMat₂ (A B B' X : Matrix (Fin 2) (Fin 2) K) (hB' : B' * B = 1) :
    bdMat A B * yMat₂ X = yMat₂ (A * X * B') * bdMat A B := by
  set X' := A * X * B' with hX'
  have key : A * X = X' * B := by rw [hX', mul_assoc (A * X), hB', mul_one]
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp only [mul_apply, Fintype.sum_prod_type, bdMat, blockDiagonal_apply, yMat₂, of_apply]
  by_cases h : b = 0 ∧ b' = 1
  · obtain ⟨rfl, rfl⟩ := h
    have := congrFun (congrFun key i) j
    simp only [mul_apply] at this
    simpa [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
  · have h1 : ∀ k c, (if b = c then (![A, B] b) i k else 0) *
        (if c = 0 ∧ b' = 1 then X k j else 0) = 0 := by
      intro k c
      by_cases hbc : b = c
      · subst hbc
        rw [ite_eq_right h, mul_zero]
      · rw [ite_eq_right hbc, zero_mul]
    have h2 : ∀ k c, (if b = 0 ∧ c = 1 then X' i k else 0) *
        (if c = b' then (![A, B] c) k j else 0) = 0 := by
      intro k c
      by_cases hc : c = b'
      · subst hc
        rw [ite_eq_right h, zero_mul]
      · rw [ite_eq_right hc, mul_zero]
    simp only [h1, h2, Finset.sum_const_zero]

@[expose] def dHom (K : Type) [Field K] : SL(2, K) × SL(2, K) →* SpecialLinearGroup I4 K where
  toFun AB := ⟨bdMat (AB.1 : Matrix (Fin 2) (Fin 2) K) AB.2, by
    rw [det_bdMat, AB.1.2, AB.2.2, mul_one]⟩
  map_one' := Subtype.ext (by
    change bdMat (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1
    exact bdMat_one)
  map_mul' x y := Subtype.ext (by
    change bdMat ((x.1 : Matrix (Fin 2) (Fin 2) K) * (y.1 : Matrix (Fin 2) (Fin 2) K))
        ((x.2 : Matrix (Fin 2) (Fin 2) K) * (y.2 : Matrix (Fin 2) (Fin 2) K)) =
      bdMat (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) *
        bdMat (y.1 : Matrix (Fin 2) (Fin 2) K) (y.2 : Matrix (Fin 2) (Fin 2) K)
    rw [bdMat_mul])

theorem coe_dHom (AB : SL(2, K) × SL(2, K)) :
    ((dHom K AB : SpecialLinearGroup I4 K) : Matrix I4 I4 K) =
      bdMat (AB.1 : Matrix (Fin 2) (Fin 2) K) AB.2 := rfl

theorem bdMat_apply_block0 (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    bdMat A B (i, 0) (j, 0) = A i j := by
  rw [bdMat, blockDiagonal_apply_eq]
  rfl

theorem bdMat_apply_block1 (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    bdMat A B (i, 1) (j, 1) = B i j := by
  rw [bdMat, blockDiagonal_apply_eq]
  rfl

end Blocks

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem det_one_add_yMat₂ (X : Matrix (Fin 2) (Fin 2) K) : (1 + yMat₂ X).det = 1 := by
  have hX : X + X = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  refine eq_one_of_mul_self_eq_one ?_
  rw [← det_mul, one_add_yMat₂_mul, hX, yMat₂_zero, add_zero, det_one]

@[expose] def uHom₂ (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Matrix (Fin 2) (Fin 2) K) →* SpecialLinearGroup I4 K where
  toFun X := ⟨1 + yMat₂ X.toAdd, det_one_add_yMat₂ _⟩
  map_one' := Subtype.ext (by
    change 1 + yMat₂ (0 : Matrix (Fin 2) (Fin 2) K) = 1
    rw [yMat₂_zero, add_zero])
  map_mul' X X' := Subtype.ext (by
    change 1 + yMat₂ (X.toAdd + X'.toAdd) = (1 + yMat₂ X.toAdd) * (1 + yMat₂ X'.toAdd)
    rw [one_add_yMat₂_mul])

omit [CharP K 2] in
theorem dHom_injective : Function.Injective (dHom K) := by
  rw [injective_iff_map_eq_one]
  intro AB h
  have h' := congrArg (fun x : SpecialLinearGroup I4 K => (x : Matrix I4 I4 K)) h
  simp only [coe_dHom, Matrix.SpecialLinearGroup.coe_one] at h'
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · ext i j
    have := congrFun (congrFun h' (i, 0)) (j, 0)
    rw [bdMat_apply_block0] at this
    simpa [Matrix.one_apply] using this
  · ext i j
    have := congrFun (congrFun h' (i, 1)) (j, 1)
    rw [bdMat_apply_block1] at this
    simpa [Matrix.one_apply] using this

theorem two_le_localRank_PSL_four [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card SL(2, K)) :
    2 ≤ localRank p (ProjectiveSpecialLinearGroup I4 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpK
  let Z : Subgroup SL(2, K) := Subgroup.zpowers g
  let _ : CommGroup Z := IsCyclic.commGroup
  let ψ : Z × Z →* SpecialLinearGroup I4 K := (dHom K).comp (Z.subtype.prodMap Z.subtype)
  have hψinj : Function.Injective ψ :=
    dHom_injective.comp (Prod.map_injective.mpr ⟨Z.subtype_injective, Z.subtype_injective⟩)
  have hZp : ∀ a : Z, a ^ p = 1 := by
    intro a
    apply Subtype.ext
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hi, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one, _root_.one_zpow]
  have hψp : ∀ a : Z × Z, ψ (a ^ p) = 1 := by
    intro a
    have : a ^ p = 1 := Prod.ext (hZp a.1) (hZp a.2)
    rw [this, map_one]
  have hE : CFSG.Assembly.IsElemAbelian p ψ.range := isElemAbelian_range_of_pow ψ hψp
  have hEc : Nat.card ψ.range = p ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, Nat.card_prod]
    have : Nat.card Z = p := by rw [Nat.card_zpowers, hg]
    rw [this, sq]
  have hEN : ψ.range ⊓ Subgroup.center (SpecialLinearGroup I4 K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨⟨a, b⟩, rfl⟩, hxc⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have hM : bdMat ((a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        ((b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = scalar I4 c := hc.symm
    have hA : ((a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = scalar (Fin 2) c := by
      ext i j
      have := congrFun (congrFun hM (i, 0)) (j, 0)
      rw [bdMat_apply_block0] at this
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply, Prod.ext_iff] using this
    have hB : ((b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = scalar (Fin 2) c := by
      ext i j
      have := congrFun (congrFun hM (i, 1)) (j, 1)
      rw [bdMat_apply_block1] at this
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply, Prod.ext_iff] using this
    have hc2 : c ^ 2 = 1 := by
      have h1 := (a : SL(2, K)).2
      rw [hA] at h1
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using h1
    have hc1 : c = 1 := by
      have h1 : (c + 1) ^ 2 = 0 := by
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        calc (c + 1) ^ 2 = c ^ 2 + 2 * c + 1 := by ring
          _ = 1 + 0 + 1 := by rw [hc2, h2, zero_mul]
          _ = 0 := by rw [add_zero]; exact CharTwo.add_self_eq_zero (1 : K)
      exact CharTwo.add_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp h1)
    have ha1 : a = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hA, hc1]
      simp
    have hb1 : b = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hB, hc1]
      simp
    rw [Subgroup.mem_bot, ha1, hb1]
    exact map_one ψ
  have hP2 : IsPGroup 2 (uHom₂ K).range := by
    intro y
    obtain ⟨X, hX⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hX, ← map_mul, OneMemClass.coe_one]
    have hXX : X * X = 1 := by
      apply Multiplicative.toAdd.injective
      ext i j
      simp only [toAdd_mul, toAdd_one, Matrix.add_apply, Matrix.zero_apply,
        CharTwo.add_self_eq_zero]
    rw [hXX, map_one]
  have hPN : ¬ (uHom₂ K).range ≤ Subgroup.center (SpecialLinearGroup I4 K) := by
    intro hP
    have h1 : uHom₂ K (Multiplicative.ofAdd 1) ∈ (uHom₂ K).range := ⟨_, rfl⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hP h1)
    have h2 : (scalar I4 c) ((0, 0) : I4) ((0, 1) : I4) =
        (1 + yMat₂ (1 : Matrix (Fin 2) (Fin 2) K) : Matrix I4 I4 K) ((0, 0) : I4) ((0, 1) : I4) := by
      rw [hc]
      rfl
    simp [yMat₂, scalar_apply, Matrix.one_apply] at h2
  have hEP : ψ.range ≤ Subgroup.normalizer ((uHom₂ K).range : Set (SpecialLinearGroup I4 K)) := by
    refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩ _ ⟨X, rfl⟩
    have hB' : (((b : SL(2, K))⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        ((b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    refine ⟨Multiplicative.ofAdd (((a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * X.toAdd *
      (((b : SL(2, K))⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)), ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Subtype.ext ?_
    change (1 + yMat₂ (((a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * X.toAdd *
        (((b : SL(2, K))⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))) *
        bdMat ((a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ((b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      bdMat ((a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ((b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        (1 + yMat₂ X.toAdd)
    rw [mul_add, add_mul, mul_one, one_mul,
      bdMat_mul_yMat₂ _ _ _ X.toAdd hB']
  exact le_localRank_quotient_of_le_normalizer _ hp hE hEc hEN hP2 hPN hEP

theorem two_le_localRank_PSL_four_fin [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card SL(2, K)) :
    2 ≤ localRank p (ProjectiveSpecialLinearGroup (Fin 4) K) := by
  rw [← localRank_eq_of_mulEquiv
    (pslReindex K (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)) hp]
  exact two_le_localRank_PSL_four hp hpK

end Main

end CFSG.RankThree.PartOne.KFU
