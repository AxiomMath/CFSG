module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432WeylRoute
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofL4
public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofE9
public import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] noncomputable def projCover4 (K : Type) [Field K] :
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 4) K →* Kˣ).ker →*
      projSL 4 K :=
  ((Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 4) K →* _).comp
    (Subgroup.subtype
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 4) K →* Kˣ).ker)).codRestrict
    (projSL 4 K) (fun x => ⟨x, x.2, rfl⟩)

theorem projCover4_surjective (K : Type) [Field K] : Function.Surjective (projCover4 K) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 4) K →* Kˣ).ker).map
      (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 4) K →* _) := hy
  obtain ⟨x, hx, rfl⟩ := hy'
  exact ⟨⟨x, hx⟩, rfl⟩

theorem projCover4_ker (K : Type) [Field K] : ∀ z ∈ (projCover4 K).ker, z ^ 4 = 1 := by
  intro z hz
  have h1 : projCover4 K z = 1 := MonoidHom.mem_ker.mp hz
  exact Item424Res5.pow_four_eq_one_of_mk_eq_one (congrArg Subtype.val h1)

theorem sl4_blk0_entry01 (K : Type) [Field K] :
    (Item424Res3.blkThree K 4 0 (by norm_num) : Matrix (Fin 4) (Fin 4) K) 0 1 = 1 := by
  show CFSG.ClassicalInvolution.Phan.blockMat 4 0 (Item424Res3.mThree K) 0 1 = 1
  simp [CFSG.ClassicalInvolution.Phan.blockMat_apply, Item424Res3.mThree]

theorem sl4_blk2_entry23 (K : Type) [Field K] :
    (Item424Res3.blkThree K 4 2 (by norm_num) : Matrix (Fin 4) (Fin 4) K) 2 3 = 1 := by
  show CFSG.ClassicalInvolution.Phan.blockMat 4 2 (Item424Res3.mThree K) 2 3 = 1
  simp [CFSG.ClassicalInvolution.Phan.blockMat_apply, Item424Res3.mThree]

theorem sl4_blk0_pow_entry23 (K : Type) [Field K] (m : ℕ) :
    ((Item424Res3.blkThree K 4 0 (by norm_num) ^ m : Matrix.SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := by
  rw [Item424Res3.coe_blkThree_pow]
  simp [CFSG.ClassicalInvolution.Phan.blockMat_apply]

theorem sl4_blk0_ne_one (K : Type) [Field K] :
    Item424Res3.blkThree K 4 0 (by norm_num) ≠ 1 := by
  intro h
  have h01 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 4) K =>
    (A : Matrix (Fin 4) (Fin 4) K) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_one] at h01
  rw [sl4_blk0_entry01, Matrix.one_apply_ne (show (0 : Fin 4) ≠ 1 by decide)] at h01
  exact one_ne_zero h01

@[expose] noncomputable def sl4a (K : Type) [Field K] :
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 4) K →* Kˣ).ker :=
  Matrix.SpecialLinearGroup.toGLKerEquiv (Item424Res3.blkThree K 4 0 (by norm_num))

@[expose] noncomputable def sl4b (K : Type) [Field K] :
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 4) K →* Kˣ).ker :=
  Matrix.SpecialLinearGroup.toGLKerEquiv (Item424Res3.blkThree K 4 2 (by norm_num))

theorem sl4a_pow_three (K : Type) [Field K] : sl4a K ^ 3 = 1 := by
  unfold sl4a
  rw [← map_pow, Item424Res3.blkThree_pow_three, map_one]

theorem sl4b_pow_three (K : Type) [Field K] : sl4b K ^ 3 = 1 := by
  unfold sl4b
  rw [← map_pow, Item424Res3.blkThree_pow_three, map_one]

theorem sl4a_ne_one (K : Type) [Field K] : sl4a K ≠ 1 := by
  intro h
  apply sl4_blk0_ne_one K
  apply Matrix.SpecialLinearGroup.toGLKerEquiv.injective
  rw [map_one]
  exact h

theorem sl4a_mul_sl4b_comm (K : Type) [Field K] : sl4a K * sl4b K = sl4b K * sl4a K := by
  unfold sl4a sl4b
  rw [← map_mul, ← map_mul,
    Item424Res3.blkThree_comm (F := K) (n := 4) (by norm_num) (by norm_num)]

theorem sl4b_not_mem_zpowers (K : Type) [Field K] : sl4b K ∉ Subgroup.zpowers (sl4a K) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨m, -, hkm⟩ := Item424Res3.exists_pow_eq_zpow_of_pow_three (sl4a_pow_three K) k
  have hbm : sl4b K = sl4a K ^ m := hk.symm.trans hkm
  have hBA : Item424Res3.blkThree K 4 2 (by norm_num) =
      Item424Res3.blkThree K 4 0 (by norm_num) ^ m := by
    apply Matrix.SpecialLinearGroup.toGLKerEquiv.injective
    rw [map_pow]
    exact hbm
  have h1 := sl4_blk2_entry23 K
  rw [hBA, sl4_blk0_pow_entry23] at h1
  exact zero_ne_one h1

theorem sl4_cover_pair_facts {X Y : Type} [Group X] [Group Y] (π : Y →* X)
    (hker : ∀ z ∈ π.ker, z ^ 4 = 1) {a b : Y} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) (hbn : b ∉ Subgroup.zpowers a) :
    orderOf (π a) = 3 ∧ π b ^ 3 = 1 ∧ π a * π b = π b * π a ∧ π b ∉ Subgroup.zpowers (π a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ w : Y, π w = 1 → w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have h4 : w ^ 4 = 1 := hker w (MonoidHom.mem_ker.mpr hw)
    have h1 : w ^ Nat.gcd 3 4 = 1 := pow_gcd_eq_one.mpr ⟨hw3, h4⟩
    rw [show Nat.gcd 3 4 = 1 by norm_num, pow_one] at h1
    exact h1
  have hx3 : π a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hx1 : π a ≠ 1 := fun h => ha1 (key a h ha3)
  have hy3 : π b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hc : π a * π b = π b * π a := by rw [← map_mul, ← map_mul, hab]
  have hn : π b ∉ Subgroup.zpowers (π a) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hw : π ((a ^ k)⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    have hak : (a ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    have hcomm : Commute (a ^ k)⁻¹ b := ((show Commute a b from hab).zpow_left k).inv_left
    have hw3 : ((a ^ k)⁻¹ * b) ^ 3 = 1 := by
      rw [hcomm.mul_pow, inv_pow, hak, inv_one, one_mul, hb3]
    exact hbn (Subgroup.mem_zpowers_iff.mpr ⟨k, inv_mul_eq_one.mp (key _ hw hw3)⟩)
  exact ⟨orderOf_eq_prime hx3 hx1, hy3, hc, hn⟩

theorem sl4_projSL_E9 (K : Type) [Field K] :
    orderOf (projCover4 K (sl4a K)) = 3 ∧ projCover4 K (sl4b K) ^ 3 = 1 ∧
      projCover4 K (sl4a K) * projCover4 K (sl4b K) =
        projCover4 K (sl4b K) * projCover4 K (sl4a K) ∧
      projCover4 K (sl4b K) ∉ Subgroup.zpowers (projCover4 K (sl4a K)) :=
  sl4_cover_pair_facts (projCover4 K) (projCover4_ker K) (sl4a_pow_three K) (sl4a_ne_one K)
    (sl4b_pow_three K) (sl4a_mul_sl4b_comm K) (sl4b_not_mem_zpowers K)

instance finite_projSL_four_sl4w (K : Type) [Field K] [Finite K] : Finite (projSL 4 K) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 4) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 4) K →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem listRow_projSL_four_of_noroot {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0) : ListRow (projSL 4 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hx0, hy3, hc, hn⟩ := sl4_projSL_E9 K
  exact listRow_of_cover_weyl (projCover4 K) (projCover4_surjective K) (projCover4_ker K)
    (fun E hE hexp hcard => Item424Res5.exists_weyl_sl4 h3 hK E hE hexp hcard) hx0 hy3 hc hn

theorem three_ne_zero_galoisField_sl4w (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (3 : GaloisField p 1) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : GaloisField p 1) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField p 1) p 3).mp h'
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem noroot_galoisField_sl4w {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (h2 : p % 3 = 2) :
    ∀ c : GaloisField p 1, c ^ 2 + c + 1 ≠ 0 := by
  intro c hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := three_ne_zero_galoisField_sl4w p hp3
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hc3 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hc
  let u : (GaloisField p 1)ˣ := Units.mk0 c hc0
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [u, hc3])
  have hu1 : u ≠ 1 := fun h => hc1 (by simpa [u] using congrArg Units.val h)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card (GaloisField p 1)ˣ := hord ▸ orderOf_dvd_natCard u
  rw [Nat.card_units, GaloisField.card p 1 (by norm_num), pow_one] at hdvd
  omega

theorem outerRow_projSL_four_sl4w (p : ℕ) [Fact p.Prime] :
    OuterRow (projSL 4 (GaloisField p 1)) := by
  apply outerRow_of_not_three_dvd_outer
  have hp : p.Prime := Fact.out
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 4 p 1 := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨hp, le_refl 1, ?_⟩
    simp
  have hT := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm
    (MulEquiv.refl (projSL 4 (GaloisField p 1)))
  have hdvd : Nat.card (Outer (projSL 4 (GaloisField p 1))) ∣ 2 * 1 * Nat.gcd 4 (p ^ 1 - 1) :=
    (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (by norm_num) hp (le_refl 1) hT).1
  rw [pow_one] at hdvd
  intro h3
  have h3' : 3 ∣ 2 * 1 * Nat.gcd 4 (p - 1) := h3.trans hdvd
  have h4 : 3 ∣ Nat.gcd 4 (p - 1) := by omega
  have h5 : 3 ∣ 4 := h4.trans (Nat.gcd_dvd_left 4 (p - 1))
  omega

theorem rowOf_four_SL_of_mod_two : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    RowOf (projSL 4 (GaloisField p 1)) := by
  intro p _ hp hmod S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSL_four_of_noroot (three_ne_zero_galoisField_sl4w p hp)
        (noroot_galoisField_sl4w hp hmod),
      outerRow_projSL_four_sl4w p⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
