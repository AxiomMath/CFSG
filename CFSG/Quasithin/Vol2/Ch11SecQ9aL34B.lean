module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34A
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Fischer Matrix

theorem orderOf_eq_fifteen {M : Type*} [Monoid M] {x : M} (h15 : x ^ 15 = 1) (h5 : x ^ 5 ≠ 1)
    (h3 : x ^ 3 ≠ 1) : orderOf x = 15 := by
  have hd : orderOf x ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨orderOf_dvd_of_pow_eq_one h15,
    by norm_num⟩
  rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h | h | h
  · exact absurd (by rw [orderOf_eq_one_iff.mp h, one_pow]) h3
  · exact absurd (by rw [← h, pow_orderOf_eq_one]) h3
  · exact absurd (by rw [← h, pow_orderOf_eq_one]) h5
  · exact h

@[expose] def c4Mat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

theorem c4Mat_det : c4Mat.det = 1 := by
  decide

theorem c4Mat_pow_fifteen : c4Mat ^ 15 = 1 := by
  decide

theorem c4Mat_pow_five : c4Mat ^ 5 ≠ 1 := by
  decide

theorem c4Mat_pow_three : c4Mat ^ 3 ≠ 1 := by
  decide

@[expose] def c4 : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨c4Mat, c4Mat_det⟩

theorem coe_c4_pow (k : ℕ) : ((c4 ^ k : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) = c4Mat ^ k :=
  Matrix.SpecialLinearGroup.coe_pow c4 k

theorem eq_one_of_mem_center_SL4 {A : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hA : A ∈ Subgroup.center (SpecialLinearGroup (Fin 4) (ZMod 2))) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have key : ∀ s : ZMod 2, s ^ 4 = 1 → s = 1 := by decide
  have h1 : r = 1 := key r hr
  ext i j
  rw [← hrA, h1, map_one]
  rfl

theorem orderOf_c4 : orderOf c4 = 15 := by
  refine orderOf_eq_fifteen ?_ ?_ ?_
  · ext i j
    rw [coe_c4_pow, c4Mat_pow_fifteen]
    rfl
  · intro h
    apply c4Mat_pow_five
    rw [← coe_c4_pow, h]
    rfl
  · intro h
    apply c4Mat_pow_three
    rw [← coe_c4_pow, h]
    rfl

theorem exists_orderOf_fifteen {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ x : ProjectiveSpecialLinearGroup (Fin 4) K, orderOf x = 15 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
  set e := slMapEquiv 4 (FiniteField.ringEquivOfCardEq hcard) with he
  set π := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 4) K)) with hπ
  refine ⟨π (e.symm c4), ?_⟩
  have hz : ∀ k : ℕ, π (e.symm c4) ^ k = 1 → c4 ^ k = 1 := by
    intro k hk
    rw [← map_pow, ← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    apply eq_one_of_mem_center_SL4
    rw [Subgroup.mem_center_iff] at hk ⊢
    intro y
    have := hk (e.symm y)
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact this
  refine orderOf_eq_fifteen ?_ ?_ ?_
  · rw [← map_pow, ← map_pow, ← orderOf_c4, pow_orderOf_eq_one, map_one, map_one]
  · intro h
    have := hz 5 h
    have h2 := orderOf_dvd_of_pow_eq_one this
    rw [orderOf_c4] at h2
    norm_num at h2
  · intro h
    have := hz 3 h
    have h2 := orderOf_dvd_of_pow_eq_one this
    rw [orderOf_c4] at h2
    norm_num at h2

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Fischer Matrix C11P9A

theorem factL34NotL42_holds : FactL34NotL42 := by
  intro X _ h3 h4
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h3
  obtain ⟨-, K', _, _, hK', ⟨e'⟩⟩ := h4
  obtain ⟨y, hy⟩ := exists_orderOf_fifteen (K := K') (by rw [hK']; norm_num)
  set φ := (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K').trans
    (e'.symm.trans (e.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm))
  exact orderOf_ne_fifteen (K := K) (by rw [hK]; norm_num) (φ y)
    ((orderOf_injective φ.toMonoidHom φ.injective y).trans hy)

theorem factL34_holds : SecA.FactL34 := by
  intro K _ _ hK f hf
  have hZ : ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), f z = 1 := by
    intro z hz
    apply eq_one_of_mem_center_SL4
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨w, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, hz w]
  obtain ⟨g, hg⟩ := hf c4
  set π := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) K)) with hπ
  have hm : 0 < orderOf (π g) := orderOf_pos _
  have hgm : g ^ orderOf (π g) ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, pow_orderOf_eq_one]
  have h15 : 15 ∣ orderOf (π g) := by
    rw [← orderOf_c4]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← hg, ← map_pow, hZ _ hgm]
  obtain ⟨d, hd⟩ := h15
  have hd0 : d ≠ 0 := by
    rintro rfl
    omega
  apply orderOf_ne_fifteen hK (π g ^ d)
  rw [orderOf_pow' _ hd0, hd, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]

end CFSG.Quasithin.Vol2.Ch11.SecS
