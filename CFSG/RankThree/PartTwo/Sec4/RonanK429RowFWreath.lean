module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt baseA wreathW)

theorem detOne_of_mul_eq_one {n : ℕ} {M N : Matrix (Fin n) (Fin n) (ZMod 2)} (h : M * N = 1) :
    M.det = 1 := by
  have h1 : M.det * N.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
  exact key _ _ h1

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {g x y : G} (h : g * x = y * g) :
    g * x * g⁻¹ = y := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

namespace W6

@[expose] def t1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def t1Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def t2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def t2Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def t3M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 1]

@[expose] def t3Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 1, 0]

@[expose] def twM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0]

@[expose] def twMi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0]

@[expose] def s1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def s2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def s3M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0]

theorem t1M_mul_t1Mi : t1M * t1Mi = 1 := by decide +kernel

theorem t2M_mul_t2Mi : t2M * t2Mi = 1 := by decide +kernel

theorem t3M_mul_t3Mi : t3M * t3Mi = 1 := by decide +kernel

theorem twM_mul_twMi : twM * twMi = 1 := by decide +kernel

theorem s1M_mul_s1M : s1M * s1M = 1 := by decide +kernel

theorem s2M_mul_s2M : s2M * s2M = 1 := by decide +kernel

theorem s3M_mul_s3M : s3M * s3M = 1 := by decide +kernel

@[expose] def mkSL6 (M N : Matrix (Fin 6) (Fin 6) (ZMod 2)) (h : M * N = 1) : SL(6, ZMod 2) :=
  ⟨M, detOne_of_mul_eq_one h⟩

@[expose] def T : Fin 3 → SL(6, ZMod 2) :=
  ![mkSL6 t1M t1Mi t1M_mul_t1Mi, mkSL6 t2M t2Mi t2M_mul_t2Mi, mkSL6 t3M t3Mi t3M_mul_t3Mi]

@[expose] def tw : SL(6, ZMod 2) := mkSL6 twM twMi twM_mul_twMi

@[expose] def s1 : SL(6, ZMod 2) := mkSL6 s1M s1M s1M_mul_s1M

@[expose] def s2 : SL(6, ZMod 2) := mkSL6 s2M s2M s2M_mul_s2M

@[expose] def s3 : SL(6, ZMod 2) := mkSL6 s3M s3M s3M_mul_s3M

theorem coe_T (i : Fin 3) :
    ((T i : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = ![t1M, t2M, t3M] i := by
  fin_cases i <;> rfl

@[expose] def r1 : SL(6, ZMod 2) := T 0

@[expose] def r2 : SL(6, ZMod 2) := T 0 * T 1

@[expose] def r3 : SL(6, ZMod 2) := T 0 * T 1 * T 2

theorem pow_T : ∀ i, T i ^ 3 = 1 := by decide +kernel

theorem comm_T : ∀ i j, T i * T j = T j * T i := by decide +kernel

theorem inj_T : ∀ v : Fin 3 → ZMod 3, vecElt T v = 1 → v = 0 := by decide +kernel

theorem pow_tw : tw ^ 3 = 1 := by decide +kernel

theorem conj0_T : tw * T 0 * tw⁻¹ = T 1 := by
  apply conj_eq_of_mul_eq
  decide +kernel

theorem conj1_T : tw * T 1 * tw⁻¹ = T 2 := by
  apply conj_eq_of_mul_eq
  decide +kernel

theorem conj2_T : tw * T 2 * tw⁻¹ = T 0 := by
  apply conj_eq_of_mul_eq
  decide +kernel

theorem t_ne_T : ∀ v : Fin 3 → ZMod 3, vecElt T v ≠ tw := by decide +kernel

theorem wreathFacts : WreathFacts T tw where
  pow_z := pow_T
  comm_z := comm_T
  inj := inj_T
  pow_t := pow_tw
  conj0 := conj0_T
  conj1 := conj1_T
  conj2 := conj2_T
  t_ne := t_ne_T

theorem card_SL6 : Nat.card SL(6, ZMod 2) = 20158709760 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem factorization_card_SL6 : (Nat.card SL(6, ZMod 2)).factorization 3 = 4 := by
  rw [card_SL6, show (20158709760 : ℕ) = 3 ^ 4 * 248872960 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW : Nat.card (wreathW T tw) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (Item434Kit.isPGroup_wreathW wreathFacts)
  rw [factorization_card_SL6] at hle
  have := Item434Kit.le_card_wreathW wreathFacts
  norm_num at hle
  omega

@[expose] def cands : List SL(6, ZMod 2) :=
  [1, s1, s2, s3, s1 * s2, s1 * s3, s2 * s3, s1 * s2 * s3,
    tw, s1 * tw, s2 * tw, s3 * tw, s1 * s2 * tw, s1 * s3 * tw, s2 * s3 * tw, s1 * s2 * s3 * tw,
    tw ^ 2, s1 * tw ^ 2, s2 * tw ^ 2, s3 * tw ^ 2, s1 * s2 * tw ^ 2, s1 * s3 * tw ^ 2,
    s2 * s3 * tw ^ 2, s1 * s2 * s3 * tw ^ 2]

theorem conj_table : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ c ∈ cands,
    c * vecElt T v = r1 * c ∨ c * vecElt T v = r2 * c ∨ c * vecElt T v = r3 * c := by
  decide +kernel

theorem isConj_rep (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    IsConj (vecElt T v) r1 ∨ IsConj (vecElt T v) r2 ∨ IsConj (vecElt T v) r3 := by
  obtain ⟨c, -, h⟩ := conj_table v hv
  rcases h with h | h | h
  · exact Or.inl (isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr h⟩)
  · exact Or.inr (Or.inl (isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr h⟩))
  · exact Or.inr (Or.inr (isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr h⟩))

theorem vecElt_zero_T : vecElt T 0 = 1 := by decide +kernel

theorem exists_rep {E : Subgroup SL(6, ZMod 2)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) {s : SL(6, ZMod 2)} (hs : s ∈ E) (hs1 : s ≠ 1) :
    IsConj s r1 ∨ IsConj s r2 ∨ IsConj s r3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW T tw)
    (by rw [card_wreathW, factorization_card_SL6]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle := Item434AltPerm.map_conj_inv_le hg
  have hcard : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective, h27]
  have hEq := Item434Kit.eq_baseA_of_le_wreathW wreathFacts card_wreathW hle
    (CFSG.Open.IsElemAbelian.map hE _) hcard
  have hs' : MulAut.conj g⁻¹ s ∈ baseA T := by
    rw [← hEq]
    exact Subgroup.mem_map_of_mem _ hs
  obtain ⟨v, hv⟩ := (Item434Kit.mem_baseA_iff wreathFacts).mp hs'
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hs1
    apply (MulAut.conj g⁻¹).injective
    rw [map_one, ← hv, vecElt_zero_T]
  have key : ∀ x : SL(6, ZMod 2), IsConj (MulAut.conj g⁻¹ s) x → IsConj s x := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    refine isConj_iff.mpr ⟨c * g⁻¹, ?_⟩
    rw [← hc, MulAut.conj_apply]
    group
  rcases isConj_rep v hv0 with h | h | h
  · rw [hv] at h
    exact Or.inl (key _ h)
  · rw [hv] at h
    exact Or.inr (Or.inl (key _ h))
  · rw [hv] at h
    exact Or.inr (Or.inr (key _ h))

end W6

namespace W7

@[expose] def t1M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def t1Mi : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def t2M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def t2Mi : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def t3M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def t3Mi : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def twM : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def twMi : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def s1M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def s2M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def s3M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1]

theorem t1M_mul_t1Mi : t1M * t1Mi = 1 := by decide +kernel

theorem t2M_mul_t2Mi : t2M * t2Mi = 1 := by decide +kernel

theorem t3M_mul_t3Mi : t3M * t3Mi = 1 := by decide +kernel

theorem twM_mul_twMi : twM * twMi = 1 := by decide +kernel

theorem s1M_mul_s1M : s1M * s1M = 1 := by decide +kernel

theorem s2M_mul_s2M : s2M * s2M = 1 := by decide +kernel

theorem s3M_mul_s3M : s3M * s3M = 1 := by decide +kernel

@[expose] def mkSL7 (M N : Matrix (Fin 7) (Fin 7) (ZMod 2)) (h : M * N = 1) : SL(7, ZMod 2) :=
  ⟨M, detOne_of_mul_eq_one h⟩

@[expose] def T : Fin 3 → SL(7, ZMod 2) :=
  ![mkSL7 t1M t1Mi t1M_mul_t1Mi, mkSL7 t2M t2Mi t2M_mul_t2Mi, mkSL7 t3M t3Mi t3M_mul_t3Mi]

@[expose] def tw : SL(7, ZMod 2) := mkSL7 twM twMi twM_mul_twMi

@[expose] def s1 : SL(7, ZMod 2) := mkSL7 s1M s1M s1M_mul_s1M

@[expose] def s2 : SL(7, ZMod 2) := mkSL7 s2M s2M s2M_mul_s2M

@[expose] def s3 : SL(7, ZMod 2) := mkSL7 s3M s3M s3M_mul_s3M

theorem coe_T (i : Fin 3) :
    ((T i : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) = ![t1M, t2M, t3M] i := by
  fin_cases i <;> rfl

@[expose] def r1 : SL(7, ZMod 2) := T 0

@[expose] def r2 : SL(7, ZMod 2) := T 0 * T 1

@[expose] def r3 : SL(7, ZMod 2) := T 0 * T 1 * T 2

theorem pow_T : ∀ i, T i ^ 3 = 1 := by decide +kernel

theorem comm_T : ∀ i j, T i * T j = T j * T i := by decide +kernel

theorem inj_T : ∀ v : Fin 3 → ZMod 3, vecElt T v = 1 → v = 0 := by decide +kernel

theorem pow_tw : tw ^ 3 = 1 := by decide +kernel

theorem conj0_T : tw * T 0 * tw⁻¹ = T 1 := by
  apply conj_eq_of_mul_eq
  decide +kernel

theorem conj1_T : tw * T 1 * tw⁻¹ = T 2 := by
  apply conj_eq_of_mul_eq
  decide +kernel

theorem conj2_T : tw * T 2 * tw⁻¹ = T 0 := by
  apply conj_eq_of_mul_eq
  decide +kernel

theorem t_ne_T : ∀ v : Fin 3 → ZMod 3, vecElt T v ≠ tw := by decide +kernel

theorem wreathFacts : WreathFacts T tw where
  pow_z := pow_T
  comm_z := comm_T
  inj := inj_T
  pow_t := pow_tw
  conj0 := conj0_T
  conj1 := conj1_T
  conj2 := conj2_T
  t_ne := t_ne_T

theorem card_SL7 : Nat.card SL(7, ZMod 2) = 163849992929280 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem factorization_card_SL7 : (Nat.card SL(7, ZMod 2)).factorization 3 = 4 := by
  rw [card_SL7, show (163849992929280 : ℕ) = 3 ^ 4 * 2022839418880 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW : Nat.card (wreathW T tw) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (Item434Kit.isPGroup_wreathW wreathFacts)
  rw [factorization_card_SL7] at hle
  have := Item434Kit.le_card_wreathW wreathFacts
  norm_num at hle
  omega

@[expose] def cands : List SL(7, ZMod 2) :=
  [1, s1, s2, s3, s1 * s2, s1 * s3, s2 * s3, s1 * s2 * s3,
    tw, s1 * tw, s2 * tw, s3 * tw, s1 * s2 * tw, s1 * s3 * tw, s2 * s3 * tw, s1 * s2 * s3 * tw,
    tw ^ 2, s1 * tw ^ 2, s2 * tw ^ 2, s3 * tw ^ 2, s1 * s2 * tw ^ 2, s1 * s3 * tw ^ 2,
    s2 * s3 * tw ^ 2, s1 * s2 * s3 * tw ^ 2]

theorem conj_table : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ c ∈ cands,
    c * vecElt T v = r1 * c ∨ c * vecElt T v = r2 * c ∨ c * vecElt T v = r3 * c := by
  decide +kernel

theorem isConj_rep (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    IsConj (vecElt T v) r1 ∨ IsConj (vecElt T v) r2 ∨ IsConj (vecElt T v) r3 := by
  obtain ⟨c, -, h⟩ := conj_table v hv
  rcases h with h | h | h
  · exact Or.inl (isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr h⟩)
  · exact Or.inr (Or.inl (isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr h⟩))
  · exact Or.inr (Or.inr (isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr h⟩))

theorem vecElt_zero_T : vecElt T 0 = 1 := by decide +kernel

theorem exists_rep {E : Subgroup SL(7, ZMod 2)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) {s : SL(7, ZMod 2)} (hs : s ∈ E) (hs1 : s ≠ 1) :
    IsConj s r1 ∨ IsConj s r2 ∨ IsConj s r3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW T tw)
    (by rw [card_wreathW, factorization_card_SL7]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle := Item434AltPerm.map_conj_inv_le hg
  have hcard : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective, h27]
  have hEq := Item434Kit.eq_baseA_of_le_wreathW wreathFacts card_wreathW hle
    (CFSG.Open.IsElemAbelian.map hE _) hcard
  have hs' : MulAut.conj g⁻¹ s ∈ baseA T := by
    rw [← hEq]
    exact Subgroup.mem_map_of_mem _ hs
  obtain ⟨v, hv⟩ := (Item434Kit.mem_baseA_iff wreathFacts).mp hs'
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hs1
    apply (MulAut.conj g⁻¹).injective
    rw [map_one, ← hv, vecElt_zero_T]
  have key : ∀ x : SL(7, ZMod 2), IsConj (MulAut.conj g⁻¹ s) x → IsConj s x := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    refine isConj_iff.mpr ⟨c * g⁻¹, ?_⟩
    rw [← hc, MulAut.conj_apply]
    group
  rcases isConj_rep v hv0 with h | h | h
  · rw [hv] at h
    exact Or.inl (key _ h)
  · rw [hv] at h
    exact Or.inr (Or.inl (key _ h))
  · rw [hv] at h
    exact Or.inr (Or.inr (key _ h))

end W7

end CFSG.RankThree.PartTwo.Sec4.RonanK429F

end
