module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2Core
public import CFSG.RankThree.PartOne.LIT.RankPSL3

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open Matrix CFSG.LieType.SeitzGeneration
open CFSG.Assembly.RankThreeEven (projSL projSU projSp sympForm)

theorem card_galoisField_two {n : ℕ} (hn : n ≠ 0) : Nat.card (GaloisField 2 n) = 2 ^ n :=
  GaloisField.card 2 n hn

theorem card_galoisField_two_mul_cast {n : ℕ} (hn : 1 ≤ n) (r : ℕ) :
    ((Nat.card (GaloisField 2 (2 * n)) : ℕ) : ZMod r) = (((2 ^ n : ℕ) : ZMod r)) ^ 2 := by
  rw [card_galoisField_two (by omega), ← Nat.cast_pow, ← pow_mul, mul_comm]

theorem natCast_ne_zero_galoisField {n r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    (r : GaloisField 2 n) ≠ 0 :=
  CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hr hr2

theorem rankLE1_projSL_three_of_ne_one {n r : ℕ} (hn : 1 ≤ n) (hr : r.Prime) (hr7 : 7 ≤ r)
    (hx : ((2 ^ n : ℕ) : ZMod r) ≠ 1) : RankLE1 r (projSL 3 (GaloisField 2 n)) := by
  set K := GaloisField 2 n
  have hr2 : r ≠ 2 := by omega
  have hrK : (r : K) ≠ 0 := natCast_ne_zero_galoisField hr hr2
  let H : Subgroup (GL (Fin 3) K) := (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker
  have hH : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) K).det = 1 := fun h hh => by
    have := MonoidHom.mem_ker.mp hh
    simpa [Units.ext_iff] using this
  have hN : ¬ r ∣ Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf H) :=
    CFSG.RankThree.PartOne.LIT.not_dvd_card_scalars (m := Fintype.card (Fin 3)) hr
      (by simpa using CFSG.RankThree.PartOne.LIT.not_dvd_three hr (by omega)) H
      fun g hg hc => CFSG.RankThree.PartOne.LIT.pow_card_eq_one_of_det g hc (hH g hg)
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K r :=
    two_le_ordQ hr hrK (by rwa [card_galoisField_two (by omega)])
  show RankLE1 r (CFSG.PGLModel.projImage H)
  exact rankLE1_projImage_of_lt hr hrK H hN (by simp only [Fintype.card_fin]; omega)

theorem rankLE1_projSp_two_of_ne {n r : ℕ} (hn : 1 ≤ n) (hr : r.Prime) (hr7 : 7 ≤ r)
    (h1 : ((2 ^ n : ℕ) : ZMod r) ≠ 1) (h2 : ((2 ^ n : ℕ) : ZMod r) ≠ -1) :
    RankLE1 r (projSp 2 (GaloisField 2 n)) := by
  set K := GaloisField 2 n
  have hr2 : r ≠ 2 := by omega
  have hrK : (r : K) ≠ 0 := natCast_ne_zero_galoisField hr hr2
  let S : Set (GL (Fin 2 ⊕ Fin 2) K) := {A | (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      sympForm 2 K * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sympForm 2 K}
  let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := Subgroup.closure S
  have hH : ∀ h ∈ H, (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * sympForm 2 K *
      (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sympForm 2 K :=
    CFSG.RankThree.PartOne.LIT.mem_closure_form fun g hg => hg
  have hN : ¬ r ∣ Nat.card ((Subgroup.center (GL (Fin 2 ⊕ Fin 2) K)).subgroupOf H) :=
    CFSG.RankThree.PartOne.LIT.not_dvd_card_scalars (m := 2) hr
      (CFSG.RankThree.PartOne.LIT.not_dvd_two hr hr2) H
      fun g hg hc => CFSG.RankThree.PartOne.LIT.sq_eq_one_of_form (sympForm 2 K)
        (CFSG.RankThree.PartOne.LIT.sympForm_det 2) g hc (hH g hg)
  have hK : ((Nat.card K : ℕ) : ZMod r) = ((2 ^ n : ℕ) : ZMod r) := by
    rw [card_galoisField_two (by omega)]
  have hd : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K r :=
    three_le_ordQ hr hrK (by rwa [hK]) (by rwa [hK])
  show RankLE1 r (CFSG.PGLModel.projImage H)
  refine rankLE1_projImage_of_lt hr hrK H hN ?_
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem rankLE2_projSp_two {K : Type} [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrK : (r : K) ≠ 0) : RankLE2 r (projSp 2 K) :=
  RankLE2.of_pRank hr (CFSG.RankThree.PartOne.LIT.pRank_projSp_two_le hr hr2 hrK)

@[expose] noncomputable def suGroup (m n : ℕ) : Subgroup (GL (Fin m) (GaloisField 2 (2 * n))) :=
  Subgroup.closure {A : GL (Fin m) (GaloisField 2 (2 * n)) |
    GeneralLinearGroup.det A = 1 ∧
    ((A : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * n))).map (· ^ (2 ^ n)))ᵀ *
      (A : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * n))) = 1}

theorem projSU_eq_projImage_suGroup (m n : ℕ) :
    projSU m 2 n = CFSG.PGLModel.projImage (suGroup m n) :=
  rfl

theorem det_of_mem_suGroup {m n : ℕ} {h : GL (Fin m) (GaloisField 2 (2 * n))}
    (hh : h ∈ suGroup m n) : (h : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * n))).det = 1 :=
  CFSG.RankThree.PartOne.LIT.mem_closure_det (fun g hg => by
    have := hg.1
    simpa [Units.ext_iff] using this) h hh

theorem not_dvd_card_scalars_suGroup {m n r : ℕ} (hr : r.Prime) (hrm : m < r) (hm : 0 < m) :
    ¬ r ∣ Nat.card ((Subgroup.center (GL (Fin m) (GaloisField 2 (2 * n)))).subgroupOf
      (suGroup m n)) :=
  CFSG.RankThree.PartOne.LIT.not_dvd_card_scalars (m := Fintype.card (Fin m)) hr
    (by
      rw [Fintype.card_fin]
      intro h
      have := Nat.le_of_dvd hm h
      omega) (suGroup m n)
    fun g hg hc => CFSG.RankThree.PartOne.LIT.pow_card_eq_one_of_det g hc (det_of_mem_suGroup hg)

theorem rankLE1_projSU_three_of_ne {n r : ℕ} (hn : 1 ≤ n) (hr : r.Prime) (hr7 : 7 ≤ r)
    (h1 : ((2 ^ n : ℕ) : ZMod r) ≠ 1) (h2 : ((2 ^ n : ℕ) : ZMod r) ≠ -1) :
    RankLE1 r (projSU 3 2 n) := by
  haveI : Fact r.Prime := ⟨hr⟩
  set K := GaloisField 2 (2 * n)
  have hr2 : r ≠ 2 := by omega
  have hrK : (r : K) ≠ 0 := natCast_ne_zero_galoisField hr hr2
  have hy : ((Nat.card K : ℕ) : ZMod r) ≠ 1 := by
    rw [card_galoisField_two_mul_cast hn]
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact h1 h
    · exact h2 h
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K r := two_le_ordQ hr hrK hy
  rw [projSU_eq_projImage_suGroup]
  refine rankLE1_projImage_of_lt hr hrK (suGroup 3 n)
    (not_dvd_card_scalars_suGroup hr (by omega) (by norm_num)) ?_
  simp only [Fintype.card_fin]
  omega

theorem rankLE1_projSU_four_of_ne {n r : ℕ} (hn : 1 ≤ n) (hr : r.Prime) (hr7 : 7 ≤ r)
    (h1 : ((2 ^ n : ℕ) : ZMod r) ≠ 1) (h2 : ((2 ^ n : ℕ) : ZMod r) ≠ -1)
    (h4 : ((2 ^ n : ℕ) : ZMod r) ^ 2 ≠ -1) : RankLE1 r (projSU 4 2 n) := by
  haveI : Fact r.Prime := ⟨hr⟩
  set K := GaloisField 2 (2 * n)
  have hr2 : r ≠ 2 := by omega
  have hrK : (r : K) ≠ 0 := natCast_ne_zero_galoisField hr hr2
  have hy1 : ((Nat.card K : ℕ) : ZMod r) ≠ 1 := by
    rw [card_galoisField_two_mul_cast hn]
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact h1 h
    · exact h2 h
  have hy2 : ((Nat.card K : ℕ) : ZMod r) ≠ -1 := by
    rw [card_galoisField_two_mul_cast hn]
    exact h4
  have hd : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K r := three_le_ordQ hr hrK hy1 hy2
  rw [projSU_eq_projImage_suGroup]
  refine rankLE1_projImage_of_lt hr hrK (suGroup 4 n)
    (not_dvd_card_scalars_suGroup hr (by omega) (by norm_num)) ?_
  simp only [Fintype.card_fin]
  omega

theorem rankLE2_projSU_three {n r : ℕ} (hn : 1 ≤ n) (hr : r.Prime) (hr2 : r ≠ 2) :
    RankLE2 r (projSU 3 2 n) :=
  RankLE2.of_pRank hr (CFSG.RankThree.PartOne.LIT.pRank_projSU_three_le hn hr hr2)

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
