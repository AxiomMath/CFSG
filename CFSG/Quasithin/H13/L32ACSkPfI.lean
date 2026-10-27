module

public import CFSG.Quasithin.H13.L32ACSkPfH
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

section L34

variable {K : Type} [Field K]

@[expose] def cyc3 (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    rw [Matrix.det_fin_three]
    simp⟩

theorem coe_cyc3 :
    ((cyc3 K : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

theorem cyc3_pow_three : cyc3 K ^ 3 = 1 := by
  ext i j
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_cyc3,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem two_le_pRank_psl34 [Finite K] (hK : Nat.card K = 2 ^ 2) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL 3 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : Nat.card Kˣ = 3 := by
    have := Nat.card_eq_card_units_add_one K
    omega
  obtain ⟨ω, hω1⟩ : ∃ ω : Kˣ, ω ≠ 1 := by
    have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  have hω3 : ω ^ 3 = 1 := by
    rw [← hU]
    exact pow_card_eq_one'
  set w : K := (ω : K) with hw
  have hw3 : w ^ 3 = 1 := by rw [hw, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hw1 : w ≠ 1 := fun h => hω1 (Units.ext h)
  have hw0 : w ≠ 0 := ω.ne_zero
  set D := KG22.diag3 1 w (w ^ 2) (by rw [one_mul]; linear_combination hw3) with hD
  have hDn : ∀ n : ℕ,
      ((D ^ n : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    intro n
    rw [Matrix.SpecialLinearGroup.coe_pow, hD, KG22.coe_diag3, diagonal_pow, diagonal_apply_eq]
    simp
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_of_gens (x := proj 3 K D)
    (y := proj 3 K (cyc3 K)) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow]
    have : D ^ 3 = 1 := by
      ext i j
      rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD,
        KG22.coe_diag3, diagonal_mul_diagonal, diagonal_mul_diagonal,
        Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp
      · linear_combination hw3
      · linear_combination (w ^ 3 + 1) * hw3
    rw [this, map_one]
  · rw [← map_pow, cyc3_pow_three, map_one]
  ·
    set s := KG22.diag3 (w ^ 2) (w ^ 2) (w ^ 2) (by linear_combination (w ^ 3 + 1) * hw3) with hs
    have hs1 : proj 3 K s = 1 := by
      rw [proj_eq_one_iff, mem_scalars]
      refine ⟨ω ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow], ?_⟩
      rw [hs, KG22.coe_diag3, Units.val_pow_eq_pow_val, ← hw, scalar_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
    have hCD : cyc3 K * D = D * cyc3 K * s := by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, coe_cyc3, hD, hs, KG22.coe_diag3, KG22.coe_diag3]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      · linear_combination -hw3
      · linear_combination -w * hw3
    change proj 3 K D * proj 3 K (cyc3 K) = proj 3 K (cyc3 K) * proj 3 K D
    rw [← map_mul, ← map_mul, hCD, map_mul (proj 3 K) (D * cyc3 K) s, hs1, mul_one]
  · intro h1
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h1)
    have h00 := congrFun (congrFun hc 0) 0
    have h11 := congrFun (congrFun hc 1) 1
    simp [hD, KG22.coe_diag3, scalar_apply] at h00 h11
    exact hw1 (h11.trans h00.symm)
  · intro n hn
    rw [← map_pow, proj_eq_proj_iff] at hn
    obtain ⟨c, -, hc⟩ := mem_scalars.mp hn
    have h1 : ((cyc3 K : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((D ^ n : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          scalar (Fin 3) (c : K) := by
      rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    have h2 := congrFun (congrFun h1 0) 0
    rw [scalar_apply, mul_diagonal, hDn, one_mul, coe_cyc3] at h2
    simp at h2
    exact c.ne_zero h2.symm

end L34

section Rank

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_ne_one_of_isPSL34 (hL : IsPSL 3 2 2 (X ⧸ Subgroup.center X)) :
    CFSG.pRank 3 X ≠ 1 := by
  intro hr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX1 : CFSG.pRank 3 ↥(⊤ : Subgroup X) ≤ 1 := by
    rw [CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt (by norm_num) Subgroup.topEquiv, hr]
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  have hcyc : ∀ A : Subgroup (X ⧸ Subgroup.center X), IsPGroup 3 A → IsCyclic A := by
    intro A hA
    obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hπ 3 Q
    rw [Sylow.coe_mapSurjective] at hAQ
    have : IsCyclic (P : Subgroup X) := CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one
      Nat.prime_three (by norm_num) le_top P.isPGroup' hX1
    have : IsCyclic ((P : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X))) :=
      isCyclic_of_surjective _ ((QuotientGroup.mk' (Subgroup.center X)).subgroupMap_surjective P)
    exact Subgroup.isCyclic_of_le hAQ
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (e.trans (K1.statedProjEquivProjectiveSL 3 K))]
    exact two_le_pRank_psl34 hK
  obtain ⟨E, -, hel, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup (X ⧸ Subgroup.center X))
  have := hcyc E (IsPGroup.of_card hcard)
  have hexp : Monoid.exponent E ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, hel.2 a a.2, OneMemClass.coe_one])
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have h9 : 3 ^ 2 ∣ 3 := (Nat.pow_dvd_pow 3 h2).trans hexp
  norm_num at h9

end Rank

theorem lieBorelTwoInner_holds :
    LieBorelTwoInner :=
  lieBorelTwoInner_of (fun _ _ _ _ hn _ hL => (n2Model_n4Model_of_isLieChar2 hn hL).2)
    fun _ _ _ _ _ hL => pRank_three_ne_one_of_isPSL34 hL

end CFSG.Quasithin.H13.L32A.C.SkPf
