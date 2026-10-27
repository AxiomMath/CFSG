module

public import CFSG.Quasithin.Vol2.KGFact1297SL
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.Quasithin.H13.KG1295

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.H13.KG1296 CFSG.Quasithin.H13.KG1297

local notation "SL₅" => SpecialLinearGroup (Fin 5) (ZMod 2)

theorem omg_mul_omg {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    omg i j hij * omg j i hij.symm = 1 := by
  simp only [omg, mul_assoc]
  rw [← mul_assoc (SpecialLinearGroup.transvection hij (1 : ZMod 2)),
    SLnTwo.transvection_mul_self, one_mul, SLnTwo.transvection_mul_self]

theorem mem_of_omg {M : Subgroup SL₅} {i j : Fin 5} (hij : i ≠ j) {g : SL₅}
    (h1 : omg i j hij ∈ M) (h2 : omg j i hij.symm * g ∈ M) : g ∈ M := by
  have e : g = omg i j hij * (omg j i hij.symm * g) := by
    rw [← mul_assoc, omg_mul_omg, one_mul]
  rw [e]
  exact M.mul_mem h1 h2

theorem mem_oTwoUpper_of_pow {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) {p : ℕ}
    (hp : p.Prime) (hp2 : Odd p) (h : x ^ p = 1) (h1 : x ≠ 1) : x ∈ oTwoUpper H := by
  have : Fact p.Prime := ⟨hp⟩
  exact mem_oTwoUpper_of_odd hx (by rw [orderOf_eq_prime h h1]; exact hp2)

theorem omg_mem_Ct {i j : Fin 5} (hij : i ≠ j) (hi0 : i ≠ 0) (hi4 : i ≠ 4) (hj0 : j ≠ 0)
    (hj4 : j ≠ 4) : omg i j hij ∈ Ct :=
  Ct.mul_mem (transvection_mem_Ct hij.symm hi0 hj4) (transvection_mem_Ct hij hj0 hi4)

theorem mem_oTwoUpper_Ct {i j : Fin 5} (hij : i ≠ j) (hi0 : i ≠ 0) (hi4 : i ≠ 4) (hj0 : j ≠ 0)
    (hj4 : j ≠ 4) (h3 : omg i j hij ^ 3 = 1) (h31 : omg i j hij ≠ 1) {g : SL₅} (hg : g ∈ Ct)
    {p : ℕ} (hp : p.Prime) (hp2 : Odd p) (hgp : (omg j i hij.symm * g) ^ p = 1)
    (hgp1 : omg j i hij.symm * g ≠ 1) : g ∈ oTwoUpper Ct :=
  mem_of_omg hij (mem_oTwoUpper_of_pow (omg_mem_Ct hij hi0 hi4 hj0 hj4) Nat.prime_three
    (by decide) h3 h31) (mem_oTwoUpper_of_pow (Ct.mul_mem (omg_mem_Ct hij.symm hj0 hj4 hi0 hi4)
    hg) hp hp2 hgp hgp1)

theorem oTwoUpper_Ct : oTwoUpper Ct = Ct := by
  refine le_antisymm (oTwoUpper_le _) ?_
  have hUC : unitriangular 5 (ZMod 2) ≤ Ct := Ct_eq ▸ KG1297.unitriangular_le_flag _
  have key : ∀ {p q : Fin 5} (hpq : p ≠ q), p ≠ 0 → p ≠ 4 → q ≠ 0 → q ≠ 4 →
      omg p q hpq ^ 3 = 1 → omg p q hpq ≠ 1 → ∀ {i j : Fin 5} (_ : i < j),
      (omg q p hpq.symm * LinearCover.rootSL (K := ZMod 2) i j) ^ 3 = 1 →
      omg q p hpq.symm * LinearCover.rootSL (K := ZMod 2) i j ≠ 1 →
      LinearCover.rootSL (K := ZMod 2) i j ∈ oTwoUpper Ct :=
    fun hpq hp0 hp4 hq0 hq4 h3 h31 _ _ hij h h1 => mem_oTwoUpper_Ct hpq hp0 hp4 hq0 hq4 h3 h31
      (hUC (LinearCover.rootSL_mem_unitriangular hij)) Nat.prime_three (by decide) h h1
  have h12 := key (p := 3) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 1) (j := 2) (by decide) (by decide) (by decide)
  have h23 := key (p := 2) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 2) (j := 3) (by decide) (by decide) (by decide)
  have h01 := key (p := 2) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 0) (j := 1) (by decide) (by decide) (by decide)
  have h34 := key (p := 3) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 3) (j := 4) (by decide) (by decide) (by decide)
  have h13 := key (p := 2) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 1) (j := 3) (by decide) (by decide) (by decide)
  have h02 := key (p := 2) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 0) (j := 2) (by decide) (by decide) (by decide)
  have h03 := key (p := 3) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 0) (j := 3) (by decide) (by decide) (by decide)
  have h14 := key (p := 2) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 1) (j := 4) (by decide) (by decide) (by decide)
  have h24 := key (p := 2) (q := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (i := 2) (j := 4) (by decide) (by decide) (by decide)
  have h04 : LinearCover.rootSL (K := ZMod 2) (0 : Fin 5) 4 ∈ oTwoUpper Ct := by
    rw [← LinearCover.commutatorElement_rootSL (K := ZMod 2) (j := 1) (by decide) (by decide)
      (by decide), commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h01 h14) (inv_mem h01)) (inv_mem h14)
  have hroot : ∀ i j : Fin 5, i < j → LinearCover.rootSL (K := ZMod 2) i j ∈ oTwoUpper Ct := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact h01 | exact h02 | exact h03 | exact h04 | exact h12 | exact h13 | exact h14
      | exact h23 | exact h24 | exact h34
  intro x hx
  have hgen := (subflag_stabilizer_generation (K := ZMod 2) (n := 5) ({1, 4} : Set ℕ)).1
  rw [Ct_eq, hgen] at hx
  refine (Subgroup.closure_le _).2 ?_ hx
  rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
  · rw [SetLike.mem_coe, BinaryParabolic.upperTriangular_eq_unitriangular] at hg
    refine (Subgroup.closure_le _).2 ?_ (LinearCover.unitriangular_le_closure_rootSL
      (Nat.card_zmod 2) hg)
    rintro _ ⟨i, j, hij, rfl⟩
    exact hroot i j hij
  · have hr : reflection 5 (ZMod 2) j hj hjn ∈ Ct :=
      Ct_eq ▸ ((subflag_stabilizer_generation (K := ZMod 2) (n := 5) ({1, 4} : Set ℕ)).2.2 j hj
        hjn).2 hjI
    have hj23 : j = 2 ∨ j = 3 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hjI
      omega
    rcases hj23 with rfl | rfl
    · have e : reflection 5 (ZMod 2) 2 hj hjn = reflection 5 (ZMod 2) 2 (by norm_num)
          (by norm_num) := rfl
      rw [e] at hr ⊢
      exact mem_oTwoUpper_Ct (i := 3) (j := 1) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hr (by norm_num : Nat.Prime 7) (by decide)
        (by decide) (by decide)
    · have e : reflection 5 (ZMod 2) 3 hj hjn = reflection 5 (ZMod 2) 3 (by norm_num)
          (by norm_num) := rfl
      rw [e] at hr ⊢
      exact mem_oTwoUpper_Ct (i := 2) (j := 1) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hr (by norm_num : Nat.Prime 7) (by decide)
        (by decide) (by decide)

end CFSG.Quasithin.H13.KG1295
