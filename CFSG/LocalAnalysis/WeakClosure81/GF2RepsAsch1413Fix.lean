module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413StrAux1
import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup

theorem a1413_exists_fixed_of_odd {Q : Type} [Group Q] [Finite Q] {A : Subgroup Q}
    (hA : IsPGroup 2 A) {D : Set Q} (hD : ∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D)
    (hodd : Odd (Nat.card D)) : ∃ d ∈ D, ∀ a ∈ A, a * d * a⁻¹ = d := by
  classical
  letI : MulAction ↥A ↥D :=
    { smul := fun a d => ⟨a.1 * d.1 * a.1⁻¹, hD a.1 a.2 d.1 d.2⟩
      one_smul := fun d => Subtype.ext (by
        show (1 : ↥A).1 * d.1 * (1 : ↥A).1⁻¹ = d.1
        simp)
      mul_smul := fun a b d => Subtype.ext (by
        show (a * b : ↥A).1 * d.1 * (a * b : ↥A).1⁻¹ =
          a.1 * (b.1 * d.1 * b.1⁻¹) * a.1⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hnotdvd : ¬ 2 ∣ Nat.card ↥D := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  obtain ⟨d, hd⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA ↥D hnotdvd
  exact ⟨d.1, d.2, fun a ha => congrArg Subtype.val (hd ⟨a, ha⟩)⟩

theorem psp4_conj_class_invariant {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (α : MulAut (StatedProj (StatedSp 2 K))) {x : StatedProj (StatedSp 2 K)}
    (hx : IsConj (u1 K) x) : IsConj (u1 K) (α x) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hchar : ringChar K ≠ 2 := by
    intro h
    have hEven : Fintype.card K % 2 = 0 := (FiniteField.even_card_iff_char_two (F := K)).mp h
    rw [← Nat.card_eq_fintype_card] at hEven
    have hOdd : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hT1sq : T1 K * T1 K = 1 := by
    apply sp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_T1, blk_mul]
    simp [blk_one_one]
  obtain ⟨A, σ, hAσ⟩ :=
    CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form hchar α
  set T' : StatedSp 2 K := conjSp 2 K A (T1 K) with hT'def
  have hconj : proj 2 K T' = conjAut 2 K A (u1 K) := by
    rw [hT'def, ← conjAut_proj, u1]
  have hne : proj 2 K T' ≠ 1 := fun h =>
    (conjAut 2 K A).injective.ne (u1_ne_one h2) (by rw [← hconj, h, map_one])
  have hT'sq : T' * T' = 1 := by
    rw [hT'def, ← map_mul, hT1sq, map_one]
  have hT'mat_sq : ((T' : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    have h := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hT'sq
    simpa using h
  have hT'ne1 : ((T' : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 1 := by
    intro h
    exact hne (by
      rw [← MonoidHom.mem_ker, ker_proj]
      exact (mem_spScalars_iff T').mpr (Or.inl h))
  have hT'neNeg : ((T' : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ -1 := by
    intro h
    exact hne (by
      rw [← MonoidHom.mem_ker, ker_proj]
      exact (mem_spScalars_iff T').mpr (Or.inr h))
  obtain ⟨g, hg⟩ := exists_conj_T1 h2 T' hT'mat_sq hT'ne1 hT'neNeg
  have hconjT' : IsConj (u1 K) (proj 2 K T') := by
    refine isConj_iff.mpr ⟨proj 2 K g, ?_⟩
    rw [u1, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [← hg]
    group
  have hfix : fieldAut 2 K σ (u1 K) = u1 K := by
    rw [u1, fieldAut_proj]
    congr 1
    apply sp_ext
    rw [coe_fieldSp, coe_T1, blk_one_neg_one_eq_diagonal, Matrix.diagonal_map (map_zero σ)]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp
  have hαu1 : IsConj (u1 K) (α (u1 K)) := by
    rw [hAσ, MulAut.mul_apply, hfix, ← hconj]
    exact hconjT'
  exact hαu1.trans (MonoidHom.map_isConj α.toMonoidHom hx)

theorem psp4_card_conj_u1_odd {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) :
    Odd (Nat.card {x : StatedProj (StatedSp 2 K) // IsConj (u1 K) x}) := by
  classical
  let P := StatedProj (StatedSp 2 K)
  let C : Subgroup P := centralizer ({u1 K} : Set P)
  set N : ℕ := Nat.card {x : P // IsConj (u1 K) x} with hNdef
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hT1sq : T1 K * T1 K = 1 := by
    apply sp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_T1, blk_mul]
    simp [blk_one_one]
  have hu1sq : u1 K * u1 K = 1 := by
    rw [u1, ← map_mul, hT1sq, map_one]
  have hOS : Nat.card (MulAction.orbit (ConjAct P) (u1 K)) *
      Nat.card (MulAction.stabilizer (ConjAct P) (u1 K)) = Nat.card P := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct P) (u1 K))
    rw [Nat.card_prod] at h
    rwa [Nat.card_congr ConjAct.ofConjAct.toEquiv] at h
  have horbit : N = Nat.card (MulAction.orbit (ConjAct P) (u1 K)) := by
    rw [hNdef]
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨x.1, ConjAct.mem_orbit_conjAct.mpr (IsConj.symm x.2)⟩
        invFun := fun x => ⟨x.1, IsConj.symm (ConjAct.mem_orbit_conjAct.mp x.2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hstab : Nat.card (MulAction.stabilizer (ConjAct P) (u1 K)) = Nat.card C := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun g => ⟨ConjAct.ofConjAct g.1, ?_⟩
        invFun := fun c => ⟨ConjAct.toConjAct c.1, ?_⟩
        left_inv := fun g => Subtype.ext (ConjAct.toConjAct_ofConjAct g.1)
        right_inv := fun c => Subtype.ext (ConjAct.ofConjAct_toConjAct c.1) }
    · rw [mem_centralizer_singleton_iff]
      have h := MulAction.mem_stabilizer_iff.mp g.2
      rw [ConjAct.smul_def] at h
      calc ConjAct.ofConjAct g.1 * u1 K =
          (ConjAct.ofConjAct g.1 * u1 K * (ConjAct.ofConjAct g.1)⁻¹) *
            ConjAct.ofConjAct g.1 := by group
        _ = u1 K * ConjAct.ofConjAct g.1 := by rw [h]
    · rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      have h := mem_centralizer_singleton_iff.mp c.2
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hN : N * Nat.card C = Nat.card P := by
    rw [horbit, ← hstab, hOS]
  have hC : Nat.card C = 2 * Nat.card (X0 K) := by
    have hrel := Subgroup.relIndex_mul_card (H := X0 K) (K := C)
    rw [a1413StrRelIndex_X0_C h2, inf_eq_left.mpr (X0_le_centralizer (K := K))] at hrel
    exact hrel.symm
  have hE1 : Nat.card (E1 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (E1Equiv h2).toEquiv]
    rw [LinearFlag.card_SL_eq (K := K) (n := 2) (by norm_num)]
    simp
  have hE2 : Nat.card (E2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (E2Equiv h2).toEquiv]
    rw [LinearFlag.card_SL_eq (K := K) (n := 2) (by norm_num)]
    simp
  have hX0 : Nat.card (X0 K) * 2 = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
    have hcomm : ∀ x ∈ E1 K, ∀ y ∈ E2 K, x * y = y * x :=
      fun x hx y hy => commute_E1_E2 hx hy
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (E1 K) (E2 K) hcomm).1
    rw [← a1413StrX0_eq_sup h2, a1413Str_inter_E1_E2 h2] at hprod
    rw [Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact hu1sq) (u1_ne_one h2)] at hprod
    rw [hE1, hE2] at hprod
    rw [hprod]
    ring
  have h1 : N * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 = Nat.card P := by
    rw [← hN, hC, mul_comm 2 (Nat.card (X0 K)), hX0]
  have h2' : N * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 * 2 =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    rw [h1, two_mul_card_P h2]
  have hq4 : Nat.card K ^ 4 - 1 =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 + 1) := by
    have h := Nat.pow_two_sub_pow_two (Nat.card K ^ 2) 1
    rw [show (1 : ℕ) ^ 2 = 1 from rfl,
      mul_comm (Nat.card K ^ 2 + 1) (Nat.card K ^ 2 - 1)] at h
    have h4 : Nat.card K ^ 4 = (Nat.card K ^ 2) ^ 2 := by ring
    rw [h4]
    exact h
  have h3 : (N * 2) * (Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) =
      (Nat.card K ^ 2 * (Nat.card K ^ 2 + 1)) *
        (Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) := by
    have hA : (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 =
        Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by ring
    rw [hA, hq4] at h2'
    nlinarith [h2']
  have hN2 : N * 2 = Nat.card K ^ 2 * (Nat.card K ^ 2 + 1) := by
    refine Nat.eq_of_mul_eq_mul_right ?_ h3
    have hq1 : 1 < Nat.card K := by omega
    have hq2 : 1 < Nat.card K ^ 2 := one_lt_pow₀ hq1 (by norm_num)
    exact Nat.mul_pos (pow_pos Nat.card_pos 2) (pow_pos (Nat.sub_pos_of_lt hq2) 2)
  obtain ⟨k, hk⟩ := hodd
  rw [hk] at hN2
  have hval : N = (4 * k ^ 2 + 4 * k + 1) * (2 * k ^ 2 + 2 * k + 1) := by
    have h : N * 2 = ((4 * k ^ 2 + 4 * k + 1) * (2 * k ^ 2 + 2 * k + 1)) * 2 := by
      rw [hN2]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  rw [hval]
  exact Odd.mul ⟨2 * k ^ 2 + 2 * k, by ring⟩ ⟨k ^ 2 + k, by ring⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
