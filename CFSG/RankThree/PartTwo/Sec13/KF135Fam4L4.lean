module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddPair
public import CFSG.RankThree.PartOne.SRC.ModelL4Two
import CFSG.Models.PGL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL
public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddGL2
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Subgroup
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartOne.SRC (diagHom4 invol4 diagHom4_comm_invol4 invol4_sq
  sq_eq_one_of_diagHom4_mem_center coe_invol4)

@[expose] noncomputable def toProjSL (n : ℕ) (K : Type*) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K →* projSL n K :=
  (Matrix.SpecialLinearGroup.toPGL : Matrix.SpecialLinearGroup (Fin n) K →* PGL(n, K)).codRestrict
    (projSL n K) fun g => by rw [projSL_eq_range_toPGL3]; exact ⟨g, rfl⟩

theorem toProjSL_eq_one_iff {n : ℕ} {K : Type*} [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    toProjSL n K g = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  rw [← Matrix.SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker, ← Subtype.coe_inj]
  rfl

theorem card_SL_two (K : Type*) [Field K] [Fintype K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Fintype.card K * (Fintype.card K ^ 2 - 1) := by
  rw [Matrix.card_SL_field]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have h1 : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, mul_left_comm, ← mul_assoc, Nat.mul_div_cancel _ (by omega)]

theorem dvd_sub_one_of_dvd_three_four {p r : ℕ} (hr : 1 ≤ r) (h3 : p ∣ r ^ 3 - 1)
    (h4 : p ∣ r ^ 4 - 1) : p ∣ r - 1 := by
  have h3' : (p : ℤ) ∣ (r : ℤ) ^ 3 - 1 := by
    have := Int.natCast_dvd_natCast.2 h3
    rwa [Nat.cast_sub (Nat.one_le_pow _ _ hr), Nat.cast_pow, Nat.cast_one] at this
  have h4' : (p : ℤ) ∣ (r : ℤ) ^ 4 - 1 := by
    have := Int.natCast_dvd_natCast.2 h4
    rwa [Nat.cast_sub (Nat.one_le_pow _ _ hr), Nat.cast_pow, Nat.cast_one] at this
  have h1 : (p : ℤ) ∣ (r : ℤ) - 1 := by
    have := dvd_sub h4' (dvd_mul_of_dvd_right h3' (r : ℤ))
    have heq : (r : ℤ) ^ 4 - 1 - r * (r ^ 3 - 1) = r - 1 := by ring
    rwa [heq] at this
  exact Int.natCast_dvd_natCast.1 (by rwa [Nat.cast_sub hr, Nat.cast_one])

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem psl4_hyp_false {r : ℕ} [Fact r.Prime] (hr3 : 3 < r)
    (φ : S ≃* projSL 4 (GaloisField r 1)) (h : KF135Hyp S p P x u V) : False := by
  set K := GaloisField r 1
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = r := by
    rw [Fintype.card_eq_nat_card, GaloisField.card r 1 one_ne_zero, pow_one]
  have hp : p.Prime := h.prime
  have hp7 := h.seven_le
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : (2 : K) ≠ 0 := by
    intro h2
    have hc : ringChar K = r := ringChar.eq K r
    have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff K r] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 4 r 1 :=
    ⟨Fact.out, le_rfl, by norm_num, by simp, by simp⟩
  have hS := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ
  obtain ⟨hout, -⟩ :=
    CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound (Or.inl rfl)
      (by norm_num) Fact.out le_rfl hS
  have hP : P ≤ inner S := by
    refine P_le_inner_of_not_dvd h fun hd => ?_
    have h8 : Nat.card (Outer S) ∣ 8 := hout.trans (by
      simp only [CFSG.RankThree.OuterOrder.determinantParameter, pow_one, mul_one]
      exact Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_left 4 (r - 1)))
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      ((Nat.Prime.dvd_of_dvd_pow hp (n := 3) (by simpa using hd.trans h8)))
    omega
  by_cases hpq : p ∣ r * (r ^ 2 - 1)
  ·
    let f₁ : Matrix.SpecialLinearGroup (Fin 2) K →* S :=
      φ.symm.toMonoidHom.comp ((toProjSL 4 K).comp (diagHom4.comp (MonoidHom.inl _ _)))
    let f₂ : Matrix.SpecialLinearGroup (Fin 2) K →* S :=
      φ.symm.toMonoidHom.comp ((toProjSL 4 K).comp (diagHom4.comp (MonoidHom.inr _ _)))
    have hf : ∀ A B, f₁ A * f₂ B = φ.symm (toProjSL 4 K (diagHom4 (A, B))) := by
      intro A B
      simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
        MulEquiv.coe_toMonoidHom, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    have hf' : ∀ A B, f₂ B * f₁ A = φ.symm (toProjSL 4 K (diagHom4 (A, B))) := by
      intro A B
      simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
        MulEquiv.coe_toMonoidHom, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    have hkey : ∀ A B, f₁ A = f₂ B → A ^ 2 = 1 := by
      intro A B hAB
      have h1 : f₁ A * (f₂ B)⁻¹ = 1 := by rw [hAB, mul_inv_cancel]
      have h2 : f₁ A * f₂ B⁻¹ = φ.symm (toProjSL 4 K (diagHom4 (A, B⁻¹))) := hf A B⁻¹
      rw [← map_inv, h2, MulEquiv.map_eq_one_iff, toProjSL_eq_one_iff] at h1
      exact congrArg Prod.fst (sq_eq_one_of_diagHom4_mem_center h1)
    have hSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [card_SL_two, hKc]; exact hpq
    refine false_of_commuting_pair h (H₁ := f₁.range) (H₂ := f₂.range) ?_
      (dvd_card_range_of_ker f₁ hp (by omega) hSL ?_)
      (dvd_card_range_of_ker f₂ hp (by omega) hSL ?_) ?_
      (z := φ.symm (toProjSL 4 K invol4)) ?_ ?_ ?_ ?_
    · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
      rw [hf, hf']
    · intro A hA
      exact hkey A 1 (by rw [hA, map_one])
    · intro B hB
      have := hkey 1 B (by rw [hB, map_one])
      have h1 : f₂ B = φ.symm (toProjSL 4 K (diagHom4 (1, B))) := by
        simp only [f₂, MonoidHom.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom]
      rw [MonoidHom.mem_ker, h1, MulEquiv.map_eq_one_iff, toProjSL_eq_one_iff] at hB
      exact congrArg Prod.snd (sq_eq_one_of_diagHom4_mem_center hB)
    · rintro g ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
      rw [← map_pow, hkey A B hB.symm, map_one]
    · rintro _ ⟨A, rfl⟩
      simp only [f₁, MonoidHom.comp_apply, MonoidHom.inl_apply, MulEquiv.coe_toMonoidHom,
        ← map_mul, diagHom4_comm_invol4]
    · rintro _ ⟨B, rfl⟩
      simp only [f₂, MonoidHom.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom,
        ← map_mul, diagHom4_comm_invol4]
    · rw [← map_pow, ← map_pow, invol4_sq, map_one, map_one]
    · rw [Ne, MulEquiv.map_eq_one_iff, toProjSL_eq_one_iff]
      intro hc
      obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
      have e00 := congrFun (congrFun hc 0) 0
      have e22 := congrFun (congrFun hc 2) 2
      simp [coe_invol4, Matrix.scalar_apply] at e00 e22
      apply hK2
      first
        | linear_combination e00 - e22
        | linear_combination e22 - e00
  ·
    refine false_of_cyclic h hP fun E hE => ?_
    have hEp : IsPGroup p (E.map φ.toMonoidHom) := hE.isPGroup.map _
    obtain ⟨T, hT, ⟨e⟩⟩ := exists_mulEquiv_lift_of_le_range_toPGL K (q := p) (n := 4)
      (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega) (projSL 4 K)
      (projSL_le_range_toPGL3 4 K) _ hEp
    have hr0 : ¬ p ∣ Fintype.card K := by
      rw [hKc]; intro hd; exact hpq (Dvd.dvd.mul_right hd _)
    have hr1 : ¬ p ∣ Fintype.card K ^ 1 - 1 := by
      rw [hKc, pow_one]; intro hd
      exact hpq (Dvd.dvd.mul_left (hd.trans (by simpa using Nat.sub_dvd_pow_sub_pow r 1 2)) _)
    have hr2 : ¬ p ∣ Fintype.card K ^ 2 - 1 := by
      rw [hKc]; intro hd; exact hpq (Dvd.dvd.mul_left hd _)
    have hTGL : IsPGroup p (T.map (Matrix.SpecialLinearGroup.toGL)) := hT.map _
    have hcyc : IsCyclic (T.map (Matrix.SpecialLinearGroup.toGL)) := by
      by_cases h4 : p ∣ Fintype.card K ^ 4 - 1
      · refine CFSG.AGLEmbeddingD2.CyclicSylowGL.isCyclic_of_isPGroup_GL (m := 4) (d := 4)
          (by norm_num) le_rfl hr0 ?_ _ hTGL
        intro j hj1 hj4 hjd
        interval_cases j
        · exact hr1
        · exact hr2
        · intro h3
          rw [hKc] at h3 h4
          exact hr1 (by rw [hKc, pow_one]; exact dvd_sub_one_of_dvd_three_four (by omega) h3 h4)
        · exact (hjd rfl).elim
      · refine CFSG.AGLEmbeddingD2.CyclicSylowGL.isCyclic_of_isPGroup_GL (m := 4) (d := 3)
          (by norm_num) (by norm_num) hr0 ?_ _ hTGL
        intro j hj1 hj4 hjd
        interval_cases j
        · exact hr1
        · exact hr2
        · exact (hjd rfl).elim
        · exact h4
    have hTc : IsCyclic T := isCyclic_of_surjective _
      (T.equivMapOfInjective _ Matrix.SpecialLinearGroup.toGL_injective).symm.surjective
    have hE'c : IsCyclic (E.map φ.toMonoidHom) := isCyclic_of_surjective _ e.symm.surjective
    exact isCyclic_of_surjective _
      (E.equivMapOfInjective φ.toMonoidHom φ.injective).symm.surjective

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
