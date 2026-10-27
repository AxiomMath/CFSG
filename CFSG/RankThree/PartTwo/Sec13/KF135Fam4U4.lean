module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddSU
public import CFSG.RankThree.PartOne.SRC.ModelU4Two
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.Models.PGL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL
public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddPair
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Subgroup
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU StatedScalars)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartOne.SRC (blockPairSU4 negDiagSU4 blockPairSU4_commute
  sq_eq_one_of_blockPairSU4_mem_scalars negDiag4_not_scalar coe_negDiag4)

@[expose] def GateU4 : Prop :=
  ∀ (r p : ℕ) [Fact r.Prime] [Fact p.Prime], 3 < r → 7 ≤ p → p ∣ r ^ 2 + 1 →
    ∀ A : Subgroup (projSU 4 r 1), CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 2 → False

theorem dvd_sub_one_iff_zmod {p m : ℕ} (hm : 1 ≤ m) : p ∣ m - 1 ↔ ((m : ZMod p) = 1) := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hm, Nat.cast_one, sub_eq_zero]

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem psu4_hyp_false_of_gate (hgate : GateU4) {r : ℕ} [Fact r.Prime] (hr3 : 3 < r)
    (φ : S ≃* projSU 4 r 1) (h : KF135Hyp S p P x u V) : False := by
  set K := GaloisField r (2 * 1)
  have hKc : Nat.card K = (r ^ 1) ^ 2 := by
    rw [GaloisField.card r (2 * 1) (by norm_num)]
    ring
  haveI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = r ^ 2 := by rw [Fintype.card_eq_nat_card, hKc, pow_one]
  have hp : p.Prime := h.prime
  have hp7 := h.seven_le
  have : Fact p.Prime := ⟨hp⟩
  have hr : r.Prime := Fact.out
  have hK2 : (2 : K) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff K r] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  have hodd : Odd (r ^ 1) := by rw [pow_one]; exact hr.odd_of_ne_two (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 r 1 := ⟨hr, le_rfl, by norm_num, by simp⟩
  have hS := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm φ
  obtain ⟨hout, -⟩ :=
    CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound (Or.inr rfl)
      (by norm_num) hr le_rfl hS
  have hP : P ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
    refine P_le_inner_of_not_dvd h fun hd => ?_
    have h8 : Nat.card (Outer S) ∣ 8 := hout.trans (by
      simp only [CFSG.RankThree.OuterOrder.determinantParameter, pow_one, mul_one]
      exact Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_left 4 (r + 1)))
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      ((Nat.Prime.dvd_of_dvd_pow hp (n := 3) (by simpa using hd.trans h8)))
    omega
  set ψ : S ≃* StatedProj (StatedSU 4 (r ^ 1) K) :=
    φ.trans (CFSG.PGLModel.projSUEquivStatedProj 4 r 1)
  set mkU := QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (r ^ 1) K))
  by_cases hpq : p ∣ r * (r ^ 2 - 1)
  ·
    have hq : 1 ≤ r ^ 1 := Nat.one_le_pow _ _ hr.pos
    let f₁ : StatedSU 2 (r ^ 1) K →* S :=
      ψ.symm.toMonoidHom.comp (mkU.comp ((blockPairSU4 hq).comp (MonoidHom.inl _ _)))
    let f₂ : StatedSU 2 (r ^ 1) K →* S :=
      ψ.symm.toMonoidHom.comp (mkU.comp ((blockPairSU4 hq).comp (MonoidHom.inr _ _)))
    have hf : ∀ A B, f₁ A * f₂ B = ψ.symm (mkU (blockPairSU4 hq (A, B))) := by
      intro A B
      simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
        MulEquiv.coe_toMonoidHom, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    have hf' : ∀ A B, f₂ B * f₁ A = ψ.symm (mkU (blockPairSU4 hq (A, B))) := by
      intro A B
      simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
        MulEquiv.coe_toMonoidHom, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    have hscal : ∀ y, ψ.symm (mkU (blockPairSU4 hq y)) = 1 → y ^ 2 = 1 := by
      intro y hy
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hy
      exact sq_eq_one_of_blockPairSU4_mem_scalars hq hy
    have hkey : ∀ A B, f₁ A = f₂ B → A ^ 2 = 1 := by
      intro A B hAB
      have h1 : f₁ A * (f₂ B)⁻¹ = 1 := by rw [hAB, mul_inv_cancel]
      rw [← map_inv, hf A B⁻¹] at h1
      exact congrArg Prod.fst (hscal _ h1)
    have hSU : p ∣ Nat.card (StatedSU 2 (r ^ 1) K) := by
      rw [CFSG.RankThree.SubgroupLists.card_statedSU_two hKc, pow_one]; exact hpq
    have hnot : negDiagSU4 (K := K) hodd ∉ (StatedScalars (Fin 4) K).subgroupOf
        (StatedSU 4 (r ^ 1) K) := fun hm => negDiag4_not_scalar hK2 hm
    refine false_of_commuting_pair h (H₁ := f₁.range) (H₂ := f₂.range) ?_
      (dvd_card_range_of_ker f₁ hp (by omega) hSU ?_)
      (dvd_card_range_of_ker f₂ hp (by omega) hSU ?_) ?_
      (z := ψ.symm (mkU (negDiagSU4 hodd))) ?_ ?_ ?_ ?_
    · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
      rw [hf, hf']
    · intro A hA
      exact hkey A 1 (by rw [hA, map_one])
    · intro B hB
      have h1 : f₂ B = ψ.symm (mkU (blockPairSU4 hq (1, B))) := by
        simp only [f₂, MonoidHom.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom]
      rw [MonoidHom.mem_ker, h1] at hB
      exact congrArg Prod.snd (hscal _ hB)
    · rintro g ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
      rw [← map_pow, hkey A B hB.symm, map_one]
    · rintro _ ⟨A, rfl⟩
      simp only [f₁, MonoidHom.comp_apply, MonoidHom.inl_apply, MulEquiv.coe_toMonoidHom,
        ← map_mul, blockPairSU4_commute hq hodd]
    · rintro _ ⟨B, rfl⟩
      simp only [f₂, MonoidHom.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom,
        ← map_mul, blockPairSU4_commute hq hodd]
    · have hsq : (negDiagSU4 (K := K) hodd) ^ 2 = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
        change ((CFSG.RankThree.PartOne.SRC.negDiag4 K : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) ^ 2 = 1
        rw [coe_negDiag4, sq, Matrix.diagonal_mul_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal, Matrix.one_apply]
      rw [← map_pow, ← map_pow, hsq, map_one, map_one]
    · rw [Ne, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hnot
  ·
    obtain ⟨E₀, hE₀, hE₀c⟩ := exists_elemAbelian_of_le_inner h hP
    have hpS : p ∣ Nat.card S := by
      have := Subgroup.card_subgroup_dvd_card E₀
      rw [hE₀c] at this
      exact (dvd_pow_self p two_ne_zero).trans this
    have hcard := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSU_four_mul r 1 le_rfl
    rw [← Nat.card_congr φ.toEquiv, pow_one] at hcard
    have hp6 : p ∣ r ^ 6 * ((r ^ 2 - 1) * (r ^ 3 + 1) * (r ^ 4 - 1)) := by
      rw [← hcard]; exact Dvd.dvd.mul_right hpS _
    have hr1 : 1 ≤ r := hr.pos
    have hy0 : (r : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd; exact hpq (Dvd.dvd.mul_right hd _)
    have hy2 : (r : ZMod p) ^ 2 ≠ 1 := by
      intro h2
      apply hpq
      apply Dvd.dvd.mul_left
      rw [dvd_sub_one_iff_zmod (Nat.one_le_pow _ _ hr1), Nat.cast_pow]
      exact h2
    have hcases : (r : ZMod p) ^ 3 = -1 ∨ (r : ZMod p) ^ 2 = -1 := by
      have h0 : ((r ^ 6 * ((r ^ 2 - 1) * (r ^ 3 + 1) * (r ^ 4 - 1)) : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hp6
      have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr1
      have hr4 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ hr1
      push_cast [Nat.cast_sub hr2, Nat.cast_sub hr4] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hy0
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd (sub_eq_zero.1 h) hy2
        · exact Or.inl (eq_neg_of_add_eq_zero_left h)
      · have h4 : ((r : ZMod p) ^ 2 - 1) * ((r : ZMod p) ^ 2 + 1) = 0 := by
          rw [← h]; ring
        rcases mul_eq_zero.1 h4 with h | h
        · exact absurd (sub_eq_zero.1 h) hy2
        · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hcases with h3 | h2
    ·
      refine false_of_cyclic h hP fun E hE => ?_
      have hEp : IsPGroup p (E.map φ.toMonoidHom) := hE.isPGroup.map _
      obtain ⟨T, hT, ⟨e⟩⟩ := exists_mulEquiv_lift_of_le_range_toPGL K (q := p) (n := 4)
        (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega) (projSU 4 r 1)
        (projSU_le_range_toPGL 4 r 1) _ hEp
      have hjd : ∀ j, 1 ≤ j → j ≤ 4 → j ≠ 3 → ¬ p ∣ Fintype.card K ^ j - 1 := by
        intro j hj1 hj4 hj3 hd
        rw [hKf, dvd_sub_one_iff_zmod (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hr1)),
          Nat.cast_pow, Nat.cast_pow, ← pow_mul] at hd
        interval_cases j
        · exact hy2 (by simpa using hd)
        · apply hy2
          have h4 : (r : ZMod p) ^ 4 = 1 := by simpa using hd
          have h4' : (r : ZMod p) ^ 4 = -(r : ZMod p) := by
            rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, neg_one_mul]
          have hr' : (r : ZMod p) = -1 := by
            have : -(r : ZMod p) = 1 := h4'.symm.trans h4
            linear_combination -this
          rw [hr']; norm_num
        · exact (hj3 rfl).elim
        · apply hy2
          have h8 : (r : ZMod p) ^ 8 = 1 := by simpa using hd
          have h6 : (r : ZMod p) ^ 6 = 1 := by
            rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3]; norm_num
          calc (r : ZMod p) ^ 2 = (r : ZMod p) ^ 6 * (r : ZMod p) ^ 2 := by rw [h6, one_mul]
            _ = (r : ZMod p) ^ 8 := by ring
            _ = 1 := h8
      have hr0 : ¬ p ∣ Fintype.card K := by
        rw [hKf]; intro hd
        exact hy0 ((ZMod.natCast_eq_zero_iff _ _).2 (hp.dvd_of_dvd_pow hd))
      have hTGL : IsPGroup p (T.map (Matrix.SpecialLinearGroup.toGL)) := hT.map _
      have hcyc : IsCyclic (T.map (Matrix.SpecialLinearGroup.toGL)) :=
        CFSG.AGLEmbeddingD2.CyclicSylowGL.isCyclic_of_isPGroup_GL (m := 4) (d := 3)
          (by norm_num) (by norm_num) hr0 hjd _ hTGL
      have hTc : IsCyclic T := isCyclic_of_surjective _
        (T.equivMapOfInjective _ Matrix.SpecialLinearGroup.toGL_injective).symm.surjective
      have hE'c : IsCyclic (E.map φ.toMonoidHom) := isCyclic_of_surjective _ e.symm.surjective
      exact isCyclic_of_surjective _
        (E.equivMapOfInjective φ.toMonoidHom φ.injective).symm.surjective
    ·
      have hpr : p ∣ r ^ 2 + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]
        push_cast
        rw [h2]; ring
      obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) p (n := 2)
        (by rw [hE₀c])
      refine hgate r p hr3 hp7 hpr ((F₀.map E₀.subtype).map φ.toMonoidHom)
        ((hE₀.mono (Subgroup.map_subtype_le F₀)).map _) ?_
      rw [Subgroup.card_map_of_injective φ.injective,
        Subgroup.card_map_of_injective E₀.subtype_injective, hF₀]

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
