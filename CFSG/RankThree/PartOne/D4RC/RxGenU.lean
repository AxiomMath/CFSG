module

import CFSG.RankThree.PartOne.TCX.F4.A2Unitary
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.PartOne.D4RC.RxA0Def

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {L : Type} [Field L]


theorem rclu_normal_dichotomy {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := h
  rcases hsimple.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center Q))) with
    h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center Q) x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) :=
      h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hMZ : M ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) M
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator Q ≤ M := by
      have e : commutator Q = ⁅M ⊔ Subgroup.center Q, M ⊔ Subgroup.center Q⁆ := by
        rw [hMZ]; rfl
      rw [e]
      have hn : (M ⊔ Subgroup.center Q).Normal := by rw [hMZ]; infer_instance
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left M M
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

def rcluP01 [CharP L 2] : SL(3, L) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; simp [CharTwo.neg_eq]⟩

def rcluP12 [CharP L 2] : SL(3, L) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by rw [Matrix.det_fin_three]; simp [CharTwo.neg_eq]⟩

theorem rclu_conj_T12 [CharP L 2] :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L) *
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : L) *
        (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L))⁻¹ =
      rcluP01 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rcluP01, Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, Matrix.adjugate_fin_three,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem rclu_P01_mem_unitary [CharP L 2] {q : ℕ} (hq : 1 ≤ q) :
    Matrix.SpecialLinearGroup.toGL (rcluP01 (L := L)) ∈ unitarySet q 3 := by
  have hq2 : q ^ 2 ≠ 0 := by positivity
  have hc : ((Matrix.SpecialLinearGroup.toGL (rcluP01 (L := L)) : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; rfl
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [hc]
    fin_cases i <;> fin_cases j <;> simp [zero_pow hq2]
  · rw [hc, Matrix.det_fin_three]; simp [CharTwo.neg_eq]
  · rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, zero_pow (show q ≠ 0 by omega)]

theorem rclu_P12_mem_unitary [CharP L 2] {q : ℕ} (hq : 1 ≤ q) :
    Matrix.SpecialLinearGroup.toGL (rcluP12 (L := L)) ∈ unitarySet q 3 := by
  have hq2 : q ^ 2 ≠ 0 := by positivity
  have hc : ((Matrix.SpecialLinearGroup.toGL (rcluP12 (L := L)) : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; rfl
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [hc]
    fin_cases i <;> fin_cases j <;> simp [zero_pow hq2]
  · rw [hc, Matrix.det_fin_three]; simp [CharTwo.neg_eq]
  · rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, zero_pow (show q ≠ 0 by omega)]

theorem rclu_P01_P12_ne [CharP L 2] :
    rcluP01 (L := L) * rcluP12 ≠ rcluP12 * rcluP01 := by
  intro h
  have h02 := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L) 0 2) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h02
  simp [rcluP01, rcluP12, Matrix.mul_apply, Fin.sum_univ_three] at h02

theorem rcl_gen_unitary {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ = 2) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (hq : 2 < ℓ ^ f)
    (Φ' : SL(3, L) ≃* SL(3, L)) (H : SL(3, L))
    (hH : ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
      Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
        (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    Subgroup.normalClosure (((rclA0AlgOf L k (H * Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (1 : L))).subgroupOf (fixSubgroup Φ') :
      Subgroup (fixSubgroup Φ')) : Set (fixSubgroup Φ')) = ⊤ := by
  subst hℓ2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : CharP k 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap k L).injective 2
  obtain ⟨K₂, _, _, _, ι, hK₂card, hK₂fix⟩ :=
    CFSG.RankThree.PartOne.KLCE.exists_subfield_card (L := L) (n := 2 * f) (by omega)
  have hK₂ : Nat.card K₂ = (2 ^ f) ^ 2 := by rw [hK₂card, ← pow_mul, mul_comm]
  obtain ⟨ψ, hψinj, hψrange⟩ :=
    CFSG.RankThree.PartOne.TCX.F4.exists_unitary_hom_of_fix ι hK₂ hK₂fix Φ' H hH
  have hne : (3, 2 ^ f) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f) hK₂
    (n := 3) le_rfl hne
  have hsimp := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K₂ 2 f hK₂ 3
    le_rfl hne
  have hQ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimp).1
  let e := (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)
  have hx : (H * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L)) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : L) *
      (H * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : L))⁻¹ =
        H * rcluP01 * H⁻¹ := by
    rw [← rclu_conj_T12]
    group
  have hmem : ∀ P : SL(3, L), Matrix.SpecialLinearGroup.toGL P ∈ unitarySet (2 ^ f) 3 →
      H * P * H⁻¹ ∈ fixSubgroup Φ' := fun P hP =>
    (hH _).2 ⟨_, hP, by simp only [map_mul, map_inv]⟩
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hxF := hmem _ (rclu_P01_mem_unitary (L := L) (q := 2 ^ f) hq1)
  have hyF := hmem _ (rclu_P12_mem_unitary (L := L) (q := 2 ^ f) hq1)
  let x : fixSubgroup Φ' := ⟨_, hxF⟩
  let y : fixSubgroup Φ' := ⟨_, hyF⟩
  have hxy : x * y ≠ y * x := by
    intro h
    apply rclu_P01_P12_ne (L := L)
    have h' := congrArg (fun z : fixSubgroup Φ' => H⁻¹ * (z : SL(3, L)) * H) h
    simpa [x, y, mul_assoc] using h'
  set N := Subgroup.normalClosure (((rclA0AlgOf L k (H * Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (1 : L))).subgroupOf (fixSubgroup Φ') :
      Subgroup (fixSubgroup Φ')) : Set (fixSubgroup Φ')) with hN
  have hxN : x ∈ N := by
    apply Subgroup.subset_normalClosure
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    show H * rcluP01 * H⁻¹ ∈ _
    rw [← hx]
    exact Subgroup.subset_closure ⟨1, by rw [map_one]⟩
  have : (N.comap e.toMonoidHom).Normal := Subgroup.Normal.comap inferInstance _
  rcases rclu_normal_dichotomy hQ (N.comap e.toMonoidHom) with hc | htop
  · exfalso
    apply hxy
    have hxc : e.symm x ∈ Subgroup.center _ := hc (by simpa using hxN)
    have h1 := congrArg e (Subgroup.mem_center_iff.mp hxc (e.symm y))
    simpa [map_mul] using h1.symm
  · rw [eq_top_iff]
    intro z _
    have : e.symm z ∈ N.comap e.toMonoidHom := htop ▸ Subgroup.mem_top _
    simpa using this

end CFSG.RankThree.PartOne.D4RC
