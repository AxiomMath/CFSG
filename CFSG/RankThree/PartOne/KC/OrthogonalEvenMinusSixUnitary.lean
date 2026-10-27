module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixRep
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module Matrix CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

section UnitaryData

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem EvenNormPlane.exists_unitaryFieldData :
    ∃ (f : ℕ) (h : UnitaryFieldData 2 f E), Nat.card K = 2 ^ f ∧ ∀ z, h.bar z = D.σ z := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hKc : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hE : Nat.card E = 2 ^ (2 * (n : ℕ)) := by rw [D.card_E, hKc, ← pow_mul, mul_comm]
  refine ⟨n, ⟨Nat.prime_two, n.pos, hE⟩, hKc, fun z => ?_⟩
  rw [UnitaryFieldData.bar_apply, D.sigma_eq_pow, hKc]

end UnitaryData

section Gram

variable {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)

theorem evenSixHerm_det_ne_zero : (evenSixHerm E).det ≠ 0 := by
  intro h0
  have := congrArg det (evenSixHerm_mul_self (E := E))
  rw [det_mul, h0, zero_mul, det_one] at this
  exact zero_ne_one this

theorem evenSixHerm_conjTranspose : ((evenSixHerm E).map h.bar)ᵀ = evenSixHerm E := by
  rw [evenSixHerm_map, evenSixHerm_transpose]

theorem gramForm_evenSixHerm_isSymm : (gramForm h (evenSixHerm E)).IsSymm :=
  gramForm_isSymm h (evenSixHerm_conjTranspose h)

theorem gramForm_evenSixHerm_separatingLeft : (gramForm h (evenSixHerm E)).SeparatingLeft :=
  gramForm_separatingLeft h evenSixHerm_det_ne_zero

variable {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra K E] (D : EvenNormPlane K E)

theorem EvenNormPlane.sixSU_eq_gramSU (hbar : ∀ z, h.bar z = D.σ z) :
    D.sixSU = gramSU h (evenSixHerm E) := by
  have hfun : (⇑h.bar : E → E) = ⇑D.σ := funext hbar
  ext g
  rw [EvenNormPlane.mem_sixSU, mem_gramSU, hfun]

theorem EvenNormPlane.nonempty_sixSU_mulEquiv (hbar : ∀ z, h.bar z = D.σ z) :
    Nonempty (D.sixSU ≃* StatedSU 4 (p ^ f) E) := by
  have hB := gramForm_evenSixHerm_isSymm h
  have hBl := gramForm_evenSixHerm_separatingLeft h
  have hdim : finrank E (Fin 4 → E) = 4 := by simp
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hB hBl
  let e : Module.Basis (Fin 4) E (Fin 4 → E) := e₀.reindex (finCongr hdim)
  have he : ∀ i j, gramForm h (evenSixHerm E) (e i) (e j) = (1 : Matrix (Fin 4) (Fin 4) E) i j := by
    intro i j
    simp only [e, Module.Basis.reindex_apply, he₀, (finCongr hdim).symm.injective.eq_iff,
      Matrix.one_apply]
  obtain ⟨φ₁⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h e he
  obtain ⟨φ₂⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h
    (Pi.basisFun E (Fin 4)) (B := gramForm h (evenSixHerm E)) (G := evenSixHerm E)
    (fun i j => by simp [gramForm_single])
  have hsu : unitarySU p f E 4 = gramSU h (1 : Matrix (Fin 4) (Fin 4) E) := unitarySU_eq_gramSU h 4
  exact ⟨((MulEquiv.subgroupCongr (D.sixSU_eq_gramSU h hbar)).trans φ₂.symm).trans
    (φ₁.trans (MulEquiv.subgroupCongr hsu.symm))⟩

end Gram

section Simple

variable {E : Type} [Field E] [CharP E 2]

theorem evenSix_eq_one_of_pow_four {c : E} (hc : c ^ 4 = 1) : c = 1 := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have h4 : (c + 1) ^ 4 = 0 := by
    linear_combination hc + (2 * c ^ 3 + 3 * c ^ 2 + 2 * c + 1) * h2
  have h5 : c + 1 = 0 := (pow_eq_zero_iff (by norm_num)).1 h4
  rw [eq_neg_of_add_eq_zero_left h5]
  exact CharTwo.neg_eq 1

theorem statedSU_four_char_two_perfect_simple {f : ℕ} (h : UnitaryFieldData 2 f E) :
    Group.IsPerfect (StatedSU 4 (2 ^ f) E) ∧ IsSimpleGroup (StatedSU 4 (2 ^ f) E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  have hF : Nat.card E = (2 ^ f) ^ 2 := h.card_eq_sq
  have hq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hh
    have := congrArg Prod.fst hh
    simp at this
  obtain ⟨hQ, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := E) (p := 2) (f := f) (n := 4) hF (by norm_num) hq
  have hbot : Subgroup.center (StatedSU 4 (2 ^ f) E) = ⊥ := by
    rw [hcen, Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hx
    have hdet := ((mem_unitarySU_iff h).1 x.2).1
    rw [← hc] at hdet
    simp [Matrix.scalar_apply, det_diagonal] at hdet
    have hc1 : c = 1 := Units.ext (evenSix_eq_one_of_pow_four hdet)
    refine Subtype.ext ?_
    rw [← hc, hc1, map_one]
    rfl
  have := hQ.2.1
  let e : StatedSU 4 (2 ^ f) E ≃* StatedSU 4 (2 ^ f) E ⧸ Subgroup.center (StatedSU 4 (2 ^ f) E) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  exact ⟨hQ.1, e.isSimpleGroup⟩

end Simple

section Facts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem EvenNormPlane.sixSU_isSimpleGroup : IsSimpleGroup D.sixSU := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  obtain ⟨f, h, -, hbar⟩ := D.exists_unitaryFieldData
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
  have := (statedSU_four_char_two_perfect_simple h).2
  exact θ.isSimpleGroup

theorem EvenNormPlane.sixSU_isPerfect : Group.IsPerfect D.sixSU := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  obtain ⟨f, h, -, hbar⟩ := D.exists_unitaryFieldData
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
  have := (statedSU_four_char_two_perfect_simple h).1
  exact Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective

theorem EvenNormPlane.card_sixSU :
    Nat.card D.sixSU = Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
      (Nat.card K ^ 4 - 1) := by
  obtain ⟨f, h, hK, hbar⟩ := D.exists_unitaryFieldData
  have hB := gramForm_evenSixHerm_isSymm h
  have hBl := gramForm_evenSixHerm_separatingLeft h
  have hdim : finrank E (Fin 4 → E) = 4 := by simp
  have hord := (CFSG.LinearGroups.unitary_full_group_order h hB hBl hdim (by norm_num)).2.1
  have hcard : Nat.card D.sixSU =
      Nat.card (CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup
        (gramForm h (evenSixHerm E))) := by
    rw [← card_gramSU,
      ← Nat.card_congr (MulEquiv.subgroupCongr (D.sixSU_eq_gramSU h hbar)).toEquiv]
  rw [hcard]
  have hq1 : ∀ k : ℕ, 1 ≤ Nat.card K ^ k := fun k => Nat.one_le_pow _ _ Nat.card_pos
  have hIcc : Finset.Icc 2 4 = {2, 3, 4} := by decide
  have e6 : 4 * (4 - 1) / 2 = 6 := by norm_num
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, ← hK, e6] at hord
  zify [hq1 2, hq1 4]
  linear_combination hord

end Facts

section Transvection

variable {E : Type} [Field E]

@[expose] def evenSixTransvectionMat (E : Type) [Field E] : Matrix (Fin 4) (Fin 4) E :=
  !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem evenSixTransvectionMat_mul_self [CharP E 2] :
    evenSixTransvectionMat E * evenSixTransvectionMat E = 1 := by
  have h2 : (1 : E) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenSixTransvectionMat, Matrix.mul_apply, Fin.sum_univ_four, h2]

@[expose] def evenSixTransvection (E : Type) [Field E] [CharP E 2] : GL (Fin 4) E :=
  ⟨evenSixTransvectionMat E, evenSixTransvectionMat E, evenSixTransvectionMat_mul_self,
    evenSixTransvectionMat_mul_self⟩

theorem coe_evenSixTransvection [CharP E 2] :
    ((evenSixTransvection E : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) =
      evenSixTransvectionMat E :=
  rfl

theorem evenSixTransvection_mem {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra K E]
    [CharP E 2] (D : EvenNormPlane K E) : evenSixTransvection E ∈ D.sixSU := by
  have h2 : (1 : E) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharTwo.two_eq_zero
  rw [EvenNormPlane.mem_sixSU, coe_evenSixTransvection]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenSixTransvectionMat, evenSixHerm, Matrix.mul_apply, Fin.sum_univ_four, h2]
  · rw [det_four]
    simp [evenSixTransvectionMat]

end Transvection

section Injective

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem EvenNormPlane.sixRho_injective : Function.Injective D.sixRho := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have hS := D.sixSU_isSimpleGroup
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hS.eq_bot_or_eq_top_of_normal D.sixRho.ker with hker | hker
  · exact hker
  · exfalso
    set t : D.sixSU := ⟨evenSixTransvection E, evenSixTransvection_mem D⟩ with ht
    have hmem : t ∈ D.sixRho.ker := by
      rw [hker]
      trivial
    have h1 : D.sixRho t = 1 := hmem
    have h2 : ((D.sixRho t (D.sixElement 0 0 1 0 0) : D.sixSpace) :
        Matrix (Fin 4) (Fin 4) E) 0 1 = 1 := by
      rw [D.coe_sixRho]
      simp [ht, coe_evenSixTransvection, evenSixTransvectionMat, EvenNormPlane.sixElement,
        EvenNormPlane.sixMat, altMat, Matrix.mul_apply, Fin.sum_univ_four]
    rw [h1] at h2
    simp [EvenNormPlane.sixElement, EvenNormPlane.sixMat, altMat] at h2

end Injective

end CFSG.RankThree.PartOne.KCOrthogonal
