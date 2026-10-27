module

public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIso
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

open scoped commutatorElement

namespace InndiagCommSU

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

theorem commutator_top_le_primeFormD [Finite K] (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) :
    ⁅(⊤ : Subgroup (MulAut (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)))), ⊤⁆ ≤
      primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  rw [← hker, Subgroup.commutator_le]
  intro α _ β _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact ringEquiv_mul_comm_of_finite _ _

variable [Finite K] [CharP K 2]

theorem primeFormConjHom_mem_ggInndiagComm
    (B : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    primeFormConjHom h _ B ∈
      ggInndiagComm (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
  have hC := isPrimeFormGram_one (K := K) (n := d)
  set φ : K ≃+* K := frobeniusEquiv K 2 with hφ
  set M := primeFormFieldU h hC φ B with hM
  have h1 : ⁅primeFormFieldHom h hC φ, primeFormConjHom h _ B⁆ =
      primeFormConjHom h _ (M * B⁻¹) := by
    rw [commutatorElement_def, primeFormField_conj_eq, map_mul, map_inv]
  set S := B⁻¹ * (M * B⁻¹) with hS
  have hdM : GeneralLinearGroup.det (M : GL (Fin d) K) =
      GeneralLinearGroup.det (B : GL (Fin d) K) ^ 2 := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val,
      GeneralLinearGroup.val_det_apply]
    change ((glAut φ (B : GL (Fin d) K) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = _
    rw [coe_glAut, show ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map φ =
      (φ : K →+* K).mapMatrix ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) from rfl,
      ← RingHom.map_det]
    exact frobeniusEquiv_apply K 2 _
  have hdetS : GeneralLinearGroup.det (S : GL (Fin d) K) = 1 := by
    have e : (S : GL (Fin d) K) = (B : GL (Fin d) K)⁻¹ * ((M : GL (Fin d) K) * (B : GL (Fin d) K)⁻¹) :=
      rfl
    rw [e, map_mul, map_mul, map_inv, hdM]
    group
  have hdetS' : ((S : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hdetS, Units.val_one]
  have hSsu : (S : GL (Fin d) K) ∈ gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    (mem_gramSU_iff_unitary h).mpr ⟨S.2, hdetS'⟩
  have h2 : primeFormConjHom h _ B =
      ⁅primeFormFieldHom h hC φ, primeFormConjHom h _ B⁆ * (primeFormConjHom h _ S)⁻¹ := by
    rw [h1, ← map_inv, ← map_mul]
    congr 1
    rw [hS]
    group
  rw [h2]
  refine Subgroup.mul_mem _ (commutator_mem_ggInndiagComm _ _)
    (Subgroup.inv_mem _ (range_conj_le_ggInndiagComm ?_))
  exact (mem_inner_primeFormP h _ (primeFormConjHom h _ S)).mpr ⟨⟨_, hSsu⟩, rfl⟩

theorem ggInndiagCommEq_unitary (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) :
    GGInndiagCommEq (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  have hd1 : 1 ≤ d := by omega
  set E := MulAut.congr (InndiagSU.projEquiv h hd1) with hE
  have hinn : (MulAut.conj : primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →*
      MulAut _).range ≤ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro α hα
    obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h _ α).mp hα
    exact ⟨_, rfl⟩
  have hDC : primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ggInndiagComm (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
    refine le_antisymm ?_ (sup_le hinn (commutator_top_le_primeFormD h hd hq))
    rintro _ ⟨B, rfl⟩
    exact primeFormConjHom_mem_ggInndiagComm h B
  have hmap : (ggInndiag (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))).map E.toMonoidHom =
      primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    apply le_antisymm
    · rw [ggInndiag, Subgroup.map_sup, map_congr_range_conj, MonoidHom.map_closure]
      refine sup_le hinn ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨φ, hφ, rfl⟩
      exact InndiagSU.congr_mem_primeFormD h hd1 hK hφ
    · rintro _ ⟨B, rfl⟩
      exact ⟨E.symm (primeFormConjHom h _ B), subset_ggInndiag (InndiagSU.congr_symm_mem h hd1 B),
        E.apply_symm_apply _⟩
  show ggInndiag _ _ = ggInndiagComm _
  apply Subgroup.map_injective (f := E.toMonoidHom) E.injective
  rw [hmap, hDC, map_congr_ggInndiagComm]

end InndiagCommSU

theorem recipeUnitary_inndiagComm {d n : ℕ} (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) {Q : LargeEvenRawCont} (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard GGInndiagCommEq R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun _ _ => InndiagCommSU.ggInndiagCommEq_unitary hn hK hd hq⟩

theorem largeEvenLabelAll_inndiagComm_unitary {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGInndiagUnitaryLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  intro Q hQ
  rcases h with h | ⟨h, hl3⟩
  · dsimp only at h
    subst h
    obtain ⟨hl2, hl2n⟩ := hl
    refine recipeUnitary_inndiagComm hn (by omega) (fun ⟨h3, h2⟩ => ?_) hQ
    change l + 1 = 3 at h3
    change 2 ^ n = 2 at h2
    have hn2 : 2 ≤ n := hl2n (by omega)
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · dsimp only at h hl3
    subst h hl3
    have h32 : (3 : ℕ) ≠ 2 := by decide
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [h32, ↓reduceIte] at hQ ⊢
    exact recipeUnitary_inndiagComm hn (by norm_num) (by omega) hQ

end CFSG.StandardType

end
