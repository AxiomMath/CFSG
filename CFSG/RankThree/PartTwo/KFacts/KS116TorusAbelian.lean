module

public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTorus

public section

namespace CFSG.RankThree.PartTwo.KFacts

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut)

variable {F : Type} [Field F] [CharP F 2]

theorem centralizer_eq_of_card_eq_sl2 [Fintype F] [DecidableEq F]
    (h8 : 8 ≤ Fintype.card F) {T : Subgroup SL(2, F)} (hTc : IsMulCommutative T)
    (hcard : Nat.card T = Fintype.card F - 1) {t₀ : SL(2, F)} (ht₀ : t₀ ∈ T)
    (ht₀ne : t₀ ≠ 1) :
    Subgroup.centralizer ({t₀} : Set SL(2, F)) = T := by
  classical
  set C := Subgroup.centralizer ({t₀} : Set SL(2, F)) with hCdef
  have hle : T ≤ C := by
    intro A hA
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro B hB
    rw [Set.mem_singleton_iff] at hB
    subst B
    exact (congrArg Subtype.val (isMulCommutative_iff.mp hTc ⟨A, hA⟩ ⟨t₀, ht₀⟩)).symm
  have hdvd : Nat.card T ∣ Nat.card C := Subgroup.card_dvd_of_le hle
  have hCle : Nat.card C ≤ Fintype.card F + 1 := KS116Proof.card_centralizer_le ht₀ne
  have hlt : Nat.card C < 2 * Nat.card T := by
    rw [hcard]
    omega
  have hCcard : Nat.card C = Nat.card T :=
    Nat.eq_of_dvd_of_lt_two_mul (Nat.card_pos (α := C)).ne' hdvd hlt
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hCcard)).symm

theorem exists_conj_of_fix_of_card_eq_sl2 [Fintype F] [DecidableEq F]
    (h8 : 8 ≤ Fintype.card F) {T : Subgroup SL(2, F)} (hTc : IsMulCommutative T)
    (hcard : Nat.card T = Fintype.card F - 1) (β : MulAut SL(2, F))
    (hfix : ∀ A ∈ T, β A = A) :
    ∃ M : SL(2, F), β = MulAut.conj M ∧ ∀ A ∈ T, M * A = A * M := by
  classical
  have hodd : Odd (Nat.card T) := by
    rw [hcard]
    have heven : Even (Fintype.card F) :=
      Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
    exact Nat.Even.sub_odd (by omega) heven odd_one
  have hcomm : ∀ A ∈ T, ∀ B ∈ T, A * B = B * A := by
    intro A hA B hB
    exact congrArg Subtype.val (isMulCommutative_iff.mp hTc ⟨A, hA⟩ ⟨B, hB⟩)
  obtain ⟨M, σ, hβeq⟩ :=
    CFSG.RankThree.PartOne.KCRootAxis.exists_conj_mul_slFieldAut (K := F) β
  have hfixσ : ∀ A ∈ T, M * slFieldAut F σ A * M⁻¹ = A := by
    intro A hA
    have h := hfix A hA
    rw [hβeq, MulAut.mul_apply, MulAut.conj_apply] at h
    exact h
  have hσ : σ = 1 :=
    KS116Proof.fieldAut_eq_one_of_fix h8 hodd hcomm (le_of_eq hcard.symm) M σ hfixσ
  have hβconj : β = MulAut.conj M := by
    rw [hβeq, hσ, map_one, mul_one]
  refine ⟨M, hβconj, ?_⟩
  intro A hA
  have h := hfix A hA
  rw [hβconj, MulAut.conj_apply] at h
  calc M * A = M * A * M⁻¹ * M := by group
    _ = A * M := by rw [h]

theorem eq_one_sl2_of_fix_of_two_pow [Fintype F] [DecidableEq F] (h8 : 8 ≤ Fintype.card F)
    {T : Subgroup SL(2, F)} (hTc : IsMulCommutative T) (hcard : Nat.card T = Fintype.card F - 1)
    (β : MulAut SL(2, F)) (hβ : ∃ k : ℕ, orderOf β = 2 ^ k) (hfix : ∀ A ∈ T, β A = A) :
    β = 1 := by
  classical
  obtain ⟨M, hβconj, hMfix⟩ :=
    exists_conj_of_fix_of_card_eq_sl2 h8 hTc hcard β hfix
  have hodd : Odd (Nat.card T) := by
    rw [hcard]
    have heven : Even (Fintype.card F) :=
      Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
    exact Nat.Even.sub_odd (by omega) heven odd_one
  have hcardT : 1 < Fintype.card T := by
    rw [← Nat.card_eq_fintype_card, hcard]
    omega
  obtain ⟨t, ht⟩ := Fintype.exists_ne_of_one_lt_card hcardT (1 : T)
  have htT : (t : SL(2, F)) ∈ T := t.2
  have htne : (t : SL(2, F)) ≠ 1 := fun h => ht (Subtype.ext h)
  have hC : Subgroup.centralizer ({(t : SL(2, F))} : Set SL(2, F)) = T :=
    centralizer_eq_of_card_eq_sl2 h8 hTc hcard htT htne
  have hMT : M ∈ T := by
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro B hB
    rw [Set.mem_singleton_iff] at hB
    subst B
    exact (hMfix _ htT).symm
  have hdvd : orderOf β ∣ Nat.card T := by
    rw [hβconj]
    exact (orderOf_map_dvd (MulAut.conj : SL(2, F) →* MulAut (SL(2, F))) M).trans
      (Subgroup.orderOf_dvd_natCard T hMT)
  have hoddβ : Odd (orderOf β) := hodd.of_dvd_nat hdvd
  obtain ⟨k, hk⟩ := hβ
  have hcop : Nat.Coprime (2 ^ k) (Nat.card T) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  have hone : 2 ^ k = 1 := by
    apply hcop.eq_one_of_dvd
    rwa [← hk]
  exact orderOf_eq_one_iff.mp (by rw [hk, hone])

end CFSG.RankThree.PartTwo.KFacts

end
