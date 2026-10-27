module

public import CFSG.RankThree.GF2n.Parrott.SpinWords
public import CFSG.RankThree.GF2n.Parrott.SylowH
public import CFSG.RankThree.GF2n.Parrott.SpinForms
public import CFSG.RankThree.GF2n.Parrott.SpinPack45

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinWords
open scoped Matrix
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack64 (pk_mul eq_of_pk conj_of pow_eq_one_of)
open CFSG.RankThree.GF2n.Parrott.Pack45 (h45 pk_one pk_u pk_v pk_a1 pk_b1 pk_a2 pk_b2 pk_s1 pk_s2
  pk_s1i)
open CFSG.RankThree.GF2n.Parrott.SpinPack45 (pk_word)


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

@[expose] def spinW0 : V := ![0, 1, 0, 1, 1, 0, 0, 0]

theorem spinW0_ne_zero : spinW0 ≠ 0 := by
  decide +kernel

theorem q_spinW0 : q spinW0 = 0 := by
  decide +kernel

private def spinAuxWordU : List ℕ := [1, 1, 0, 2, 1, 0, 1, 1, 1, 1, 0, 2, 1, 1, 1]

private def spinAuxWordV : List ℕ := [0, 2]

private def spinAuxWordA1 : List ℕ := [1, 1, 0, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1]

private def spinAuxWordB1 : List ℕ := [2, 1, 0, 2, 1, 1, 1, 0, 1, 2, 1, 1, 2, 1, 1]

private def spinAuxWordA2 : List ℕ := [0, 1, 1, 0, 1, 1, 0, 1, 2, 1, 1, 2, 1, 1, 1]

private def spinAuxWordB2 : List ℕ := [1, 0, 2, 1, 1, 2, 1, 1]

private def spinAuxWordS1 : List ℕ := [1, 0, 1, 2, 1, 1, 2, 1, 0, 1, 0, 1, 1]

private def spinAuxWordS2 : List ℕ := [0, 1, 1, 0, 1, 0, 1, 0, 1, 2, 1, 1, 1, 2]

private theorem spinAuxU_eq_word : uA = wordElem spinAuxWordU := by
  apply Subtype.ext
  rw [coe_wordElem]
  show u = wordPerm spinAuxWordU
  exact eq_of_pk h45 pk_u (pk_word _) (by decide +kernel)

private theorem spinAuxV_eq_word : vA = wordElem spinAuxWordV := by
  apply Subtype.ext
  rw [coe_wordElem]
  show v = wordPerm spinAuxWordV
  exact eq_of_pk h45 pk_v (pk_word _) (by decide +kernel)

private theorem spinAuxA1_eq_word : a1A = wordElem spinAuxWordA1 := by
  apply Subtype.ext
  rw [coe_wordElem]
  show alpha1 = wordPerm spinAuxWordA1
  exact eq_of_pk h45 pk_a1 (pk_word _) (by decide +kernel)

private theorem spinAuxB1_eq_word : b1A = wordElem spinAuxWordB1 := by
  apply Subtype.ext
  rw [coe_wordElem]
  show beta1 = wordPerm spinAuxWordB1
  exact eq_of_pk h45 pk_b1 (pk_word _) (by decide +kernel)

private theorem spinAuxA2_eq_word : a2A = wordElem spinAuxWordA2 := by
  apply Subtype.ext
  rw [coe_wordElem]
  show alpha2 = wordPerm spinAuxWordA2
  exact eq_of_pk h45 pk_a2 (pk_word _) (by decide +kernel)

private theorem spinAuxB2_eq_word : b2A = wordElem spinAuxWordB2 := by
  apply Subtype.ext
  rw [coe_wordElem]
  show beta2 = wordPerm spinAuxWordB2
  exact eq_of_pk h45 pk_b2 (pk_word _) (by decide +kernel)

private theorem spinAuxS1_eq_word : s1A = wordElem spinAuxWordS1 := by
  apply Subtype.ext
  rw [coe_wordElem]
  show sigma1 = wordPerm spinAuxWordS1
  exact eq_of_pk h45 pk_s1 (pk_word _) (by decide +kernel)

private theorem spinAuxS2_eq_word : s2A = wordElem spinAuxWordS2 := by
  apply Subtype.ext
  rw [coe_wordElem]
  show sigma2 = wordPerm spinAuxWordS2
  exact eq_of_pk h45 pk_s2 (pk_word _) (by decide +kernel)

private theorem spinAuxWordElem_append (w₁ w₂ : List ℕ) :
    wordElem (w₁ ++ w₂) = wordElem w₁ * wordElem w₂ := by
  simp [wordElem, List.map_append, List.prod_append]

private theorem spinAuxS1S2_eq_word : s1A * s2A = wordElem (spinAuxWordS1 ++ spinAuxWordS2) := by
  rw [spinAuxS1_eq_word, spinAuxS2_eq_word, ← spinAuxWordElem_append]

private theorem spinAuxMemS1 :
    s1A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
  Subgroup.mem_subgroupOf.mpr sigma1_mem_Q

private theorem spinAuxMemS2 :
    s2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
  Subgroup.mem_subgroupOf.mpr sigma2_mem_Q

private theorem spinAuxMemS1S2 :
    s1A * s2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
  Subgroup.mul_mem _ spinAuxMemS1 spinAuxMemS2

private theorem spinAuxS1_pow_three : s1A ^ 3 = 1 := by
  rw [spinAuxS1_eq_word]
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_wordElem, Subgroup.coe_one]
  show wordPerm spinAuxWordS1 ^ 3 = 1
  exact pow_eq_one_of h45 pk_one (pk_word _) 3 (by decide +kernel)

private theorem spinAuxS2_pow_three : s2A ^ 3 = 1 := by
  rw [spinAuxS2_eq_word]
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_wordElem, Subgroup.coe_one]
  show wordPerm spinAuxWordS2 ^ 3 = 1
  exact pow_eq_one_of h45 pk_one (pk_word _) 3 (by decide +kernel)

private theorem spinAuxS1S2_pow_three : (s1A * s2A) ^ 3 = 1 := by
  rw [spinAuxS1S2_eq_word]
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_wordElem, Subgroup.coe_one]
  show wordPerm (spinAuxWordS1 ++ spinAuxWordS2) ^ 3 = 1
  exact pow_eq_one_of h45 pk_one (pk_word _) 3 (by decide +kernel)

private theorem spinAuxConjU :
    uA * (s1A * s2A) * uA⁻¹ = s1A * s2A ∨
      uA * (s1A * s2A) * uA⁻¹ = (s1A * s2A)⁻¹ := by
  left
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact conj_of h45 pk_u (pk_mul h45 pk_s1 pk_s2) (pk_mul h45 pk_s1 pk_s2) (by decide +kernel)

private theorem spinAuxConjV : vA * s1A * vA⁻¹ = s1A ∨ vA * s1A * vA⁻¹ = s1A⁻¹ := by
  right
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact conj_of h45 pk_v pk_s1 pk_s1i (by decide +kernel)

private theorem spinAuxConjA1 : a1A * s2A * a1A⁻¹ = s2A ∨ a1A * s2A * a1A⁻¹ = s2A⁻¹ := by
  left
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact conj_of h45 pk_a1 pk_s2 pk_s2 (by decide +kernel)

private theorem spinAuxConjB1 : b1A * s2A * b1A⁻¹ = s2A ∨ b1A * s2A * b1A⁻¹ = s2A⁻¹ := by
  left
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact conj_of h45 pk_b1 pk_s2 pk_s2 (by decide +kernel)

private theorem spinAuxConjA2 : a2A * s1A * a2A⁻¹ = s1A ∨ a2A * s1A * a2A⁻¹ = s1A⁻¹ := by
  left
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact conj_of h45 pk_a2 pk_s1 pk_s1 (by decide +kernel)

private theorem spinAuxConjB2 : b2A * s1A * b2A⁻¹ = s1A ∨ b2A * s1A * b2A⁻¹ = s1A⁻¹ := by
  left
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact conj_of h45 pk_b2 pk_s1 pk_s1 (by decide +kernel)

private theorem spinAuxFixU :
    ((rhoA uA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 = spinW0 := by
  rw [spinAuxU_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxFixV :
    ((rhoA vA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 = spinW0 := by
  rw [spinAuxV_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxFixA1 :
    ((rhoA a1A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 = spinW0 := by
  rw [spinAuxA1_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxFixB1 :
    ((rhoA b1A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 = spinW0 := by
  rw [spinAuxB1_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxFixA2 :
    ((rhoA a2A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 = spinW0 := by
  rw [spinAuxA2_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxFixB2 :
    ((rhoA b2A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 = spinW0 := by
  rw [spinAuxB2_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxTraceU :
    spinW0 + ((rhoA (s1A * s2A) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 +
      ((rhoA (s1A * s2A) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA (s1A * s2A) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0) = 0 := by
  rw [spinAuxS1S2_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxTraceS1 :
    spinW0 + ((rhoA s1A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 +
      ((rhoA s1A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA s1A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0) = 0 := by
  rw [spinAuxS1_eq_word, rhoA_wordElem]
  decide +kernel

private theorem spinAuxTraceS2 :
    spinW0 + ((rhoA s2A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 +
      ((rhoA s2A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA s2A : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0) = 0 := by
  rw [spinAuxS2_eq_word, rhoA_wordElem]
  decide +kernel

theorem spinTraceData :
    ∀ g ∈ ({⟨u, u_mem_A⟩, ⟨v, v_mem_A⟩, ⟨alpha1, alpha1_mem_A⟩, ⟨beta1, beta1_mem_A⟩,
        ⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set ↥QA45.originalSubgroup),
      ((rhoA g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
          spinW0 = spinW0 ∧
        ∃ r : ↥QA45.originalSubgroup,
          r ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ∧ r ^ 3 = 1 ∧
          (g * r * g⁻¹ = r ∨ g * r * g⁻¹ = r⁻¹) ∧
          spinW0 + ((rhoA r : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
              Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 +
            ((rhoA r : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
              Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
              (((rhoA r : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
                Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0) = 0 := by
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨spinAuxFixU, ⟨s1A * s2A, spinAuxMemS1S2, spinAuxS1S2_pow_three, spinAuxConjU,
      spinAuxTraceU⟩⟩
  · exact ⟨spinAuxFixV, ⟨s1A, spinAuxMemS1, spinAuxS1_pow_three, spinAuxConjV,
      spinAuxTraceS1⟩⟩
  · exact ⟨spinAuxFixA1, ⟨s2A, spinAuxMemS2, spinAuxS2_pow_three, spinAuxConjA1,
      spinAuxTraceS2⟩⟩
  · exact ⟨spinAuxFixB1, ⟨s2A, spinAuxMemS2, spinAuxS2_pow_three, spinAuxConjB1,
      spinAuxTraceS2⟩⟩
  · exact ⟨spinAuxFixA2, ⟨s1A, spinAuxMemS1, spinAuxS1_pow_three, spinAuxConjA2,
      spinAuxTraceS1⟩⟩
  · exact ⟨spinAuxFixB2, ⟨s1A, spinAuxMemS1, spinAuxS1_pow_three, spinAuxConjB2,
      spinAuxTraceS1⟩⟩

theorem spinFixedCard_t :
    fixCard (((rhoA (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) :
      Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) = 64 := by
  have h : (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) = ⟨x45, Q45_le_A45 x45_mem_Q⟩ :=
    Subtype.ext rfl
  rw [h, rhoA_x]
  show fixCard Mx = 64
  decide +kernel

end CFSG.RankThree.GF2n.Parrott
