module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32AC47k

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Matrix

section SL3

@[expose] def grM (A g : A6.SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((g⁻¹ : A6.SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
    ((A⁻¹ : A6.SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2))

theorem sl3_graph_X1 : ∀ A : A6.SL3.S,
    ¬ ((∀ p ∈ A6.SL3.P0list, grM A p 1 0 = 0 ∧ grM A p 2 0 = 0 ∧ grM A p 2 1 = 0) ∧
      grM A A6.SL3.s2 1 0 = 0 ∧ grM A A6.SL3.s2 2 0 = 0) := by
  decide +kernel

theorem sl3_graph_X2 : ∀ A : A6.SL3.S,
    ¬ ((∀ p ∈ A6.SL3.P0list, grM A p 1 0 = 0 ∧ grM A p 2 0 = 0 ∧ grM A p 2 1 = 0) ∧
      grM A A6.SL3.s1 2 0 = 0 ∧ grM A A6.SL3.s1 2 1 = 0) := by
  decide +kernel

theorem s2_mem_X1_s1_mem_X2 : A6.SL3.InX1 A6.SL3.s2 ∧ A6.SL3.InX2 A6.SL3.s1 := by
  decide +kernel

theorem zmod_two_ringEquiv_apply (σ : ZMod 2 ≃+* ZMod 2) (x : ZMod 2) : σ x = x := by
  fin_cases x
  · exact map_zero σ
  · exact map_one σ

theorem det_eq_one_of_GL (A : GL (Fin 3) (ZMod 2)) :
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have hu : IsUnit (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
  obtain ⟨u, hu⟩ := hu
  rw [← hu]
  have : u = 1 := Subsingleton.elim _ _
  rw [this, Units.val_one]

theorem mem_inner_of_normalizes (β : MulAut A6.SL3.S) (hP : ∀ p ∈ A6.SL3.P0, β p ∈ A6.SL3.P0)
    (hX : (∀ x ∈ A6.SL3.X1, β x ∈ A6.SL3.X1) ∨ ∀ x ∈ A6.SL3.X2, β x ∈ A6.SL3.X2) :
    β ∈ inner A6.SL3.S := by
  obtain ⟨A, σ, hA | hA⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl
    (n := 3) le_rfl β
  all_goals
    have hσ : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.map σ = M := fun M => by
      ext i j
      exact zmod_two_ringEquiv_apply σ _
    set A' : A6.SL3.S := ⟨A, det_eq_one_of_GL A⟩ with hA'
    have hinv : ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        ((A'⁻¹ : A6.SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      show (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        adjugate (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1
      rw [mul_adjugate, det_eq_one_of_GL A, one_smul]
  ·
    refine ⟨A', ?_⟩
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rw [hA g, hσ, hinv, MulAut.conj_apply]
    rfl
  ·
    exfalso
    have hgr : ∀ g : A6.SL3.S, ((β g : A6.SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = grM A' g :=
      fun g => by rw [hA g, hσ, hinv]; rfl
    have hP' : ∀ p ∈ A6.SL3.P0list, grM A' p 1 0 = 0 ∧ grM A' p 2 0 = 0 ∧ grM A' p 2 1 = 0 := by
      intro p hp
      have h := hP p (A6.SL3.P0list_mem le_rfl p hp)
      obtain ⟨⟨h1, h2⟩, -, h3⟩ := h
      rw [hgr] at h1 h2 h3
      exact ⟨h1, h2, h3⟩
    rcases hX with hX | hX
    · have h := hX _ s2_mem_X1_s1_mem_X2.1
      obtain ⟨h1, h2⟩ := h
      rw [hgr] at h1 h2
      exact sl3_graph_X1 A' ⟨hP', h1, h2⟩
    · have h := hX _ s2_mem_X1_s1_mem_X2.2
      obtain ⟨h1, h2⟩ := h
      rw [hgr] at h1 h2
      exact sl3_graph_X2 A' ⟨hP', h1, h2⟩

theorem not_isTwoThree_168 : ¬ IsTwoThree 168 := by
  rintro ⟨a, b, h⟩
  have h7 : 7 ∣ 2 ^ a * 3 ^ b := h ▸ (by norm_num : 7 ∣ 168)
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h7 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_three).mp
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
    omega

end SL3

end CFSG.Quasithin.H13.L32A.C
