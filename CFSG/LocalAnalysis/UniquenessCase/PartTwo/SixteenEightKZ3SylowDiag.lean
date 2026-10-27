module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3F4Diag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3F4Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Polynomial Matrix

noncomputable section

private noncomputable def s16k_d (i : Fin 3) : S16kGL6 where
  val := s16kBlockMat i
  inv := s16kBlockMat i * s16kBlockMat i
  val_inv := by
    fin_cases i <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp only [Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply] <;>
      decide
  inv_val := by
    fin_cases i <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp only [Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply] <;>
      decide

@[simp] private lemma s16k_d_val (i : Fin 3) :
    ((s16k_d i : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i := rfl

private lemma s16k_d_cubed (i : Fin 3) : (s16k_d i) ^ 3 = 1 := by
  ext r c <;> fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp only [s16k_d, Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply,
      Units.val_pow_eq_pow_val] <;>
    decide

private lemma s16k_d_ne_one (i : Fin 3) : s16k_d i ≠ 1 := by
  fin_cases i <;> decide

private lemma s16k_d_comm (i j : Fin 3) : Commute (s16k_d i) (s16k_d j) := by
  ext r c <;> fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;>
    simp only [s16k_d, Matrix.mul_apply, s16kBlockMat, Matrix.of_apply] <;>
    decide

private lemma s16k_diag_gen_eq :
    {g : S16kGL6 | ∃ i : Fin 3, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i}
      = ({s16k_d 0, s16k_d 1, s16k_d 2} : Set S16kGL6) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Units.ext hi)
    · exact Or.inr (Or.inl (Units.ext hi))
    · exact Or.inr (Or.inr (Units.ext hi))
  · rintro (h | h | h)
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
    · exact ⟨2, by rw [h]; rfl⟩

private lemma s16k_d_mem_diag (i : Fin 3) : s16k_d i ∈ s16kDiag := by
  rw [s16kDiag]
  exact Subgroup.subset_closure ⟨i, rfl⟩

private def s16kAddFin (a b : Fin 3) : Fin 3 := ⟨(a.val + b.val) % 3, by omega⟩

private def s16kNegFin (a : Fin 3) : Fin 3 := ⟨(3 - a.val) % 3, by omega⟩

private lemma s16k_d_pow_mul (i : Fin 3) (a b : Fin 3) :
    s16k_d i ^ (a : ℕ) * s16k_d i ^ (b : ℕ) = s16k_d i ^ ((s16kAddFin a b) : ℕ) := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> decide

private lemma s16k_reorder (a b c a' b' c' : Fin 3) :
    (s16k_d 0 ^ (a : ℕ) * s16k_d 1 ^ (b : ℕ) * s16k_d 2 ^ (c : ℕ)) *
        (s16k_d 0 ^ (a' : ℕ) * s16k_d 1 ^ (b' : ℕ) * s16k_d 2 ^ (c' : ℕ)) =
      (s16k_d 0 ^ (a : ℕ) * s16k_d 0 ^ (a' : ℕ)) *
        ((s16k_d 1 ^ (b : ℕ) * s16k_d 1 ^ (b' : ℕ)) *
          (s16k_d 2 ^ (c : ℕ) * s16k_d 2 ^ (c' : ℕ))) := by
  have h20 : Commute (s16k_d 2 ^ (c : ℕ)) (s16k_d 0 ^ (a' : ℕ)) :=
    (s16k_d_comm 2 0).pow_pow c a'
  have h10 : Commute (s16k_d 1 ^ (b : ℕ)) (s16k_d 0 ^ (a' : ℕ)) :=
    (s16k_d_comm 1 0).pow_pow b a'
  have h21 : Commute (s16k_d 2 ^ (c : ℕ)) (s16k_d 1 ^ (b' : ℕ)) :=
    (s16k_d_comm 2 1).pow_pow c b'
  simp only [mul_assoc]
  rw [h20.left_comm, h10.left_comm, h21.left_comm]

private lemma s16k_prod_mul (a b c a' b' c' : Fin 3) :
    (s16k_d 0 ^ (a : ℕ) * s16k_d 1 ^ (b : ℕ) * s16k_d 2 ^ (c : ℕ)) *
      (s16k_d 0 ^ (a' : ℕ) * s16k_d 1 ^ (b' : ℕ) * s16k_d 2 ^ (c' : ℕ)) =
    s16k_d 0 ^ ((s16kAddFin a a') : ℕ) * s16k_d 1 ^ ((s16kAddFin b b') : ℕ) *
      s16k_d 2 ^ ((s16kAddFin c c') : ℕ) := by
  rw [s16k_reorder a b c a' b' c', s16k_d_pow_mul 0 a a', s16k_d_pow_mul 1 b b',
    s16k_d_pow_mul 2 c c']
  rw [mul_assoc]

private lemma s16k_mem_diag_exists_prod (x : S16kGL6) (hx : x ∈ s16kDiag) :
    ∃ a b c : Fin 3, x = s16k_d 0 ^ (a : ℕ) * s16k_d 1 ^ (b : ℕ) * s16k_d 2 ^ (c : ℕ) := by
  rw [s16kDiag, s16k_diag_gen_eq] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul y z hy hz ihy ihz =>
      obtain ⟨a, b, c, rfl⟩ := ihy
      obtain ⟨a', b', c', rfl⟩ := ihz
      exact ⟨s16kAddFin a a', s16kAddFin b b', s16kAddFin c c', s16k_prod_mul a b c a' b' c'⟩
  | inv y hy ihy =>
      obtain ⟨a, b, c, rfl⟩ := ihy
      exact ⟨s16kNegFin a, s16kNegFin b, s16kNegFin c, by
        fin_cases a <;> fin_cases b <;> fin_cases c <;> decide⟩

private noncomputable def s16kDiagF (p : Fin 3 × Fin 3 × Fin 3) : S16kGL6 :=
  s16k_d 0 ^ (p.1 : ℕ) * s16k_d 1 ^ (p.2.1 : ℕ) * s16k_d 2 ^ (p.2.2 : ℕ)

private lemma s16kDiagF_mem (p : Fin 3 × Fin 3 × Fin 3) : s16kDiagF p ∈ s16kDiag :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ (s16k_d_mem_diag 0) _)
      (Subgroup.pow_mem _ (s16k_d_mem_diag 1) _))
    (Subgroup.pow_mem _ (s16k_d_mem_diag 2) _)

private lemma s16kDiagF_surj (x : S16kGL6) (hx : x ∈ s16kDiag) :
    ∃ p : Fin 3 × Fin 3 × Fin 3, s16kDiagF p = x := by
  obtain ⟨a, b, c, rfl⟩ := s16k_mem_diag_exists_prod x hx
  exact ⟨(a, b, c), rfl⟩

private lemma s16kDiagF_inj : Function.Injective s16kDiagF := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
    first
      | rfl
      | exact absurd h (by decide)

theorem s16k_diag_card : Nat.card ↥s16kDiag = 27 := by
  have hbij : Function.Bijective
      (fun p : Fin 3 × Fin 3 × Fin 3 =>
        (⟨s16kDiagF p, s16kDiagF_mem p⟩ : ↥s16kDiag)) := by
    refine ⟨fun p q hpq => s16kDiagF_inj (Subtype.ext_iff.mp hpq), fun x => ?_⟩
    obtain ⟨p, hp⟩ := s16kDiagF_surj (x : S16kGL6) x.2
    exact ⟨p, Subtype.ext hp⟩
  calc Nat.card ↥s16kDiag = Nat.card (Fin 3 × Fin 3 × Fin 3) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = 27 := by simp [Nat.card_prod, Nat.card_fin]


theorem s16k_z3_elem3_diag {E : Subgroup S16kGL6}
    (hE : E ≤ Subgroup.centralizer (s16kScal : Set S16kGL6)) (hE1 : IsElemAbelian 3 E) :
    ∃ c ∈ Subgroup.centralizer (s16kScal : Set S16kGL6),
      E.map (MulAut.conj c).toMonoidHom ≤ s16kDiag := by
  obtain ⟨c, hc, μ, hμ⟩ := s16k_f4_conj_diag hE hE1
  refine ⟨c, hc, ?_⟩
  rintro x ⟨e, he, rfl⟩
  exact s16k_mem_diag_of_theta (c * e * c⁻¹) (μ ⟨e, he⟩) (fun i => (hμ ⟨e, he⟩ i).1)
    (fun v i => (hμ ⟨e, he⟩ i).2 v)

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
