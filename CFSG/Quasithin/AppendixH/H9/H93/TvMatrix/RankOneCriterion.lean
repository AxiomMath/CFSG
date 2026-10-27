module

public import CFSG.Quasithin.AppendixH.H9.H93.TvMatrix.CommutatorImage
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

private theorem mulVec_sub_self_of_eq_one_add {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    {u f : Fin n → ZMod 2} (hA : A = 1 + Matrix.vecMulVec u f) (a : Fin n → ZMod 2) :
    A *ᵥ a - a = (f ⬝ᵥ a) • u := by
  rw [hA, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  abel

private theorem exists_dotProduct_eq_one {f : Fin n → ZMod 2} (hf : f ≠ 0) :
    ∃ a : Fin n → ZMod 2, f ⬝ᵥ a = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := Function.ne_iff.mp hf
  have h1 : f i = 1 := by
    revert hi
    generalize f i = x
    revert x
    decide
  exact ⟨Pi.single i 1, by rw [dotProduct_single_one, h1]⟩

theorem rk_commOn_V1n_zpowers_pairActN_eq_one_iff (A : GL (Fin n) (ZMod 2)) :
    rk ↥(commOn (V1n n) (Subgroup.zpowers (pairActN n A))) = 1 ↔
      ∃ u f : Fin n → ZMod 2, u ≠ 0 ∧ f ≠ 0 ∧
        (A : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + Matrix.vecMulVec u f := by
  have hmem := mem_commOn_V1n_zpowers_pairActN A
  generalize commOn (V1n n) (Subgroup.zpowers (pairActN n A)) = W at hmem ⊢
  constructor
  · intro hrk
    have hcard : Nat.card ↥W = 2 := by
      have hG : @IsPGroup 2 (PairN n) CommGroup.toGroup := fun x => ⟨1, by
        rw [pow_one]
        exact pairN_sq x⟩
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hG.to_subgroup W)
      unfold rk at hrk
      rw [hm, padicValNat.prime_pow] at hrk
      rw [hm, hrk]
      norm_num
    obtain ⟨y₀, hy₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).mp hcard
    obtain ⟨z₀, hz₀⟩ := (hmem y₀.1).mp y₀.2
    have hu0 : (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z₀ - z₀ ≠ 0 := by
      intro h0
      apply hy₀
      apply Subtype.ext
      exact (hz₀.trans (by rw [h0])).trans pairVec_one.symm
    have hdich : ∀ a : Fin n → ZMod 2,
        (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a = 0 ∨
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a =
            (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z₀ - z₀ := by
      intro a
      by_cases h : (⟨pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a) 0,
          (hmem _).mpr ⟨a, rfl⟩⟩ : ↥W) = 1
      · left
        have h1 := congrArg Subtype.val h
        exact (pairVec_inj.mp (h1.trans pairVec_one)).1
      · right
        have h1 := congrArg Subtype.val (huniq _ h)
        exact (pairVec_inj.mp (h1.trans hz₀)).1
    generalize hu : (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z₀ - z₀ = u at hu0 hdich
    classical
    let f : Fin n → ZMod 2 := fun i =>
      if (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single i 1 - Pi.single i 1 = u then 1 else 0
    have hcol : ∀ i, (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single i 1 - Pi.single i 1 =
        f i • u := by
      intro i
      by_cases h : (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single i 1 - Pi.single i 1 = u
      · simp only [f, if_pos h, one_smul]
        exact h
      · simp only [f, if_neg h, zero_smul]
        exact (hdich _).resolve_right h
    have hM : (A : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + Matrix.vecMulVec u f := by
      ext i j
      have h1 := congrFun (hcol j) i
      simp only [Pi.sub_apply, Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
        smul_eq_mul, Pi.single_apply] at h1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
      rw [mul_comm, ← h1]
      generalize (if i = j then (1 : ZMod 2) else 0) = c
      ring
    refine ⟨u, f, hu0, ?_, hM⟩
    intro hf0
    apply hu0
    have h2 := mulVec_sub_self_of_eq_one_add hM z₀
    rw [hf0, zero_dotProduct, zero_smul] at h2
    exact hu.symm.trans h2
  · rintro ⟨u, f, hu, hf, hA⟩
    have hsub := mulVec_sub_self_of_eq_one_add hA
    obtain ⟨a₀, ha₀⟩ := exists_dotProduct_eq_one hf
    have hy1mem : pairVec u 0 ∈ W := (hmem _).mpr ⟨a₀, by rw [hsub, ha₀, one_smul]⟩
    have hcard : Nat.card ↥W = 2 := by
      refine (Nat.card_eq_two_iff' (1 : ↥W)).mpr ⟨⟨pairVec u 0, hy1mem⟩, ?_, ?_⟩
      · intro h
        have h1 := congrArg Subtype.val h
        exact hu (pairVec_inj.mp (h1.trans pairVec_one)).1
      · rintro ⟨y, hy⟩ hne
        obtain ⟨a, rfl⟩ := (hmem y).mp hy
        apply Subtype.ext
        show pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a) 0 = pairVec u 0
        rcases zmod_two_cases (f ⬝ᵥ a) with h | h
        · exfalso
          apply hne
          apply Subtype.ext
          show pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a - a) 0 = 1
          rw [hsub, h, zero_smul]
          exact pairVec_one.symm
        · rw [hsub, h, one_smul]
    unfold rk
    rw [hcard]
    exact padicValNat_self

end CFSG.ASVolI.ChH
