module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bFlip

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer

open Matrix CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.X7
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Semidihedral.Principal Representation

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem card_fixed_flipEquiv_le {A : Finset ℕ} (hf : 1 ≤ f) (hA : A ⊆ Finset.range (2 * f))
    (hsh : shiftSet f f A = A) (hne : A.Nonempty) :
    Fintype.card {x : ↥A → Fin 4 // flipEquiv hA hsh x = x} ≤ 4 ^ (A.card - 1) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  let j : ↥A := ⟨i₀, hi₀⟩
  let r : {x : ↥A → Fin 4 // flipEquiv hA hsh x = x} → ({i : ↥A // i ≠ j} → Fin 4) :=
    fun x i => x.1 i
  have hr : Function.Injective r := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    funext i
    by_cases hij : i = j
    · rw [hij]
      have h1 : x j = x (shiftFun hsh j) := by
        have := congrFun hx j
        rw [flipEquiv_apply] at this
        exact this.symm
      have h2 : y j = y (shiftFun hsh j) := by
        have := congrFun hy j
        rw [flipEquiv_apply] at this
        exact this.symm
      show x j = y j
      rw [h1, h2]
      exact congrFun h ⟨shiftFun hsh j, shiftFun_ne_self hf hA hsh j⟩
    · exact congrFun h ⟨i, hij⟩
  calc Fintype.card {x : ↥A → Fin 4 // flipEquiv hA hsh x = x}
      ≤ Fintype.card ({i : ↥A // i ≠ j} → Fin 4) := Fintype.card_le_of_injective r hr
    _ = 4 ^ (A.card - 1) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_coe,
        Fintype.card_unique]

theorem three_mul_card_le_two_mul_rank_of_flip (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f))
    (S : Matrix (↥A → Fin 4) (↥A → Fin 4) F) (hSS : S * S = 1)
    (hS : ∀ g, S * tensorRepS (F := F) F A g =
      tensorRepS (F := F) F A ((minorAut F ^ f) g) * S) :
    3 * A.card ≤ 2 * (S - 1).rank := by
  rcases A.eq_empty_or_nonempty with hA0 | hne
  · simp [hA0]
  have hsh : shiftSet f f A = A := by
    have hiso : MatIso (tensorRepS (F := F) F A)
        ((tensorRepS (F := F) F A).comp (minorAut F ^ f).toMonoidHom) S S := ⟨hSS, hSS, hS⟩
    obtain ⟨e1⟩ := hiso.equiv
    obtain ⟨e2⟩ := tensorRepS_comp_shift (F := F) F hF hA f
    exact ((tensorRepS_absolutely_irreducible_and_distinct (k := F) hF hf).2 A hA (shiftSet f f A)
      (shiftSet_subset hf f A) ⟨e1.trans e2⟩).symm
  set e := flipEquiv hA hsh with he
  have hMat := flip_matIso hA hsh hF
  have hee : e.symm = e := flipEquiv_symm hA hsh
  rw [← he, hee] at hMat
  set P := permMat F e with hP
  have hP2 : P * P = 1 := hMat.mul_inv
  have hPT : ∀ g, P * tensorRepS (F := F) F A ((minorAut F ^ f) g) =
      tensorRepS (F := F) F A g * P := fun g => hMat.comm g
  have hC : ∀ g, (P * S) * tensorRepS (F := F) F A g = tensorRepS (F := F) F A g * (P * S) := by
    intro g
    rw [Matrix.mul_assoc, hS g, ← Matrix.mul_assoc, hPT g, Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := schur_tensorRepS hF hA (P * S) hC
  have hSP : S = c • P := by
    calc S = (P * P) * S := by rw [hP2, Matrix.one_mul]
      _ = P * (P * S) := by rw [Matrix.mul_assoc]
      _ = c • P := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  have hcc : c * c = 1 := by
    have h1 : S * S = (c * c) • (1 : Matrix (↥A → Fin 4) (↥A → Fin 4) F) := by
      rw [hSP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP2]
    rw [hSS] at h1
    have h2 := congrFun (congrFun h1 (fun _ => 0)) (fun _ => 0)
    simpa using h2.symm
  have hc1 : c = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h : (c + 1) * (c + 1) = 0 := by linear_combination hcc + (c + 1) * h2
    have := mul_self_eq_zero.mp h
    exact CharTwo.add_eq_zero.mp this
  rw [hc1, one_smul] at hSP
  subst hSP
  have hperm : e * e = 1 := Equiv.ext fun x => flipEquiv_flipEquiv hA hsh x
  have hrank : (P - 1).rank * 2 + Fintype.card {x : ↥A → Fin 4 // e x = x} =
      Fintype.card (↥A → Fin 4) := rank_permMat_sub_one (k := F) e hperm
  have hfix := card_fixed_flipEquiv_le hf hA hsh hne
  rw [← he] at hfix
  have hcard : Fintype.card (↥A → Fin 4) = 4 ^ A.card := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hk : 1 ≤ A.card := Finset.card_pos.mpr hne
  have h4 : 4 ^ A.card = 4 * 4 ^ (A.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hlt : A.card ≤ 4 ^ (A.card - 1) := by
    have : A.card - 1 < 4 ^ (A.card - 1) := Nat.lt_pow_self (by norm_num)
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer
