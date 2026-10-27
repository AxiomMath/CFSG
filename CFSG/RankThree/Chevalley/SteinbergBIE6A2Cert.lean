module

public import CFSG.RankThree.Chevalley.SteinbergBIE6BitPack

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.Monster.B.Classical.E6Adjoint CFSG.Monster.B.E6.StdF4

@[expose] def a2Letter (i j a : ℕ) : List (List ℕ) :=
  if a = 0 then opSparse (6 + i) else if a = 1 then opSparse (12 + 2 * i)
  else if a = 2 then opSparse (6 + j) else opSparse (12 + 2 * j)

@[expose] def a2WordsXi : List (List ℕ) :=
  [[3], [1, 0], [2, 1], [2, 3], [0, 1, 0], [0, 2, 0], [3, 0, 1], [0, 2, 1], [3, 2, 1], [3, 0, 2],
    [2, 3, 2], [2, 0, 1, 0], [3, 0, 1, 0], [0, 2, 1, 0], [1, 0, 2, 0], [2, 0, 2, 0],
    [2, 3, 2, 0], [0, 2, 0, 1], [2, 3, 2, 1], [0, 2, 3, 1], [3, 1, 0, 2], [2, 3, 0, 2]]

@[expose] def a2WordsYi : List (List ℕ) :=
  [[], [1], [3], [3, 1], [3, 2], [1, 3], [2, 3], [3, 2, 1], [1, 3, 1], [2, 3, 1], [1, 3, 2],
    [2, 3, 2], [2, 1, 3], [1, 3, 2, 1], [2, 3, 2, 1], [2, 1, 3, 1], [2, 1, 3, 2], [3, 2, 1, 3]]

@[expose] def a2WordsXj : List (List ℕ) :=
  [[1], [2, 1], [0, 2, 0], [1, 0, 2, 0], [2, 0, 2, 0], [0, 2, 0, 1]]

@[expose] def a2WordsYj : List (List ℕ) :=
  [[], [3, 1], [3, 2], [1, 3], [2, 3], [0, 1, 0], [3, 2, 1], [1, 3, 1], [2, 3, 1], [1, 3, 2],
    [2, 1, 3], [3, 0, 1, 0], [0, 1, 3, 0], [1, 3, 0, 1], [1, 3, 2, 1], [2, 1, 3, 1]]

@[expose] def a2CertOK (i j : ℕ) : Bool :=
  ((sparseOK (opSparse (6 + i)) && sparseOK (opSparse (12 + 2 * i))) &&
    (sparseOK (opSparse (6 + j)) && sparseOK (opSparse (12 + 2 * j)))) &&
  ((sparseOK (adSparse (6 + i)) && sparseOK (adSparse (12 + 2 * i))) &&
    (sparseOK (adSparse (6 + j)) && sparseOK (adSparse (12 + 2 * j)))) &&
  ((certPack (a2Letter i j) a2WordsXi == packMul idPack (adSparse (6 + i))) &&
    (certPack (a2Letter i j) a2WordsYi == packMul idPack (adSparse (12 + 2 * i)))) &&
  ((certPack (a2Letter i j) a2WordsXj == packMul idPack (adSparse (6 + j))) &&
    (certPack (a2Letter i j) a2WordsYj == packMul idPack (adSparse (12 + 2 * j))))

theorem a2CertOK_02 : a2CertOK 0 2 = true := by decide +kernel

theorem a2CertOK_45 : a2CertOK 4 5 = true := by decide +kernel

section Semantics

variable {R : Type*} [Field R] [CharP R 2] {X : Module.End R (RootModule Tag.E6 R)}

theorem commute_of_commute_one_add_add {M : Type*} [Ring M] {X A T : M}
    (h : Commute X (1 + A + T)) (hA : Commute X A) : Commute X T := by
  have e := h.eq
  rw [mul_add, mul_add, add_mul, add_mul, mul_one, one_mul, hA.eq] at e
  exact add_left_cancel e

theorem commute_xOp_of_commute_ad (i : Fin Tag.E6.rank) (h1 : Commute X (xOp Tag.E6 R i 1))
    (had : Commute X (ad R (Finsupp.single (lab ⟨6 + i, six_add_lt i⟩) 1))) (c : R) :
    Commute X (xOp Tag.E6 R i c) := by
  have e := xOp_eq_lab i (1 : R)
  rw [one_smul, one_pow, one_smul] at e
  rw [e] at h1
  have hT := commute_of_commute_one_add_add (M := Module.End R (RootModule Tag.E6 R)) h1 had
  rw [xOp_eq_lab]
  exact ((Commute.one_right X).add_right (had.smul_right c)).add_right (hT.smul_right _)

theorem commute_yOp_of_commute_ad (i : Fin Tag.E6.rank) (h1 : Commute X (yOp Tag.E6 R i 1))
    (had : Commute X (ad R (Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1))) (c : R) :
    Commute X (yOp Tag.E6 R i c) := by
  have e := yOp_eq_lab i (1 : R)
  rw [one_smul, one_pow, one_smul] at e
  rw [e] at h1
  have hT := commute_of_commute_one_add_add (M := Module.End R (RootModule Tag.E6 R)) h1 had
  rw [yOp_eq_lab]
  exact ((Commute.one_right X).add_right (had.smul_right c)).add_right (hT.smul_right _)

theorem commute_of_a2CertOK {i j : Fin Tag.E6.rank} (hc : a2CertOK i j = true)
    (hxi : Commute X (xOp Tag.E6 R i 1)) (hyi : Commute X (yOp Tag.E6 R i 1))
    (hxj : Commute X (xOp Tag.E6 R j 1)) (hyj : Commute X (yOp Tag.E6 R j 1)) (c : R) :
    Commute X (xOp Tag.E6 R i c) ∧ Commute X (yOp Tag.E6 R i c) ∧
      Commute X (xOp Tag.E6 R j c) ∧ Commute X (yOp Tag.E6 R j c) := by
  simp only [a2CertOK, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨l1, l2⟩, l3, l4⟩, ⟨t1, t2⟩, t3, t4⟩, c1, c2⟩, c3, c4⟩ := hc
  have hL : ∀ a, sparseOK (a2Letter i j a) = true ∧ Commute X (sparseEnd R (a2Letter i j a)) := by
    intro a
    unfold a2Letter
    split_ifs
    · exact ⟨l1, by rw [sparseEnd_opSparse_x]; exact hxi⟩
    · exact ⟨l2, by rw [sparseEnd_opSparse_y]; exact hyi⟩
    · exact ⟨l3, by rw [sparseEnd_opSparse_x]; exact hxj⟩
    · exact ⟨l4, by rw [sparseEnd_opSparse_y]; exact hyj⟩
  have hW : ∀ W : List (List ℕ), ∀ w ∈ W, ∀ a ∈ w,
      sparseOK (a2Letter i j a) = true ∧ Commute X (sparseEnd R (a2Letter i j a)) :=
    fun _ _ _ a _ => hL a
  have a1 := commute_sparseEnd_of_cert _ _ c1 t1 (hW _)
  have a2 := commute_sparseEnd_of_cert _ _ c2 t2 (hW _)
  have a3 := commute_sparseEnd_of_cert _ _ c3 t3 (hW _)
  have a4 := commute_sparseEnd_of_cert _ _ c4 t4 (hW _)
  rw [show adSparse (6 + (i : ℕ)) = adSparse ((⟨6 + i, six_add_lt i⟩ : Fin 78) : ℕ) from rfl,
    sparseEnd_adSparse] at a1
  rw [show adSparse (12 + 2 * (i : ℕ)) =
      adSparse ((⟨12 + 2 * i, twelve_add_lt i⟩ : Fin 78) : ℕ) from rfl, sparseEnd_adSparse] at a2
  rw [show adSparse (6 + (j : ℕ)) = adSparse ((⟨6 + j, six_add_lt j⟩ : Fin 78) : ℕ) from rfl,
    sparseEnd_adSparse] at a3
  rw [show adSparse (12 + 2 * (j : ℕ)) =
      adSparse ((⟨12 + 2 * j, twelve_add_lt j⟩ : Fin 78) : ℕ) from rfl, sparseEnd_adSparse] at a4
  exact ⟨commute_xOp_of_commute_ad i hxi a1 c, commute_yOp_of_commute_ad i hyi a2 c,
    commute_xOp_of_commute_ad j hxj a3 c, commute_yOp_of_commute_ad j hyj a4 c⟩

end Semantics

end CFSG.RankThree.Chevalley
