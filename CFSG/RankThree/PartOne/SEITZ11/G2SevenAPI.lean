module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenRep
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenForm

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.RankTwo CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps CFSG.Blueprint.Chevalley

section Form

variable (R : Type*) [CommRing R]

@[expose] def formSubgroup : Subgroup (GL (Fin 7) R) where
  carrier := {A | (A : Matrix (Fin 7) (Fin 7) R).transpose * gram R *
    (A : Matrix (Fin 7) (Fin 7) R) = gram R}
  one_mem' := by simp
  mul_mem' := fun {A B} hA hB => by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at hA hB ⊢
    calc (↑B : Matrix (Fin 7) (Fin 7) R).transpose * (↑A : Matrix (Fin 7) (Fin 7) R).transpose *
          gram R * (↑A * ↑B)
        = (↑B : Matrix (Fin 7) (Fin 7) R).transpose *
          ((↑A : Matrix (Fin 7) (Fin 7) R).transpose * gram R * ↑A) * ↑B := by
          simp only [Matrix.mul_assoc]
      _ = gram R := by rw [hA, hB]
  inv_mem' := fun {A} hA => by
    simp only [Set.mem_ofPred_eq] at hA ⊢
    set M : Matrix (Fin 7) (Fin 7) R := (A : Matrix (Fin 7) (Fin 7) R) with hM
    set N : Matrix (Fin 7) (Fin 7) R := ((A⁻¹ : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R)
      with hN
    have h1 : N.transpose * M.transpose = 1 := by
      rw [← Matrix.transpose_mul, hN, hM]
      simp
    have h2 : M * N = 1 := by rw [hN, hM]; simp
    calc N.transpose * gram R * N
        = N.transpose * (M.transpose * gram R * M) * N := by rw [hA]
      _ = (N.transpose * M.transpose) * gram R * (M * N) := by simp only [Matrix.mul_assoc]
      _ = gram R := by rw [h1, h2]; simp

theorem posU_mem_formSubgroup (g : ℕ) (hg : g < 12) (t : R) :
    posU R g t ∈ formSubgroup R := by
  show ((posU R g t : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R).transpose * gram R *
    ((posU R g t : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) = gram R
  rw [val_posU R g hg]
  exact rootMat_form g hg t

end Form

theorem formVal_mulVec {R : Type*} [CommRing R] {A : Matrix (Fin 7) (Fin 7) R}
    (hA : A.transpose * gram R * A = gram R) (v : Fin 7 → R) :
    formVal (A.mulVec v) = formVal v := by
  unfold formVal
  generalize hw : (gram R).mulVec (A.mulVec v) = w
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose,
    ← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]

section Image

variable
    (k : Type) [Field k] [Finite k]

theorem rep7_mem_of_roots (S : Subgroup (GL (Fin 7) k))
    (hS : ∀ γ, IsRoot .G2 γ → ∀ c, yfam k γ c ∈ S) (g : adjointGroup .G2 k) : rep7 k g ∈ S := by
  have h : S.comap (rep7 k) = ⊤ := by
    rw [eq_top_iff, ← iSup_rootGroup_eq_top (rootOperatorFamily .G2) k]
    refine iSup₂_le fun γ hγ => ?_
    intro g hg
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
    show rep7 k (xPar (rootOperatorFamily .G2) γ c) ∈ S
    rw [rep7_xPar k hγ]
    exact hS γ hγ c
  have := Subgroup.mem_top g
  rw [← h] at this
  exact this

theorem rep7_form (g : adjointGroup .G2 k) :
    ((rep7 k g : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k).transpose * gram k *
      ((rep7 k g : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k) = gram k := by
  refine rep7_mem_of_roots k (formSubgroup k) (fun γ hγ c => ?_) g
  classical
  unfold yfam
  split_ifs
  exact posU_mem_formSubgroup k _ (pos_lt_twelve _) c

theorem rep7_formVal (g : adjointGroup .G2 k) (v : Fin 7 → k) :
    formVal (((rep7 k g : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k).mulVec v) = formVal v :=
  formVal_mulVec (rep7_form k g) v

end Image

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
