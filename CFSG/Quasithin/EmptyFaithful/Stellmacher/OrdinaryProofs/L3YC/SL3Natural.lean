module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

open CFSG.Open

def tA : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

def cA : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

def tB : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 1, 0, 1]

lemma det_tA : tA.det = 1 := by decide

lemma det_cA : cA.det = 1 := by decide

lemma det_tB : tB.det = 1 := by decide

def gA : GL (Fin 3) (ZMod 2) := Matrix.GeneralLinearGroup.mkOfDetNeZero tA (by rw [det_tA]; decide)

def gC : GL (Fin 3) (ZMod 2) := Matrix.GeneralLinearGroup.mkOfDetNeZero cA (by rw [det_cA]; decide)

def gB : GL (Fin 3) (ZMod 2) := Matrix.GeneralLinearGroup.mkOfDetNeZero tB (by rw [det_tB]; decide)

lemma gA_mem : gA ∈ StatedSL 3 (ZMod 2) :=
  Subgroup.subset_closure (show (gA : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 from det_tA)

lemma gC_mem : gC ∈ StatedSL 3 (ZMod 2) :=
  Subgroup.subset_closure (show (gC : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 from det_cA)

lemma gB_mem : gB ∈ StatedSL 3 (ZMod 2) :=
  Subgroup.subset_closure (show (gB : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 from det_tB)

theorem end_natural_scalar (P : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hP : ∀ g ∈ StatedSL 3 (ZMod 2),
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * P = P * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    P = 0 ∨ P = 1 := by
  have key : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2),
      tA * X = X * tA → cA * X = X * cA → tB * X = X * tB → X = 0 ∨ X = 1 := by
    decide +kernel
  exact key P (hP gA gA_mem) (hP gC gC_mem) (hP gB gB_mem)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

end
