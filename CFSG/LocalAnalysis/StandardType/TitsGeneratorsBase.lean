module

public import CFSG.LocalAnalysis.StandardType.TitsOvergroupSound
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.StandardType.TitsGenerators

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.Schreier.Tits (titsD titsDGen titsDArr)

@[expose] noncomputable def titsS : List (Equiv.Perm (Fin 1755)) := [titsDGen 0, titsDGen 1]

theorem titsD_eq_closure_titsS : titsD = Subgroup.closure {g | g ∈ titsS} := by
  unfold titsD titsS
  congr 1
  ext x
  simp [Fin.exists_fin_two, eq_comm]

theorem titsDArr_size (j : ℕ) : (titsDArr j).size = 1755 := by
  unfold titsDArr CFSG.Sporadic.Schreier.Tits.commArr
  unfold CFSG.Monster.B.Co2.Native.compA
  exact Array.size_ofFn

theorem tab_titsDGen {j : ℕ} (hj : j < 2) :
    TabRep (titsDArr j) (titsDGen j) :=
  ⟨titsDArr_size j, fun i => CFSG.Sporadic.Schreier.Tits.titsDArr_rep hj i⟩

end CFSG.StandardType.TitsGenerators
