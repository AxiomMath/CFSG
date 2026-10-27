module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXE
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_eight_false_of_indivisible (h : Cfg133 A t 3) (hI : IsIndivisible A) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N) : False := by
  obtain ⟨htop, hrk6⟩ := s13_eight_comps_rk h hI hD
  have hW6 := s13_eight_W6_comp h hD
  exact s13_eight_cost_false h hD htop hW6 (s13_eight_t_fixes_comps h hD hrk6)
    (s13_eight_t_central_off_W6 h hD hrk6 hW6)

end CFSG.LocalAnalysis.WeakClosure81
