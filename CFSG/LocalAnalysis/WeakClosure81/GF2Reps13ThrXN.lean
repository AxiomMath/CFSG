module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXNE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_case_three_nonab_N (h : Cfg133 A t 3)
    (hab : ∀ x ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, ∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
      x * y = y * x)
    (hX : ∃ a ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆),
      ∃ b ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆), a * b ≠ b * a) :
    ∃ L : Subgroup (MulAut W), L ≤ pCoreOf 3 A ∧ Conc4_133 A t L ∧ IsPOnePlusTwo 3 ↥L ∧
      rk ↥(commSub ⊤ L) = 6 ∧ ∀ n ∈ pCoreOf 3 A, L.map (MulAut.conj n).toMonoidHom = L := by
  exact w16n_main (w16n_hnon h hab hX) le_rfl

end CFSG.LocalAnalysis.WeakClosure81
