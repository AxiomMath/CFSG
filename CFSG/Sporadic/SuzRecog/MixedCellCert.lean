module

public import Certificates.Certificate15121

public section

namespace CFSG.Sporadic.SuzRecog.MixedCell

open CFSG.Sporadic.SuzRecog.MixedCellCheck

theorem single_checks : ∀ n < 24, singleMem n := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, -⟩ := Certificates.certificate15121
  intro n hn
  interval_cases n
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23]

theorem pair_checks : ∀ n < 12, pairMem n := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := Certificates.certificate15121
  intro n hn
  interval_cases n
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem model_checks :
    mcPermsOK = true ∧ mcMembersOK = true ∧ mcCommOK = true ∧ mcLettersOK = true ∧
      mcRelsOK = true ∧ mcCellsOK = true ∧ mcBoundOK 0 = true ∧ mcBoundOK 2 = true ∧
      mcRemarkOK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, h⟩ := Certificates.certificate15121
  exact h

theorem perms_check : mcPermsOK = true := model_checks.1

theorem members_check : mcMembersOK = true := model_checks.2.1

theorem comm_check : mcCommOK = true := model_checks.2.2.1

theorem letters_check : mcLettersOK = true :=
  model_checks.2.2.2.1

theorem rels_check : mcRelsOK = true := model_checks.2.2.2.2.1

theorem cells_check : mcCellsOK = true :=
  model_checks.2.2.2.2.2.1

theorem bound0_check : mcBoundOK 0 = true :=
  model_checks.2.2.2.2.2.2.1

theorem bound2_check : mcBoundOK 2 = true :=
  model_checks.2.2.2.2.2.2.2.1

theorem remark_check : mcRemarkOK = true :=
  model_checks.2.2.2.2.2.2.2.2

end CFSG.Sporadic.SuzRecog.MixedCell
