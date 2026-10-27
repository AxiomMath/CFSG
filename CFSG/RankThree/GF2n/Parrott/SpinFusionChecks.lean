module

public import CFSG.RankThree.GF2n.Parrott.SpinXChecks

public section

namespace CFSG.RankThree.GF2n.Parrott.SpinRigid

theorem exists_nonsingular_image :
    ∃ m ∈ wZero, qTab.getD (m ^^^ bapply bX m) 0 ≠ 0 := by
  decide +kernel

theorem exists_singular_image :
    ∃ m ∈ wZero, (m ^^^ bapply bX m) ≠ 0 ∧ qTab.getD (m ^^^ bapply bX m) 0 = 0 := by
  decide +kernel

theorem singular_unique : ∀ m₁ ∈ wZero, m₁ ∈ fixX → ∀ m₂ ∈ wZero, m₂ ∈ fixX →
    qTab.getD m₁ 0 = 0 → qTab.getD m₂ 0 = 0 → m₁ ≠ 0 → m₂ ≠ 0 → m₁ = m₂ := by
  decide +kernel

end CFSG.RankThree.GF2n.Parrott.SpinRigid
