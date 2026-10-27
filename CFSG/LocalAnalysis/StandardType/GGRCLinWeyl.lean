module

public import CFSG.LocalAnalysis.StandardType.GGRCSignedClass
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRC_linWeyl_of_monomial_pm1 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (hn : 4 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    ZS.LinWeyl p A := by
  rcases ggRC_signed_class hp2 hn b A hirr hgen hmon with hB | hD
  · exact ggRC_linWeyl_of_signed hp2 (by omega) b A hB
  · exact ggRC_linWeyl_of_even_signed hp2 hn b A hD

end CFSG.StandardType
