module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.Quasithin.Stroth

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

theorem isLieOverTwo_un5 {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ k) ^ 2) (hk : 1 ≤ k) :
    IsLieOverTwo .PSU 5 k
      (SU (unitaryInvolution F 2 k) 5 ⧸ Subgroup.center (SU (unitaryInvolution F 2 k) 5)) := by
  have hne : (5, 2 ^ k) ≠ (3, 2) := by simp
  have hZ := (isQuasisimple_statedSU_of_card (p := 2) (f := k) (n := 5) hF (by norm_num) hne).2
  unfold IsLieOverTwo
  refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ⟨Nat.prime_two, hk, by norm_num, hne⟩,
    F, inferInstance, inferInstance, hF, ⟨?e⟩⟩
  exact centerQuotientEquivStatedProj (p := 2) (f := k) (n := 5) hF hZ

end CFSG.Quasithin.Stroth
