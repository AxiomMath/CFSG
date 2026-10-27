module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Model

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

noncomputable def un5Equiv (hF : Nat.card F = (2 ^ f) ^ 2) :
    SU (unitaryInvolution F 2 f) 5 ⧸ Subgroup.center (SU (unitaryInvolution F 2 f) 5) ≃*
      StatedProj (StatedSU 5 (2 ^ f) F) :=
  centerQuotientEquivStatedProj hF (isQuasisimple_statedSU_of_card hF (by norm_num)
    fun hq => absurd (Prod.mk.inj hq).1 (by norm_num)).2

theorem isSimpleGroup_un5 (hF : Nat.card F = (2 ^ f) ^ 2) :
    IsSimpleGroup (SU (unitaryInvolution F 2 f) 5 ⧸
      Subgroup.center (SU (unitaryInvolution F 2 f) 5)) := by
  rw [(un5Equiv hF).isSimpleGroup_congr]
  exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 f hF 5 (by norm_num)
    fun hq => absurd (Prod.mk.inj hq).1 (by norm_num)

end Model

theorem un5_model_equiv {D : Type} [Group D] {f : ℕ}
    (hD : CFSG.Blueprint.LieModel D .PSU 5 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = (2 ^ f) ^ 2),
      Nonempty (SU (unitaryInvolution K 2 f) 5 ⧸
        Subgroup.center (SU (unitaryInvolution K 2 f) 5) ≃* D) := by
  rcases hD with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ (f * 2) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    have : CharP K 2 := charP_of_card_eq_prime_pow hcard
    exact ⟨K, inferInstance, inferInstance, inferInstance, hK, ⟨(un5Equiv hK).trans e.symm⟩⟩
  all_goals exact absurd hn (by norm_num)

end CFSG.Quasithin.H13.F431.Un
