module

public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Model

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

theorem statedScalars_inf_eq_bot (hF : Nat.card F = (2 ^ f) ^ 2) :
    (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (2 ^ f) F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hg2 : (g : GL (Fin 4) F) ∈ SUid (unitaryInvolution F 2 f) 4 := by
    rw [SUid_eq_statedSU hF 4]
    exact g.2
  have hdet : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := hg2.1
  rw [← hc, GeneralLinearGroup.coe_scalar] at hdet
  simp only [Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hc1 : (c : F) = 1 := by
    have h4 : ((c : F) + 1) ^ 4 = 0 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have hc4 : (c : F) ^ 4 = 1 := by simpa using hdet
      linear_combination hc4 + (2 * (c : F) ^ 3 + 3 * (c : F) ^ 2 + 2 * (c : F) + 1) * h2
    have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h4
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
    exact this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, Subgroup.coe_one, show c = 1 from Units.ext hc1, map_one]

noncomputable def unEquivProj (hF : Nat.card F = (2 ^ f) ^ 2) :
    SU (unitaryInvolution F 2 f) 4 ≃* StatedProj (StatedSU 4 (2 ^ f) F) :=
  (equivStatedSU hF 4).trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_inf_eq_bot hF).symm))

theorem isSimpleGroup_unSU (hF : Nat.card F = (2 ^ f) ^ 2) :
    IsSimpleGroup (SU (unitaryInvolution F 2 f) 4) := by
  rw [(unEquivProj hF).isSimpleGroup_congr]
  exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 f hF 4 (by norm_num)
    fun hq => absurd (Prod.mk.inj hq).1 (by norm_num)

end Model

theorem un_model_equiv {D : Type} [Group D] {f : ℕ}
    (hD : CFSG.Blueprint.LieModel D .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = (2 ^ f) ^ 2),
      Nonempty (SU (unitaryInvolution K 2 f) 4 ≃* D) := by
  rcases hD with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ (f * 2) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    have : CharP K 2 := charP_of_card_eq_prime_pow hcard
    exact ⟨K, inferInstance, inferInstance, inferInstance, hK, ⟨(unEquivProj hK).trans e.symm⟩⟩
  all_goals exact absurd hn (by norm_num)

end CFSG.Quasithin.H13.F431.Un
