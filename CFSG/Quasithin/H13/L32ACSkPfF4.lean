module

public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem n2Model_n4Model_of_is2F4
    {M : Type} [Group M]
    {n : ℕ} (h : Is2F4 n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, -, -, -, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := large_Ree_model_Schreier _ 2 n h
  obtain ⟨-, a, hfa, hmodel'⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel'
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := n) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have ha : 1 ≤ a := by omega
  obtain ⟨hNF, hF⟩ := CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK'
  have hZ := large_Ree_fixed_group_center_trivial a K hK'
  have h2 := n2Model_n4Model_of_two_inner hZ fun α hα =>
    mem_range_conj_of_pow_two_pow (F4.reeGammaFieldAutHom K a) hNF (fun β hβ => hF β hβ)
      (f := 2 * a + 1) ⟨a, rfl⟩ (ringAut_pow_eq_one hK') hα
  exact ⟨h2.1.of_mulEquiv E.symm, h2.2.of_mulEquiv E.symm⟩

end CFSG.Quasithin.H13.L32A.C.SkPf
