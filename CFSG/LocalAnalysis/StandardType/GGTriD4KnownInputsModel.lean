module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneProof
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneAutRank
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTriality
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Model


theorem ggTriD4InnDiagInput_holds : GGTriD4InnDiagInput := by
  intro n hn K _ _ hK _
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    have := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK hφ
    simpa [MonoidHom.coe_range] using this
  · rintro _ ⟨r, rfl⟩
    exact conj_mem_chevIDImage _ r

theorem ggTriD4AutRankInput_holds : GGTriD4AutRankInput := by
  intro n hn K _ _ hK _
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (GGTriD4R n K) := Finite.of_equiv _ e.symm.toEquiv
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := center_eq_bot_of_mulEquiv e hZC
  have hR : ∀ E : Subgroup (GGTriD4R n K), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
    intro E hE
    have h1 := TableBExcSmallRanks.card_lt_of_isElemAbelian_triD4 hn K hK σ hσ
      (CFSG.Open.IsElemAbelian.map hE e.toMonoidHom)
    rw [Subgroup.card_map_of_injective e.injective] at h1
    obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
    rw [hk] at h1 ⊢
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h1))
  intro A hA
  exact card_le_of_isElemAbelian_aut Nat.prime_three hZ (ggOutCyclic_triD4 hn K hK) hR hA

theorem ggL44iiiTriD4NoneInput_of_model (hsub : GGNbrSubcomponentInput)
    (hSchur : GGTriD4SchurInput) (hComp : GGTriD4ComponentsInput) (hL : GGTriD4StdSubInput)
    (hE6 : GGTwE6LocalRankInput) : GGL44iiiTriD4NoneInput :=
  ggL44iiiTriD4NoneInput_of_known hsub
    ⟨ggTriD4InnDiagInput_holds, hSchur, ggTriD4AutRankInput_holds, hComp⟩ hL hE6

theorem ggL44iiiTriD4LangInput_of_model (hsub : GGNbrSubcomponentInput)
    (hSchur : GGTriD4SchurInput) (hComp : GGTriD4ComponentsInput) (hL : GGTriD4StdSubInput)
    (hE6 : GGTwE6LocalRankInput) : GGL44iiiTriD4LangInput :=
  ggL44iiiTriD4LangInput_of_none (ggL44iiiTriD4NoneInput_of_model hsub hSchur hComp hL hE6)

end Model

end CFSG.StandardType
