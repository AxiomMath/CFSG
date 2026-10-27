module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
import CFSG.LocalAnalysis.StandardType.GGNbrGraphField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal

theorem ggPsiInnerDiag_of_cube_of_label_omegaPlus_two {m : ℕ} (hm : 5 ≤ m)
    {U : Type*} [Group U] (Δ : UniversalRootDatum U)
    {X : Type} [Group X] [Finite X] (ψ : U →* X)
    (hperf : commutator ↥ψ.range = ⊤)
    (hlabel : GGHasLabel ⟨.D, m, 1⟩ (↥ψ.range ⧸ Subgroup.center ↥ψ.range))
    {c : X} (hc : c ∈ Subgroup.normalizer (ψ.range : Set X)) (hc3 : c ^ 3 = 1) :
    GGPsiInnerDiag Δ ψ c := by
  classical
  have hm3 : ¬ m = 3 := by omega
  simp only [GGHasLabel, LargeEvenRawDatum, if_neg hm3, pow_one] at hlabel
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := hlabel
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  obtain ⟨r, hr⟩ := OrthRest.mem_range_conj_plus_two (m := m) hm hK
    (ggLAut_pow_eq_one ψ.range θ (Subgroup.inv_mem _ hc) (by rw [inv_pow, hc3, inv_one]))
  apply ggPsiInnerDiag_of_induces_conj Δ ψ hperf θ hc
  rw [hr]
  exact largeEvenInduces_ggLAut_inv ψ.range θ (Subgroup.inv_mem _ hc)

end CFSG.StandardType
