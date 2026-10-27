module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Y1Cnt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Canon

public section

namespace CFSG.Quasithin.S15223P4.Y1

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem conj_mem_inf (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    {K₂ : Subgroup G} (hKX : ⁅X, K₂⁆ ≤ pCoreOf 2 X) {k : G} (hk : k ∈ K₂) {x : G}
    (hx : x ∈ X ⊓ M) : k * x * k⁻¹ ∈ X ⊓ M := by
  have hcomm : ⁅k, x⁆ ∈ pCoreOf 2 X := by
    apply hKX
    rw [Subgroup.commutator_comm X K₂]
    exact Subgroup.commutator_mem_commutator hk hx.1
  have hA : ⁅k, x⁆ ∈ sOf152 T Mc M B₀ ⊓ X := hN.A_sylow.pCoreOf_le hcomm
  have hAM : ⁅k, x⁆ ∈ X ⊓ M := ⟨hA.2, (c.S_le_N hA.1).1⟩
  have e : k * x * k⁻¹ = ⁅k, x⁆ * x := by rw [commutatorElement_def]; group
  rw [e]
  exact (X ⊓ M).mul_mem hAM hx

theorem le_normalizer_oPrimeResidualOf (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))
    {K₂ : Subgroup G} (hKX : ⁅X, K₂⁆ ≤ pCoreOf 2 X) :
    K₂ ≤ Subgroup.normalizer (oPrimeResidualOf 3 (M ⊓ I) : Set G) := by
  refine le_normalizer_of_forall_conj fun k hk y hy => ?_
  have key : oPrimeResidualOf 3 (M ⊓ I) ≤
      (oPrimeResidualOf 3 (M ⊓ I)).comap (MulAut.conj k).toMonoidHom := by
    refine oPrimeResidualOf_le_of_forall fun x hx j hj => ?_
    have h1 := conj_mem_inf c hN hKX hk (mem_inf_of_orderOf c hN h3 hx hj)
    refine mem_oPrimeResidualOf_three (inf_le_inf_N c h1) (k := j) ?_
    show orderOf (k * x * k⁻¹) = 3 ^ j
    rw [orderOf_conj_eq]
    exact hj
  exact key hy

theorem commutator_le (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))
    {K₂ : Subgroup G} (hKX : ⁅X, K₂⁆ ≤ pCoreOf 2 X)
    (hXK : X ≤ Subgroup.normalizer (K₂ : Set G)) :
    ⁅oPrimeResidualOf 3 (M ⊓ I), K₂⁆ ≤ oPrimeResidualOf 3 (M ⊓ I) ⊓ K₂ :=
  S15223.commutator_le_inf_of_normalizes
    ((oPrimeResidualOf_le_inf c hN h3).trans (inf_le_left.trans hXK))
    (le_normalizer_oPrimeResidualOf c hN h3 hKX)

end CFSG.Quasithin.S15223P4.Y1
