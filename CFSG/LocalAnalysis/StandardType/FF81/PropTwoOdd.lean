module

public import CFSG.LocalAnalysis.StandardType.FF81.PropTwoDict
public import CFSG.RankThree.PartTwo.Sec21.FF81P51Tau
import CFSG.LocalAnalysis.StandardType.GGFFNine

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 (Nor)
open Matrix
open CFSG.RankThree.PartTwo.Sec21.FF81.P51 (V Mat GL4 e cfgOf mB exists_tau_of_mB)

theorem exists_tau_of_bCoordModel {G : Type} [Group G]
    {K : Subgroup G} {b : G} {z : Fin 3 → K} {Γ : Subgroup GL4} {cv : G → V}
    (hM : BCoordModel b z Γ cv) (hB : (cfgOf Γ).1 = mB) :
    ∃ τ ∈ Nor (GGFF.Bt b z), τ * b * τ⁻¹ = b * GGFF.zetaOf (GGFF.zs z) ^ 2 ∧
      τ * GGFF.zetaOf (GGFF.zs z) * τ⁻¹ = GGFF.zetaOf (GGFF.zs z) := by
  obtain ⟨g, hg, hgz, hg0⟩ := exists_tau_of_mB hM.hyp hB
  obtain ⟨n, hn, hcol⟩ := hM.to_nor g hg
  have hconj : ∀ x ∈ GGFF.Bt b z, n * x * n⁻¹ ∈ GGFF.Bt b z := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have hb : b ∈ GGFF.Bt b z := xs_mem_Bt b z 0
  have h1 : GGFF.zs z 0 ∈ GGFF.Bt b z := xs_mem_Bt b z 1
  have h2 : GGFF.zs z 1 ∈ GGFF.Bt b z := xs_mem_Bt b z 2
  have h3 : GGFF.zs z 2 ∈ GGFF.Bt b z := xs_mem_Bt b z 3
  have hζ := zeta_mem_Bt b z
  have hcζ : cv (n * GGFF.zetaOf (GGFF.zs z) * n⁻¹) = e 1 + e 2 + e 3 := by
    have c1 : cv (n * GGFF.zs z 0 * n⁻¹) = (g : Mat) *ᵥ e 1 := (hcol 1).symm
    have c2 : cv (n * GGFF.zs z 1 * n⁻¹) = (g : Mat) *ᵥ e 2 := (hcol 2).symm
    have c3 : cv (n * GGFF.zs z 2 * n⁻¹) = (g : Mat) *ᵥ e 3 := (hcol 3).symm
    have : n * GGFF.zetaOf (GGFF.zs z) * n⁻¹ =
        (n * GGFF.zs z 0 * n⁻¹) * (n * GGFF.zs z 1 * n⁻¹) * (n * GGFF.zs z 2 * n⁻¹) := by
      unfold GGFF.zetaOf; group
    rw [this, hM.mul _ ((GGFF.Bt b z).mul_mem (hconj _ h1) (hconj _ h2)) _ (hconj _ h3),
      hM.mul _ (hconj _ h1) _ (hconj _ h2), c1, c2, c3, ← Matrix.mulVec_add, ← Matrix.mulVec_add]
    exact hgz
  refine ⟨n, hn, ?_, ?_⟩
  · have hbζ2 : b * GGFF.zetaOf (GGFF.zs z) ^ 2 ∈ GGFF.Bt b z :=
      (GGFF.Bt b z).mul_mem hb ((GGFF.Bt b z).pow_mem hζ 2)
    have e0 : cv (n * b * n⁻¹) = (g : Mat) *ᵥ e 0 := (hcol 0).symm
    have hpow : cv (GGFF.zetaOf (GGFF.zs z) ^ 2) = e 1 + e 2 + e 3 + (e 1 + e 2 + e 3) := by
      rw [pow_two, hM.mul _ hζ _ hζ, hM.cv_zeta]
    refine hM.inj _ (hconj b hb) _ hbζ2 ?_
    have h0 : cv b = e 0 := hM.basis 0
    rw [e0, hg0, hM.mul _ hb _ ((GGFF.Bt b z).pow_mem hζ 2), hpow, h0]
    ext j
    fin_cases j <;> simp [e] <;> decide
  · exact hM.inj _ (hconj _ hζ) _ hζ (by rw [hcζ, hM.cv_zeta])

theorem odd_card_cenS_of_mB {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {b : G} {z : Fin 3 → K} {Γ : Subgroup GL4} {cv : G → V}
    (h : GGFF.Setting b K z) (hN : GGFF.ModelN K z) (hchar : CFSG.Open.IsCharTwoType G)
    (hM : BCoordModel b z Γ cv) (hB : (cfgOf Γ).1 = mB) :
    Odd (Nat.card (Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G))) := by
  obtain ⟨τ, hτ, hτb, hτζ⟩ := exists_tau_of_bCoordModel hM hB
  have hbot := h.cenB_two_eq_bot hN hchar hτ hτb hτζ
  by_contra hodd
  have heven : 2 ∣ Nat.card (Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G)) :=
    (Nat.not_odd_iff_even.mp hodd).two_dvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hle : Subgroup.zpowers (x : G) ≤
      Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).mpr x.2
  have hp : IsPGroup 2 (Subgroup.zpowers (x : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_submonoid x, hx, pow_one]
  have hx1 := hbot _ hle hp
  rw [Subgroup.zpowers_eq_bot] at hx1
  have : orderOf (x : G) = 1 := by rw [hx1, orderOf_one]
  rw [orderOf_submonoid x, hx] at this
  omega

end CFSG.StandardType.FF81

end
