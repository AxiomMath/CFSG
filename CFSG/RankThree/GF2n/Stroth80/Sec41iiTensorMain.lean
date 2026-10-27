module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiCard
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSide
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiPointSp
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiPointSL
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiPointOmega
public import CFSG.RankThree.GF2n.Stroth80.Sec43
public import CFSG.RankThree.GF2n.Stroth80.Sec45Cases
public import CFSG.RankThree.GF2n.Stroth80.Sec42
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Glue

theorem stroth41iiTensor_of_pieces (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hCQ : ClassicalQuasisimpleStatement)
    (hSetup : TensorSetupStatement) (hSide : TensorSideStatement) :
    Stroth41iiTensorStatement := by
  intro G _ _ M Q Z B hN hc n hw hn hno hgen X₁ X₂ h₁ h₂ hXY hSL₁ hSL₂ t τ htLB hτLB ht₁ ht1 hτ₂
    hτ1 hC
  classical
  have hcs := hc.compSimple h34 h44 hw hn hno hgen
  have hNorm := hc.normal_bar_Lgen
  have hX₁c : IsComponent X₁ := isComponent_of_normal_normal hNorm h₁.1 h₁.2.1 h₁.2.2
  have hX₂c : IsComponent X₂ := isComponent_of_normal_normal hNorm h₂.1 h₂.2.1 h₂.2.2
  have hne : X₁ ≠ X₂ := by
    intro h
    apply ne_bot_of_isComponent hX₁c
    have := hXY
    rw [← h, inf_idem] at this
    exact this
  have hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x := comm_of_ne_component hX₁c hX₂c hne
  have htQ : (t : G) ∉ Q := fun h =>
    ht1 ((QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_subgroupOf.mpr h))
  have hτQ : (τ : G) ∉ Q := fun h =>
    hτ1 ((QuotientGroup.eq_one_iff τ).mpr (Subgroup.mem_subgroupOf.mpr h))
  obtain ⟨K, hF, hFin, γ, M₀, ρ, b, hS⟩ := hSetup G M Q Z B hc n hw hn hno hgen
  obtain ⟨W₂, d₂, S₂⟩ := hSide G M Q Z B hc n hw hn hno hgen K γ M₀ ρ b hS X₂ h₂ hSL₂ t htLB ht1
    (fun x hx => hcomm _ ht₁ x hx)
  obtain ⟨W₁, d₁, S₁⟩ := hSide G M Q Z B hc n hw hn hno hgen K γ M₀ ρ b hS X₁ h₁ hSL₁ τ hτLB hτ1
    (fun x hx => (hcomm x hx _ hτ₂).symm)
  have hR₂ : X₂ ≤ bar M Q (Rt M (LB M Q B) (t : G)) :=
    hc.component_le_bar_Rt h34 hw hn hno hgen hcs hX₂c htLB fun x hx => (hcomm _ ht₁ x hx).symm
  have hR₁ : X₁ ≤ bar M Q (Rt M (LB M Q B) (τ : G)) :=
    hc.component_le_bar_Rt h34 hw hn hno hgen hcs hX₁c hτLB fun x hx => hcomm x hx _ hτ₂
  have hn₂ : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t : G)), ∀ x ∈ X₂, r * x * r⁻¹ ∈ X₂ :=
    fun r hr x hx => conj_mem_of_subgroupOf_normal h₂.1 h₂.2.1
      (Ctx.bar_Rt_le_bar_Lgen (t : G) hr) hx
  have hn₁ : ∀ r ∈ bar M Q (Rt M (LB M Q B) (τ : G)), ∀ x ∈ X₁, r * x * r⁻¹ ∈ X₁ :=
    fun r hr x hx => conj_mem_of_subgroupOf_normal h₁.1 h₁.2.1
      (Ctx.bar_Rt_le_bar_Lgen (τ : G) hr) hx
  have hXN₂ : X₂ ⊓ bar M Q (hc.CN (t : G)) = ⊥ :=
    hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs htLB hX₂c hR₂
  have hXN₁ : X₁ ⊓ bar M Q (hc.CN (τ : G)) = ⊥ :=
    hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs hτLB hX₁c hR₁
  have hsup₂ := hc.Rt_eq_CN_sup h34 h310 hCQ hw hn hno hgen hcs htLB htQ hX₂c hR₂ hn₂ hSL₂
  have hsup₁ := hc.Rt_eq_CN_sup h34 h310 hCQ hw hn hno hgen hcs hτLB hτQ hX₁c hR₁ hn₁ hSL₁
  have hCN₂ : bar M Q (hc.CN (t : G)) ≤ Subgroup.normalizer (X₂ : Set (Mbar M Q)) := fun m hm =>
    Subgroup.mem_normalizer_fintype fun x hx => hn₂ m (hc.bar_CN_le_bar_Rt _ hm) x hx
  have hCN₁ : bar M Q (hc.CN (τ : G)) ≤ Subgroup.normalizer (X₁ : Set (Mbar M Q)) := fun m hm =>
    Subgroup.mem_normalizer_fintype fun x hx => hn₁ m (hc.bar_CN_le_bar_Rt _ hm) x hx
  have hcard := card_le_mul_projections (Λ := bar M Q (LB M Q B))
    (N₁ := bar M Q (hc.CN (t : G))) (X₁ := X₂) (R₁ := bar M Q (Rt M (LB M Q B) (t : G)))
    (N₂ := bar M Q (hc.CN (τ : G))) (X₂ := X₁) (R₂ := bar M Q (Rt M (LB M Q B) (τ : G)))
    (hc.bar_LB_le_bar_Rt htLB) (hc.bar_CN_le_bar_Rt _) hR₂
    (fun r hr m hm => hc.bar_CN_conj_mem htLB hr hm)
    (fun r hr => by
      rw [hsup₂] at hr
      obtain ⟨m, hm, x, hx, hmx⟩ := exists_mul_of_mem_sup_of_le_normalizer hCN₂ hr
      exact ⟨m, hm, x, hx, hmx.symm⟩)
    (by rw [inf_comm]; exact hXN₂)
    (hc.bar_LB_le_bar_Rt hτLB) (hc.bar_CN_le_bar_Rt _) hR₁
    (fun r hr m hm => hc.bar_CN_conj_mem hτLB hr hm)
    (fun r hr => by
      rw [hsup₁] at hr
      obtain ⟨m, hm, x, hx, hmx⟩ := exists_mul_of_mem_sup_of_le_normalizer hCN₁ hr
      exact ⟨m, hm, x, hx, hmx.symm⟩)
    (by rw [inf_comm]; exact hXN₁) hC
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hcardΛ : Nat.card (bar M Q (LB M Q B)) = Nat.card K ^ (n - 1) := by
    rw [hc.card_bar_LB_of_34 h34 hw hn hno hgen, ← hS.card]
  rw [hcardΛ] at hcard
  have h3 : Nat.card K ^ (n - 1) ≤ Nat.card K ^ (d₂ - 1) * Nat.card K ^ (d₁ - 1) :=
    hcard.trans (Nat.mul_le_mul S₂.pcard S₁.pcard)
  rw [← pow_add] at h3
  have h4 := (Nat.pow_le_pow_iff_right hq).mp h3
  have hd1 := S₁.three
  have hd2 := S₂.three
  have hn' : n + 1 ≤ d₁ + d₂ := by omega
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hX₁H : X₁ ≤ bar M Q (H0 M Z) := h₁.1.trans hc.bar_Lgen_le_bar_H0
  have hX₂H : X₂ ≤ bar M Q (H0 M Z) := h₂.1.trans hc.bar_Lgen_le_bar_H0
  exact tensor_count_false M₀.B M₀.alt M₀.nondeg ρ hS.dim hcomm S₁ S₂
    (fun x hx v w => hS.iso x (hX₁H hx) v w) (fun x hx v w => hS.iso x (hX₂H hx) v w) hn'

theorem stroth41iiTensor_of_310 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hCQ : ClassicalQuasisimpleStatement)
    (hCG : ClassicalPointStatement) : Stroth41iiTensorStatement :=
  stroth41iiTensor_of_pieces h34 h310 h44 hCQ (tensorSetup_of_34 h34)
    (tensorSide_of_ctx h34 h310 h44 hCQ hCG)

theorem stroth45_of_classical (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hCG : ClassicalPointStatement)
    (hO4 : ClassicalOrderFourStatement) (hOm : OmegaMinusFourSylowStatement) :
    Stroth45Statement :=
  stroth45_of_42_43 h34 h310 h44 classicalQuasisimpleStatement_holds
      (stroth42_of_41ii h34 h310
          (stroth41ii_of_tensor h34 h310 h44 classicalQuasisimpleStatement_holds
              (stroth41iiTensor_of_310 h34 h310 h44 classicalQuasisimpleStatement_holds hCG)) h44
          classicalQuasisimpleStatement_holds hO4 hOm)
      (stroth43_of_310 h34 h310 h44 classicalQuasisimpleStatement_holds)

theorem classicalPointStatement_of_nonsingular (hNS : ClassicalPointNonsingularStatement) :
    ClassicalPointStatement :=
  ⟨classicalPointSL, classicalPointSp, (classicalPointOmega_of_nonsingular hNS).1,
    (classicalPointOmega_of_nonsingular hNS).2⟩

theorem stroth45_of_nonsingular (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hNS : ClassicalPointNonsingularStatement)
    (hO4 : ClassicalOrderFourStatement) (hOm : OmegaMinusFourSylowStatement) :
    Stroth45Statement :=
  stroth45_of_classical h34 h310 h44 (classicalPointStatement_of_nonsingular hNS) hO4 hOm

end Glue

end CFSG.RankThree.GF2n.Stroth80
