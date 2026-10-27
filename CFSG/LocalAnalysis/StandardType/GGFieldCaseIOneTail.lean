module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48TailCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

theorem ggL47_of_cyclic {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁) {g : G}
    (hgU : g ∈ U) (hU : U ≤ Subgroup.zpowers g ⊔ U₁) {R : Subgroup G} (hRp : IsPGroup p R)
    (hRM : R ≤ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) (hUR : U ≤ R) :
    ∀ A ∈ thompsonAbelianSubgroups R, ⁅⁅U₁, A⁆, A⁆ = ⊥ → A ≤ U := by
  intro A hA hAAA
  have hcfg := hS.1.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hp := (Fact.out : p.Prime)
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  obtain ⟨hUC, hUp, hUmax, -⟩ := hS.2.2.2.2.2.2.1
  have hUN : U ≤ Subgroup.normalizer (U₁ : Set G) :=
    (Subgroup.le_normalizer).trans (normalizer_le_normalizer_of_forall_eq h46.2.2.1)
  have hΩw : ∀ w ∈ U, w ^ p ∈ U₁ → w ∈ Subgroup.zpowers x ⊔ U₁ := fun w hwU hwp =>
    mem_zpowers_sup_of_cyclic hUN hgU hU (hS.2.2.2.2.2.2.1.2.2.2 hxBs)
      (not_mem_of_ggL46 h46) (hBs.2 x hxBs) hwU hwp
  obtain ⟨hab, ⟨s, hs, hexp, hord, ⟨x', hx'x, hx'⟩, H, r, hHU₁, -, hHcard, hHB₁, hB₁card⟩, hJU,
    hΩ₁, -, hOp⟩ := h46
  have hx'p : x' ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx'x ▸ Subgroup.mem_zpowers x')
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard := card_le_mul_card_ggPowSubgroup hp (by omega) hab hΩ₁ hHU₁ hHcard hHB₁ hB₁card
  have hΩ' : ∀ w ∈ U, w ^ p ∈ U₁ → w ∈ Subgroup.zpowers x' ⊔ U₁ := fun w hw hwp => by
    rw [hx'x]
    exact hΩw w hw hwp
  intro a ha
  refine mem_of_quadratic hs hab hΩ₁ hexp hord hx' hx'p hcard hUC hUp hUmax hJU hOp hRp hRM hUR
    hΩ' (hA.1 ha) fun u hu => ?_
  have hc : ⁅⁅u⁻¹, a⁻¹⁆, a⁆ ∈ ⁅⁅U₁, A⁆, A⁆ :=
    Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (U₁.inv_mem hu) (A.inv_mem ha)) ha
  rw [hAAA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  have e : u⁻¹ * (a⁻¹ * u * a) = ⁅u⁻¹, a⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact hc

theorem ggL47IOneInput_of_cyclic (hcyc : GGL46CyclicIOneInput) : GGL47IOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hI1 h46 R hRp hRM _ hUR
  obtain ⟨g, hgU, hU⟩ := hcyc G p B Bs x L D J X B₂ d y K U U₁ hS hI1
  exact ggL47_of_cyclic hS h46 hgU hU hRp hRM hUR

end CFSG.StandardType

end
