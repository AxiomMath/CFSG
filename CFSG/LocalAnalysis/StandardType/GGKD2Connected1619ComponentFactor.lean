module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents


public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrspb1_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x : G | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine ⟨a * c, A.mul_mem ha hc, b * d, B.mul_mem hb hd, ?_⟩
        calc (a * b) * (c * d) = a * (b * c) * d := by group
          _ = a * (c * b) * d := by rw [← hcomm c hc b hb]
          _ = (a * c) * (b * d) := by group
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [hcomm a ha b hb]
          _ = a⁻¹ * b⁻¹ := by group }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

private theorem ltrspb1_component_subgroupOf_top {G : Type*} [Group G] {C Y : Subgroup G}
    (hC : CFSG.Assembly.IsComponentOf C Y) :
    CFSG.Open.IsComponentOf (C.subgroupOf Y) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (CFSG.Assembly.IsSubnormal.subgroupOf hC.2.1)
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hC.1) (show CFSG.Open.IsQuasisimple C from hC.2.2)

theorem component_le_factor {H : Type} [Group H] [Finite H] {A₁ A₂ Y : Subgroup H}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hY : A₁ ⊔ A₂ = Y) {C : Subgroup H}
    (hC : CFSG.Assembly.IsComponentOf C Y) : C ≤ A₁ ∨ C ≤ A₂ := by
  have hA₁Y : A₁ ≤ Y := by rw [← hY]; exact le_sup_left
  have hA₂Y : A₂ ≤ Y := by rw [← hY]; exact le_sup_right
  have hCY : C ≤ Y := hC.1
  have hcomp : CFSG.Open.IsComponentOf (C.subgroupOf Y) ⊤ :=
    ltrspb1_component_subgroupOf_top hC
  have hn₁ : (A₁.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hA₁Y]
    intro h k hh hk
    obtain ⟨a, ha, b, hb, hkab⟩ :=
      ltrspb1_mem_sup_of_commute hcomm (by rw [hY]; exact hk)
    rw [hkab]
    have hbh : b * h * b⁻¹ = h := by rw [← hcomm h hh b hb]; group
    have hconj : (a * b) * h * (a * b)⁻¹ = a * h * a⁻¹ := by
      calc (a * b) * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ := by group
        _ = a * h * a⁻¹ := by rw [hbh]
    rw [hconj]
    exact A₁.mul_mem (A₁.mul_mem ha hh) (A₁.inv_mem ha)
  have hn₂ : (A₂.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hA₂Y]
    intro h k hh hk
    obtain ⟨a, ha, b, hb, hkab⟩ :=
      ltrspb1_mem_sup_of_commute hcomm (by rw [hY]; exact hk)
    rw [hkab]
    have hmem : b * h * b⁻¹ ∈ A₂ := A₂.mul_mem (A₂.mul_mem hb hh) (A₂.inv_mem hb)
    have hay : a * (b * h * b⁻¹) * a⁻¹ = b * h * b⁻¹ := by
      rw [hcomm a ha (b * h * b⁻¹) hmem]; group
    have hconj : (a * b) * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ := by group
    rw [hconj, hay]
    exact hmem
  letI : (A₁.subgroupOf Y).Normal := hn₁
  letI : (A₂.subgroupOf Y).Normal := hn₂
  rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
      (C.subgroupOf Y) (A₁.subgroupOf Y) hcomp with hle₁ | hcomm₁
  · left
    intro x hx
    exact hle₁ (show (⟨x, hCY hx⟩ : Y) ∈ C.subgroupOf Y from hx)
  rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
      (C.subgroupOf Y) (A₂.subgroupOf Y) hcomp with hle₂ | hcomm₂
  · right
    intro x hx
    exact hle₂ (show (⟨x, hCY hx⟩ : Y) ∈ C.subgroupOf Y from hx)
  · exfalso
    have hCA₁ : ⁅C, A₁⁆ = ⊥ := by
      have hmap := congrArg (Subgroup.map Y.subtype) hcomm₁
      simpa only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hCY,
        Subgroup.map_subgroupOf_eq_of_le hA₁Y, Subgroup.map_bot] using hmap
    have hCA₂ : ⁅C, A₂⁆ = ⊥ := by
      have hmap := congrArg (Subgroup.map Y.subtype) hcomm₂
      simpa only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hCY,
        Subgroup.map_subgroupOf_eq_of_le hA₂Y, Subgroup.map_bot] using hmap
    have hcommA₁ : C ≤ Subgroup.centralizer (A₁ : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCA₁
    have hcommA₂ : C ≤ Subgroup.centralizer (A₂ : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCA₂
    have hcentY : C ≤ Subgroup.centralizer (Y : Set H) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        ltrspb1_mem_sup_of_commute hcomm (by rw [hY]; exact hy)
      have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp (hcommA₁ hc) a ha
      have hcb : b * c = c * b := Subgroup.mem_centralizer_iff.mp (hcommA₂ hc) b hb
      calc (a * b) * c = a * (b * c) := by group
        _ = a * (c * b) := by rw [hcb]
        _ = (a * c) * b := by group
        _ = (c * a) * b := by rw [hca]
        _ = c * (a * b) := by group
    have hcommC : ∀ p q : ↥C, p * q = q * p := fun p q => Subtype.ext (by
      have hqY : (q : H) ∈ Y := hCY q.2
      exact (Subgroup.mem_centralizer_iff.mp (hcentY p.2) (q : H) hqY).symm)
    exact CFSG.LieType.SemisimpleCentralizers.Held.not_isQuasisimple_of_comm hcommC
      (show CFSG.Open.IsQuasisimple C from hC.2.2)

end S2MathAs3_1619Final

end
