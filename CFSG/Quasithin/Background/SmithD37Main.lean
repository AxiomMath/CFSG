module

public import CFSG.Quasithin.Background.SmithD37Cases
public import CFSG.Quasithin.Background.SmithD37L32
public import CFSG.Quasithin.Background.SmithD37Out1
public import CFSG.Quasithin.Background.SmithD37Mat
public import CFSG.Quasithin.Background.SmithD37Base
public import CFSG.Quasithin.Background.F918L4
public import CFSG.Quasithin.Background.B5NonSQTK

public section

namespace CFSG.Quasithin.SmithD37

open scoped commutatorElement

section Module

variable {U : Type} [CommGroup U] [Finite U] {X L₁ L₂ : Subgroup (MulAut U)} {s : MulAut U}

omit [Finite U] in
theorem comm_of_dim_one {F : Type} [Field F] (Mm : MatModel L₁ L₂ F 1) (a b : ↥L₁) :
    a * b = b * a := by
  apply Mm.inj₁
  rw [map_mul, map_mul]
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem core_concl
    (hC : Core X L₁ L₂ s) (hnc : ∃ a b : ↥L₁, a * b ≠ b * a) :
    (∃ n, IsPSL 2 2 n ↥L₁ ∧ Omega4PlusModule (L₁ ⊔ L₂) n) ∨
      (IsPSL 3 2 1 ↥L₁ ∧ TensorNatL32 (L₁ ⊔ L₂)) := by
  have := hC.nt
  obtain ⟨F, _, _, _, d, hd0, ⟨Mm⟩⟩ :=
    exists_matModel hC.exp hC.comm hC.irr s hC.swap₁ hC.swap₂
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · obtain ⟨a, b, hab⟩ := hnc
      exact absurd (comm_of_dim_one Mm a b) hab
    · exact Or.inl (omega4_of_dim_two Mm hC.a38 hC.swap.a38)
  · obtain ⟨hd3, hq2, hL⟩ := big_case hC Mm hd
    subst hd3
    have h₁ := natCard_of_isPSL_two_seven hL
    have h₂ : Nat.card ↥L₂ = 168 := by
      rw [← h₁]
      exact (Nat.card_congr hC.equiv.toEquiv).symm
    exact Or.inr (l32_of_dim_three Mm hq2 h₁ h₂)

end Module

theorem exists_ne_comm_autSub {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {V : Subgroup W} (hLV : L ≤ stabSub V) (hLq : CFSG.IsQuasisimple ↥L)
    (hnt : autSub L V ≠ ⊥) : ∃ a b : ↥(autSub L V), a * b ≠ b * a := by
  by_contra h
  push Not at h
  apply hnt
  rw [autSub_eq_bot_iff hLV, commSub_eq_bot_iff]
  have hperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hLq.1
    exact Subgroup.commutator_eq_self
  have key : ∀ g₁ ∈ L, ∀ g₂ ∈ L, ⁅g₁, g₂⁆ ∈ centSub V := by
    intro g₁ h₁ g₂ h₂
    have hc := congrArg Subtype.val
      (h ⟨resHom V ⟨g₁, hLV h₁⟩, mem_autSub.mpr ⟨⟨g₁, hLV h₁⟩, h₁, rfl⟩⟩
        ⟨resHom V ⟨g₂, hLV h₂⟩, mem_autSub.mpr ⟨⟨g₂, hLV h₂⟩, h₂, rfl⟩⟩)
    simp only [Subgroup.coe_mul] at hc
    have hcomm : ∀ v ∈ V, g₁ (g₂ v) = g₂ (g₁ v) := fun v hv =>
      congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : W)) hc
    intro u hu
    have hv : (g₁⁻¹ * g₂⁻¹) u ∈ V :=
      ((stabSub V).mul_mem ((stabSub V).inv_mem (hLV h₁)) ((stabSub V).inv_mem (hLV h₂)) u).2 hu
    have e : ⁅g₁, g₂⁆ u = g₁ (g₂ ((g₁⁻¹ * g₂⁻¹) u)) := by
      rw [commutatorElement_def]
      simp only [MulAut.mul_apply]
    rw [e, hcomm _ hv]
    simp only [MulAut.mul_apply]
    rw [show g₁ (g₁⁻¹ (g₂⁻¹ u)) = g₂⁻¹ u by
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply],
      MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hle : L ≤ centSub V := by
    rw [← hperf]
    exact Subgroup.commutator_le.mpr key
  intro u hu g hg
  exact hle hg u hu

theorem d37_of_inputs
    (hL38 : D3L38) (hA21 : AsA21SQTKSection) : D37 := by
  intro W _ _ M Mp T L V std hVT t htT htn hMp
  obtain ⟨htV, hC, hsup⟩ := core_of_d3Std hL38 hA21 std hVT htT htn hMp
  rw [hsup]
  refine core_concl hC ?_
  obtain ⟨hA38, -, -, -⟩ := hL38 W M Mp T L V std t htT htn hMp
  have hLq := insp5a_sec_isQuasisimple std.hyp hA38
  have hLV : L ≤ stabSub V := insp5a_le_stabSub std.hyp
  have : IsSimpleGroup ↥(autSub L V) := hC.simple
  have hnt : autSub L V ≠ ⊥ := by
    have : Nontrivial ↥(autSub L V) := IsSimpleGroup.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  exact exists_ne_comm_autSub hLV hLq hnt

end CFSG.Quasithin.SmithD37

namespace CFSG.Quasithin

theorem d37_holds :
    D37 :=
  SmithD37.d37_of_inputs (d3L38_of_a38 d3A38_holds) asA21SQTKSection

end CFSG.Quasithin
