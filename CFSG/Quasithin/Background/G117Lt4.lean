module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem normal_centralizer_subgroupOf {Γ H : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    ((Γ ⊓ Subgroup.centralizer (H : Set (GLV V))).subgroupOf Γ).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
  refine ⟨Γ.mul_mem (Γ.mul_mem g.2 hn.1) (Γ.inv_mem g.2), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h1 : (g : GLV V)⁻¹ * h * (g : GLV V) ∈ H := by
    simpa using hN (g : GLV V)⁻¹ (Γ.inv_mem g.2) h hh
  have h2 := Subgroup.mem_centralizer_iff.1 hn.2 _ h1
  have e : (g : GLV V) * (n : GLV V) * (g : GLV V)⁻¹ * h =
      h * ((g : GLV V) * (n : GLV V) * (g : GLV V)⁻¹) := by
    calc (g : GLV V) * (n : GLV V) * (g : GLV V)⁻¹ * h
        = (g : GLV V) * ((n : GLV V) * ((g : GLV V)⁻¹ * h * (g : GLV V))) * (g : GLV V)⁻¹ := by
          group
      _ = (g : GLV V) * (((g : GLV V)⁻¹ * h * (g : GLV V)) * (n : GLV V)) * (g : GLV V)⁻¹ := by
          rw [h2]
      _ = h * ((g : GLV V) * (n : GLV V) * (g : GLV V)⁻¹) := by group
  exact e.symm

theorem pCore_three_eq {Γ H : Subgroup (GLV V)} (hHΓ : H ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hsimple : IsSimpleGroup ↥H)
    (hH3 : ¬ IsPGroup 3 ↥H)
    (hC3 : IsPGroup 3 ↥(Γ ⊓ Subgroup.centralizer (H : Set (GLV V)))) :
    CFSG.pCore 3 ↥Γ = (Γ ⊓ Subgroup.centralizer (H : Set (GLV V))).subgroupOf Γ := by
  set P : Subgroup ↥Γ := (Γ ⊓ Subgroup.centralizer (H : Set (GLV V))).subgroupOf Γ with hP
  have hPn : P.Normal := normal_centralizer_subgroupOf hN
  have hP3 : IsPGroup 3 ↥P :=
    hC3.of_surjective (Subgroup.subgroupOfEquivOfLe (inf_le_left : Γ ⊓
      Subgroup.centralizer (H : Set (GLV V)) ≤ Γ)).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.surjective
  apply le_antisymm
  · refine sSup_le fun K ⟨hKn, hK3⟩ => ?_
    set H' : Subgroup ↥Γ := H.subgroupOf Γ with hH'
    have hH'n : H'.Normal := ⟨fun n hn g => by
      rw [hH', Subgroup.mem_subgroupOf] at hn ⊢
      exact hN g g.2 n hn⟩
    have : IsSimpleGroup ↥H' :=
      (Subgroup.subgroupOfEquivOfLe hHΓ : ↥H' ≃* ↥H).isSimpleGroup
    have hinf : K ⊓ H' = ⊥ := by
      have hnorm : ((K ⊓ H').subgroupOf H').Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
        refine ⟨?_, ?_⟩
        · have := hKn.conj_mem (n : ↥Γ) hn.1 (g : ↥Γ)
          simpa using this
        · exact H'.mul_mem (H'.mul_mem g.2 hn.2) (H'.inv_mem g.2)⟩
      have := hnorm
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ H').subgroupOf H') with h0 | h1
      · rw [eq_bot_iff]
        intro x hx
        have hx' : (⟨x, hx.2⟩ : ↥H') ∈ (K ⊓ H').subgroupOf H' := hx
        rw [h0, Subgroup.mem_bot] at hx'
        have : x = 1 := congrArg Subtype.val hx'
        rw [this]
        exact Subgroup.one_mem _
      · exfalso
        apply hH3
        have hle : H' ≤ K := fun x hx => (show (⟨x, hx⟩ : ↥H') ∈ (K ⊓ H').subgroupOf H' by
          rw [h1]; exact Subgroup.mem_top _).1
        have h3H' : IsPGroup 3 ↥H' := hK3.of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
        exact h3H'.of_surjective (Subgroup.subgroupOfEquivOfLe hHΓ).toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hHΓ).surjective
    intro k hk
    rw [hP, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨k.2, fun h hh => ?_⟩
    set h' : ↥Γ := ⟨h, hHΓ hh⟩ with hh'
    have hh'mem : h' ∈ H' := hh
    have hcomm : k * h' * k⁻¹ * h'⁻¹ ∈ K ⊓ H' := by
      refine ⟨?_, ?_⟩
      · have := hKn.conj_mem k⁻¹ (K.inv_mem hk) h'
        have h5 := K.mul_mem hk (by simpa using this)
        simpa [mul_assoc] using h5
      · exact H'.mul_mem (hH'n.conj_mem h' hh'mem k) (H'.inv_mem hh'mem)
    rw [hinf, Subgroup.mem_bot] at hcomm
    have h6 : k * h' * k⁻¹ = h' := mul_inv_eq_one.1 hcomm
    have h7 : k * h' = h' * k := by
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6
    exact (congrArg Subtype.val h7).symm
  · exact le_sSup ⟨hPn, hP3⟩

end G117

end G11

end CFSG.Quasithin
