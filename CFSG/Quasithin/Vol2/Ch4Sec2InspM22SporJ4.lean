module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Layer0J4
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Out
public import CFSG.Sporadic.Schreier.J4SNoComp

public section

namespace CFSG.Quasithin.H13.Ch4

theorem isComponent_subgroupOf_of_eq {L : Type} [Group L] {H K D : Subgroup L} (h : H = K)
    (hDH : D ≤ H) (hsn : (D.subgroupOf H).IsSubnormal) (hq : CFSG.IsQuasisimple ↥D) :
    CFSG.IsComponent (D.subgroupOf K) := by
  subst h
  exact ⟨CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDH) hq, hsn⟩

theorem j4_no_component_fixSub
    (L : Type) [Group L]
    (e : L ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) (β : MulAut L)
    (h2 : β ^ 2 = 1) (h1 : β ≠ 1) (D : Subgroup L) (hD : ∀ x ∈ D, β x = x)
    (hsn : (D.subgroupOf (CFSG.Sporadic.Schreier.fixSub β)).IsSubnormal)
    (hq : CFSG.IsQuasisimple ↥D) : False := by
  obtain ⟨x, hx⟩ := j4OutTrivial_holds L ⟨e⟩ β
  have hsq : ∀ y, β (β y) = y := by
    intro y
    simpa [pow_two] using congrArg (fun φ : MulAut L => φ y) h2
  have hcomm : ∀ g : L, g * x ^ 2 = x ^ 2 * g := by
    intro g
    have h := hsq g
    simp only [hx] at h
    calc g * x ^ 2 = x * (x * g * x⁻¹) * x⁻¹ * x ^ 2 := by rw [h]
      _ = x * x * g := by group
      _ = x ^ 2 * g := by rw [pow_two]
  have hcen : Subgroup.center L = ⊥ :=
    CFSG.EvenSporadicStandard.J4Std.center_eq_bot_of_isSporadic (Y := L) ⟨e⟩
  have hx2 : x ^ 2 = 1 := by
    have hmem : x ^ 2 ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr hcomm
    rw [hcen, Subgroup.mem_bot] at hmem
    exact hmem
  have hx1 : x ≠ 1 := by
    intro h
    apply h1
    ext y
    simp [hx, h]
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hfix : CFSG.Sporadic.Schreier.fixSub β = Subgroup.centralizer ({x} : Set L) := by
    ext y
    rw [CFSG.Sporadic.Schreier.mem_fixSub, Subgroup.mem_centralizer_singleton_iff, hx,
      mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hDH : D ≤ CFSG.Sporadic.Schreier.fixSub β := fun y hy =>
    CFSG.Sporadic.Schreier.mem_fixSub.mpr (hD y hy)
  have hB : CFSG.IsComponent (D.subgroupOf (Subgroup.centralizer ({x} : Set L))) :=
    isComponent_subgroupOf_of_eq hfix hDH hsn hq
  exact CFSG.ComponentClassification.RestrictedStd.Spor.j4NoComponentsInput L ⟨e⟩ x hord _ hB

end CFSG.Quasithin.H13.Ch4
