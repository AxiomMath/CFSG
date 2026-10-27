module

public import CFSG.Quasithin.H13.L32NThm1443
public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Core
public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Img

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.Quasithin.H13.Q8SqE9
open scoped MatrixGroups

theorem q8SqE9Decomp_holds : Q8SqE9Decomp := by
  intro G _ _ H hQ8 _hE hcard hcm
  obtain ⟨hQ32, A', B', ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := hQ8
  have hsup : A'.map (pCoreOf 2 H).subtype ⊔ B'.map (pCoreOf 2 H).subtype = pCoreOf 2 H := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm : A'.map (pCoreOf 2 H).subtype ≤
      Subgroup.centralizer (B'.map (pCoreOf 2 H).subtype : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb)
  have hcfg : Cfg (A'.map (pCoreOf 2 H).subtype) (B'.map (pCoreOf 2 H).subtype) :=
    ⟨hcomm,
      ⟨(A'.equivMapOfInjective _ (pCoreOf 2 H).subtype_injective).symm.trans eA⟩,
      ⟨(B'.equivMapOfInjective _ (pCoreOf 2 H).subtype_injective).symm.trans eB⟩,
      by rw [hsup]; exact hQ32⟩
  have hQH : pCoreOf 2 H ≤ H := Subgroup.map_subtype_le _
  have hQnorm : ∀ x ∈ H, ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ ∈ pCoreOf 2 H := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hx) q).mp hq
  have hKcard : Nat.card (oTwoUpper H) =
      9 * Nat.card ↥(oTwoUpper H ⊓ pCoreOf 2 H) := by
    have h := card_eq_card_image_mul H (oTwoUpper H) (oTwoUpper_le H) (CFSG.Open.pCore 2 ↥H)
    have h9 : Nat.card ↥(((oTwoUpper H).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))) = 9 := hcard
    rw [h9] at h
    exact h
  have hC : ∀ x ∈ H, (∀ q ∈ pCoreOf 2 H, x * q = q * x) → x ∈ pCoreOf 2 H := by
    intro x hx hxq
    rw [← hcm]
    refine ⟨hx, ?_, fun u hu => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro z
      have hz : ∀ z ∈ centerOf (pCoreOf 2 H), x * z * x⁻¹ = z := fun z hh => by
        rw [mul_inv_eq_iff_eq_mul]
        exact hxq z hh.1
      constructor
      · intro hh
        rw [hz z hh]
        exact hh
      · intro hh
        have hw := hxq _ hh.1
        have h1 : z = x * z * x⁻¹ := by
          have h2 : x⁻¹ * (x * z * x⁻¹) * x = x * z * x⁻¹ := by
            calc x⁻¹ * (x * z * x⁻¹) * x = x⁻¹ * ((x * z * x⁻¹) * x) := by group
              _ = x⁻¹ * (x * (x * z * x⁻¹)) := by rw [hw]
              _ = x * z * x⁻¹ := by group
          calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
            _ = x * z * x⁻¹ := h2
        rw [h1]
        exact hh
    · have h1 : x * u * x⁻¹ = u := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hxq u hu
      rw [h1, mul_inv_cancel]
      exact one_mem _
  have hcenter : centerOf (pCoreOf 2 H) =
      A'.map (pCoreOf 2 H).subtype ⊓ B'.map (pCoreOf 2 H).subtype := by
    ext x
    constructor
    · rintro ⟨hxQ, hxc⟩
      have hxQ' : x ∈ A'.map (pCoreOf 2 H).subtype ⊔ B'.map (pCoreOf 2 H).subtype := by
        rw [hsup]; exact hxQ
      refine (hcfg.mem_inf_iff x).mpr ((hcfg.center_iff hxQ').mp fun q hq => ?_)
      rw [hsup] at hq
      exact (Subgroup.mem_centralizer_iff.mp hxc q hq).symm
    · intro hx
      have hxQ : x ∈ A'.map (pCoreOf 2 H).subtype ⊔ B'.map (pCoreOf 2 H).subtype :=
        Subgroup.mem_sup_left hx.1
      refine ⟨by rw [← hsup]; exact hxQ, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      rw [← hsup] at hq
      exact ((hcfg.center_iff hxQ).mpr ((hcfg.mem_inf_iff x).mp hx) q hq).symm
  obtain ⟨hle, K₁, K₂, h1, h2, h3, h4, h5, h6⟩ :=
    hcfg.core hsup hQH hQnorm (oTwoUpper_le H) (fun x hx ho => mem_oTwoUpper_of_odd hx ho)
      hKcard hC
  exact ⟨hle, K₁, K₂, h1, h2.trans hcenter.symm, h3, h4, h5, h6⟩

end CFSG.Quasithin.H13
