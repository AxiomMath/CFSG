module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base5
public import CFSG.Quasithin.Background.HTriPermute

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2.KGNat
open scoped IsMulCommutative

variable {G : Type} [Group G]


theorem conjAct_coe (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = (g : G) * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V _ v

theorem autOn_le_normZH {L V X : Subgroup G} [IsMulCommutative ↥V]
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    autOn X V ≤ normZH (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) := by
  rintro _ ⟨⟨x, hxN⟩, hxX, rfl⟩
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hXN ⟨hxX, hxN⟩
  have hxL' : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hxL
  refine ⟨fun z => ?_, fun h => ?_⟩
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change (z : G) ∈ _ ↔ ((conjAct V ⟨x, hxN⟩ z : ↥V) : G) ∈ _
    rw [conjAct_coe]
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro hz l hl
      have h1 := hz (x⁻¹ * l * x⁻¹⁻¹) ((Subgroup.mem_normalizer_iff.mp hxL' l).mp hl)
      calc l * (x * z * x⁻¹) = x * ((x⁻¹ * l * x⁻¹⁻¹) * z) * x⁻¹ := by group
        _ = x * (z * (x⁻¹ * l * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
        _ = x * z * x⁻¹ * l := by group
    · intro hz l hl
      have h1 := hz (x * l * x⁻¹) ((Subgroup.mem_normalizer_iff.mp hxL l).mp hl)
      calc l * (z : G) = x⁻¹ * ((x * l * x⁻¹) * (x * z * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * z * x⁻¹) * (x * l * x⁻¹)) * x := by rw [h1]
        _ = z * l := by group
  · constructor
    · rintro ⟨⟨l, hlN⟩, hlL, rfl⟩
      refine ⟨⟨x * l * x⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem hxN hlN)
        ((Subgroup.normalizer (V : Set G)).inv_mem hxN)⟩,
        (Subgroup.mem_normalizer_iff.mp hxL l).mp hlL, ?_⟩
      ext v
      simp only [MulAut.mul_apply, conjAct_coe]
      rw [← map_inv, conjAct_coe]
      simp only [Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    · rintro ⟨⟨l, hlN⟩, hlL, hl⟩
      refine ⟨⟨x⁻¹ * l * x⁻¹⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem ((Subgroup.normalizer (V : Set G)).inv_mem hxN)
          hlN) ((Subgroup.normalizer (V : Set G)).inv_mem
          ((Subgroup.normalizer (V : Set G)).inv_mem hxN))⟩,
        (Subgroup.mem_normalizer_iff.mp hxL' l).mp hlL, ?_⟩
      have h2 : h = (conjAct V ⟨x, hxN⟩)⁻¹ * conjAct V ⟨l, hlN⟩ * conjAct V ⟨x, hxN⟩ := by
        rw [hl]
        group
      rw [h2]
      ext v
      simp only [MulAut.mul_apply]
      rw [← map_inv]
      simp only [conjAct_coe, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group

theorem autOn_fix_cent {L V : Subgroup G} :
    ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z := by
  rintro _ ⟨⟨l, hlN⟩, hlL, rfl⟩ z hz
  apply Subtype.ext
  change ((conjAct V ⟨l, hlN⟩ z : ↥V) : G) = z
  rw [conjAct_coe]
  have h1 : l * (z : G) = (z : G) * l := (Subgroup.mem_centralizer_iff.mp hz) l hlL
  calc l * (z : G) * l⁻¹ = (z : G) * l * l⁻¹ := by rw [h1]
    _ = z := by group

theorem commV_autOn_eq_top {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, L⁆ = V) :
    commV (autOn L V) = ⊤ :=
  CFSG.Quasithin.AutOn.commV_autOn_eq_top hLV hcomm

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
