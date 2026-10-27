module

public import CFSG.Quasithin.H13.A7NatInputs
public import CFSG.Quasithin.H13.VolIAltCoverSeven

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup
open scoped IsMulCommutative

theorem asI16AltSevenCover_holds : AsI16AltSevenCover := by
  intro G _ _ L V _ hV2 hLV hcomm hnat
  classical
  set H := autOn L V with hH
  set Z : Subgroup ↥V := (centralizer (L : Set G)).subgroupOf V with hZ
  have hZH : Z ≤ fixV H := by
    intro z hz y hy
    obtain ⟨n, hn, rfl⟩ := hy
    rw [SetLike.mem_coe, mem_subgroupOf] at hn
    have hnz : (n : G) * z * (n : G)⁻¹ = z := by
      have := mem_centralizer_iff.1 (mem_subgroupOf.1 hz) n hn
      rw [this, mul_inv_cancel_right]
    exact Subtype.ext hnz
  have hcommV : commV H = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    have hv' : v ∈ ⁅V, L⁆ := hcomm.symm ▸ hv
    set C : Subgroup G := (commV H).map V.subtype with hC
    suffices hVC : ⁅V, L⁆ ≤ C by
      obtain ⟨w, hw, hwv⟩ := hVC hv'
      have : w = ⟨v, hv⟩ := Subtype.ext hwv
      rw [← this]
      exact hw
    rw [commutator_le]
    intro a ha l hl
    have hlN : l ∈ normalizer (V : Set G) := hLV hl
    have hmem : conjAct V ⟨l, hlN⟩ ∈ H :=
      mem_map_of_mem _ (show (⟨l, hlN⟩ : normalizer (V : Set G)) ∈
        L.subgroupOf (normalizer (V : Set G)) from hl)
    refine ⟨(conjAct V ⟨l, hlN⟩) (⟨a, ha⟩⁻¹ : ↥V) * (⟨a, ha⟩⁻¹ : ↥V)⁻¹,
      subset_closure ⟨_, hmem, _, rfl⟩, ?_⟩
    show l * a⁻¹ * l⁻¹ * a⁻¹⁻¹ = a * l * a⁻¹ * l⁻¹
    have hcom : (l * a⁻¹ * l⁻¹) * a = a * (l * a⁻¹ * l⁻¹) := by
      have h1 : l * a⁻¹ * l⁻¹ ∈ V := (mem_normalizer_iff.1 hlN _).1 (V.inv_mem ha)
      have := IsMulCommutative.is_comm.comm (⟨l * a⁻¹ * l⁻¹, h1⟩ : ↥V) ⟨a, ha⟩
      exact congrArg Subtype.val this
    rw [inv_inv, hcom]
    group
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hV2 w w.2)
  have h := VolI.altNaturalCoverSeven_holds ↥V hW2 H Z hZH hcommV hnat
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : ↥V) ∈ Z := mem_subgroupOf.2 hx.2
  rw [h, mem_bot] at hxZ
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val hxZ)

end CFSG.Quasithin.H13.A7
