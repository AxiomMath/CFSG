module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.H13.VolIAltCover

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.Quasithin Subgroup
open scoped IsMulCommutative

theorem as_I_1_6_one_holds : AS_I_1_6_one := by
  intro G _ _ L W hLW hW hcomm ⟨hc, hnat⟩
  classical
  set H := autOn L W with hH
  set Z : Subgroup ↥W := (centralizer (L : Set G)).subgroupOf W with hZ
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
    have hv' : v ∈ ⁅W, L⁆ := hcomm ▸ hv
    set C : Subgroup G := (commV H).map W.subtype with hC
    suffices hWC : ⁅W, L⁆ ≤ C by
      obtain ⟨w, hw, hwv⟩ := hWC hv'
      have : w = ⟨v, hv⟩ := Subtype.ext hwv
      rw [← this]
      exact hw
    rw [commutator_le]
    intro a ha l hl
    have hlN : l ∈ normalizer (W : Set G) := hLW hl
    have hmem : conjAct W ⟨l, hlN⟩ ∈ H :=
      mem_map_of_mem _ (show (⟨l, hlN⟩ : normalizer (W : Set G)) ∈
        L.subgroupOf (normalizer (W : Set G)) from hl)
    refine ⟨(conjAct W ⟨l, hlN⟩) (⟨a, ha⟩⁻¹ : ↥W) * (⟨a, ha⟩⁻¹ : ↥W)⁻¹,
      subset_closure ⟨_, hmem, _, rfl⟩, ?_⟩
    show l * a⁻¹ * l⁻¹ * a⁻¹⁻¹ = a * l * a⁻¹ * l⁻¹
    have hcom : (l * a⁻¹ * l⁻¹) * a = a * (l * a⁻¹ * l⁻¹) := by
      have h1 : l * a⁻¹ * l⁻¹ ∈ W := (mem_normalizer_iff.1 hlN _).1 (W.inv_mem ha)
      have := IsMulCommutative.is_comm.comm (⟨l * a⁻¹ * l⁻¹, h1⟩ : ↥W) ⟨a, ha⟩
      exact congrArg Subtype.val this
    rw [inv_inv, hcom]
    group
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (hW.2 w w.2)
  have h := H13.VolI.altNaturalCoverFive_holds ↥W hW2 H Z hZH hcommV hnat
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : ↥W) ∈ Z := mem_subgroupOf.2 hx.2
  rw [h, mem_bot] at hxZ
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val hxZ)

end CFSG.Quasithin.ASInputs
