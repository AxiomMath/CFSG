module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsClose81

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec8Outer (hc : Ctx M Q Z B) (n : ℕ) (t r g : G) : Prop where
  hs : Sec8Hyp hc n t
  hr : Sec7A hc t r
  hna : ¬ Conc81a hc t
  hg : g ∈ M
  hxt : ⁅g * t * g⁻¹, t⁆ ∈ Q
  hvan : ∀ v ∈ Sec8V1 M Q Z B t r, ⁅g * t * g⁻¹, v⁆ ∈ Z
  hout : ∃ w ∈ Sec8W1 M Q Z B t r, ⁅g * t * g⁻¹, w⁆ ∉ Sec8V1 M Q Z B t r

theorem sec8Outer_of_close82 {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (h : Close82Hyp hc n t r) :
    ∃ g : G, Sec8Outer hc n t r g := by
  obtain ⟨hs, hr, hna, -, ⟨x, hx, hxt, w, hw, hxw⟩, hvan⟩ := h
  have htM : t ∈ M := hc.LB_le_M hs.toSec5.mem
  obtain ⟨g, hg, hq'⟩ := sec8_conjMod_decomp hc htM hx
  have hx₀M : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hxe : x = (g * t * g⁻¹) * ((g * t * g⁻¹)⁻¹ * x) := by group
  have hx₀t : ⁅g * t * g⁻¹, t⁆ ∈ Q := by
    have h1 := hxt
    rw [hxe] at h1
    exact (sec8_comm_mul_Q_mem_iff hc hx₀M htM hq').mp h1
  have hZV₁ : Z ≤ Sec8V1 M Q Z B t r := sec39_Z_le_Vt.trans (le_inf le_sup_right le_sup_right)
  refine ⟨g, hs, hr, hna, hg, hx₀t, hvan _ (sec8_conjMod_conj htM hg) hx₀t, w, hw, fun h' => hxw ?_⟩
  rw [hxe]
  exact (comm_mul_Q_mem_iff hc hZV₁ hx₀M hq' hw.1).mpr h'

end CFSG.RankThree.GF2n.Stroth80
