module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpFixRoot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.RankThree.PartOne.KCSpFull

variable {k n : ℕ} {F : Type} [Field F] [Finite F]

theorem mem_range_conj_of_fix_conj_iff_commute_statedSp (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hk : 1 ≤ k) {t₀ : ↥(StatedSp k F)} (ht : IsSymplecticTransvectionIn k t₀)
    (α : MulAut ↥(StatedSp k F)) (g : ↥(StatedSp k F)) (hα : α t₀ = t₀)
    (hfix : ∀ s : ↥(StatedSp k F),
      α (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ ↔ g * (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ * g) :
    α ∈ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range := by
  obtain ⟨a, c, ha, hc, rfl⟩ := borel86_spn_eq_spTransvection ht
  have hg : g * spTransvection a c = spTransvection a c * g := by
    simpa using (hfix 1).mp (by simpa using hα)
  refine borel86_spr_mem_range_conj hF hn hk ha α fun s => ?_
  rcases eq_or_ne s 0 with rfl | hs
  · rw [borel86_spn_spTransvection_param_zero, map_one]
  · obtain ⟨h, hh, hgs⟩ := borel86_spn_exists_conj_commute hF ha hc hg hs
    rw [← hh]
    exact (hfix h).mpr (by rw [hh]; exact hgs)

end CFSG.LocalAnalysis.WeakClosure81

end
