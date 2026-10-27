module

public import CFSG.LocalAnalysis.UniquenessCase.UCK898b
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898A
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898B
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898C
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898E
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.ComponentClassification.Burgoyne.U

theorem u3Fix3Field_of_center (hCen : U3Center) : U3Fix3Field := by
  intro X _ _ hX α hα hni
  obtain ⟨K, _, h, e, M, φ, hφord, hrn, hcard, hbar, hfix⟩ :=
    u3_prime_descent hX (r := 7) (by norm_num) (by norm_num) (by norm_num) hα hni
  have h37 : (21 : ℕ) / 7 = 3 := by norm_num
  rw [h37] at hcard hbar
  obtain ⟨ζ, hζ0, hζ9, hφζ, hζN⟩ := exists_fixed_norm_one_order h hcard hbar (d := 9) (by norm_num)
  obtain ⟨e', f', g', he3, hf3, hef, hfn, hge, hgf, hfix'⟩ := toral_E9_data h hζ0 hζN hζ9
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : StatedProj (StatedSU 3 (2 ^ 21) K) ≃* (X ⧸ center X),
      ∀ y, Φ y = e.symm (uConjAut h (by norm_num) M y) :=
    ⟨(uConjAut h (by norm_num) M).trans e.symm, fun y => rfl⟩
  refine lift_E9_fixed (hCen X 21 hX) (e := Φ e') (f := Φ f') (g := Φ g') ?_ ?_ ?_ ?_ ?_ ?_
    (r := 7) (by norm_num) (by norm_num) (by norm_num) α hα ?_ ?_
  · rw [MulEquiv.orderOf_eq]; exact he3
  · rw [MulEquiv.orderOf_eq]; exact hf3
  · rw [← map_mul, ← map_mul, hef]
  · intro hmem
    apply hfn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← map_zpow] at hk
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Φ.injective hk⟩
  · rw [← map_mul, ← map_mul, hge]
  · rw [← map_mul, ← map_inv, ← map_mul, hgf]
  · rw [hΦ]
    exact hfix e' (hfix' φ hφζ).1
  · rw [hΦ]
    exact hfix f' (hfix' φ hφζ).2

theorem u3Fix3Field_holds (hG : CFSG.Open.GriessAllModelsStatement) : U3Fix3Field :=
  u3Fix3Field_of_center (u3Center_of_griess hG)

end CFSG.LocalAnalysis.UniquenessCase.UCK
