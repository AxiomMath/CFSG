module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Cent
public import CFSG.LocalAnalysis.UniquenessCase.UC6M11C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutEbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ABGLocalTools
open CFSG.LargeExtraspecial.S45Q (card_dvd_factorial_index)
open CFSG.Sporadic.Schreier.M11Sylow (p0 q0)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)


theorem c626gen_of_m11 (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.C626gen := by
  classical
  obtain ⟨φ0⟩ := id hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  have hcen : Subgroup.center m.Lbar = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv φ m11_center_eq_bot'
  have hE9 : Nat.card m.Ebar = 9 := by
    rw [m.card_Ebar h620, hr3]
    norm_num
  refine m.c626gen_of_Lbar_cent h619 h620 ?_ ?_
  · intro p hp hp2 hpr α hα
    obtain ⟨g, hg⟩ := M11K.allInner (MulAut.congr φ α)
    refine ⟨φ.symm g, ?_, ?_⟩
    · apply (MulAut.congr φ).injective
      rw [hg, congr_conj_uc6, MulEquiv.apply_symm_apply]
    · have h1 : MulAut.conj (φ.symm g) = α := by
        apply (MulAut.congr φ).injective
        rw [hg, congr_conj_uc6, MulEquiv.apply_symm_apply]
      rw [← hα, ← h1]
      exact (orderOf_injective _ (conj_injective_of_center_eq_bot hcen) (φ.symm g)).symm
  · intro K hK x hxK hxp hx2 hxr
    have hx3 : orderOf x ≠ 3 := hr3 ▸ hxr
    have hxo : orderOf (φ x) = orderOf x := MulEquiv.orderOf_eq φ x
    have hcases := M11K.prime_order_cases (φ x) hxp hxo hx3
    rw [hxo] at hcases
    have h511 : orderOf x = 5 ∨ orderOf x = 11 := by
      rcases hcases with h | h | h
      · exact absurd h hx2
      · exact Or.inl h
      · exact Or.inr h
    exact M11K.k626_of_isSpor_m11 hX hE9 K hK x hxK h511

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
