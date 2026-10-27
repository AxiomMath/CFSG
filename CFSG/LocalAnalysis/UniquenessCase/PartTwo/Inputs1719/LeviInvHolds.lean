module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1919Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.NineteenNineteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvOdd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo


theorem k_19_19_leviInv_holds : K_19_19_leviInv := by
  intro G _ _ M Dsub hq hlist hP hO d K J hKJ
  obtain ⟨d', L, hLfam, -, hblk⟩ := LeviFamily.exists_isLeviFamily_inf_blk
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.1 hq) hlist hP hO
  refine ⟨fun _ X hXD hXDM hXo k => ?_, fun k => ?_⟩
  · rcases hblk.2 with hd | ⟨s, hs6, -, hLs⟩
    · exact LeviFamily.LeviUniq.le_normalizer_of_odd_of_le_two hLfam hd hKJ hXDM hXo k
    · exact LeviFamily.LeviUniq.le_normalizer_of_odd_of_lieModel_psl_two hq hP hO
        (by omega) hLs hKJ hXD hXDM hXo k
  · obtain ⟨σ, hσ⟩ := LeviFamily.LeviUniq.exists_equiv_of_isDynkinFamilyIn_gen hLfam hKJ
    have key : ∀ A : Subgroup G, A = S17.oUpperTwo (L (σ k)) →
        3 ∣ Nat.card (Bar2 A) ∧ (IsQuasisimple (Bar2 A) ∨
          (Nonempty (Bar2 A ≃* Multiplicative (ZMod 3)) ∧ S19.IsLieTypeOver2 (BarInf Dsub))) := by
      rintro A rfl
      obtain ⟨h3, h⟩ := hblk.1 (σ k)
      exact ⟨h3, h.imp_left CFSG.Quasithin.A3.isQuasisimple_iff_open.2⟩
    exact key (J k) (by rw [hKJ.2.2.2.2 k, hσ k])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
