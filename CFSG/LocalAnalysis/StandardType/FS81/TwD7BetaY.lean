module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7RootInverter
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameHolds
import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open E7Frame

theorem exists_Y_twD7_gen_of_attached {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) {J' : Subgroup G}
    (ψ : ↥L7 ≃* ↥J') (hJC : J' ≤ centralizer ({b₀ * B.b 1} : Set G))
    (hJgen : J' ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G))
    (hMJ : ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J')
    (hAd : Adapted B.twD7Beta (b₀ * B.b 1) J' E)
    (hNJ : (normalizer (zpowers (b₀ * B.b 1) : Set G) ⊓ normalizer (E : Set G)) ⊓
      normalizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
        centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ≤ normalizer (J' : Set G))
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1) :
    ∃ Y : Subgroup G, IsEm 8 Y ∧ E ≤ Y ∧ centralizer ({B.b 1} : Set G) ⊓ K ≤ Y ∧
      Y ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G) ∧ Y ≤ J' ⊔ K := by
  obtain ⟨-, i, hi, hiE, hiβ, -⟩ := exists_root_inverter_of_std_twD7 hstd B hB hrec ψ hz hψz hJC hMJ
  have hEJ : E ≤ zpowers (b₀ * B.b 1) ⊔ J' := by
    rw [← hAd.1]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = 0
    · subst hk
      rw [hAd.2.1]
      exact (le_sup_left : zpowers (b₀ * B.b 1) ≤ _) (mem_zpowers _)
    · exact (le_sup_right : J' ≤ _) (hAd.2.2 k hk)
  have : IsSimpleGroup ↥L7 :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 (ZMod 2))
  exact exists_Y_twD7_of_inverter e7NatFrame_holds e7NatHigh_holds e7NatCent_holds e7NatPsi_holds
    e7NatTau_holds e7NatA5_holds e7NatWeyl_holds hstd hB hrec ψ.symm.isSimpleGroup ψ hJC hJgen hMJ
    hEJ hz hψz hNJ hi hiβ hiE

end CFSG.StandardType.FrameRoute.FS81
