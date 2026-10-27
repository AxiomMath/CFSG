module

public import CFSG.Milestones.ASVolI.B610.Concl
public import CFSG.Milestones.ASVolI.B2

public section

namespace CFSG.Quasithin.B610T.Fin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem burnsideB610_Jj_zero (H : Subgroup G) :
    CFSG.ASVolI.ChB.Jj H 0 = thompsonJ H := by
  unfold CFSG.ASVolI.ChB.Jj
  rw [if_pos (Nat.zero_le _), CFSG.higherElemThompson_zero,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]

theorem burnsideB610_baumOf_eq (H : Subgroup G) :
    CFSG.ASVolI.ChB.baumOf H = baum H := by
  unfold CFSG.ASVolI.ChB.baumOf baum
  rw [burnsideB610_Jj_zero]

theorem burnsideB610_concl {H T M V L X₀ : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hLH : L ≤ H) (hLX : L ≤ X₀)
    (hcomm : ⁅V, X₀⁆ = ⁅V, L⁆)
    (hnorm : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)),
      g ∈ Subgroup.normalizer (X₀ : Set G) →
      convI hV ⟨g, hg⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
        Set (MulAut (IntMod V hV))))
    (hR1 : omegaOneCenterOf (thompsonJ T) =
      (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G)))
    (hR2 : baum T ≤ Subgroup.normalizer (X₀ : Set G))
    (hR4 : V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ≤
      ((⁅V, X₀⁆ : Subgroup G) ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ⊓ Subgroup.centralizer (X₀ : Set G)))
    (hLres : L ≤ twoResidual L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))
    (hsyl : IsSylowTwoOf (autI hV (baum T) ⊓ autI hV L) (autI hV L)) :
    (∀ s ∈ baum T, ∀ hs : s ∈ Subgroup.normalizer (V : Set G),
        convI hV ⟨s, hs⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
          Set (MulAut (IntMod V hV)))) ∧
      IsSylowTwoOf (baum T) (⨆ l ∈ L, (baum T).map (MulAut.conj l).toMonoidHom) ∧
      (twoResidual L = L →
        omegaOneCenterOf (thompsonJ T) =
          (⁅V, L⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
            (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (L : Set G))) := by
  have hT := hMP.isSylow
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun h => hJ ((hJT.trans hT.1).trans h)
  have h1 : ∀ s ∈ baum T, ∀ hs : s ∈ Subgroup.normalizer (V : Set G),
      convI hV ⟨s, hs⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
        Set (MulAut (IntMod V hV))) :=
    fun s hs hsN => hnorm s hsN (hR2 hs)
  have hSN : autI hV (baum T) ≤
      Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))) := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    exact h1 g hg g.2
  have hE : omegaOneCenterOf (thompsonJ T) ≤ (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
      (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual L : Set G)) :=
    hR1.le.trans (sup_le_sup_left
      (inf_le_inf_left _ (Subgroup.centralizer_le (F6.twoResidual_mono hLH))) _)
  refine ⟨h1, burnsideB610_isSylowTwoOf_join hV hMP hred hHV hLH hLres hE hSN hsyl,
    fun hLL => ?_⟩
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hCE : V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ≤ omegaOneCenterOf (thompsonJ T) :=
    inf_centralizer_thompsonJ_le hV hVT
  have hLK : L ≤ twoResidual H := hLL ▸ F6.twoResidual_mono hLH
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hred.2.1
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  apply le_antisymm
  · refine hR1.le.trans (sup_le ?_ ?_)
    · refine hR4.trans (sup_le ?_ ?_)
      · rw [hcomm]
        exact le_sup_left
      · exact (le_inf (inf_le_left.trans hCE)
          (inf_le_right.trans (Subgroup.centralizer_le hLX))).trans le_sup_right
    · exact (inf_le_inf_left _ (Subgroup.centralizer_le hLK)).trans le_sup_right
  · exact sup_le ((inf_le_inf_right _ hWV).trans hCE) inf_le_left

end CFSG.Quasithin.B610T.Fin
