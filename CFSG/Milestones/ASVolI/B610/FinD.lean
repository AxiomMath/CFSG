module

public import CFSG.Milestones.ASVolI.B610.FinB
public import CFSG.Milestones.ASVolI.B610.FinC
public import CFSG.Milestones.ASVolI.B6

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.B610T CFSG.Quasithin.B610T.Fin CFSG.Open CFSG.QuasithinUnique

theorem burnsideB610_B_6_10_of_compFam (hcomp : CFSG.Quasithin.B610T.burnsideB610_CompFamTarget) :
    CFSG.ASVolI.B_6_10 := by
  intro G _ _ H T M V L n hMP _hFstar hred hL hnat hJ0
  rw [burnsideB610_Jj_zero] at hJ0 ⊢
  rw [burnsideB610_baumOf_eq]
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := fun h => hJ0 (by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h)
  have key : (∀ s ∈ baum T, ∀ hs : s ∈ Subgroup.normalizer (V : Set G),
        convI hV ⟨s, hs⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
          Set (MulAut (IntMod V hV)))) ∧
      IsSylowTwoOf (baum T) (⨆ l ∈ L, (baum T).map (MulAut.conj l).toMonoidHom) ∧
      (twoResidual L = L →
        omegaOneCenterOf (thompsonJ T) =
          (⁅V, L⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
            (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (L : Set G))) := by
    by_cases hn : 2 ≤ n
    · exact burnsideB610_case_ge_two hcomp hV hMP hred hL hJ hn hnat
    · have hn1 : n = 1 := by
        rcases hnat with ⟨h1, -⟩ | ⟨h1, -⟩
        · omega
        · exact h1
      subst hn1
      exact burnsideB610_case_one hV hMP hred hL hJ hnat
  obtain ⟨h1, h2, h3⟩ := key
  exact ⟨fun s hs hsN => h1 s hs hsN, h2, h3⟩

end CFSG.ASVolI
