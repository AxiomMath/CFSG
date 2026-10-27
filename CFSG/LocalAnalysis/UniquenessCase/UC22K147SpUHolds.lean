module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147UDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUSp4
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUU3
import CFSG.LocalAnalysis.UniquenessCase.UC22K147UToK147
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem k147SpU_sp4 [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) {n : ℕ}
    (h : 1 < n ∧ Odd n ∧ IsSp4 ↥(Ext.lgConj L) n ∧ ∃ g : G, ActsNontrivOnDiagramIn (Ext.lgConj L) g) :
    n + 1 < F05.mGV ρ := by
  obtain ⟨hn1, hodd, hsp, g, hg⟩ := h
  obtain ⟨hs, hnab⟩ := uc22p22a_sp4_simple _ n hsp
  haveI := hs
  have heq := Ext.lgConj_eq_of_isQuasisimple hL (uc22p22a_isQuasisimple_of_simple hnab)
  have hLn : L.Normal := heq ▸ uc22p22r_lgConj_normal L
  rw [heq] at hsp hg
  have hn3 : 3 ≤ n := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  exact sp4_lt_mGV ρ hρ hirr hLn hn3 hodd hsp hg

section Holds

set_option linter.unusedSectionVars false

theorem k147SpU_su3 [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) {n : ℕ}
    (h : IsSU3 ↥(Ext.lgConj L) n) : n + 1 < F05.mGV ρ := by
  have heq := Ext.lgConj_eq_of_isQuasisimple hL h.1
  have hLn : L.Normal := heq ▸ uc22p22r_lgConj_normal L
  rw [heq] at h
  exact su3_lt_mGV ρ hρ hirr hLn h

end Holds

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

theorem k147SpU_holds :
    K147SpU := by
  intro G _ _ V _ _ _ ρ _ _ hρ hirr L hL n _ hcase hm
  exfalso
  rcases hcase with h | h
  · have := K147SpU.k147SpU_sp4 ρ hρ hirr hL h
    omega
  · have := K147SpU.k147SpU_su3 ρ hρ hirr hL h
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
