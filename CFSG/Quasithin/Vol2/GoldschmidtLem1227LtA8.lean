module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtSLFam
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtUI

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lem1227Lt

section A8

variable {G : Type} [Group G] [Finite G] {T K Y H M₀ : Subgroup G}

theorem false_of_alt8 (h : LtHyp G T K Y) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (hfam : B69.E22Fam ↥(E2.star M₀ H K))
    (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* ↥(alternatingGroup (Fin 8)))
    (hν : Function.Surjective ν) : False := by
  obtain ⟨e8⟩ := nonempty_mulEquiv_alternating_eight_sl_four
  have := isSimpleGroup_sl_four_zmod_two
  have hnonab := sl_four_zmod_two_nonabelian
  have hν' : Function.Surjective (e8.toMonoidHom.comp ν) := e8.surjective.comp hν
  obtain ⟨φ, hφs, hk, hS⟩ := exists_phi_sylow h hnonab (SL.isSylowTwoOf_unitriangular
    (by norm_num : 1 ≤ 4)) (e8.toMonoidHom.comp ν) hν'
  obtain ⟨m, hm, hd, Θ, hΘ⟩ := sl_data h (le_refl 4) (by norm_num) φ hk hS
  obtain ⟨d, hd13, hdN⟩ := hd rfl
  refine false_of_sl_model h hKH hHK hmin hker hq hlist hfam φ hφs hk hm Θ hΘ ?_
  intro t α hα hαB
  have hαN : (stabilizer (flagSpace 4 (ZMod 2) d)).map α.toMonoidHom =
      stabilizer (flagSpace 4 (ZMod 2) d) := by
    rw [← hdN]
    exact map_normalizer_eq α hαB
  exact SL.inner_of_stabilizer (by norm_num) (by omega) (by omega) (by omega) α hαN

end A8

end Lem1227Lt

end CFSG.Quasithin.H13
