module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Cent
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutL2
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.PSL2Table CFSG.GH74.GLS.IVK.L2Borel
open scoped MatrixGroups
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC6.Mz614 (sup_zpowers_eq_top_of_lieModel_three)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem c626gen_of_lieModel_three (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3)
    (hL : LieModel m.Lbar .PSL 2 m.r 2) : m.C626gen := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hEs := m.isSylowOf_Ebar_of_lieModel h620 hL
  have hcen : Subgroup.center m.Lbar = ⊥ := by
    obtain ⟨F, _, _, e, -, -⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' m.hr m.d.odd hL
    exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv (CFSG.GH74.GLS.IVK.toPSL e)
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  have hEab := (UC22.uc22p22q_psl2_sylow_elem m.hr m.d.odd hL hEs).1
  refine m.c626gen_of_Lbar_cent h619 h620 ?_ ?_
  · intro p hp hp2 hpr α hα
    obtain ⟨s, hs⟩ := CFSG.ComponentClassification.AutL2Facts.oddOuterInner_lieModel_sq m.hr m.Lbar hL α
      (by rw [hα]; exact hp.odd_of_ne_two hp2)
    refine ⟨s, hs, ?_⟩
    rw [← hα, hs]
    exact (orderOf_injective _ (conj_injective_of_center_eq_bot hcen) s).symm
  · intro K hK x hxK hxp hx2 hxr
    have hEbne : m.Ebar ≠ ⊥ := by
      intro h
      have := m.card_Ebar h620
      rw [h, Subgroup.card_bot] at this
      have h1 : 1 < m.r ^ 2 := Nat.one_lt_pow (by norm_num) m.hr.one_lt
      omega
    obtain ⟨e0, he01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hEbne
    have hEK : m.Ebar ≤ K := fun e' he' =>
      hK e0 e0.2 (fun h => he01 (Subtype.ext h)) e' (by
        have := hEab.1.is_comm.comm ⟨e', he'⟩ e0
        exact congrArg Subtype.val this)
    have := sup_zpowers_eq_top_of_lieModel_three hr3 hL m.Ebar hEs hxp hx2 hxr
    rw [eq_top_iff, ← this]
    exact sup_le hEK ((Subgroup.zpowers_le).2 hxK)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
