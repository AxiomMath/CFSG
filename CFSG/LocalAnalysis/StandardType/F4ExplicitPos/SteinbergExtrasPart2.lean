module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankOneTorusPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SteinbergExtrasPart1

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.SteinbergExtras
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.TitsSimplicity CFSG.StandardType.F4ExplicitPos.UnipotentNo117
open scoped commutatorElement
variable {τ : Tag} {K : Type} [Field K]

section Actual
variable [CharP K 2]

theorem f4_steinbergExtras_without117 :
    SteinbergExtras (f4Datum K) (CFSG.LieType.Chevalley.weylElement Tag.F4 K)
      (torus (τ := Tag.F4) K) where
  ne_bot γ hγ :=
    rootGroup_ne_botN (rootOperatorFamily Tag.F4)
      ((mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).1 hγ)
  two_smul_le γ hγ h2 :=
    absurd (eq_one_of_isRoot_nsmul_without117
      ((mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).1 h2)) (by norm_num)
  commutator_mem γ hγ δ hδ hlin x hx y hy :=
    f4_commutator_memN hγ hδ hlin hx hy
  prodInjective_pos L hnd hmem hsort :=
    prodInjectiveN (rootOperatorFamily Tag.F4) htHom L hnd
      (fun γ hγ => ⟨(mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).1 ((hmem γ).1 hγ).1,
        ((hmem γ).1 hγ).2.1⟩) hsort
  prodInjective_neg L hnd hmem hsort :=
    prodInjectiveN (rootOperatorFamily Tag.F4) (-htHom) L hnd
      (fun γ hγ => ⟨(mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).1 ((hmem γ).1 hγ).1, by
        rw [AddMonoidHom.neg_apply, htHom_apply]
        exact neg_pos.2 ((hmem γ).1 hγ).2.1⟩)
      (hsort.imp fun h => by
        rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, htHom_apply, htHom_apply]
        exact neg_le_neg h)
  posPart_inf_negPart :=
    eq_bot_iff.2 ((inf_le_inf
      (iSup₂_le fun γ hγ => rootGroup_le_unipN (rootOperatorFamily Tag.F4) htHom hγ.2)
      (iSup₂_le fun γ hγ => rootGroup_le_unipN (rootOperatorFamily Tag.F4) (-htHom) (by
        rw [AddMonoidHom.neg_apply, htHom_apply]
        exact neg_pos.2 hγ.2))).trans (unip_inf_unip_negN htHom).le)
  rankOne_bruhat i g hg :=
    CFSG.StandardType.F4ExplicitPos.RankOneTorus.rankOne_bruhat_f4Datum (K := K) i hg
  eq_one_of_mem_normalizer i u hu hn :=
    CFSG.StandardType.F4ExplicitPos.RankOneTorus.eq_one_of_mem_normalizer_f4Datum (K := K) i hu hn
  torus_commute i j h hh h' hh' :=
    CFSG.StandardType.F4ExplicitPos.RankOneTorus.torus_commute_f4Datum (K := K) hh hh'
  torus_iSupIndep :=
    CFSG.StandardType.F4ExplicitPos.RankOneTorus.torus_iSupIndep_f4Datum (K := K)
  torus_inf_posPart :=
    eq_bot_iff.2 ((inf_le_inf_left _
      (iSup₂_le fun γ hγ => rootGroup_le_unipN (rootOperatorFamily Tag.F4) htHom hγ.2)).trans
      (iSup_torus_inf_unipN htHom).le)

theorem f4_bruhatExtras_without117 :
    BruhatExtras (f4Datum K) (torus (τ := Tag.F4) K) where
  borel_inf_negUnipotent := eq_bot_iff.2 ((inf_le_inf
    (sup_le (iSup_le fun i => (torus_le_diagN (τ := Tag.F4) i).trans (diag_le_triN htHom))
      ((iSup₂_le fun γ hγ =>
        rootGroup_le_unipN (rootOperatorFamily Tag.F4) htHom hγ.2).trans (unip_le_triN htHom)))
    (iSup₂_le fun γ hγ => rootGroup_le_unipN (rootOperatorFamily Tag.F4) (-htHom) (by
      rw [AddMonoidHom.neg_apply, htHom_apply]
      exact neg_pos.2 hγ.2))).trans (tri_inf_unip_negN htHom).le)

theorem f4_rootGroupCommutators_without117 :
    RootGroupCommutators (f4Datum K) := by
  refine RootGroupCommutators.of_divisible_eq_empty (D := f4Datum K) rfl fun γ hγ x hx y hy => ?_
  have hγ' : IsRoot Tag.F4 γ := (mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).1 hγ
  obtain ⟨a, rfl⟩ := (mem_rootGroup_iffN (rootOperatorFamily Tag.F4) hγ' x).1 hx
  obtain ⟨b, rfl⟩ := (mem_rootGroup_iffN (rootOperatorFamily Tag.F4) hγ' y).1 hy
  rw [Commute, SemiconjBy, ← xPar_add_without117 (rootOperatorFamily Tag.F4),
    ← xPar_add_without117 (rootOperatorFamily Tag.F4), add_comm]

end Actual

end CFSG.StandardType.F4ExplicitPos.SteinbergExtras

end

end
