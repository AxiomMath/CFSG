module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6D4Roots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldTorus
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent

public section

namespace CFSG.StandardType.SmallExc.E6Node

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.StandardType.TableBExc.E6Three CFSG.SeitzReduction
open CFSG.LieType.Chevalley.C2E6Std (setD)


local instance : NeZero Tag.E6.rank := ⟨by decide⟩

section Certs


section Weyl

variable (L : Type) [Field L]

@[expose] noncomputable def mD4 : ModGL .E6 L :=
  weylElt .E6 L 1 1 * weylElt .E6 L 2 1

@[expose] noncomputable def gD4 : ModGL .E6 L :=
  (d4Word.map fun i => weylElt .E6 L i 1).prod

theorem gD4_mul_mD4 :
    gD4 L * mD4 L = ((d4Word ++ [1, 2]).map fun i => weylElt .E6 L i 1).prod := by
  rw [gD4, mD4, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

end Weyl

section R

variable
  {L : Type} [Field L]

@[expose] noncomputable def nD4 (P : SL2 L) : ModGL .E6 L :=
  rootSL2 .E6 L (bE6 0) P * rootSL2 .E6 L (bE6 1) P

theorem nD4_mem (P : SL2 L) : nD4 P ∈ adjointGroup .E6 L :=
  mul_mem (rootSL2_mem_adjointGroup (isRoot_bE6 0) P) (rootSL2_mem_adjointGroup (isRoot_bE6 1) P)

section S


theorem map_conj_gD4_rootSpan {l : Lˣ} (hl : orderOf l = 3) :
    (rootSpan .E6 L (rootCharKernel (chiD4 l))).map (MulAut.conj (gD4 L)).toMonoidHom =
      subsystemGroup .E6 L setD := by
  rw [show subsystemGroup .E6 L setD = rootSpan .E6 L (parabolicRoots .E6 setD) from
    subsystemGroup_eq_rootSpan _]
  simp only [rootSpan, Subgroup.map_iSup]
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) (iSup₂_le fun δ hδ => ?_)
  · obtain ⟨hr, h3⟩ := (mem_rootCharKernel_chiD4 hl).1 hγ
    exact (map_conj_prod_weylElt_rootSubgroup L d4Word hr).le.trans
      (le_iSup₂_of_le _ (smul_d4Word_of_mem hr h3).1 le_rfl)
  · obtain ⟨γ, hr, h3, rfl⟩ := exists_smul_d4Word_eq hδ
    exact le_iSup₂_of_le γ ((mem_rootCharKernel_chiD4 hl).2 ⟨hr, h3⟩)
      (map_conj_prod_weylElt_rootSubgroup L d4Word hr).ge


theorem entrywise_nD4 [CharP L 2] {x : L} (hx : x ^ 2 + x + 1 = 0) (σ : L →+* L)
    (hσ : σ x = x ^ 2) :
    Units.map (entrywiseHom σ) (nD4 (TableBExcTwoFusion.langP hx)) =
      nD4 (TableBExcTwoFusion.langP hx) * mD4 L := by
  have h0 : rootSL2 .E6 L (bE6 0) (nSL 1) = weylElt .E6 L 1 1 :=
    (rootSL2_single_apply .E6 1 _).trans (E6SignedGraph.simpleRootSL2_nSL 1 1)
  have h1 : rootSL2 .E6 L (bE6 1) (nSL 1) = weylElt .E6 L 2 1 :=
    (rootSL2_single_apply .E6 2 _).trans (E6SignedGraph.simpleRootSL2_nSL 2 1)
  have hc : Commute (rootSL2 .E6 L (bE6 0) (nSL 1)) (rootSL2 .E6 L (bE6 1)
      (TableBExcTwoFusion.langP hx)) := rootSL2_bE6_commute (by decide) _ _
  rw [nD4, map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field,
    TableBExcTwoFusion.map_langP hx σ hσ, map_mul, map_mul, mD4, ← h0, ← h1]
  calc _ = rootSL2 .E6 L (bE6 0) (TableBExcTwoFusion.langP hx) *
        (rootSL2 .E6 L (bE6 0) (nSL 1) * rootSL2 .E6 L (bE6 1) (TableBExcTwoFusion.langP hx)) *
          rootSL2 .E6 L (bE6 1) (nSL 1) := by simp only [mul_assoc]
    _ = _ := by rw [hc.eq]; simp only [mul_assoc]

theorem twistHom_conj_gD4 [CharP L 2] (σ : L →+* L) {l : Lˣ} (hl : orderOf l = 3)
    {x : ModGL .E6 L} (hx : x ∈ rootSpan .E6 L (rootCharKernel (chiD4 l))) :
    twistHom TwistTag.E6 L σ (gD4 L * x * (gD4 L)⁻¹) =
      gD4 L * mD4 L * Units.map (entrywiseHom σ) x * (gD4 L * mD4 L)⁻¹ := by
  have key : rootSpan .E6 L (rootCharKernel (chiD4 l)) ≤
      ((twistHom TwistTag.E6 L σ).comp (MulAut.conj (gD4 L)).toMonoidHom).eqLocus
        ((MulAut.conj (gD4 L * mD4 L)).toMonoidHom.comp (Units.map (entrywiseHom σ))) := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨hr, h3⟩ := (mem_rootCharKernel_chiD4 hl).1 hγ
    have e1 : gD4 L * pinnedX .E6 L γ c * (gD4 L)⁻¹ =
        pinnedX .E6 L ((coxeterSystem .E6).wordProd d4Word • γ) c :=
      list_prod_weylElt_conj_pinnedX_of_charTwo d4Word hr c
    have e2 : twistHom TwistTag.E6 L σ (pinnedX .E6 L ((coxeterSystem .E6).wordProd d4Word • γ) c) =
        pinnedX .E6 L (permLattice (τ := Tag.E6) TwistTag.E6.perm
          ((coxeterSystem .E6).wordProd d4Word • γ)) (σ c) :=
      E6GraphRadical.twistHom_pinnedX_of_two CharTwo.two_eq_zero σ (IsRoot.smul hr _) c
    have e3 : Units.map (entrywiseHom σ) (pinnedX .E6 L γ c) = pinnedX .E6 L γ (σ c) :=
      E6GraphLevi.units_map_entrywiseHom_pinnedX' σ γ c
    have e4 : gD4 L * mD4 L * pinnedX .E6 L γ (σ c) * (gD4 L * mD4 L)⁻¹ =
        pinnedX .E6 L ((coxeterSystem .E6).wordProd (d4Word ++ [1, 2]) • γ) (σ c) := by
      rw [gD4_mul_mD4]
      exact list_prod_weylElt_conj_pinnedX_of_charTwo _ hr _
    show twistHom TwistTag.E6 L σ (gD4 L * pinnedX .E6 L γ c * (gD4 L)⁻¹) =
      gD4 L * mD4 L * Units.map (entrywiseHom σ) (pinnedX .E6 L γ c) * (gD4 L * mD4 L)⁻¹
    rw [e1, e2, e3, e4, (smul_d4Word_of_mem hr h3).2]
  have h : ((twistHom TwistTag.E6 L σ).comp (MulAut.conj (gD4 L)).toMonoidHom) x =
      ((MulAut.conj (gD4 L * mD4 L)).toMonoidHom.comp (Units.map (entrywiseHom σ))) x := key hx
  exact h

theorem exists_baseChangeGL_eq_of_frob_fixed_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {y : ModGL .E6 (FiniteField.Extension K 2 2)}
    (hy : y ∈ adjointGroup .E6 (FiniteField.Extension K 2 2))
    (hFy : Units.map (entrywiseHom (TableBExcTwoFusion.frobHom K)) y = y) :
    ∃ c ∈ adjointGroup .E6 K, baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) c = y := by
  have hσσ : ∀ c, (FiniteField.Extension.frob K 2 2).toRingEquiv
      ((FiniteField.Extension.frob K 2 2).toRingEquiv c) = c :=
    TwistedE6Pilot.apply_apply_eq (f := 1) (σ := TableBExcTwoFusion.frobHom K)
      ((TableBExcTwoFusion.natCard_ext hK).trans (by norm_num)) fun c => by
        rw [TableBExcTwoFusion.frobHom_apply, TableBExcTwoFusion.frob_eq_sq hK, pow_one]
  have h1 : y ∈ entrywiseFixedGroup .E6 (FiniteField.Extension.frob K 2 2).toRingEquiv :=
    mem_entrywiseFixedGroup.2 ⟨hy, hFy⟩
  rw [E6Pilot.entrywiseFixedGroup_eq_fixedFieldImage_E6 _ hσσ, fixedFieldImage,
    map_adjointGroup_baseChangeGL_eq_of_range_eq _ (algebraMap K (FiniteField.Extension K 2 2))
      ?_] at h1
  · obtain ⟨c, hc, rfl⟩ := h1
    exact ⟨c, hc, rfl⟩
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (F4Pilot.frob_eq_self_iff (w : FiniteField.Extension K 2 2)).1 w.2
    · intro hz
      exact ⟨⟨z, (F4Pilot.frob_eq_self_iff z).2 hz⟩, rfl⟩

end S

end R

end Certs

end CFSG.StandardType.SmallExc.E6Node

end
