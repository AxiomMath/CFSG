module

public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.Permutation.TranspositionCentralizer

public section

namespace CFSG.StandardType

theorem injective_perm_action_of_typeA_equiv
    {A H : Type} [Group A] [Group H] {r : ℕ}
    (ρ : Equiv.Perm (Fin (r + 1)) →* H) (e : (CoxeterMatrix.A r).Group ≃* A)
    (ι : A →* H) (hι : Function.Injective ι)
    (hs : ∀ i, ρ (Equiv.swap i.castSucc i.succ) = ι (e ((CoxeterMatrix.A r).simple i))) :
    Function.Injective ρ := by
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm r
  have hcomp : ρ.comp e0.toMonoidHom = ι.comp e.toMonoidHom := by
    refine (CoxeterMatrix.A r).toCoxeterSystem.ext_simple fun i => ?_
    change ρ (e0 ((CoxeterMatrix.A r).simple i)) = ι (e ((CoxeterMatrix.A r).simple i))
    rw [he0 i]
    exact hs i
  have hρeq : ρ = (ι.comp e.toMonoidHom).comp e0.symm.toMonoidHom := by
    rw [← hcomp]
    ext σ
    simp [MulEquiv.apply_symm_apply]
  rw [hρeq]
  exact (hι.comp e.injective).comp e0.symm.injective

theorem rank_eq_of_ggLabelIso_typeA_right
    {lab : CFSG.Assembly.LargeEvenLabel} {r f : ℕ} (hr : 2 ≤ r)
    (hiso : GGLabelIso lab ⟨.A, r, f⟩) : lab.rank = r := by
  unfold GGLabelIso at hiso
  rcases hiso with he | h | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact congrArg CFSG.Assembly.LargeEvenLabel.rank he
  · have ht := h.2.1
    simp only [reduceCtorEq, or_self] at ht
  · have hb3 : r = 3 := congrArg CFSG.Assembly.LargeEvenLabel.rank hb
    have ha3 : lab.rank = 3 := congrArg CFSG.Assembly.LargeEvenLabel.rank ha
    omega
  · have ht := congrArg CFSG.Assembly.LargeEvenLabel.tag hb
    contradiction
  · have ht := congrArg CFSG.Assembly.LargeEvenLabel.tag hb
    contradiction
  · have ht := congrArg CFSG.Assembly.LargeEvenLabel.tag hb
    contradiction
  · have hr1 : r = 1 := congrArg CFSG.Assembly.LargeEvenLabel.rank hb
    omega
  · have ht := congrArg CFSG.Assembly.LargeEvenLabel.tag ha
    contradiction

theorem card_supported_eq_of_ggResSideDatum
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (hr : 1 ≤ r)
    (ρ : Equiv.Perm (Fin (r + 1)) →* MulAut Bs) (hρinj : Function.Injective ρ)
    (eX : (CoxeterMatrix.A r).Group ≃* ↥(ggAutomizer X Bs))
    (S : Finset (Fin (r + 1))) (hS : 2 ≤ S.card)
    (hAutoEqJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)).map ρ)
    (hSide : GGResSideDatum p Bs X J) : S.card = r := by
  classical
  let Fix : Subgroup (Equiv.Perm (Fin (r + 1))) :=
    fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)
  let eMap : Fix ≃* Fix.map ρ := Subgroup.equivMapOfInjective Fix ρ hρinj
  let eFixAuto : Fix ≃* ↥(ggAutomizer J Bs) :=
    eMap.trans (MulEquiv.subgroupCongr hAutoEqJ.symm)
  have hFixRange : Fix =
      (Equiv.Perm.ofSubtype (p := (· ∈ (S : Set (Fin (r + 1)))))).range :=
    CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin (r + 1))))
  let ePermRange : Equiv.Perm S ≃*
      (Equiv.Perm.ofSubtype (p := (· ∈ (S : Set (Fin (r + 1)))))).range :=
    MonoidHom.ofInjective (Equiv.Perm.ofSubtype_injective
      (p := (· ∈ (S : Set (Fin (r + 1))))))
  let ePermFix : Equiv.Perm S ≃* Fix :=
    ePermRange.trans (MulEquiv.subgroupCongr hFixRange.symm)
  let ePermPerm : Equiv.Perm S ≃* Equiv.Perm (Fin S.card) := S.equivFin.permCongrHom
  let eJperm : ↥(ggAutomizer J Bs) ≃* Equiv.Perm (Fin S.card) :=
    eFixAuto.symm.trans (ePermFix.symm.trans ePermPerm)
  obtain ⟨Λ, iΛ, dΛ, b, M, C, MJ, V', iV', dV', ι', φ', h', α',
    hM, hC, hMJ, hsub, hlin', hrefl', hpair', ⟨fX, hfX⟩, hclos', ⟨fJ, hfJ⟩,
    hclosJ, hconj⟩ := hSide
  have hrankΛ : Fintype.card Λ = r := by
    have h := ggWeylTypeData_rank_eq_of_mulEquiv hM (ggHLT_weyl_A hr) (fX.trans eX.symm)
    simpa using h
  have hcardΛ : Fintype.card {j : Λ // j ≠ b} = Fintype.card Λ - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i = b), Fintype.card_subtype_eq]
  obtain ⟨e0J, -⟩ := ggCoxeterA_mulEquivPerm (S.card - 1)
  let eFin : Equiv.Perm (Fin S.card) ≃* Equiv.Perm (Fin (S.card - 1 + 1)) :=
    Equiv.permCongrHom (finCongr (show S.card = S.card - 1 + 1 by omega))
  let eJgroup : MJ.Group ≃* (CoxeterMatrix.A (S.card - 1)).Group :=
    (fJ.trans eJperm).trans (eFin.trans e0J.symm)
  have hrankJ := ggWeylTypeData_rank_eq_of_mulEquiv hMJ (ggHLT_weyl_A (by omega)) eJgroup
  have hcardJ : Fintype.card {j : Λ // j ≠ b} = S.card - 1 := by
    simpa using hrankJ
  omega

end CFSG.StandardType

end
