module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Gen
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Frame
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableB
open CFSG.StandardType.PhiTwoRootGen

private theorem phiTwoComp_eq_of_excRefl_eq_F4
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type} [Field K]
    {g0 : ModGL .F4 (AlgebraicClosure K)} {β β' : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β)
    (hβ' : IsRoot .F4 β')
    (h : ExcSplitRootGen.excRefl (p := p) β = ExcSplitRootGen.excRefl (p := p) β') :
    PhiTwoRootGen.phiTwoComp g0 β = PhiTwoRootGen.phiTwoComp g0 β' := by
  have hτ4 : Tag.F4 = .E6 ∨ Tag.F4 = .E7 ∨ Tag.F4 = .E8 ∨ Tag.F4 = .F4 :=
    Or.inr (Or.inr (Or.inr rfl))
  have hiff : ∀ t : Fin Tag.F4.rank → ZMod p,
      (∑ j, (β j : ZMod p) * t j = 0) ↔ (∑ j, (β' j : ZMod p) * t j = 0) := by
    intro t
    rw [← ExcSplitRootGen.excRefl_eq_self_iff hp2 hβ,
      ← ExcSplitRootGen.excRefl_eq_self_iff hp2 hβ', h]
  rcases ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero hτ4 hp2 hβ hβ'
      (fun t => (hiff t).1) with h' | h'
  · rw [h']
  · rw [h', PhiTwoRootGen.phiTwoComp_neg]

theorem ggTorusModelAt_phiTwo_F4
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E) :
    GGTorusModelAt p E := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hτ4 : Tag.F4 = .E6 ∨ Tag.F4 = .E7 ∨ Tag.F4 = .E8 ∨ Tag.F4 = .F4 :=
    Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hζo, hι₀, hrange, hbase⟩ :=
    exists_langFrame_F4_of_sc hp5 hpq hE hSC
  have hcent : ∀ v : WeylGroup .F4, v * CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg =
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg * v := f4Neg_comm
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) hp2
  have hrat : ∀ X : Subgroup (ModGL .F4 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .F4 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .F4 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X _ hXC hXF x hx =>
      mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr (hXC hx) (hXF x hx)
  obtain ⟨T, hTinj, hTrange, hTcoe⟩ := exists_phiTwoTorus hdet hζ hι₀ hbase
  have hneg : ∀ β : Fin Tag.F4.rank → ℤ, IsRoot .F4 β →
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg • β = -β :=
    fun β _ => CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul β
  have hroot : ∀ α β : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → IsRoot .F4 β →
      (∀ t : Fin Tag.F4.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
        ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α :=
    fun α β hα hβ h => ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero hτ4 hp2 hα hβ h
  haveI : Nonempty {α : Fin Tag.F4.rank → ℤ // IsRoot Tag.F4 α} :=
    ⟨⟨Pi.single ⟨0, Tag.F4.rank_pos⟩ 1, isRoot_single Tag.F4 _⟩⟩
  have hres : GGTorusModelAt p T.range := by
    refine ggTorusModelAt_of_reflFamily hTinj (fun β : {α : Fin Tag.F4.rank → ℤ // IsRoot .F4 α} =>
        (exists_phiTwoWeyl hrat hcent hg0C hg0 β.2).choose)
      (fun β => ExcSplitRootGen.excRefl β.1) (fun β => PhiTwoRootGen.phiTwoComp g0 β.1)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i t
      exact conj_phiTwoTorus hζ hTcoe (v := rootReflection i.1)
        (n := (exists_phiTwoWeyl hrat hcent hg0C hg0 i.2).choose)
        (exists_phiTwoWeyl hrat hcent hg0C hg0 i.2).choose_spec.2 t
    · intro i t
      exact ExcSplitRootGen.excRefl_excRefl i.2 t
    · intro i
      exact ExcSplitRootGen.card_fix_excRefl hp2 i.2
    · intro i
      exact (exists_phiTwoWeyl hrat hcent hg0C hg0 i.2).choose_spec.1
    · intro i
      exact isComponentOf_phiTwoComp hK hFr hrat hg0C hg0 hζo hζ hTcoe i.2 (hneg i.1 i.2)
        (fun t => ExcSplitRootGen.excRefl_eq_self_iff hp2 i.2 t)
        (fun γ hγ h => hroot i.1 γ i.2 hγ h)
    · intro i
      exact dvd_card_phiTwoComp hpq hFr hrat hg0C hg0 i.2 (hneg i.1 i.2)
    · intro i j hij
      exact phiTwoComp_eq_of_excRefl_eq_F4 hp2 i.2 j.2 hij
    · intro j
      exact iSup_phiTwoComp_ne_F4 hK hp2 hFr hcent hneg hg0C hg0 j
  rwa [hTrange, hrange] at hres

theorem ggTorusRootGenAvoidKG_F4Plus
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K) :
    GGTorusRootGenAvoidKG p 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  haveI : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  haveI : Finite (TableBF4.RecipeGroup K) :=
    Finite.of_equiv (adjointGroup .F4 K) (TableBF4.recipeEquiv K).symm.toEquiv
  have hIp : GGOutdiagPrime p (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
    fun _ hφ _ => TableBF4.idImage_subset_inn K hφ
  have hcp : GGCenterPrime p (TableBF4.RecipeGroup K) :=
    ExcSplitL.ggCenterPrime_recipe_F4 hp hp2
  refine ggTorusRootGenAvoidKG_of_scTorusModel_centerPrime hp
    (TableBF4.center_recipeGroup_eq_bot K) hIp hcp ?_
  intro E hE _ _ hsc
  let e := TableBF4.recipeEquiv K
  have hEmap : IsElemAbelian p (E.map e.toMonoidHom) := hE.map e.toMonoidHom
  have hsc' : ∀ x : adjointGroup .F4 K,
      (∀ b ∈ E.map e.toMonoidHom, x * b = b * x) → x ^ p = 1 → x ∈ E.map e.toMonoidHom :=
    CFSG.GroupTheory.selfCentralizing_map_mulEquiv e hsc
  have hcen : ∀ x ∈ Subgroup.centralizer
      ((E.map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)),
      x ^ p = 1 → x ∈ E.map e.toMonoidHom :=
    fun x hx hxp => hsc' x (fun b hb => (Subgroup.mem_centralizer_iff.mp hx b hb).symm) hxp
  have hmod : GGTorusModelAt p (E.map e.toMonoidHom) :=
    ggTorusModelAt_phiTwo_F4 hp5 hpq hK hEmap hcen
  have hback : GGTorusModelAt p ((E.map e.toMonoidHom).map e.symm.toMonoidHom) :=
    GGTorusModelAt.map hmod e.symm
  have hmap : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id (TableBF4.RecipeGroup K) := MonoidHom.ext fun x => by simp
    rw [hcomp, Subgroup.map_id]
  rwa [hmap] at hback

end CFSG.StandardType

end
