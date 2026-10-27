module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Gen
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourDefs
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenExcRefl
public import CFSG.GroupTheory.SelfCentralizingMap

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableB
open CFSG.StandardType.PhiTwoRootGen

theorem ggTorusModelAt_phiTwo_F4Three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq3 : 3 ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) (h4 : 3 ^ 4 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E) :
    GGTorusModelAt 3 E := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hτ4 : Tag.F4 = .E6 ∨ Tag.F4 = .E7 ∨ Tag.F4 = .E8 ∨ Tag.F4 = .F4 :=
    Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hζo, hι₀, hrange, hbase⟩ :=
    exists_langFrame_F4_three hq3 hE h4 hSC
  have hcent : ∀ v : WeylGroup .F4, v * CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg =
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg * v := f4Neg_comm
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod 3) :=
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
      (∀ t : Fin Tag.F4.rank → ZMod 3, ∑ j, (α j : ZMod 3) * t j = 0 →
        ∑ j, (β j : ZMod 3) * t j = 0) → β = α ∨ β = -α :=
    fun α β hα hβ h => ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero hτ4 hp2 hα hβ h
  haveI : Nonempty {α : Fin Tag.F4.rank → ℤ // IsRoot Tag.F4 α} :=
    ⟨⟨Pi.single ⟨0, Tag.F4.rank_pos⟩ 1, isRoot_single Tag.F4 _⟩⟩
  have hres : GGTorusModelAt 3 T.range := by
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
      exact dvd_card_phiTwoComp hq3 hFr hrat hg0C hg0 i.2 (hneg i.1 i.2)
    · intro i j hij
      exact phiTwoComp_eq_of_excRefl_eq hp2 hτ4 i.2 j.2 hij
    · intro j
      exact iSup_phiTwoComp_ne_F4 hK hp2 hFr hcent hneg hg0C hg0 j
  rwa [hTrange, hrange] at hres

theorem ggF4ThreePlusKGAvoid_holds :
    GGF4ThreePlusKGAvoid := by
  intro K _ _ _ hK hq3
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  haveI : Finite (TableBF4.RecipeGroup K) :=
    Finite.of_equiv (adjointGroup .F4 K) (TableBF4.recipeEquiv K).symm.toEquiv
  have hIp : GGOutdiagPrime 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
    fun _ hφ _ => TableBF4.idImage_subset_inn K hφ
  have hcp : GGCenterPrime 3 (TableBF4.RecipeGroup K) :=
    ExcSplitL.ggCenterPrime_recipe_F4 hp hp2
  refine ggTorusRootGenAvoidKG_of_scTorusModel_centerPrime hp
    (TableBF4.center_recipeGroup_eq_bot K) hIp hcp ?_
  intro E hE h4 _ hsc
  let e := TableBF4.recipeEquiv K
  have hEmap : IsElemAbelian 3 (E.map e.toMonoidHom) := hE.map e.toMonoidHom
  have hsc' : ∀ x : adjointGroup .F4 K,
      (∀ b ∈ E.map e.toMonoidHom, x * b = b * x) → x ^ 3 = 1 → x ∈ E.map e.toMonoidHom :=
    CFSG.GroupTheory.selfCentralizing_map_mulEquiv e hsc
  have hcen : ∀ x ∈ Subgroup.centralizer
      ((E.map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)),
      x ^ 3 = 1 → x ∈ E.map e.toMonoidHom :=
    fun x hx hxp => hsc' x (fun b hb => (Subgroup.mem_centralizer_iff.mp hx b hb).symm) hxp
  have h4' : 3 ^ 4 ≤ Nat.card (E.map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]; exact h4
  have hmod : GGTorusModelAt 3 (E.map e.toMonoidHom) :=
    ggTorusModelAt_phiTwo_F4Three hq3 hK hEmap h4' hcen
  have hback : GGTorusModelAt 3 ((E.map e.toMonoidHom).map e.symm.toMonoidHom) :=
    GGTorusModelAt.map hmod e.symm
  have hmap : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id (TableBF4.RecipeGroup K) := MonoidHom.ext fun x => by simp
    rw [hcomp, Subgroup.map_id]
  rwa [hmap] at hback

end CFSG.StandardType

end
