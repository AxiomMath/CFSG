module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflFamily
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidCenterPrime
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLarge
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot
public import CFSG.GroupTheory.SelfCentralizingMap

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableB
open CFSG.StandardType.PhiTwoRootGen

private theorem finite_fixed_le_map_adjointGroup_E7_E8
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (X : Subgroup (ModGL τ (AlgebraicClosure K))) (hX : Finite X)
    (hXC : X ≤ adjointGroup τ (AlgebraicClosure K))
    (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  haveI := hX
  rcases hτ with rfl | rfl
  · exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF
  · exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1
      (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
        (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)

private theorem phiTwoComp_eq_of_excRefl_eq
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    {g0 : ModGL τ (AlgebraicClosure K)} {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hβ' : IsRoot τ β')
    (h : ExcSplitRootGen.excRefl (p := p) β = ExcSplitRootGen.excRefl (p := p) β') :
    PhiTwoRootGen.phiTwoComp g0 β = PhiTwoRootGen.phiTwoComp g0 β' := by
  have hτ4 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  have hiff : ∀ t : Fin τ.rank → ZMod p,
      (∑ j, (β j : ZMod p) * t j = 0) ↔ (∑ j, (β' j : ZMod p) * t j = 0) := by
    intro t
    rw [← ExcSplitRootGen.excRefl_eq_self_iff hp2 hβ,
      ← ExcSplitRootGen.excRefl_eq_self_iff hp2 hβ', h]
  rcases ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero hτ4 hp2 hβ hβ'
      (fun t => (hiff t).1) with h' | h'
  · rw [h']
  · rw [h', PhiTwoRootGen.phiTwoComp_neg]

theorem ggTorusModelAt_phiTwo_of_sc
    {τ : Tag} (hGen : PhiTwoGenAt τ) (hτ : τ = .E7 ∨ τ = .E8)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K) {E : Subgroup (adjointGroup τ K)}
    (hE : IsElemAbelian p E) (hcard : p ^ (τ.rank - 1) ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) :
    GGTorusModelAt p E := by
  classical
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hτ4 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcent, hζo, hι₀, hrange, hbase⟩ :=
    exists_langFrame_of_sc_odd hτ hp2 K hpq E hE hcard hSC
  have hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (hτ.elim (fun h => Or.inr (Or.inl h))
      (fun h => Or.inr (Or.inr h))) hp2
  have hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X hX hXC hXF => finite_fixed_le_map_adjointGroup_E7_E8 hτ Fr hFr X hX hXC hXF
  obtain ⟨T, hTinj, hTrange, hTcoe⟩ := exists_phiTwoTorus hdet hζ hι₀ hbase
  have hw₀ := torusAct_eq_neg_of_langFrame hpq hdet hFr hg0 hζo hζ hbase
  have hp3 : 3 ≤ p := by have h2 : 2 ≤ p := Nat.Prime.two_le Fact.out; omega
  have hneg : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → w • β = -β :=
    fun β hβ => smul_eq_neg_of_torusAct_eq_neg hτ hp3 hw₀ hβ
  have hroot : ∀ α β : Fin τ.rank → ℤ, IsRoot τ α → IsRoot τ β →
      (∀ t : Fin τ.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
        ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α :=
    fun α β hα hβ h => ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero hτ4 hp2 hα hβ h
  haveI : Nonempty {α : Fin τ.rank → ℤ // IsRoot τ α} :=
    ⟨⟨Pi.single ⟨0, τ.rank_pos⟩ 1, isRoot_single τ _⟩⟩
  have hres : GGTorusModelAt p T.range := by
    refine ggTorusModelAt_of_reflFamily hTinj (fun β : {α : Fin τ.rank → ℤ // IsRoot τ α} =>
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
      exact phiTwoComp_eq_of_excRefl_eq hp2 hτ i.2 j.2 hij
    · intro j
      exact iSup_phiTwoComp_ne hGen hτ hK hFr hrat hcent hneg hg0C hg0
        (fun α hα t => ExcSplitRootGen.excRefl_eq_self_iff hp2 hα t)
        (fun α β hα hβ h => hroot α β hα hβ h) j
  rwa [hTrange, hrange] at hres

theorem ggTorusRootGenAvoidKG_excPlus_of_lss92
    {τ : Tag} (hGen : PhiTwoGenAt τ) {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hτ : τ = .E7 ∨ τ = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K) :
    GGTorusRootGenAvoidKG p (τ.rank - 1) (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (TableBExc.RecipeGroup τ K) := TableBExc.finite_recipeGroup τ K
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hfK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hIp : GGOutdiagPrime p (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
    rcases hτ with rfl | rfl
    · exact fun _ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ
    · exact fun _ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ
  have hcp : GGCenterPrime p (TableBExc.RecipeGroup τ K) := by
    rcases hτ with rfl | rfl
    · exact ExcSplitL.ggCenterPrime_recipe_E7 hf1 hfK hp hp2
    · exact ExcSplitL.ggCenterPrime_recipe_E8 (K := K) hp hp2
  refine ggTorusRootGenAvoidKG_of_scTorusModel_centerPrime hp
    (TableBExc.center_recipeGroup_eq_bot τ K) hIp hcp ?_
  intro E hE hr h3 hsc
  let e := TableBExc.recipeEquiv τ K
  have hEmap : IsElemAbelian p (E.map e.toMonoidHom) := hE.map e.toMonoidHom
  have hcard' : p ^ (τ.rank - 1) ≤ Nat.card (E.map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hr
  have hsc' : ∀ x : adjointGroup τ K,
      (∀ b ∈ E.map e.toMonoidHom, x * b = b * x) → x ^ p = 1 → x ∈ E.map e.toMonoidHom :=
    CFSG.GroupTheory.selfCentralizing_map_mulEquiv e hsc
  have hcen : ∀ x ∈ Subgroup.centralizer
      ((E.map e.toMonoidHom : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)),
      x ^ p = 1 → x ∈ E.map e.toMonoidHom :=
    fun x hx hxp => hsc' x (fun b hb => (Subgroup.mem_centralizer_iff.mp hx b hb).symm) hxp
  have hmod : GGTorusModelAt p (E.map e.toMonoidHom) :=
    ggTorusModelAt_phiTwo_of_sc hGen hτ hp2 hpq hK hEmap hcard' hcen
  have hback : GGTorusModelAt p ((E.map e.toMonoidHom).map e.symm.toMonoidHom) :=
    GGTorusModelAt.map hmod e.symm
  have hmap : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id (TableBExc.RecipeGroup τ K) := MonoidHom.ext fun x => by simp
    rw [hcomp, Subgroup.map_id]
  rwa [hmap] at hback

end CFSG.StandardType

end
