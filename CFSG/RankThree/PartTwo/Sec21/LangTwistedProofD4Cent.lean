module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLang
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate2121
public import Certificates.Certificate2122
public import Certificates.Certificate2123
public import Certificates.Certificate2173
public import Certificates.Certificate2178
public import Certificates.Certificate2179
public import Certificates.Certificate2183
public import Certificates.Certificate2214
public import Certificates.Certificate2215
public import Certificates.Certificate2217
public import Certificates.Certificate7233Base

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv

open scoped CFSG.ConvolutionPoints


section Torus

@[expose] def d4Fold : Fin 4 → Fin 2 :=
  ![0, 0, 1, 0]

@[expose] def d4Unfold : Fin 2 → Fin 4 :=
  ![0, 2]

theorem d4Fold_perm_symm (l : Fin TwistTag.D4.tag.rank) :
    d4Fold (TwistTag.D4.perm.symm l) = d4Fold l := by
  have h : ∀ l : Fin 4, d4Fold ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 3).symm l) =
      d4Fold l := by decide
  exact h l

theorem eq_unfold_of_perm_invariant {α : Type*} {a : Fin TwistTag.D4.tag.rank → α}
    (ha : (fun i => a (TwistTag.D4.perm.symm i)) = a) (l : Fin TwistTag.D4.tag.rank) :
    a (d4Unfold (d4Fold l)) = a l := by
  have h : ∀ i, a (TwistTag.D4.perm.symm i) = a i := fun i => congrFun ha i
  have hcases : ∀ l : Fin 4, d4Unfold (d4Fold l) = l ∨
      d4Unfold (d4Fold l) = (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 3).symm l ∨
      d4Unfold (d4Fold l) = (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 3).symm
        ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 3).symm l) := by decide
  rcases hcases l with e | e | e
  · rw [e]
  · rw [e]
    exact h l
  · rw [e]
    exact (h _).trans (h l)

variable {k : Type} [Field k]

theorem rootDiagUnit_commute_diagramMap_iff (a : Fin TwistTag.D4.tag.rank → kˣ) :
    rootDiagUnit TwistTag.D4.tag a * diagramMap TwistTag.D4 k =
        diagramMap TwistTag.D4 k * rootDiagUnit TwistTag.D4.tag a ↔
      (fun i => a (TwistTag.D4.perm.symm i)) = a := by
  rw [diagramMap_mul_rootDiagUnit, mul_left_inj, rootDiagUnit_injective.eq_iff, eq_comm]

variable (R : Type) [CommRing R]

@[expose] def d4FixedTorusParam (s : Fin 2 → Rˣ) (j : Fin TwistTag.D4.tag.rank) : Rˣ :=
  ∏ i, s (d4Fold i) ^ TwistTag.D4.tag.cartan.adjugate i j

@[expose] def d4FixedTorusWord (s : Fin 2 → Rˣ) : List (Letter TwistTag.D4.tag × R) :=
  ((List.finRange TwistTag.D4.tag.rank).map fun j =>
    torusWord TwistTag.D4.tag R j (d4FixedTorusParam R s j)).flatten

variable {R}

theorem mapWord_d4FixedTorusWord {S : Type} [CommRing S] (f : R →+* S) (s : Fin 2 → Rˣ) :
    mapWord f (d4FixedTorusWord R s) =
      d4FixedTorusWord S fun i => Units.map f.toMonoidHom (s i) := by
  simp only [d4FixedTorusWord, mapWord_flatten, List.map_map, Function.comp_def,
    mapWord_torusWord]
  congr 2
  funext j
  congr 1
  simp [d4FixedTorusParam, map_prod, map_zpow]

theorem wordUnit_d4FixedTorusWord (s : Fin 2 → kˣ) :
    wordUnit TwistTag.D4.tag k (d4FixedTorusWord k s) =
      rootDiagUnit TwistTag.D4.tag fun l => s (d4Fold l) ^ (4 : ℤ) := by
  rw [d4FixedTorusWord, wordUnit_flatten, List.map_map]
  have h : (wordUnit TwistTag.D4.tag k ∘ fun j =>
      torusWord TwistTag.D4.tag k j (d4FixedTorusParam k s j)) =
      fun j => torusElt TwistTag.D4.tag k j (d4FixedTorusParam k s j) := by
    funext j
    exact wordUnit_torusWord j _
  rw [h, list_prod_torusElt_eq_rootDiagUnit]
  have h4 := cartanChar_prod_zpow_eq_smul (τ := TwistTag.D4.tag) (K := k)
    (Matrix.adjugate_mul TwistTag.D4.tag.cartan) fun i => s (d4Fold i)
  rw [show TwistTag.D4.tag.cartan.det = 4 from det_cartan_D4] at h4
  exact congrArg (rootDiagUnit TwistTag.D4.tag) h4

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem wordUnit_d4FixedTorusCurve (z : TorusAffine k 2 0 →ₐ[k] k) :
    wordUnit TwistTag.D4.tag k (mapWord (z : TorusAffine k 2 0 →+* k)
        (d4FixedTorusWord _ (torusUnit k 2 0))) =
      rootDiagUnit TwistTag.D4.tag fun l =>
        Units.map (z : TorusAffine k 2 0 →+* k).toMonoidHom (torusUnit k 2 0 (d4Fold l)) ^
          (4 : ℤ) := by
  rw [mapWord_d4FixedTorusWord, wordUnit_d4FixedTorusWord]

variable (k) in
@[expose] def d4FixedTorusCurve : WordCurve TwistTag.D4.tag k :=
  WordCurve.ofWord (TorusAffine k 2 0) (d4FixedTorusWord _ (torusUnit k 2 0))
    (torusAffinePoint (fun _ => 1) Fin.elim0) (by
      rw [wordUnit_d4FixedTorusCurve]
      simp only [units_map_torusUnit, one_zpow]
      exact rootDiagUnit_one)

theorem values_d4FixedTorusCurve_eq_range :
    (d4FixedTorusCurve k).values = Set.range fun s : Fin 2 → kˣ =>
      rootDiagUnit TwistTag.D4.tag fun l => s (d4Fold l) ^ (4 : ℤ) := by
  rw [d4FixedTorusCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun i => Units.map (z : TorusAffine k 2 0 →+* k).toMonoidHom (torusUnit k 2 0 i),
      (wordUnit_d4FixedTorusCurve z).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨torusAffinePoint t Fin.elim0, (wordUnit_d4FixedTorusCurve _).trans ?_⟩
    simp only [units_map_torusUnit]

theorem values_d4FixedTorusCurve :
    (d4FixedTorusCurve k).values = ((torusGroup TwistTag.D4.tag k ⊓
      graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k) :
        Subgroup (ModGL TwistTag.D4.tag k)) : Set (ModGL TwistTag.D4.tag k)) := by
  rw [values_d4FixedTorusCurve_eq_range]
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hmem : rootDiagUnit TwistTag.D4.tag (fun l => s (d4Fold l) ^ (4 : ℤ)) ∈
        torusGroup TwistTag.D4.tag k := by
      rw [← wordUnit_d4FixedTorusWord, d4FixedTorusWord, wordUnit_flatten, List.map_map]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      rw [Function.comp_apply, wordUnit_torusWord]
      exact Subgroup.subset_closure ⟨(j, _), rfl⟩
    refine Subgroup.mem_inf.2 ⟨hmem, Subgroup.mem_inf.2
      ⟨(exceptional_Lang_adjoint_diagonal_lift TwistTag.D4.tag k
        (fun l => s (d4Fold l) ^ (4 : ℤ))).1, ?_⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    beta_reduce
    rw [rootDiagUnit_commute_diagramMap_iff]
    funext i
    exact congrArg (fun j => s j ^ (4 : ℤ)) (d4Fold_perm_symm i)
  · intro hg
    rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_inf] at hg
    obtain ⟨hgT, -, hgc⟩ := hg
    have hT : torusGroup TwistTag.D4.tag k ≤ (rootDiagUnitHom TwistTag.D4.tag k).range := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, u⟩, rfl⟩
      exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩
    obtain ⟨a, rfl⟩ := hT hgT
    change rootDiagUnit TwistTag.D4.tag a ∈ Subgroup.centralizer _ at hgc
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    have ha := (rootDiagUnit_commute_diagramMap_iff a).1 hgc
    have hroot : ∀ i : Fin 2, ∃ u : kˣ, u ^ (4 : ℤ) = a (d4Unfold i) := by
      intro i
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a (d4Unfold i) : k) (n := 4)
        (by norm_num)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num)] at hz
        exact (a (d4Unfold i)).ne_zero hz.symm
      exact ⟨Units.mk0 z hz0, Units.ext (by
        rw [zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩
    choose u hu using hroot
    refine ⟨u, ?_⟩
    change rootDiagUnit TwistTag.D4.tag _ = rootDiagUnit TwistTag.D4.tag a
    congr 1
    funext l
    rw [hu]
    exact eq_unfold_of_perm_invariant ha l

end Torus

theorem graphCentralizer_inv {τ : Tag} {k : Type} [Field k] (A : ModGL τ k) :
    graphCentralizer τ k A⁻¹ = graphCentralizer τ k A := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · calc g * A = A * (A⁻¹ * g) * A := by group
      _ = A * (g * A⁻¹) * A := by rw [h]
      _ = A * g := by group
  · calc g * A⁻¹ = A⁻¹ * (A * g) * A⁻¹ := by group
      _ = A⁻¹ * (g * A) * A⁻¹ := by rw [h]
      _ = A⁻¹ * g := by group

theorem isPointIrreducible_d4DiagramCentralizer (k : Type) [Field k] [IsAlgClosed k] :
    IsPointIrreducible k (transportPoints (modGLPoint TwistTag.D4.tag k)
      (graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k))) := by
  have hZ := twistedFixedGroup_id_eq (k := k) TwistTag.D4
  let H : Option ({w // w ∈ relWeylTwist TwistTag.D4} × Fin TwistTag.D4.foldedTag.rank) →
      Subgroup (ModGL TwistTag.D4.tag k) := fun o => match o with
    | none => torusGroup TwistTag.D4.tag k ⊓
        graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)
    | some i => rootSpan TwistTag.D4.tag k ((fun j => i.1.1 • (Pi.single j 1 :
        Fin TwistTag.D4.tag.rank → ℤ)) '' ↑(TwistTag.D4.orbit i.2)) ⊓
          twistedFixedGroup TwistTag.D4 k (RingHom.id k)
  let F : Option ({w // w ∈ relWeylTwist TwistTag.D4} × Fin TwistTag.D4.foldedTag.rank) →
      WordCurve TwistTag.D4.tag k := fun o => match o with
    | none => d4FixedTorusCurve k
    | some i => orbitConjCurve k i.1.1 i.2
  have hFH : ∀ o, (F o).values = (H o : Set (ModGL TwistTag.D4.tag k)) := by
    rintro (_ | ⟨⟨w, hw⟩, a⟩)
    · exact values_d4FixedTorusCurve
    · exact values_orbitConjCurve_eq hw a
  have hset := (fixed_root_generated_normal_subgroup TwistTag.D4 k (RingEquiv.refl k)).2.1
  have hgen := (fixed_positive_orbit_collection TwistTag.D4 k (RingEquiv.refl k)).2
  rw [RingEquiv.toRingHom_refl'] at hset hgen
  have hsup : graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k) = ⨆ o, H o := by
    refine le_antisymm (fun g hg => ?_) (iSup_le fun o => ?_)
    · rw [← hZ, ← SetLike.mem_coe, hset] at hg
      obtain ⟨h, hh, c, hc, rfl⟩ := Set.mem_mul.1 hg
      refine mul_mem (Subgroup.mem_iSup_of_mem none ?_) ?_
      · obtain ⟨hhT, hhZ⟩ := Subgroup.mem_inf.1 hh
        refine Subgroup.mem_inf.2 ⟨hhT, ?_⟩
        rw [← hZ]
        exact hhZ
      · rw [SetLike.mem_coe, hgen] at hc
        refine (Subgroup.closure_le _).2 ?_ hc
        rintro _ ⟨w, hw, a, c', rfl⟩
        refine Subgroup.mem_iSup_of_mem (some (⟨w, hw⟩, a)) ?_
        obtain ⟨e, he⟩ := (fixed_root_orbit_parametrization TwistTag.D4 k (RingHom.id k)).1 a w hw
        rw [← he c']
        exact (e _).2
    · rcases o with _ | ⟨⟨w, hw⟩, a⟩
      · exact inf_le_right
      · rw [← hZ]
        exact inf_le_right
  rw [hsup]
  exact isPointIrreducible_iSup_wordCurves F H hFH

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

namespace CFSG.RankThree.PartTwo.Sec8

open LangTwistedProof

theorem d4DiagramCentIrred_holds :
    D4DiagramCentIrred := by
  intro L _ _ _
  rw [graphCentralizer_inv]
  exact isPointIrreducible_d4DiagramCentralizer L

end CFSG.RankThree.PartTwo.Sec8
