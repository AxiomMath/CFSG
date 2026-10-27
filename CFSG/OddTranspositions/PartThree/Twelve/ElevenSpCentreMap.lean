module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.OddTranspositions.PartThree.Twelve.FourSp
import CFSG.OddTranspositions.PartThree.Twelve.Six
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.ClassicalGroups.Symplectic.PointRadicalNormal
import CFSG.ClassicalGroups.Alternating.I4SpPlane
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpElt
import CFSG.RankThree.PartOne.S11d.OddAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ClassicalGroups.Alternating.I4SpLineElt

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.Open
open CFSG.ClassicalInvolution.Models.SymplecticPairs (fixing mem_fixing)
open CFSG.OddTranspositions.PartFour CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open CFSG.OddTranspositions.PartThree

variable {k : ℕ} {F : Type} [Field F]

theorem spTransvection_mem_fixing_singleton (y : Fin k ⊕ Fin k → F) (c : F) :
    spTransvection y c ∈ fixing {y} := by
  rintro v rfl
  change spEnd (spTransvection v c) v = v
  rw [spEnd_spTransvection, spForm_isAlt.self_eq_zero, mul_zero, zero_smul, add_zero]

theorem spTransvection_mem_fixing_singleton_iff {y a : Fin k ⊕ Fin k → F} {c : F} (hc : c ≠ 0) :
    spTransvection a c ∈ fixing {y} ↔ spForm k F a y = 0 := by
  have hya : spForm k F y a = 0 ↔ spForm k F a y = 0 := by
    rw [← spForm_isAlt.neg_eq a y, neg_eq_zero]
  rw [mem_fixing]
  refine ⟨fun h => ?_, fun h v hv => ?_⟩
  · have h1 : spEnd (spTransvection a c) y = y := h y (Set.mem_singleton y)
    rw [spEnd_spTransvection, add_eq_left, smul_eq_zero, mul_eq_zero] at h1
    rcases h1 with (h1 | h1) | rfl
    · exact absurd h1 hc
    · exact hya.mp h1
    · exact LinearMap.map_zero₂ _ y
  · rw [Set.mem_singleton_iff.mp hv]
    change spEnd (spTransvection a c) y = y
    rw [spEnd_spTransvection, hya.mpr h, mul_zero, zero_smul, add_zero]

private noncomputable def vecPerp (y : Fin k ⊕ Fin k → F) : Submodule F (Fin k ⊕ Fin k → F) :=
  LinearMap.ker ((spForm k F).flip y)

private theorem mem_vecPerp {y a : Fin k ⊕ Fin k → F} :
    a ∈ vecPerp y ↔ spForm k F a y = 0 := Iff.rfl

private theorem self_mem_vecPerp (y : Fin k ⊕ Fin k → F) : y ∈ vecPerp y := by
  rw [mem_vecPerp, spForm_isAlt.self_eq_zero]

private def selfVecPerp (y : Fin k ⊕ Fin k → F) : vecPerp y := ⟨y, self_mem_vecPerp y⟩

private theorem coe_selfVecPerp (y : Fin k ⊕ Fin k → F) : (selfVecPerp y : Fin k ⊕ Fin k → F) = y :=
  rfl

private theorem mem_span_of_forall_spForm_eq_zero {y x : Fin k ⊕ Fin k → F}
    (h : ∀ z ∈ vecPerp y, spForm k F x z = 0) :
    x ∈ Submodule.span F {y} := by
  have h := CFSG.ClassicalGroups.Alternating.mem_span_of_forall_orthogonal
    (B := spForm k F) spForm_nondegenerate (v := fun _ : Fin 1 => y) x ?_
  · simpa using h
  intro w hw
  have hw' : w ∈ vecPerp y := by
    rw [mem_vecPerp]
    have h' := spForm_isAlt.neg_eq w y
    rw [hw 0] at h'
    exact neg_eq_zero.mp h'
  exact h w hw'

private theorem exists_mem_vecPerp_spForm_ne_zero [CharP F 2] {y x : Fin k ⊕ Fin k → F}
    (hxspan : x ∉ Submodule.span F {y}) :
    ∃ w ∈ vecPerp y, spForm k F w x ≠ 0 := by
  by_contra h
  push Not at h
  refine hxspan (mem_span_of_forall_spForm_eq_zero fun z hz => ?_)
  rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
  exact h z hz

private theorem spTransvection_one_eq_one_iff {a : Fin k ⊕ Fin k → F} :
    spTransvection a (1 : F) = 1 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    obtain ⟨z, hz⟩ := CFSG.OddTranspositions.PartThree.exists_spForm_ne_zero ha
    have h1 := congrArg (fun g : StatedSp k F => spEnd g z) h
    change spEnd (spTransvection a 1) z = spEnd (1 : StatedSp k F) z at h1
    rw [spEnd_spTransvection, spEnd_one, Module.End.one_apply] at h1
    have h2 : (spForm k F z a) • a = 0 := by
      have h3 : z + (spForm k F z a) • a = z + 0 := by simpa using h1
      exact add_left_cancel h3
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hz h3
    · exact ha h3
  · rintro rfl
    exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.spTransvection_zero_eq_one 1

private theorem spTransvection_one_eq_iff [CharP F 2] {v w : Fin k ⊕ Fin k → F} :
    spTransvection v 1 = spTransvection w 1 ↔ v = w := by
  constructor
  · intro h
    by_cases hw : w = 0
    · subst hw
      rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.spTransvection_zero_eq_one] at h
      exact spTransvection_one_eq_one_iff.mp h
    · exact CFSG.OddTranspositions.PartThree.eq_of_spTransvection_eq one_ne_zero hw h
  · rintro rfl
    rfl

private theorem spEnd_spTransvection_mul_apply (u v x : Fin k ⊕ Fin k → F) :
    spEnd (spTransvection u 1 * spTransvection v 1) x =
      x + (spForm k F x v) • v +
        (spForm k F x u + spForm k F x v * spForm k F v u) • u := by
  rw [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, spEnd_spTransvection]
  simp only [one_mul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

private theorem mem_span_of_spTransvection_mul_eq_of_linearIndependent [CharP F 2]
    {u v w : Fin k ⊕ Fin k → F} (hind : LinearIndependent F ![u, v])
    (h : spTransvection u 1 * spTransvection v 1 = spTransvection w 1) :
    u ∈ Submodule.span F {w} ∧ w ∈ Submodule.span F {u} := by
  obtain ⟨x, hx⟩ := CFSG.ClassicalGroups.Alternating.exists_apply_eq_of_linearIndependent
    (BN := spForm k F) spForm_nondegenerate (v := ![u, v]) hind
    (fun i : Fin 2 => if i = 0 then 1 else 0)
  have hxu : spForm k F x u = 1 := by simpa using hx 0
  have hxv : spForm k F x v = 0 := by simpa using hx 1
  have h1 := congrArg (fun g : StatedSp k F => spEnd g x) h
  rw [spEnd_spTransvection_mul_apply, spEnd_spTransvection, hxu, hxv] at h1
  simp only [one_mul, zero_mul, add_zero, one_smul, zero_smul] at h1
  have hu_eq : u = (spForm k F x w) • w := by
    have h1' : x + u = x + (spForm k F x w) • w := by simpa using h1
    exact add_left_cancel h1'
  have hu_mem : u ∈ Submodule.span F {w} :=
    Submodule.mem_span_singleton.mpr ⟨spForm k F x w, hu_eq.symm⟩
  have hc : spForm k F x w ≠ 0 := by
    rintro h0
    rw [h0, zero_smul] at hu_eq
    exact hind.ne_zero 0 (by simpa using hu_eq)
  have hw_mem : w ∈ Submodule.span F {u} := by
    refine Submodule.mem_span_singleton.mpr ⟨(spForm k F x w)⁻¹, ?_⟩
    rw [hu_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact ⟨hu_mem, hw_mem⟩

private theorem mem_span_of_spTransvection_mul_eq_of_mem_span [CharP F 2]
    {u v w : Fin k ⊕ Fin k → F} (hind : LinearIndependent F ![u, v])
    (huw : u ∈ Submodule.span F {w})
    (h : spTransvection u 1 * spTransvection v 1 = spTransvection w 1) :
    v ∈ Submodule.span F {w} := by
  obtain ⟨x', hx'⟩ := CFSG.ClassicalGroups.Alternating.exists_apply_eq_of_linearIndependent
    (BN := spForm k F) spForm_nondegenerate (v := ![u, v]) hind
    (fun i : Fin 2 => if i = 1 then 1 else 0)
  have hx'u : spForm k F x' u = 0 := by simpa using hx' 0
  have hx'v : spForm k F x' v = 1 := by simpa using hx' 1
  have h2 := congrArg (fun g : StatedSp k F => spEnd g x') h
  rw [spEnd_spTransvection_mul_apply, spEnd_spTransvection, hx'u, hx'v] at h2
  simp only [one_mul, one_smul] at h2
  have hv_eq : v + (spForm k F v u) • u = (spForm k F x' w) • w := by
    have h2' : x' + (v + (spForm k F v u) • u) = x' + (spForm k F x' w) • w := by
      simpa only [add_assoc, zero_add] using h2
    exact add_left_cancel h2'
  have hvv : v = (spForm k F x' w) • w - (spForm k F v u) • u := by
    rw [← hv_eq, add_sub_cancel_right]
  rw [hvv]
  exact Submodule.sub_mem _ (Submodule.mem_span_singleton.mpr ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ huw)

private theorem mem_span_of_spTransvection_mul_eq [CharP F 2]
    {u v w : Fin k ⊕ Fin k → F} (hu : u ≠ 0)
    (h : spTransvection u 1 * spTransvection v 1 = spTransvection w 1) :
    v ∈ Submodule.span F {u} := by
  by_contra hspan
  have hind : LinearIndependent F ![u, v] := by
    rw [LinearIndependent.pair_iff' hu]
    intro a ha
    exact hspan (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)
  obtain ⟨huw, hwu⟩ := mem_span_of_spTransvection_mul_eq_of_linearIndependent hind h
  exact hspan ((Submodule.span_singleton_le_iff_mem w (Submodule.span F {u})).mpr hwu
    (mem_span_of_spTransvection_mul_eq_of_mem_span hind huw h))

private abbrev PreservesUnitTransvections {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'})) : Prop :=
  ∀ p : ↥(fixing {y}),
    (∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (p : ↥(StatedSp k F)) = spTransvection a 1) ↔
      ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (α p : ↥(StatedSp k F)) = spTransvection a 1

private theorem exists_image_centerMap {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (a : vecPerp y) (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) :
    ∃ b : Fin k ⊕ Fin k → F, b ≠ 0 ∧ b ∈ vecPerp y' ∧
      (α ⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩ :
        ↥(StatedSp k F)) = spTransvection b 1 := by
  obtain ⟨b, hb, hbT⟩ := (hα ⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
    (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩).mp
      ⟨a, ha, rfl⟩
  refine ⟨b, hb, ?_, hbT⟩
  have hmem : (α ⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩ :
        ↥(StatedSp k F)) ∈ fixing {y'} := (α _).2
  rw [hbT] at hmem
  exact (spTransvection_mem_fixing_singleton_iff one_ne_zero).mp hmem

private noncomputable def centerMap {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (a : vecPerp y) : vecPerp y' := by
  classical
  exact if ha : (a : Fin k ⊕ Fin k → F) = 0 then 0
  else
    ⟨Classical.choose (exists_image_centerMap α hα a ha),
      (Classical.choose_spec (exists_image_centerMap α hα a ha)).2.1⟩

private theorem centerMap_apply {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (a : vecPerp y) (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) :
    (α ⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩ :
      ↥(StatedSp k F)) =
      spTransvection (centerMap α hα a : Fin k ⊕ Fin k → F) 1 := by
  rw [centerMap]
  split_ifs with h
  · exact absurd h ha
  · exact (Classical.choose_spec (exists_image_centerMap α hα a ha)).2.2

private theorem centerMap_zero {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α) :
    centerMap α hα (0 : vecPerp y) = 0 := by
  rw [centerMap]
  simp

private theorem centerMap_ne_zero {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {a : vecPerp y} (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) :
    centerMap α hα a ≠ 0 := by
  intro hzero
  have h1 : spTransvection (centerMap α hα a : Fin k ⊕ Fin k → F) 1 = (1 : StatedSp k F) := by
    rw [hzero]
    exact spTransvection_zero_eq_one 1
  have h2 : (α ⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩ :
      ↥(StatedSp k F)) = 1 := by
    rw [centerMap_apply α hα a ha]
    exact h1
  have h3 : (⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩ :
      ↥(fixing {y})) = 1 := α.injective (by
        rw [map_one]
        exact Subtype.ext h2)
  have h4 : spTransvection (a : Fin k ⊕ Fin k → F) 1 = 1 := congrArg Subtype.val h3
  exact ha (spTransvection_one_eq_one_iff.mp h4)

private theorem centerMap_val_ne_zero {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {a : vecPerp y} (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) :
    (centerMap α hα a : Fin k ⊕ Fin k → F) ≠ 0 := by
  intro h0
  exact centerMap_ne_zero α hα ha (Subtype.ext h0)

private theorem centerMap_injective [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α) :
    Function.Injective (centerMap α hα) := by
  intro a z h
  by_cases ha : (a : Fin k ⊕ Fin k → F) = 0
  · have hz : (z : Fin k ⊕ Fin k → F) = 0 := by
      by_contra hz
      have hzm : centerMap α hα z ≠ 0 := centerMap_ne_zero α hα hz
      apply hzm
      rw [← h, show a = 0 from Subtype.ext ha, centerMap_zero]
    exact Subtype.ext (ha.trans hz.symm)
  · have hz : (z : Fin k ⊕ Fin k → F) ≠ 0 := by
      intro hz
      have ham : centerMap α hα a ≠ 0 := centerMap_ne_zero α hα ha
      apply ham
      rw [h, show z = 0 from Subtype.ext hz, centerMap_zero]
    have h5 : (α ⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩ :
        ↥(StatedSp k F)) = (α ⟨spTransvection (z : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp z.2)⟩ :
        ↥(StatedSp k F)) := by
      rw [centerMap_apply α hα a ha, centerMap_apply α hα z hz, h]
    have h1 : spTransvection (a : Fin k ⊕ Fin k → F) 1 =
        spTransvection (z : Fin k ⊕ Fin k → F) 1 :=
      congrArg Subtype.val (α.injective (Subtype.ext h5))
    exact Subtype.ext (spTransvection_one_eq_iff.mp h1)

private theorem centerMap_surjective [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α) :
    Function.Surjective (centerMap α hα) := by
  intro b
  by_cases hb : (b : Fin k ⊕ Fin k → F) = 0
  · exact ⟨0, by rw [centerMap_zero]; exact Subtype.ext hb.symm⟩
  · have hbm : spTransvection (b : Fin k ⊕ Fin k → F) 1 ∈ fixing {y'} :=
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp b.2)
    let p : ↥(fixing {y}) := α.symm ⟨spTransvection (b : Fin k ⊕ Fin k → F) 1, hbm⟩
    have hpα : (α p : ↥(StatedSp k F)) = spTransvection (b : Fin k ⊕ Fin k → F) 1 := by
      simp only [p, MulEquiv.apply_symm_apply]
    obtain ⟨a, ha, hpa⟩ := (hα p).mpr ⟨b, hb, hpα⟩
    have ham : a ∈ vecPerp y :=
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mp (hpa ▸ p.2)
    have hsub : (⟨spTransvection a 1, (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
        (mem_vecPerp.mp ham)⟩ : ↥(fixing {y})) = p := by
      apply Subtype.ext
      exact hpa.symm
    refine ⟨⟨a, ham⟩, ?_⟩
    have h1 : spTransvection (centerMap α hα ⟨a, ham⟩ : Fin k ⊕ Fin k → F) 1 =
        spTransvection (b : Fin k ⊕ Fin k → F) 1 := by
      rw [← centerMap_apply α hα ⟨a, ham⟩ ha, hsub, hpα]
    exact Subtype.ext (spTransvection_one_eq_iff.mp h1)

private theorem centerMap_self [CharP F 2] {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) :
    centerMap α hα (selfVecPerp y) = selfVecPerp y' := by
  have h1 : spTransvection (centerMap α hα (selfVecPerp y) : Fin k ⊕ Fin k → F) 1 =
      spTransvection y' 1 := by
    rw [← centerMap_apply α hα (selfVecPerp y) hy]
    have hsub : (⟨spTransvection ((selfVecPerp y : vecPerp y) : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
          (mem_vecPerp.mp (selfVecPerp y).2)⟩ : ↥(fixing {y})) =
        ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ := by
      apply Subtype.ext
      rfl
    rw [hsub, hαy]
  exact Subtype.ext (spTransvection_one_eq_iff.mp h1)

private theorem spEnd_mem_vecPerp {y : Fin k ⊕ Fin k → F} {g : ↥(fixing {y})}
    {x : Fin k ⊕ Fin k → F} (hx : x ∈ vecPerp y) : spEnd g x ∈ vecPerp y := by
  rw [mem_vecPerp] at hx ⊢
  have hgy : spEnd g y = y := (mem_fixing.mp g.2) y (Set.mem_singleton y)
  have hiso := spForm_spEnd_spEnd g x y
  rw [hgy, hx] at hiso
  exact hiso

private noncomputable def vecPerpMap {y : Fin k ⊕ Fin k → F} (g : ↥(fixing {y}))
    (x : vecPerp y) : vecPerp y := by
  refine ⟨spEnd g (x : Fin k ⊕ Fin k → F), ?_⟩
  exact spEnd_mem_vecPerp (y := y) (g := g) (x := (x : Fin k ⊕ Fin k → F)) x.2

private theorem coe_vecPerpMap {y : Fin k ⊕ Fin k → F} (g : ↥(fixing {y})) (x : vecPerp y) :
    (vecPerpMap g x : Fin k ⊕ Fin k → F) = spEnd g (x : Fin k ⊕ Fin k → F) := rfl

private theorem centerMap_vecPerpMap [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (g : ↥(fixing {y})) (x : vecPerp y) :
    centerMap α hα (vecPerpMap g x) = vecPerpMap (α g) (centerMap α hα x) := by
  by_cases hx : (x : Fin k ⊕ Fin k → F) = 0
  · have hx0 : x = 0 := Subtype.ext hx
    subst hx0
    have hz : vecPerpMap g (0 : vecPerp y) = 0 := by
      apply Subtype.ext
      exact map_zero (spEnd (g : StatedSp k F))
    have hzα : vecPerpMap (α g) (0 : vecPerp y') = 0 := by
      apply Subtype.ext
      exact map_zero (spEnd (α g : StatedSp k F))
    rw [hz, centerMap_zero, hzα]
  · have hgx : (vecPerpMap g x : Fin k ⊕ Fin k → F) ≠ 0 := by
      rw [coe_vecPerpMap]
      exact fun h0 => hx (by
        simpa [h0] using (CFSG.RankThree.PartOne.CTP.spEnd_spEnd_inv
          (g := (g : StatedSp k F)⁻¹) x).symm)
    let G : ↥(fixing {y}) :=
      ⟨spTransvection (x : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp x.2)⟩
    let G' : ↥(fixing {y}) :=
      ⟨spTransvection (vecPerpMap g x : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
          (mem_vecPerp.mp (vecPerpMap g x).2)⟩
    have hconj : g * G * g⁻¹ = G' := by
      apply Subtype.ext
      simp only [G, G', Subgroup.coe_mul, Subgroup.coe_inv]
      rw [coe_vecPerpMap]
      exact conj_spTransvection (g : StatedSp k F) (x : Fin k ⊕ Fin k → F) 1
    have hmap := congrArg (fun p : ↥(fixing {y}) => (α p : ↥(StatedSp k F))) hconj
    simp only [G, G', Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at hmap
    rw [centerMap_apply α hα x hx, centerMap_apply α hα (vecPerpMap g x) hgx] at hmap
    rw [conj_spTransvection] at hmap
    apply Subtype.ext
    rw [coe_vecPerpMap]
    exact (spTransvection_one_eq_iff.mp hmap).symm

private theorem commute_spTransvection_centerMap_iff [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x z : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ≠ 0)
    (hz : (z : Fin k ⊕ Fin k → F) ≠ 0) :
    Commute (spTransvection (x : Fin k ⊕ Fin k → F) 1)
        (spTransvection (z : Fin k ⊕ Fin k → F) 1) ↔
      Commute (spTransvection (centerMap α hα x : Fin k ⊕ Fin k → F) 1)
        (spTransvection (centerMap α hα z : Fin k ⊕ Fin k → F) 1) := by
  let X : ↥(fixing {y}) :=
    ⟨spTransvection (x : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp x.2)⟩
  let Z : ↥(fixing {y}) :=
    ⟨spTransvection (z : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp z.2)⟩
  have hcoe : Commute (X : StatedSp k F) (Z : StatedSp k F) ↔ Commute X Z :=
    _root_.commute_map_iff (x := X) (y := Z) (Subgroup.subtype_injective (fixing {y}))
  have hcomm : Commute X Z ↔ Commute (α X) (α Z) :=
    (_root_.commute_map_iff (x := X) (y := Z) α.injective).symm
  have hcoe' : Commute (α X : StatedSp k F) (α Z : StatedSp k F) ↔
      Commute (α X) (α Z) :=
    _root_.commute_map_iff (x := α X) (y := α Z)
      (Subgroup.subtype_injective (fixing {y'}))
  have hX : (α X : StatedSp k F) =
      spTransvection (centerMap α hα x : Fin k ⊕ Fin k → F) 1 :=
    centerMap_apply α hα x hx
  have hZ : (α Z : StatedSp k F) =
      spTransvection (centerMap α hα z : Fin k ⊕ Fin k → F) 1 :=
    centerMap_apply α hα z hz
  have hX' : (X : StatedSp k F) = spTransvection (x : Fin k ⊕ Fin k → F) 1 := rfl
  have hZ' : (Z : StatedSp k F) = spTransvection (z : Fin k ⊕ Fin k → F) 1 := rfl
  rw [← hX', ← hZ', ← hX, ← hZ]
  exact hcoe.trans (hcomm.trans hcoe'.symm)

private theorem centerMap_spForm_eq_zero_iff [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (x z : vecPerp y) :
    spForm k F (x : Fin k ⊕ Fin k → F) (z : Fin k ⊕ Fin k → F) = 0 ↔
      spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα z : Fin k ⊕ Fin k → F) = 0 := by
  by_cases hx : (x : Fin k ⊕ Fin k → F) = 0
  · have hx0 : (centerMap α hα x : Fin k ⊕ Fin k → F) = 0 := by
      rw [show x = 0 from Subtype.ext hx, centerMap_zero]
      rfl
    rw [hx, hx0]
    simp
  by_cases hz : (z : Fin k ⊕ Fin k → F) = 0
  · have hz0 : (centerMap α hα z : Fin k ⊕ Fin k → F) = 0 := by
      rw [show z = 0 from Subtype.ext hz, centerMap_zero]
      rfl
    rw [hz, hz0]
    simp
  rw [← commute_spTransvection_iff (a := (x : Fin k ⊕ Fin k → F))
      (b := (z : Fin k ⊕ Fin k → F)) one_ne_zero one_ne_zero,
    commute_spTransvection_centerMap_iff α hα hx hz,
    commute_spTransvection_iff (a := (centerMap α hα x : Fin k ⊕ Fin k → F))
      (b := (centerMap α hα z : Fin k ⊕ Fin k → F)) one_ne_zero one_ne_zero]

private theorem spTransvection_mul_smul [CharP F 2] (a : Fin k ⊕ Fin k → F) (c : F) :
    spTransvection a 1 * spTransvection (c • a) 1 = spTransvection ((1 + c) • a) 1 := by
  rw [spTransvection_smul_eq, spTransvection_smul_eq,
    CFSG.LocalAnalysis.WeakClosure81.spConf_transvection_mul]
  congr 1
  have h2 : (1 + c) * (1 + c) = 1 + c * c := by
    rw [← pow_two, CharTwo.add_sq, pow_two]
    ring
  rw [h2]
  ring

private theorem exists_smul_centerMap [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {a : vecPerp y} (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) (c : F) :
    ∃ μ : F, centerMap α hα (c • a) = μ • centerMap α hα a := by
  by_cases hc0 : c = 0
  · subst hc0
    refine ⟨0, ?_⟩
    rw [zero_smul, centerMap_zero, zero_smul]
  by_cases hc1 : c = 1
  · subst hc1
    exact ⟨1, by rw [one_smul, one_smul]⟩
  have hca : ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) ≠ 0 := by
    simpa using smul_ne_zero hc0 ha
  have h1c : (1 + c : F) ≠ 0 := fun h => hc1 (CharTwo.add_eq_zero.mp h).symm
  have h1ca : (((1 + c) • a : vecPerp y) : Fin k ⊕ Fin k → F) ≠ 0 := by
    simpa using smul_ne_zero h1c ha
  let A : ↥(fixing {y}) :=
    ⟨spTransvection (a : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp a.2)⟩
  let B : ↥(fixing {y}) :=
    ⟨spTransvection ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
        (mem_vecPerp.mp (c • a).2)⟩
  let D : ↥(fixing {y}) :=
    ⟨spTransvection (((1 + c) • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
        (mem_vecPerp.mp ((1 + c) • a).2)⟩
  have hABD : A * B = D := by
    apply Subtype.ext
    exact spTransvection_mul_smul (a : Fin k ⊕ Fin k → F) c
  have himg := congrArg (fun p : ↥(fixing {y}) => (α p : ↥(StatedSp k F))) hABD
  rw [map_mul] at himg
  change (α A : StatedSp k F) * (α B : StatedSp k F) = (α D : StatedSp k F) at himg
  rw [centerMap_apply α hα a ha, centerMap_apply α hα (c • a) hca,
    centerMap_apply α hα ((1 + c) • a) h1ca] at himg
  have hmem := mem_span_of_spTransvection_mul_eq (centerMap_val_ne_zero α hα ha) himg
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨μ, Subtype.ext hμ.symm⟩

private theorem exists_smul_centerMap_all [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (a : vecPerp y) (c : F) :
    ∃ μ : F, centerMap α hα (c • a) = μ • centerMap α hα a ∧
      ((a : Fin k ⊕ Fin k → F) = 0 → μ = 0) := by
  by_cases ha : (a : Fin k ⊕ Fin k → F) = 0
  · refine ⟨0, ?_, fun _ => rfl⟩
    have ha0 : a = 0 := Subtype.ext ha
    subst ha0
    simp [centerMap_zero]
  · obtain ⟨μ, hμ⟩ := exists_smul_centerMap α hα ha c
    exact ⟨μ, hμ, fun h => absurd h ha⟩

private noncomputable def mu [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (a : vecPerp y) (c : F) : F :=
  Classical.choose (exists_smul_centerMap_all α hα a c)

private theorem mu_apply [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (a : vecPerp y) (c : F) :
    centerMap α hα (c • a) = mu α hα a c • centerMap α hα a :=
  (Classical.choose_spec (exists_smul_centerMap_all α hα a c)).1

private theorem mu_eq_zero_of_eq_zero [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {a : vecPerp y} (ha : (a : Fin k ⊕ Fin k → F) = 0) (c : F) : mu α hα a c = 0 :=
  (Classical.choose_spec (exists_smul_centerMap_all α hα a c)).2 ha

private theorem mu_zero [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (a : vecPerp y) : mu α hα a 0 = 0 := by
  by_cases ha : (a : Fin k ⊕ Fin k → F) = 0
  · exact mu_eq_zero_of_eq_zero α hα ha 0
  · have h := mu_apply α hα a 0
    rw [zero_smul, centerMap_zero] at h
    have h' : mu α hα a 0 • centerMap α hα a = (0 : F) • centerMap α hα a := by
      rw [zero_smul, ← h]
    have h'' := congrArg Subtype.val h'
    simpa using smul_left_injective F (centerMap_val_ne_zero α hα ha) h''

private theorem mu_one [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {a : vecPerp y} (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) : mu α hα a 1 = 1 := by
  have h := mu_apply α hα a 1
  rw [one_smul] at h
  have h' : mu α hα a 1 • centerMap α hα a = (1 : F) • centerMap α hα a := by
    rw [one_smul, ← h]
  have h'' := congrArg Subtype.val h'
  simpa using smul_left_injective F (centerMap_val_ne_zero α hα ha) h''

private theorem spTransvection_mul_smul_smul [CharP F 2] (a : Fin k ⊕ Fin k → F) (c d : F) :
    spTransvection (c • a) 1 * spTransvection (d • a) 1 =
      spTransvection ((c + d) • a) 1 := by
  rw [spTransvection_smul_eq, spTransvection_smul_eq,
    CFSG.LocalAnalysis.WeakClosure81.spConf_transvection_mul, spTransvection_smul_eq]
  congr 1
  have h2 : (c + d) * (c + d) = c * c + d * d := by
    rw [← pow_two, CharTwo.add_sq, pow_two, pow_two]
  rw [h2]
  ring

private theorem mu_add [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {a : vecPerp y} (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) (c d : F) :
    mu α hα a (c + d) = mu α hα a c + mu α hα a d := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [zero_add, mu_zero, zero_add]
  by_cases hd0 : d = 0
  · subst hd0
    rw [add_zero, mu_zero, add_zero]
  by_cases hcd : c + d = 0
  · have hdc : d = c := (CharTwo.add_eq_zero.mp hcd).symm
    subst hdc
    rw [hcd, mu_zero, CharTwo.add_self_eq_zero]
  have hca : ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) ≠ 0 := by
    simpa using smul_ne_zero hc0 ha
  have hda : ((d • a : vecPerp y) : Fin k ⊕ Fin k → F) ≠ 0 := by
    simpa using smul_ne_zero hd0 ha
  have hcda : (((c + d) • a : vecPerp y) : Fin k ⊕ Fin k → F) ≠ 0 := by
    simpa using smul_ne_zero hcd ha
  have hprod : (⟨spTransvection ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
        (mem_vecPerp.mp (c • a).2)⟩ : ↥(fixing {y})) *
      ⟨spTransvection ((d • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
          (mem_vecPerp.mp (d • a).2)⟩ =
      ⟨spTransvection (((c + d) • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
          (mem_vecPerp.mp ((c + d) • a).2)⟩ := by
    apply Subtype.ext
    exact spTransvection_mul_smul_smul (a : Fin k ⊕ Fin k → F) c d
  have himg := congrArg (fun p : ↥(fixing {y}) => (α p : ↥(StatedSp k F))) hprod
  rw [map_mul] at himg
  change (α ⟨spTransvection ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp (c • a).2)⟩ :
      StatedSp k F) *
      (α ⟨spTransvection ((d • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
          (mem_vecPerp.mp (d • a).2)⟩ : StatedSp k F) =
      (α ⟨spTransvection (((c + d) • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
          (mem_vecPerp.mp ((c + d) • a).2)⟩ : StatedSp k F) at himg
  simp only [centerMap_apply α hα (c • a) hca, centerMap_apply α hα (d • a) hda,
    centerMap_apply α hα ((c + d) • a) hcda, mu_apply α hα a c, mu_apply α hα a d,
    mu_apply α hα a (c + d)] at himg
  simp only [Submodule.coe_smul] at himg
  rw [spTransvection_mul_smul_smul] at himg
  have h := spTransvection_one_eq_iff.mp himg
  exact (smul_left_injective F (centerMap_val_ne_zero α hα ha) h).symm

private theorem coe_vecPerpMap_of_spTransvection {y : Fin k ⊕ Fin k → F}
    (g : ↥(fixing {y})) (x a : vecPerp y) (c : F)
    (hg : (g : StatedSp k F) =
      spTransvection ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) 1) :
    (vecPerpMap g x : Fin k ⊕ Fin k → F) =
      (x : Fin k ⊕ Fin k → F) + ((c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F)
        (a : Fin k ⊕ Fin k → F)) • (a : Fin k ⊕ Fin k → F)) := by
  rw [coe_vecPerpMap, hg, spEnd_spTransvection]
  simp only [one_mul, map_smul, smul_eq_mul, Submodule.coe_smul]
  congr 1
  rw [smul_smul]
  congr 1
  ring

private theorem centerMap_add_smul [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (x a : vecPerp y) (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) (c : F) :
    centerMap α hα (x + ((c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F)
        (a : Fin k ⊕ Fin k → F)) • a)) =
      centerMap α hα x + ((mu α hα a c) ^ 2 * spForm k F
        (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα a : Fin k ⊕ Fin k → F)) • centerMap α hα a := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [mu_zero]
    simp
  have hca : ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) ≠ 0 := by
    simpa using smul_ne_zero hc0 ha
  let g : ↥(fixing {y}) :=
    ⟨spTransvection ((c • a : vecPerp y) : Fin k ⊕ Fin k → F) 1,
      (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
        (mem_vecPerp.mp (c • a).2)⟩
  have h := centerMap_vecPerpMap α hα g x
  have hgx := coe_vecPerpMap_of_spTransvection g x a c rfl
  have hαg : (α g : StatedSp k F) =
      spTransvection (((mu α hα a c) • centerMap α hα a : vecPerp y') :
        Fin k ⊕ Fin k → F) 1 := by
    rw [show (α g : StatedSp k F) =
      spTransvection (centerMap α hα (c • a) : Fin k ⊕ Fin k → F) 1 from
      centerMap_apply α hα (c • a) hca]
    rw [show (centerMap α hα (c • a) : Fin k ⊕ Fin k → F) =
      (((mu α hα a c) • centerMap α hα a : vecPerp y') : Fin k ⊕ Fin k → F) from
      congrArg Subtype.val (mu_apply α hα a c)]
  have hR := coe_vecPerpMap_of_spTransvection (α g) (centerMap α hα x)
    (centerMap α hα a) (mu α hα a c) hαg
  have hpg : vecPerpMap g x =
      (⟨(x : Fin k ⊕ Fin k → F) + ((c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F)
        (a : Fin k ⊕ Fin k → F)) • (a : Fin k ⊕ Fin k → F)),
        (vecPerp y).add_mem x.2 (Submodule.smul_mem _ _ a.2)⟩ : vecPerp y) :=
    Subtype.ext hgx
  have hpa : vecPerpMap (α g) (centerMap α hα x) =
      (⟨(centerMap α hα x : Fin k ⊕ Fin k → F) + (((mu α hα a c) ^ 2 * spForm k F
        (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα a : Fin k ⊕ Fin k → F)) •
        (centerMap α hα a : Fin k ⊕ Fin k → F)),
        (vecPerp y').add_mem (centerMap α hα x).2
          (Submodule.smul_mem _ _ (centerMap α hα a).2)⟩ : vecPerp y') :=
    Subtype.ext hR
  rw [hpg, hpa] at h
  exact h

private theorem exists_sq_mul_eq_one [Fintype F] [CharP F 2] {s : F} (hs : s ≠ 0) :
    ∃ c : F, c ^ 2 * s = 1 ∧ c ≠ 0 := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) s⁻¹
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact inv_ne_zero hs hc
  refine ⟨c, ?_, hc0⟩
  rw [pow_two, ← hc, inv_mul_cancel₀ hs]

private theorem centerMap_smul_add [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (x a : vecPerp y) (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) (c d : F)
    (hc : c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) = 1) :
    centerMap α hα (d • x + d • a) = mu α hα x d • centerMap α hα (x + a) := by
  have hE := centerMap_add_smul α hα (d • x) a ha c
  have hcoef : c ^ 2 * spForm k F ((d • x : vecPerp y) : Fin k ⊕ Fin k → F)
      (a : Fin k ⊕ Fin k → F) = d := by
    rw [Submodule.coe_smul]
    simp only [map_smul, smul_eq_mul, LinearMap.smul_apply]
    calc c ^ 2 * (d * spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F)) =
        d * (c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F)) := by ring
      _ = d * 1 := by rw [hc]
      _ = d := mul_one d
  rw [hcoef] at hE
  have hE1 := centerMap_add_smul α hα x a ha c
  rw [hc, one_smul] at hE1
  rw [mu_apply α hα x d] at hE
  rw [hE, hE1, smul_add, smul_smul]
  simp only [Submodule.coe_smul, map_smul, smul_eq_mul, LinearMap.smul_apply]
  congr 1
  ring_nf

private theorem centerMap_smul_add' [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (x a : vecPerp y) (hx : (x : Fin k ⊕ Fin k → F) ≠ 0) (c d : F)
    (hc : c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) = 1) :
    centerMap α hα (d • a + d • x) = mu α hα a d • centerMap α hα (a + x) := by
  have hB : spForm k F (a : Fin k ⊕ Fin k → F) (x : Fin k ⊕ Fin k → F) =
      spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) :=
    (CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt
      (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F)).symm
  have hE := centerMap_add_smul α hα (d • a) x hx c
  have hcoef : c ^ 2 * spForm k F ((d • a : vecPerp y) : Fin k ⊕ Fin k → F)
      (x : Fin k ⊕ Fin k → F) = d := by
    rw [Submodule.coe_smul]
    simp only [map_smul, smul_eq_mul, LinearMap.smul_apply]
    rw [hB]
    calc c ^ 2 * (d * spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F)) =
        d * (c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F)) := by ring
      _ = d * 1 := by rw [hc]
      _ = d := mul_one d
  rw [hcoef] at hE
  have hE1 := centerMap_add_smul α hα a x hx c
  rw [hB, hc, one_smul] at hE1
  rw [mu_apply α hα a d] at hE
  rw [hE, hE1, smul_add, smul_smul]
  simp only [Submodule.coe_smul, map_smul, smul_eq_mul, LinearMap.smul_apply]
  congr 1
  ring_nf

private theorem mu_eq_of_spForm_ne_zero [Fintype F] [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (x a : vecPerp y) (hxa : spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) ≠ 0)
    (d : F) :
    mu α hα x d = mu α hα a d := by
  have hx0 : (x : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    apply hxa
    rw [h0]
    simp
  have ha0 : (a : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxa
    exact hxa rfl
  obtain ⟨c, hc, hc0⟩ := exists_sq_mul_eq_one hxa
  have h1 := centerMap_smul_add α hα x a ha0 c d hc
  have h2 := centerMap_smul_add' α hα x a hx0 c d hc
  have hxa0 : ((x + a : vecPerp y) : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    apply hxa
    have h0' : (x : Fin k ⊕ Fin k → F) + (a : Fin k ⊕ Fin k → F) = 0 := by
      simpa using h0
    have hh := congrArg (fun z : Fin k ⊕ Fin k → F =>
      spForm k F (x : Fin k ⊕ Fin k → F) z) h0'
    rw [map_add, spForm_isAlt.self_eq_zero, zero_add, map_zero] at hh
    exact hh
  have hcomm : (d • x + d • a : vecPerp y) = d • a + d • x := add_comm _ _
  have hsum : (x + a : vecPerp y) = a + x := add_comm _ _
  have h : mu α hα x d • centerMap α hα (x + a) =
      mu α hα a d • centerMap α hα (x + a) := by
    rw [← h1, show (d • x + d • a : vecPerp y) = d • a + d • x from add_comm _ _, h2,
      show (a + x : vecPerp y) = x + a from add_comm _ _]
  have hval := congrArg Subtype.val h
  simp only [Submodule.coe_smul] at hval
  exact smul_left_injective F (centerMap_val_ne_zero α hα hxa0) hval

private theorem exists_mem_vecPerp_spForm_ne_zero_pair [CharP F 2]
    {y x z : Fin k ⊕ Fin k → F}
    (hxs : x ∉ Submodule.span F {y}) (hzs : z ∉ Submodule.span F {y}) :
    ∃ w ∈ vecPerp y, spForm k F x w ≠ 0 ∧ spForm k F z w ≠ 0 := by
  obtain ⟨w₁, hw₁, hw₁x⟩ := exists_mem_vecPerp_spForm_ne_zero hxs
  obtain ⟨w₂, hw₂, hw₂z⟩ := exists_mem_vecPerp_spForm_ne_zero hzs
  have hxw₁ : spForm k F x w₁ ≠ 0 := by
    rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt] at hw₁x
  have hzw₂ : spForm k F z w₂ ≠ 0 := by
    rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt] at hw₂z
  by_cases hz₁ : spForm k F z w₁ ≠ 0
  · exact ⟨w₁, hw₁, hxw₁, hz₁⟩
  · push Not at hz₁
    by_cases hx₂ : spForm k F x w₂ ≠ 0
    · exact ⟨w₂, hw₂, hx₂, hzw₂⟩
    · push Not at hx₂
      refine ⟨w₁ + w₂, (vecPerp y).add_mem hw₁ hw₂, ?_, ?_⟩
      · rw [map_add, hx₂, add_zero]
        exact hxw₁
      · rw [map_add, hz₁, zero_add]
        exact hzw₂

private theorem mu_eq_of_notMem_span [Fintype F] [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x z : vecPerp y} (hxs : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hzs : (z : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) (d : F) :
    mu α hα x d = mu α hα z d := by
  obtain ⟨w, hw, hxw, hzw⟩ := exists_mem_vecPerp_spForm_ne_zero_pair hxs hzs
  have h1 : mu α hα x d = mu α hα ⟨w, hw⟩ d :=
    mu_eq_of_spForm_ne_zero α hα x ⟨w, hw⟩ hxw d
  have h2 : mu α hα z d = mu α hα ⟨w, hw⟩ d :=
    mu_eq_of_spForm_ne_zero α hα z ⟨w, hw⟩ hzw d
  rw [h1, h2]

private theorem exists_notMem_span_vecPerp (hk : 2 ≤ k) {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) :
    ∃ x : vecPerp y, (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} := by
  obtain ⟨x, hx, hx'⟩ := exists_spForm_eq_zero_forall_ne_smul hk hy
  refine ⟨⟨x, by rwa [mem_vecPerp]⟩, ?_⟩
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact hx' c hc.symm

private noncomputable def basePoint (hk : 2 ≤ k) {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) :
    vecPerp y :=
  Classical.choose (exists_notMem_span_vecPerp hk hy)

private theorem basePoint_notMem (hk : 2 ≤ k) {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) :
    (basePoint hk hy : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} :=
  Classical.choose_spec (exists_notMem_span_vecPerp hk hy)

private theorem basePoint_ne_zero (hk : 2 ≤ k) {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) :
    (basePoint hk hy : Fin k ⊕ Fin k → F) ≠ 0 := by
  intro h0
  exact basePoint_notMem hk hy (by rw [h0]; exact Submodule.zero_mem _)

private noncomputable def sigmaFun [CharP F 2] (hk : 2 ≤ k) {y y' : Fin k ⊕ Fin k → F}
    (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (c : F) : F :=
  mu α hα (basePoint hk hy) c

private theorem sigmaFun_add [CharP F 2] (hk : 2 ≤ k) {y y' : Fin k ⊕ Fin k → F}
    (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (c d : F) :
    sigmaFun hk hy α hα (c + d) = sigmaFun hk hy α hα c + sigmaFun hk hy α hα d :=
  mu_add α hα (basePoint_ne_zero hk hy) c d

private theorem sigmaFun_zero [CharP F 2] (hk : 2 ≤ k) {y y' : Fin k ⊕ Fin k → F}
    (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α) :
    sigmaFun hk hy α hα 0 = 0 :=
  mu_zero α hα (basePoint hk hy)

private theorem sigmaFun_one [CharP F 2] (hk : 2 ≤ k) {y y' : Fin k ⊕ Fin k → F}
    (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α) :
    sigmaFun hk hy α hα 1 = 1 :=
  mu_one α hα (basePoint_ne_zero hk hy)

private theorem sigmaFun_mul [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (c d : F) :
    sigmaFun hk hy α hα (c * d) = sigmaFun hk hy α hα c * sigmaFun hk hy α hα d := by
  by_cases hd : d = 0
  · subst hd
    rw [mul_zero, sigmaFun_zero]
    exact (mul_zero (sigmaFun hk hy α hα c)).symm
  have hdnot : ((d • basePoint hk hy : vecPerp y) : Fin k ⊕ Fin k → F) ∉
      Submodule.span F {y} :=
      (Submodule.smul_mem_iff _ hd).not.mpr (basePoint_notMem hk hy)
  have hbpne : (basePoint hk hy : Fin k ⊕ Fin k → F) ≠ 0 := basePoint_ne_zero hk hy
  have h1 := mu_apply α hα (basePoint hk hy) (c * d)
  have h2 := mu_apply α hα (d • basePoint hk hy) c
  have h3 := mu_apply α hα (basePoint hk hy) d
  have h4 : mu α hα (d • basePoint hk hy) c = sigmaFun hk hy α hα c :=
    mu_eq_of_notMem_span α hα hdnot (basePoint_notMem hk hy) c
  have h6 : centerMap α hα (c • (d • basePoint hk hy)) =
      (mu α hα (d • basePoint hk hy) c * mu α hα (basePoint hk hy) d) •
        centerMap α hα (basePoint hk hy) := by
    rw [h2, h3, smul_smul]
  have h7 : c • (d • basePoint hk hy) = (c * d) • basePoint hk hy := smul_smul c d _
  rw [h7, h1] at h6
  have hval := congrArg Subtype.val h6
  simp only [Submodule.coe_smul] at hval
  have hsc := smul_left_injective F (centerMap_val_ne_zero α hα hbpne) hval
  rw [h4] at hsc
  simpa [sigmaFun] using hsc

private theorem sigmaFun_injective [CharP F 2] (hk : 2 ≤ k) {y y' : Fin k ⊕ Fin k → F}
    (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α) :
    Function.Injective (sigmaFun hk hy α hα) := by
  intro c d h
  have h1 : mu α hα (basePoint hk hy) c = mu α hα (basePoint hk hy) d := by
    simpa [sigmaFun] using h
  have hcd : c • basePoint hk hy = d • basePoint hk hy := by
    apply centerMap_injective α hα
    rw [mu_apply α hα (basePoint hk hy) c, mu_apply α hα (basePoint hk hy) d, h1]
  have hval := congrArg Subtype.val hcd
  simp only [Submodule.coe_smul] at hval
  have hdiff : (c - d) • (basePoint hk hy : Fin k ⊕ Fin k → F) = 0 := by
    rw [sub_smul, hval, sub_self]
  rcases smul_eq_zero.mp hdiff with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (basePoint_ne_zero hk hy)

private noncomputable def centerFieldEquiv [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α) :
    F ≃+* F :=
  let f : F →+* F :=
    { toFun := sigmaFun hk hy α hα
      map_one' := sigmaFun_one hk hy α hα
      map_mul' := sigmaFun_mul hk hy α hα
      map_zero' := sigmaFun_zero hk hy α hα
      map_add' := sigmaFun_add hk hy α hα }
  RingEquiv.ofBijective f
    (Finite.injective_iff_bijective.mp (sigmaFun_injective hk hy α hα))

private theorem centerFieldEquiv_apply [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (c : F) : centerFieldEquiv hk hy α hα c = sigmaFun hk hy α hα c :=
  RingEquiv.ofBijective_apply _ _ c

private theorem mu_eq_sigmaFun [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) (c : F) :
    mu α hα x c = centerFieldEquiv hk hy α hα c := by
  rw [centerFieldEquiv_apply]
  exact mu_eq_of_notMem_span α hα hx (basePoint_notMem hk hy) c

private theorem centerMap_smul_of_notMem [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) (c : F) :
    centerMap α hα (c • x) = centerFieldEquiv hk hy α hα c • centerMap α hα x := by
  rw [mu_apply α hα x c, mu_eq_sigmaFun hk hy α hα hx c]

private theorem notMem_span_of_spForm_ne_zero_right [CharP F 2] {y x a : Fin k ⊕ Fin k → F}
    (hx : x ∈ vecPerp y) (hxa : spForm k F x a ≠ 0) :
    a ∉ Submodule.span F {y} := by
  intro hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  apply hxa
  rw [← ht, map_smul, smul_eq_mul, mem_vecPerp.mp hx, mul_zero]

private theorem add_eq_zero_of_add_eq_add_smul [CharP F 2]
    {v w : Fin k ⊕ Fin k → F} {κ : F} (h : v + κ • w = w + κ • v) (hκ : κ ≠ 1) :
    v + w = 0 := by
  have h2 : (1 + κ) • (v + w) = 0 := by
    rw [add_smul, one_smul, smul_add]
    calc v + w + (κ • v + κ • w) = (v + κ • w) + (w + κ • v) := by abel
      _ = (w + κ • v) + (w + κ • v) := by rw [h]
      _ = 0 := by
        rw [← two_smul (R := F)]
        rw [CharTwo.two_eq_zero (R := F), zero_smul]
  have h1 : (1 + κ) ≠ 0 := fun h0 => hκ (CharTwo.add_eq_zero.mp h0).symm
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 h1
  · exact h3

private theorem centerMap_add_eq_add_smul_of_sq_mul_spForm_eq_one [Fintype F] [CharP F 2]
    (hk : 2 ≤ k) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x a : vecPerp y} (ha : (a : Fin k ⊕ Fin k → F) ≠ 0) {c : F}
    (hc : c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) = 1) :
    centerMap α hα (x + a) = centerMap α hα x + ((centerFieldEquiv hk hy α hα c) ^ 2 *
      spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα a : Fin k ⊕ Fin k → F)) • centerMap α hα a := by
  have hxa : spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hc
    exact zero_ne_one hc
  have hσa : mu α hα a c = centerFieldEquiv hk hy α hα c :=
    mu_eq_sigmaFun hk hy α hα (notMem_span_of_spForm_ne_zero_right x.2 hxa) c
  have hX := centerMap_add_smul α hα x a ha c
  rw [hc, one_smul, hσa] at hX
  exact hX

private theorem centerMap_smul_swap_eq [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x a : vecPerp y}
    (hxa : spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) ≠ 0)
    {c : F} (hc : c ^ 2 * spForm k F (x : Fin k ⊕ Fin k → F)
      (a : Fin k ⊕ Fin k → F) = 1) :
    (centerMap α hα x : Fin k ⊕ Fin k → F) +
        ((centerFieldEquiv hk hy α hα c) ^ 2 *
          spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
            (centerMap α hα a : Fin k ⊕ Fin k → F)) •
          (centerMap α hα a : Fin k ⊕ Fin k → F) =
      (centerMap α hα a : Fin k ⊕ Fin k → F) +
        ((centerFieldEquiv hk hy α hα c) ^ 2 *
          spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
            (centerMap α hα a : Fin k ⊕ Fin k → F)) •
          (centerMap α hα x : Fin k ⊕ Fin k → F) := by
  have hx0 : (x : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    exact hxa (by rw [h0]; simp)
  have ha0 : (a : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    exact hxa (by rw [h0]; simp)
  have hfirst := congrArg Subtype.val
    (centerMap_add_eq_add_smul_of_sq_mul_spForm_eq_one hk hy α hα ha0 hc)
  have hc' : c ^ 2 * spForm k F (a : Fin k ⊕ Fin k → F) (x : Fin k ⊕ Fin k → F) = 1 := by
    rw [← CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt
      (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F)]
    exact hc
  have hsecond := congrArg Subtype.val
    (centerMap_add_eq_add_smul_of_sq_mul_spForm_eq_one hk hy α hα hx0 hc')
  rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt
    (centerMap α hα a : Fin k ⊕ Fin k → F)
    (centerMap α hα x : Fin k ⊕ Fin k → F)] at hsecond
  calc (centerMap α hα x : Fin k ⊕ Fin k → F) +
        ((centerFieldEquiv hk hy α hα c) ^ 2 *
          spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
            (centerMap α hα a : Fin k ⊕ Fin k → F)) •
          (centerMap α hα a : Fin k ⊕ Fin k → F) =
      (centerMap α hα (x + a) : Fin k ⊕ Fin k → F) := hfirst.symm
    _ = (centerMap α hα (a + x) : Fin k ⊕ Fin k → F) := by
      rw [show (x + a : vecPerp y) = a + x from add_comm x a]
    _ = (centerMap α hα a : Fin k ⊕ Fin k → F) +
        ((centerFieldEquiv hk hy α hα c) ^ 2 *
          spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
            (centerMap α hα a : Fin k ⊕ Fin k → F)) •
          (centerMap α hα x : Fin k ⊕ Fin k → F) := hsecond

private theorem centerMap_coefficient_eq_one [Fintype F] [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x a : vecPerp y}
    (hxa : spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) ≠ 0)
    {κ : F}
    (hsum : (centerMap α hα x : Fin k ⊕ Fin k → F) + κ •
        (centerMap α hα a : Fin k ⊕ Fin k → F) =
      (centerMap α hα a : Fin k ⊕ Fin k → F) + κ •
        (centerMap α hα x : Fin k ⊕ Fin k → F)) : κ = 1 := by
  by_contra hκ1
  have hvw := add_eq_zero_of_add_eq_add_smul hsum hκ1
  have hfxa : (centerMap α hα x : Fin k ⊕ Fin k → F) =
      (centerMap α hα a : Fin k ⊕ Fin k → F) := by
    have hneg : (centerMap α hα x : Fin k ⊕ Fin k → F) =
        -(centerMap α hα a : Fin k ⊕ Fin k → F) := eq_neg_of_add_eq_zero_left hvw
    rw [CFSG.ClassicalGroups.Orthogonal.neg_eq_self_of_two_eq_zero
      (CharTwo.two_eq_zero (R := F))] at hneg
    exact hneg
  have hxaeq : x = a := centerMap_injective α hα (Subtype.ext hfxa)
  exact hxa (by rw [hxaeq, spForm_isAlt.self_eq_zero])

private theorem centerMap_add_and_spForm_of_spForm_ne_zero [Fintype F] [CharP F 2]
    (hk : 2 ≤ k) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x a : vecPerp y}
    (hxa : spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) ≠ 0) :
    centerMap α hα (x + a) = centerMap α hα x + centerMap α hα a ∧
      spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα a : Fin k ⊕ Fin k → F) =
        centerFieldEquiv hk hy α hα (spForm k F (x : Fin k ⊕ Fin k → F)
          (a : Fin k ⊕ Fin k → F)) := by
  have hx0 : (x : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    apply hxa
    rw [h0]
    simp
  have ha0 : (a : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    apply hxa
    rw [h0]
    simp
  obtain ⟨c, hc, hc0⟩ := exists_sq_mul_eq_one hxa
  have hX := centerMap_add_eq_add_smul_of_sq_mul_spForm_eq_one hk hy α hα ha0 hc
  have hsum := centerMap_smul_swap_eq hk hy α hα hxa hc
  have hκ1 : (centerFieldEquiv hk hy α hα c) ^ 2 *
      spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα a : Fin k ⊕ Fin k → F) = 1 :=
    centerMap_coefficient_eq_one α hα hxa hsum
  have hσc : centerFieldEquiv hk hy α hα c ≠ 0 := by
    intro h0
    apply hc0
    exact (centerFieldEquiv hk hy α hα).injective (by rw [h0, map_zero])
  have hB : spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
      (centerMap α hα a : Fin k ⊕ Fin k → F) =
      centerFieldEquiv hk hy α hα (spForm k F (x : Fin k ⊕ Fin k → F)
        (a : Fin k ⊕ Fin k → F)) := by
    have h2 : (centerFieldEquiv hk hy α hα c) ^ 2 *
        centerFieldEquiv hk hy α hα (spForm k F (x : Fin k ⊕ Fin k → F)
          (a : Fin k ⊕ Fin k → F)) = 1 := by
      rw [← map_pow, ← map_mul, hc, map_one]
    exact mul_left_cancel₀ (pow_ne_zero 2 hσc) (hκ1.trans h2.symm)
  refine ⟨?_, hB⟩
  rw [hX, hκ1, one_smul]

private theorem centerMap_add_of_spForm_ne_zero [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x a : vecPerp y}
    (hxa : spForm k F (x : Fin k ⊕ Fin k → F) (a : Fin k ⊕ Fin k → F) ≠ 0) :
    centerMap α hα (x + a) = centerMap α hα x + centerMap α hα a :=
  (centerMap_add_and_spForm_of_spForm_ne_zero hk hy α hα hxa).1

private theorem centerMap_spForm_eq_sigma [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x z : vecPerp y} :
    spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
      (centerMap α hα z : Fin k ⊕ Fin k → F) =
      centerFieldEquiv hk hy α hα (spForm k F (x : Fin k ⊕ Fin k → F)
        (z : Fin k ⊕ Fin k → F)) := by
  by_cases hxz : spForm k F (x : Fin k ⊕ Fin k → F) (z : Fin k ⊕ Fin k → F) ≠ 0
  · exact (centerMap_add_and_spForm_of_spForm_ne_zero hk hy α hα hxz).2
  · push Not at hxz
    have h := (centerMap_spForm_eq_zero_iff α hα x z).mp hxz
    rw [h, hxz, map_zero]

private theorem spForm_selfVecPerp_eq_zero {y z : Fin k ⊕ Fin k → F} (hz : z ∈ vecPerp y) :
    spForm k F y z = 0 := by
  have h := spForm_isAlt.neg_eq z y
  rw [mem_vecPerp.mp hz] at h
  simpa using h.symm

private theorem centerMap_mem_span_of_mem_span [Fintype F] [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F} (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}) :
    (centerMap α hα x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y'} := by
  refine mem_span_of_forall_spForm_eq_zero ?_
  intro w hw
  obtain ⟨z, hz⟩ := centerMap_surjective α hα ⟨w, hw⟩
  have hwz : w = (centerMap α hα z : Fin k ⊕ Fin k → F) := (congrArg Subtype.val hz).symm
  rw [hwz, ← centerMap_spForm_eq_zero_iff α hα x z]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
  rw [← ht, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hzy : spForm k F y (z : Fin k ⊕ Fin k → F) = 0 := spForm_selfVecPerp_eq_zero z.2
  simp [hzy]

private theorem add_smul_selfVecPerp_notMem_span [CharP F 2]
    {y : Fin k ⊕ Fin k → F} {w : vecPerp y}
    (hw : (w : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) (d : F) :
    ((w + d • selfVecPerp y : vecPerp y) : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} := by
  rw [Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp]
  intro hmem
  apply hw
  have hd : d • y ∈ Submodule.span F {y} :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  have hsub := Submodule.sub_mem (Submodule.span F {y}) hmem hd
  simpa [add_sub_cancel_right] using hsub

private theorem spForm_centerMap_sub_centerMap_eq_zero [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {w : vecPerp y} (d : F) (u : vecPerp y) :
    spForm k F (centerMap α hα (w + d • selfVecPerp y) - centerMap α hα w :
      Fin k ⊕ Fin k → F) (centerMap α hα u : Fin k ⊕ Fin k → F) = 0 := by
  have hsub : spForm k F
      ((centerMap α hα (w + d • selfVecPerp y) : Fin k ⊕ Fin k → F) -
        (centerMap α hα w : Fin k ⊕ Fin k → F))
      (centerMap α hα u : Fin k ⊕ Fin k → F) =
      spForm k F (centerMap α hα (w + d • selfVecPerp y) : Fin k ⊕ Fin k → F)
        (centerMap α hα u : Fin k ⊕ Fin k → F) -
      spForm k F (centerMap α hα w : Fin k ⊕ Fin k → F)
        (centerMap α hα u : Fin k ⊕ Fin k → F) := by
    exact map_sub ((spForm k F).flip (centerMap α hα u : Fin k ⊕ Fin k → F)) _ _
  by_cases hu : (u : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
  · have hzu : (centerMap α hα u : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y'} :=
      centerMap_mem_span_of_mem_span α hα hu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hzu
    have h1 : spForm k F (centerMap α hα (w + d • selfVecPerp y) : Fin k ⊕ Fin k → F)
        (centerMap α hα u : Fin k ⊕ Fin k → F) = 0 := by
      rw [← ht, map_smul]
      simp [mem_vecPerp.mp (centerMap α hα (w + d • selfVecPerp y)).2]
    have h2 : spForm k F (centerMap α hα w : Fin k ⊕ Fin k → F)
        (centerMap α hα u : Fin k ⊕ Fin k → F) = 0 := by
      rw [← ht, map_smul]
      simp [mem_vecPerp.mp (centerMap α hα w).2]
    rw [hsub, h1, h2, sub_self]
  · have h1 : spForm k F (centerMap α hα (w + d • selfVecPerp y) : Fin k ⊕ Fin k → F)
        (centerMap α hα u : Fin k ⊕ Fin k → F) =
        centerFieldEquiv hk hy α hα (spForm k F
          ((w + d • selfVecPerp y : vecPerp y) : Fin k ⊕ Fin k → F) (u : Fin k ⊕ Fin k → F)) :=
      centerMap_spForm_eq_sigma hk hy α hα
    have h2 : spForm k F (centerMap α hα w : Fin k ⊕ Fin k → F)
        (centerMap α hα u : Fin k ⊕ Fin k → F) =
        centerFieldEquiv hk hy α hα (spForm k F (w : Fin k ⊕ Fin k → F)
          (u : Fin k ⊕ Fin k → F)) :=
      centerMap_spForm_eq_sigma hk hy α hα
    have h3 : spForm k F ((w + d • selfVecPerp y : vecPerp y) : Fin k ⊕ Fin k → F)
        (u : Fin k ⊕ Fin k → F) = spForm k F (w : Fin k ⊕ Fin k → F)
        (u : Fin k ⊕ Fin k → F) := by
      simp only [Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        spForm_selfVecPerp_eq_zero u.2, mul_zero, add_zero]
    rw [hsub, h1, h2, h3, sub_self]

private theorem centerMap_sub_mem_span [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {w : vecPerp y} (d : F) :
    (centerMap α hα (w + d • selfVecPerp y) - centerMap α hα w :
      Fin k ⊕ Fin k → F) ∈ Submodule.span F {y'} := by
  refine mem_span_of_forall_spForm_eq_zero ?_
  intro z hz
  obtain ⟨u, hu⟩ := centerMap_surjective α hα ⟨z, hz⟩
  have hzval : z = (centerMap α hα u : Fin k ⊕ Fin k → F) := (congrArg Subtype.val hu).symm
  rw [hzval]
  exact spForm_centerMap_sub_centerMap_eq_zero hk hy α hα d u

private theorem exists_radicalShift [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (w : vecPerp y) (d : F) :
    ∃ ν : F, ((w : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} →
        centerMap α hα (w + d • selfVecPerp y) =
          centerMap α hα w + ν • selfVecPerp y') ∧
      ((w : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y} → ν = 0) := by
  by_cases hw : (w : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
  · exact ⟨0, fun h => absurd hw h, fun _ => rfl⟩
  · obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp
      (centerMap_sub_mem_span hk hy α hα d)
    refine ⟨ν, fun _ => ?_, fun h => absurd h hw⟩
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp]
    have h := hν.symm
    rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]

private noncomputable def radicalShift [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (w : vecPerp y) (d : F) : F :=
  Classical.choose (exists_radicalShift hk hy α hα w d)

private theorem radicalShift_apply [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {w : vecPerp y} (hw : (w : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) (d : F) :
    centerMap α hα (w + d • selfVecPerp y) =
      centerMap α hα w + radicalShift hk hy α hα w d • selfVecPerp y' :=
  (Classical.choose_spec (exists_radicalShift hk hy α hα w d)).1 hw

private theorem add_smul_selfVecPerp_injective [CharP F 2] {y' : Fin k ⊕ Fin k → F}
    (hy' : y' ≠ 0) {a : vecPerp y'} {ν μ : F}
    (h : a + ν • selfVecPerp y' = a + μ • selfVecPerp y') : ν = μ := by
  have h' := add_left_cancel h
  have hval := congrArg Subtype.val h'
  simp only [Submodule.coe_smul, coe_selfVecPerp] at hval
  exact smul_left_injective F hy' hval

private theorem radicalShift_eq_add_of_spForm_ne_zero [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {w u : vecPerp y} (hw : (w : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hwu : spForm k F (w : Fin k ⊕ Fin k → F) (u : Fin k ⊕ Fin k → F) ≠ 0) (d : F) :
    radicalShift hk hy α hα w d = radicalShift hk hy α hα (w + u) d := by
  have hwunot : ((w + u : vecPerp y) : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} := by
    intro hmem
    apply hwu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have hwuval : (w : Fin k ⊕ Fin k → F) + (u : Fin k ⊕ Fin k → F) = t • y := by
      simpa using ht.symm
    have hu_eq : (u : Fin k ⊕ Fin k → F) = t • y - (w : Fin k ⊕ Fin k → F) := by
      rw [← hwuval]
      abel
    rw [hu_eq, map_sub, map_smul]
    simp [mem_vecPerp.mp w.2, spForm_isAlt.self_eq_zero]
  have hB : spForm k F ((w + d • selfVecPerp y : vecPerp y) : Fin k ⊕ Fin k → F)
      (u : Fin k ⊕ Fin k → F) ≠ 0 := by
    simp only [Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_selfVecPerp_eq_zero u.2, mul_zero, add_zero]
    exact hwu
  have h1 := centerMap_add_of_spForm_ne_zero hk hy α hα (x := w + d • selfVecPerp y) (a := u) hB
  have h2 := centerMap_add_of_spForm_ne_zero hk hy α hα (x := w) (a := u) hwu
  have h3 := radicalShift_apply hk hy α hα hw d
  have h4 := radicalShift_apply hk hy α hα hwunot d
  have heq : (w + d • selfVecPerp y) + u = (w + u) + d • selfVecPerp y := by abel
  have hA : centerMap α hα ((w + d • selfVecPerp y) + u) =
      (centerMap α hα w + radicalShift hk hy α hα w d • selfVecPerp y') +
        centerMap α hα u := by
    rw [h1, h3]
  have hB' : centerMap α hα ((w + u) + d • selfVecPerp y) =
      (centerMap α hα w + centerMap α hα u) +
        radicalShift hk hy α hα (w + u) d • selfVecPerp y' := by
    rw [h4, h2]
  have hcomb : (centerMap α hα w + radicalShift hk hy α hα w d • selfVecPerp y') +
        centerMap α hα u =
      (centerMap α hα w + centerMap α hα u) +
        radicalShift hk hy α hα (w + u) d • selfVecPerp y' := by
    rw [← hA, heq, hB']
  have hcomb' : (centerMap α hα w + centerMap α hα u) +
        radicalShift hk hy α hα w d • selfVecPerp y' =
      (centerMap α hα w + centerMap α hα u) +
        radicalShift hk hy α hα (w + u) d • selfVecPerp y' := by
    rw [← hcomb]
    abel
  exact add_smul_selfVecPerp_injective hy' hcomb'

private theorem radicalShift_eq_of_spForm_ne_zero [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {w u : vecPerp y} (hw : (w : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hu : (u : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hwu : spForm k F (w : Fin k ⊕ Fin k → F) (u : Fin k ⊕ Fin k → F) ≠ 0) (d : F) :
    radicalShift hk hy α hα w d = radicalShift hk hy α hα u d := by
  have h1 := radicalShift_eq_add_of_spForm_ne_zero hk hy hy' α hα hw hwu d
  have hwu' : spForm k F (u : Fin k ⊕ Fin k → F) (w : Fin k ⊕ Fin k → F) ≠ 0 := by
    rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt
      (w : Fin k ⊕ Fin k → F) (u : Fin k ⊕ Fin k → F)] at hwu
  have h2 := radicalShift_eq_add_of_spForm_ne_zero hk hy hy' α hα hu hwu' d
  rw [h1, h2, add_comm u w]

private theorem radicalShift_eq [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {w u : vecPerp y} (hw : (w : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hu : (u : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) (d : F) :
    radicalShift hk hy α hα w d = radicalShift hk hy α hα u d := by
  obtain ⟨v, hv, hwv, huv⟩ := exists_mem_vecPerp_spForm_ne_zero_pair hw hu
  have hvnot : (v : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} := by
    intro hvspan
    apply hwv
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hvspan
    rw [← ht, map_smul]
    simp [mem_vecPerp.mp w.2]
  have h1 : radicalShift hk hy α hα w d = radicalShift hk hy α hα ⟨v, hv⟩ d :=
    radicalShift_eq_of_spForm_ne_zero hk hy hy' α hα hw hvnot hwv d
  have h2 : radicalShift hk hy α hα u d = radicalShift hk hy α hα ⟨v, hv⟩ d :=
    radicalShift_eq_of_spForm_ne_zero hk hy hy' α hα hu hvnot huv d
  rw [h1, h2]

private noncomputable def radicalScalar [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (d : F) : F :=
  radicalShift hk hy α hα (basePoint hk hy) d

private theorem radicalScalar_apply [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {w : vecPerp y} (hw : (w : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) (d : F) :
    centerMap α hα (w + d • selfVecPerp y) =
      centerMap α hα w + radicalScalar hk hy α hα d • selfVecPerp y' := by
  rw [radicalShift_apply hk hy α hα hw d,
    show radicalShift hk hy α hα w d = radicalScalar hk hy α hα d from
      radicalShift_eq hk hy hy' α hα hw (basePoint_notMem hk hy) d]

private theorem radicalScalar_mul [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (c d : F) : radicalScalar hk hy α hα (c * d) =
      centerFieldEquiv hk hy α hα c * radicalScalar hk hy α hα d := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_mul, map_zero, zero_mul]
    have hw := basePoint_notMem hk hy
    have h : centerMap α hα (basePoint hk hy + (0 : F) • selfVecPerp y) =
        centerMap α hα (basePoint hk hy) + radicalScalar hk hy α hα 0 • selfVecPerp y' :=
      radicalScalar_apply hk hy hy' α hα hw (0 : F)
    rw [zero_smul, add_zero] at h
    have h0 : centerMap α hα (basePoint hk hy) + (0 : F) • selfVecPerp y' =
        centerMap α hα (basePoint hk hy) + radicalScalar hk hy α hα 0 • selfVecPerp y' := by
      rw [zero_smul, add_zero]
      exact h
    exact (add_smul_selfVecPerp_injective hy' h0).symm
  have hw := basePoint_notMem hk hy
  have hwd : ((basePoint hk hy + d • selfVecPerp y : vecPerp y) : Fin k ⊕ Fin k → F) ∉
      Submodule.span F {y} := add_smul_selfVecPerp_notMem_span hw d
  have hcw : ((c • basePoint hk hy : vecPerp y) : Fin k ⊕ Fin k → F) ∉
      Submodule.span F {y} := (Submodule.smul_mem_iff _ hc).not.mpr hw
  have h1 : centerMap α hα (basePoint hk hy + d • selfVecPerp y) =
      centerMap α hα (basePoint hk hy) + radicalScalar hk hy α hα d • selfVecPerp y' :=
    radicalScalar_apply hk hy hy' α hα hw d
  have h2 : centerMap α hα (c • (basePoint hk hy + d • selfVecPerp y)) =
      centerFieldEquiv hk hy α hα c •
        centerMap α hα (basePoint hk hy + d • selfVecPerp y) :=
    centerMap_smul_of_notMem hk hy α hα hwd c
  have h3 : centerMap α hα (c • basePoint hk hy + (c * d) • selfVecPerp y) =
      centerMap α hα (c • basePoint hk hy) +
        radicalScalar hk hy α hα (c * d) • selfVecPerp y' :=
    radicalScalar_apply hk hy hy' α hα hcw (c * d)
  have h4 : centerMap α hα (c • basePoint hk hy) =
      centerFieldEquiv hk hy α hα c • centerMap α hα (basePoint hk hy) :=
    centerMap_smul_of_notMem hk hy α hα hw c
  have heq : (c • (basePoint hk hy + d • selfVecPerp y : vecPerp y) : vecPerp y) =
      (c • basePoint hk hy + (c * d) • selfVecPerp y : vecPerp y) := by
    rw [smul_add, smul_smul]
  have hval : centerFieldEquiv hk hy α hα c • centerMap α hα (basePoint hk hy) +
        radicalScalar hk hy α hα (c * d) • selfVecPerp y' =
      centerFieldEquiv hk hy α hα c • centerMap α hα (basePoint hk hy) +
        (centerFieldEquiv hk hy α hα c * radicalScalar hk hy α hα d) • selfVecPerp y' := by
    rw [← h4, ← h3, ← heq, h2, h1, smul_add, smul_smul, h4]
  exact add_smul_selfVecPerp_injective hy' hval

private theorem radicalScalar_eq_sigma_mul_one [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0) (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (d : F) : radicalScalar hk hy α hα d =
      centerFieldEquiv hk hy α hα d * radicalScalar hk hy α hα 1 := by
  have h := radicalScalar_mul hk hy hy' α hα d 1
  rwa [mul_one] at h

private theorem spTransvection_mul_of_isotropic_plane [CharP F 2]
    {x y : Fin k ⊕ Fin k → F} (hxy : spForm k F x y = 0) (b s : F) :
    spTransvection x 1 * spTransvection (b • x + ((1 + b) * s) • y) 1 *
      spTransvection ((1 + b) • x + (b * s) • y) 1 = spTransvection (s • y) 1 := by
  have hxy' : spForm k F y x = 0 := by
    rw [← CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt x y]
    exact hxy
  have huw : spForm k F (s • y) (x + s • y) = 0 := by
    simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, hxy', mul_zero, add_zero]
  have h1 : s • y + b • (x + s • y) = b • x + ((1 + b) * s) • y := by
    module
  have h2 : s • y + (x + s • y) = x := by
    rw [show s • y + (x + s • y) = x + (s • y + s • y) by abel,
      ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have h3 : s • y + (b + 1) • (x + s • y) = (1 + b) • x + (b * s) • y := by
    rw [show s • y + (b + 1) • (x + s • y) =
        (1 + b) • x + (s + (1 + b) * s) • y by module,
      show s + (1 + b) * s = b * s by
        rw [add_mul, one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]]
  have hxu : spForm k F x (b • x + ((1 + b) * s) • y) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, spForm_isAlt.self_eq_zero, hxy, mul_zero,
      add_zero]
  have hcomm : spTransvection x 1 *
      spTransvection (b • x + ((1 + b) * s) • y) 1 =
      spTransvection (b • x + ((1 + b) * s) • y) 1 * spTransvection x 1 := by
    have hu : spEnd (spTransvection (b • x + ((1 + b) * s) • y) 1) x = x := by
      rw [spEnd_spTransvection, hxu, mul_zero, zero_smul, add_zero]
    exact CFSG.RankThree.PartOne.CTP.commute_spTransvection hu 1
  have h := CFSG.OddTranspositions.PartThree.spTransvection_eq_mul_mul
    (u := s • y) (w := x + s • y) (c := 1) (l := b) huw
  rw [h1, h2, h3] at h
  rw [hcomm, ← h]

private theorem smul_selfVecPerp_ne_zero {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) {s : F}
    (hs : s ≠ 0) : (s • selfVecPerp y : vecPerp y) ≠ 0 := by
  intro h0
  have h0' : s • (selfVecPerp y : Fin k ⊕ Fin k → F) = 0 := congrArg Subtype.val h0
  rcases smul_eq_zero.mp h0' with h1 | h1
  · exact hs h1
  · rw [coe_selfVecPerp] at h1
    exact hy h1

private theorem centerMap_spTransvection_mul_three_eq [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F} (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x u2 u3 : vecPerp y} {s : F}
    (hx0 : (x : Fin k ⊕ Fin k → F) ≠ 0) (hu20 : (u2 : Fin k ⊕ Fin k → F) ≠ 0)
    (hu30 : (u3 : Fin k ⊕ Fin k → F) ≠ 0)
    (hsY : (s • selfVecPerp y : vecPerp y) ≠ 0)
    (hsource : spTransvection (x : Fin k ⊕ Fin k → F) 1 *
      spTransvection (u2 : Fin k ⊕ Fin k → F) 1 *
      spTransvection (u3 : Fin k ⊕ Fin k → F) 1 = spTransvection (s • y) 1) :
    spTransvection (centerMap α hα x : Fin k ⊕ Fin k → F) 1 *
      spTransvection (centerMap α hα u2 : Fin k ⊕ Fin k → F) 1 *
      spTransvection (centerMap α hα u3 : Fin k ⊕ Fin k → F) 1 =
      spTransvection (centerMap α hα (s • selfVecPerp y) : Fin k ⊕ Fin k → F) 1 := by
  let F1 : ↥(fixing {y}) := ⟨spTransvection (x : Fin k ⊕ Fin k → F) 1,
    (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp x.2)⟩
  let F2 : ↥(fixing {y}) := ⟨spTransvection (u2 : Fin k ⊕ Fin k → F) 1,
    (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp u2.2)⟩
  let F3 : ↥(fixing {y}) := ⟨spTransvection (u3 : Fin k ⊕ Fin k → F) 1,
    (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp u3.2)⟩
  let G : ↥(fixing {y}) := ⟨spTransvection (s • (selfVecPerp y : Fin k ⊕ Fin k → F)) 1,
    (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr
      (mem_vecPerp.mp (s • selfVecPerp y).2)⟩
  have hGval : (G : StatedSp k F) = spTransvection (s • y) 1 := by
    simp [G, coe_selfVecPerp]
  have hFprod : F1 * F2 * F3 = G := by
    apply Subtype.ext
    simp only [F1, F2, F3, Subgroup.coe_mul, hGval]
    exact hsource
  have himg := congrArg (fun p : ↥(fixing {y}) => (α p : ↥(StatedSp k F))) hFprod
  rw [map_mul, map_mul] at himg
  simp only [F1, F2, F3, G, Subgroup.coe_mul] at himg
  rw [centerMap_apply α hα x hx0, centerMap_apply α hα u2 hu20,
    centerMap_apply α hα u3 hu30] at himg
  have hGs : (α G : StatedSp k F) =
      spTransvection (centerMap α hα (s • selfVecPerp y) : Fin k ⊕ Fin k → F) 1 := by
    simpa [G] using centerMap_apply α hα (s • selfVecPerp y) (by
      intro h0
      exact hsY (Subtype.ext h0))
  rw [hGs] at himg
  simpa using himg

private theorem centerMap_smul_selfVecPerp_product [Fintype F] [CharP F 2]
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x : vecPerp y} (hxnot : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hx0 : (x : Fin k ⊕ Fin k → F) ≠ 0)
    {b s : F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hs : s ≠ 0) :
    let u2 : vecPerp y := b • x + ((1 + b) * s) • selfVecPerp y
    let u3 : vecPerp y := (1 + b) • x + (b * s) • selfVecPerp y
    spTransvection (centerMap α hα x : Fin k ⊕ Fin k → F) 1 *
      spTransvection (centerMap α hα u2 : Fin k ⊕ Fin k → F) 1 *
      spTransvection (centerMap α hα u3 : Fin k ⊕ Fin k → F) 1 =
      spTransvection (centerMap α hα (s • selfVecPerp y) : Fin k ⊕ Fin k → F) 1 := by
  let u2 : vecPerp y := b • x + ((1 + b) * s) • selfVecPerp y
  let u3 : vecPerp y := (1 + b) • x + (b * s) • selfVecPerp y
  have hbxn : ((b • x : vecPerp y) : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} :=
    (Submodule.smul_mem_iff _ hb0).not.mpr hxnot
  have h1b : (1 + b : F) ≠ 0 := fun h => hb1 (CharTwo.add_eq_zero.mp h).symm
  have h1bxn : (((1 + b) • x : vecPerp y) : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} :=
    (Submodule.smul_mem_iff _ h1b).not.mpr hxnot
  have hu2not : (u2 : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} :=
    add_smul_selfVecPerp_notMem_span (w := b • x) hbxn ((1 + b) * s)
  have hu3not : (u3 : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} :=
    add_smul_selfVecPerp_notMem_span (w := (1 + b) • x) h1bxn (b * s)
  have hu20 : (u2 : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    exact hu2not (by rw [h0]; exact Submodule.zero_mem _)
  have hu30 : (u3 : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    exact hu3not (by rw [h0]; exact Submodule.zero_mem _)
  have hsY := smul_selfVecPerp_ne_zero hy hs
  have hsource : spTransvection (x : Fin k ⊕ Fin k → F) 1 *
      spTransvection (u2 : Fin k ⊕ Fin k → F) 1 *
      spTransvection (u3 : Fin k ⊕ Fin k → F) 1 = spTransvection (s • y) 1 := by
    simpa [u2, u3, Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp] using
      spTransvection_mul_of_isotropic_plane (x := (x : Fin k ⊕ Fin k → F)) (y := y)
        (mem_vecPerp.mp x.2) b s
  exact centerMap_spTransvection_mul_three_eq α hα hx0 hu20 hu30 hsY hsource

private theorem centerMap_smul_selfVecPerp_values [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x : vecPerp y} (hxnot : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    {b s : F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    let b' : F := centerFieldEquiv hk hy α hα b
    let s' : F := centerFieldEquiv hk hy α hα s * radicalScalar hk hy α hα 1
    (centerMap α hα (b • x + ((1 + b) * s) • selfVecPerp y) : Fin k ⊕ Fin k → F) =
        b' • (centerMap α hα x : Fin k ⊕ Fin k → F) + ((1 + b') * s') •
          (y' : Fin k ⊕ Fin k → F) ∧
      (centerMap α hα ((1 + b) • x + (b * s) • selfVecPerp y) : Fin k ⊕ Fin k → F) =
        (1 + b') • (centerMap α hα x : Fin k ⊕ Fin k → F) + (b' * s') •
          (y' : Fin k ⊕ Fin k → F) := by
  have hbxn : ((b • x : vecPerp y) : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} :=
    (Submodule.smul_mem_iff _ hb0).not.mpr hxnot
  have h1b : (1 + b : F) ≠ 0 := fun h => hb1 (CharTwo.add_eq_zero.mp h).symm
  have h1bxn : (((1 + b) • x : vecPerp y) : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} :=
    (Submodule.smul_mem_iff _ h1b).not.mpr hxnot
  let b' : F := centerFieldEquiv hk hy α hα b
  let s' : F := centerFieldEquiv hk hy α hα s * radicalScalar hk hy α hα 1
  have hσ1b : centerFieldEquiv hk hy α hα (1 + b) = 1 + b' := by
    simp [b', map_add]
  have h2 : centerMap α hα (b • x) = b' • centerMap α hα x := by
    simpa [b'] using centerMap_smul_of_notMem (x := x) hk hy α hα hxnot b
  have h3 : radicalScalar hk hy α hα ((1 + b) * s) = (1 + b') * s' := by
    rw [radicalScalar_mul hk hy hy' α hα (1 + b) s,
      radicalScalar_eq_sigma_mul_one hk hy hy' α hα s, hσ1b]
  have h4 : radicalScalar hk hy α hα (b * s) = b' * s' := by
    rw [radicalScalar_mul hk hy hy' α hα b s,
      radicalScalar_eq_sigma_mul_one hk hy hy' α hα s]
  refine ⟨?_, ?_⟩
  · have h := radicalScalar_apply hk hy hy' α hα (w := b • x) hbxn ((1 + b) * s)
    rw [h, h2, h3]
    simp only [Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp, b', s']
  · have h := radicalScalar_apply hk hy hy' α hα (w := (1 + b) • x) h1bxn (b * s)
    have h2' : centerMap α hα ((1 + b) • x) = (1 + b') • centerMap α hα x := by
      simpa [hσ1b] using centerMap_smul_of_notMem (x := x) hk hy α hα hxnot (1 + b)
    rw [h, h2', h4]
    simp only [Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp, b', s']

private theorem centerMap_smul_selfVecPerp_aux [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {s : F} (hs : s ≠ 0) :
    centerMap α hα (s • selfVecPerp y) =
      (centerFieldEquiv hk hy α hα s * radicalScalar hk hy α hα 1) • selfVecPerp y' := by
  have h4 : 4 ≤ Nat.card F := by simpa [Nat.card_eq_fintype_card] using hF
  obtain ⟨b, hb0, hb1⟩ := exists_ne_zero_ne_one_of_four_le h4
  let x : vecPerp y := basePoint hk hy
  let u2 : vecPerp y := b • x + ((1 + b) * s) • selfVecPerp y
  let u3 : vecPerp y := (1 + b) • x + (b * s) • selfVecPerp y
  let b' : F := centerFieldEquiv hk hy α hα b
  let s' : F := centerFieldEquiv hk hy α hα s * radicalScalar hk hy α hα 1
  have hxnot : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} := basePoint_notMem hk hy
  have hx0 : (x : Fin k ⊕ Fin k → F) ≠ 0 := basePoint_ne_zero hk hy
  have himg : spTransvection (centerMap α hα x : Fin k ⊕ Fin k → F) 1 *
      spTransvection (centerMap α hα u2 : Fin k ⊕ Fin k → F) 1 *
      spTransvection (centerMap α hα u3 : Fin k ⊕ Fin k → F) 1 =
      spTransvection (centerMap α hα (s • selfVecPerp y) : Fin k ⊕ Fin k → F) 1 := by
    simpa [x, u2, u3] using centerMap_smul_selfVecPerp_product hy α hα hxnot hx0 hb0 hb1 hs
  obtain ⟨hu2eq, hu3eq⟩ := centerMap_smul_selfVecPerp_values hk hy hy' α hα hxnot hb0 hb1
  have hb'0 : b' ≠ 0 := by
    intro h0
    apply hb0
    apply (centerFieldEquiv hk hy α hα).injective
    have h0' : centerFieldEquiv hk hy α hα b = 0 := h0
    rw [h0', map_zero]
  have hb'1 : b' ≠ 1 := by
    intro h0
    apply hb1
    apply (centerFieldEquiv hk hy α hα).injective
    have h0' : centerFieldEquiv hk hy α hα b = 1 := h0
    rw [h0', map_one]
  have htarget := spTransvection_mul_of_isotropic_plane
    (x := (centerMap α hα x : Fin k ⊕ Fin k → F)) (y := y')
    (mem_vecPerp.mp (centerMap α hα x).2) b' s'
  have hT : spTransvection (centerMap α hα (s • selfVecPerp y) : Fin k ⊕ Fin k → F) 1 =
      spTransvection (s' • (y' : Fin k ⊕ Fin k → F)) 1 := by
    rw [← himg, hu2eq, hu3eq]
    exact htarget
  have hval : (centerMap α hα (s • selfVecPerp y) : Fin k ⊕ Fin k → F) =
      s' • (y' : Fin k ⊕ Fin k → F) := spTransvection_one_eq_iff.mp hT
  apply Subtype.ext
  rw [hval]
  simp only [Submodule.coe_smul, coe_selfVecPerp, s']

private theorem radicalScalar_one_eq_one [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) :
    radicalScalar hk hy α hα 1 = 1 := by
  have h : centerMap α hα ((1 : F) • selfVecPerp y) =
      (centerFieldEquiv hk hy α hα 1 * radicalScalar hk hy α hα 1) • selfVecPerp y' :=
    centerMap_smul_selfVecPerp_aux hk hF hy hy' α hα one_ne_zero
  rw [one_smul, centerMap_self hy α hα hαy] at h
  have hσ1 : centerFieldEquiv hk hy α hα 1 = 1 := map_one _
  rw [hσ1, one_mul] at h
  have hv := congrArg Subtype.val h
  simp only [Submodule.coe_smul, coe_selfVecPerp] at hv
  have hv' : (1 : F) • y' = radicalScalar hk hy α hα 1 • y' := by
    rw [one_smul]
    exact hv
  exact (smul_left_injective F hy' hv').symm

private theorem centerMap_smul_selfVecPerp [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) (s : F) :
    centerMap α hα (s • selfVecPerp y) = centerFieldEquiv hk hy α hα s • selfVecPerp y' := by
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, centerMap_zero, map_zero, zero_smul]
  · rw [centerMap_smul_selfVecPerp_aux hk hF hy hy' α hα hs,
      radicalScalar_one_eq_one hk hF hy hy' α hα hαy, mul_one]

private theorem exists_mem_vecPerp_forall_spForm_right_ne_zero [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) {y : Fin k ⊕ Fin k → F} (a : Fin 3 → vecPerp y)
    (has : ∀ i, (a i : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) :
    ∃ v : vecPerp y, ∀ i, spForm k F (v : Fin k ⊕ Fin k → F)
      (a i : Fin k ⊕ Fin k → F) ≠ 0 := by
  classical
  let p : Fin 3 → Submodule F (vecPerp y) := fun i =>
    LinearMap.ker (((spForm k F).flip (a i : Fin k ⊕ Fin k → F)).comp (vecPerp y).subtype)
  have hproper : ∀ i, p i ≠ ⊤ := by
    intro i htop
    obtain ⟨v, hv, hva⟩ := exists_mem_vecPerp_spForm_ne_zero (has i)
    have : (⟨v, hv⟩ : vecPerp y) ∈ p i := by
      rw [htop]
      exact Submodule.mem_top
    exact hva (LinearMap.mem_ker.mp this)
  have h4 : 3 < Fintype.card F := by
    have := hF
    omega
  have hcard : (Finset.univ : Finset (Fin 3)).card < ENat.card F := by
    rw [Finset.card_univ, Fintype.card_fin, ENat.card_eq_coe_natCard,
      Nat.card_eq_fintype_card]
    exact_mod_cast h4
  have hunion := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
    (s := (Finset.univ : Finset (Fin 3))) (p := p) hproper hcard
  obtain ⟨v, -, hvnot⟩ := Set.exists_of_ssubset hunion
  refine ⟨v, fun i => ?_⟩
  intro hzero
  exact hvnot (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
    ⟨Finset.mem_univ i, LinearMap.mem_ker.mpr hzero⟩⟩)

private theorem exists_mem_vecPerp_forall_spForm_ne_zero [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) {y x z w : Fin k ⊕ Fin k → F}
    (hx : x ∈ vecPerp y) (hz : z ∈ vecPerp y) (hw : w ∈ vecPerp y)
    (hxs : x ∉ Submodule.span F {y}) (hzs : z ∉ Submodule.span F {y})
    (hws : w ∉ Submodule.span F {y}) :
    ∃ v : vecPerp y, spForm k F x (v : Fin k ⊕ Fin k → F) ≠ 0 ∧
      spForm k F z (v : Fin k ⊕ Fin k → F) ≠ 0 ∧
      spForm k F w (v : Fin k ⊕ Fin k → F) ≠ 0 := by
  let a : Fin 3 → vecPerp y := ![⟨x, hx⟩, ⟨z, hz⟩, ⟨w, hw⟩]
  have has : ∀ i, (a i : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y} := by
    intro i
    fin_cases i
    · exact hxs
    · exact hzs
    · exact hws
  obtain ⟨v, hv⟩ := exists_mem_vecPerp_forall_spForm_right_ne_zero hF a has
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [← CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt (v : Fin k ⊕ Fin k → F) x]
    exact hv 0
  · rw [← CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt (v : Fin k ⊕ Fin k → F) z]
    exact hv 1
  · rw [← CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt (v : Fin k ⊕ Fin k → F) w]
    exact hv 2

private theorem centerMap_add_of_mem_span_both [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1)
    {x z : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y})
    (hz : (z : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}) :
    centerMap α hα (x + z) = centerMap α hα x + centerMap α hα z := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hz
  have hx' : x = a • selfVecPerp y := Subtype.ext (by
    rw [Submodule.coe_smul, coe_selfVecPerp]
    exact ha.symm)
  have hz' : z = b • selfVecPerp y := Subtype.ext (by
    rw [Submodule.coe_smul, coe_selfVecPerp]
    exact hb.symm)
  have hxzy : x + z = (a + b) • selfVecPerp y := by
    apply Subtype.ext
    rw [Submodule.coe_add, ha.symm, hb.symm, Submodule.coe_smul, coe_selfVecPerp, add_smul]
  rw [hxzy, hx', hz', centerMap_smul_selfVecPerp hk hF hy hy' α hα hαy (a + b),
    centerMap_smul_selfVecPerp hk hF hy hy' α hα hαy a,
    centerMap_smul_selfVecPerp hk hF hy hy' α hα hαy b, map_add, add_smul]

private theorem centerMap_add_of_mem_span_left [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1)
    {x z : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y})
    (hz : (z : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) :
    centerMap α hα (x + z) = centerMap α hα x + centerMap α hα z := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  have hx' : x = a • selfVecPerp y := Subtype.ext (by
    rw [Submodule.coe_smul, coe_selfVecPerp]
    exact ha.symm)
  have hnu : radicalScalar hk hy α hα a = centerFieldEquiv hk hy α hα a := by
    rw [radicalScalar_eq_sigma_mul_one hk hy hy' α hα a,
      radicalScalar_one_eq_one hk hF hy hy' α hα hαy, mul_one]
  have hxz : x + z = z + a • selfVecPerp y := by
    rw [hx']
    abel
  rw [hxz, radicalScalar_apply hk hy hy' α hα hz a, hx',
    centerMap_smul_selfVecPerp hk hF hy hy' α hα hαy a, hnu]
  exact add_comm _ _

private theorem centerMap_add_of_mem_span_right [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1)
    {x z : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hz : (z : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}) :
    centerMap α hα (x + z) = centerMap α hα x + centerMap α hα z := by
  rw [add_comm x z, centerMap_add_of_mem_span_left hk hF hy hy' α hα hαy hz hx, add_comm]

private theorem centerMap_add_of_orthogonal_of_add_mem_span [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1)
    {x z : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hsum : ((x + z : vecPerp y) : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}) :
    centerMap α hα (x + z) = centerMap α hα x + centerMap α hα z := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsum
  have hxvz : (x : Fin k ⊕ Fin k → F) + (z : Fin k ⊕ Fin k → F) = a • y := by
    simpa [Submodule.coe_add] using ha.symm
  have hz_eq : z = x + a • selfVecPerp y := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, coe_selfVecPerp]
    have hzsub : (z : Fin k ⊕ Fin k → F) = a • y - (x : Fin k ⊕ Fin k → F) := by
      rw [← hxvz]
      abel
    rw [hzsub, sub_eq_add_neg, CFSG.ClassicalGroups.Orthogonal.neg_eq_self_of_two_eq_zero
      (CharTwo.two_eq_zero (R := F))]
    abel
  have hxzs : x + z = a • selfVecPerp y := by
    apply Subtype.ext
    rw [Submodule.coe_add, hxvz, Submodule.coe_smul, coe_selfVecPerp]
  have hnu : radicalScalar hk hy α hα a = centerFieldEquiv hk hy α hα a := by
    rw [radicalScalar_eq_sigma_mul_one hk hy hy' α hα a,
      radicalScalar_one_eq_one hk hF hy hy' α hα hαy, mul_one]
  have htwoV : (centerMap α hα x : Fin k ⊕ Fin k → F) +
      (centerMap α hα x : Fin k ⊕ Fin k → F) = 0 := by
    rw [← two_smul (R := F), CharTwo.two_eq_zero, zero_smul]
  have htwo : (centerMap α hα x + centerMap α hα x : vecPerp y') = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_add]
    exact htwoV
  rw [hxzs, centerMap_smul_selfVecPerp hk hF hy hy' α hα hαy a, hz_eq,
    radicalScalar_apply hk hy hy' α hα hx a, hnu]
  rw [← add_assoc]
  rw [htwo, zero_add]

private theorem centerMap_add_of_orthogonal_of_add_notMem_span [Fintype F] [CharP F 2]
    (hk : 2 ≤ k) (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x z : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hz : (z : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hxz : spForm k F (x : Fin k ⊕ Fin k → F) (z : Fin k ⊕ Fin k → F) = 0)
    (hsum : ((x + z : vecPerp y) : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y}) :
    centerMap α hα (x + z) = centerMap α hα x + centerMap α hα z := by
  obtain ⟨v, hxv, hzv, hxzv⟩ := exists_mem_vecPerp_forall_spForm_ne_zero hF x.2 z.2
    (x + z).2 hx hz hsum
  have hxz' : spForm k F ((x + v : vecPerp y) : Fin k ⊕ Fin k → F)
      (z : Fin k ⊕ Fin k → F) ≠ 0 := by
    rw [Submodule.coe_add, map_add, LinearMap.add_apply, hxz, zero_add]
    rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt
      (z : Fin k ⊕ Fin k → F) (v : Fin k ⊕ Fin k → F)] at hzv
  have h1 := centerMap_add_of_spForm_ne_zero hk hy α hα (x := x + v) (a := z) hxz'
  have h2 := centerMap_add_of_spForm_ne_zero hk hy α hα (x := x) (a := v) hxv
  have h3 := centerMap_add_of_spForm_ne_zero hk hy α hα (x := x + z) (a := v) hxzv
  have hleft : centerMap α hα ((x + v) + z) =
      (centerMap α hα x + centerMap α hα v) + centerMap α hα z := by
    rw [h1, h2]
  have hright : centerMap α hα ((x + z) + v) =
      centerMap α hα (x + z) + centerMap α hα v := h3
  have heq : ((x + v) + z) = ((x + z) + v) := by abel
  have hEq : (centerMap α hα x + centerMap α hα v) + centerMap α hα z =
      centerMap α hα (x + z) + centerMap α hα v := by
    rw [← hleft, heq, hright]
  have key : (centerMap α hα x + centerMap α hα z) + centerMap α hα v =
      centerMap α hα (x + z) + centerMap α hα v := by
    rw [← hEq]
    abel
  exact (add_right_cancel key).symm

private theorem centerMap_add_of_orthogonal_notMem_span [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1)
    {x z : vecPerp y} (hx : (x : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hz : (z : Fin k ⊕ Fin k → F) ∉ Submodule.span F {y})
    (hxz : spForm k F (x : Fin k ⊕ Fin k → F) (z : Fin k ⊕ Fin k → F) = 0) :
    centerMap α hα (x + z) = centerMap α hα x + centerMap α hα z := by
  by_cases hsum : ((x + z : vecPerp y) : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
  · exact centerMap_add_of_orthogonal_of_add_mem_span hk hF hy hy' α hα hαy hx hsum
  · exact centerMap_add_of_orthogonal_of_add_notMem_span hk hF hy α hα hx hz hxz hsum

private theorem centerMap_add [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) (x z : vecPerp y) :
    centerMap α hα (x + z) = centerMap α hα x + centerMap α hα z := by
  by_cases hx0 : (x : Fin k ⊕ Fin k → F) = 0
  · have hx : x = 0 := Subtype.ext hx0
    subst hx
    rw [zero_add, centerMap_zero, zero_add]
  by_cases hz0 : (z : Fin k ⊕ Fin k → F) = 0
  · have hz : z = 0 := Subtype.ext hz0
    subst hz
    rw [add_zero, centerMap_zero, add_zero]
  by_cases hxs : (x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
  · by_cases hzs : (z : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
    · exact centerMap_add_of_mem_span_both hk hF hy hy' α hα hαy hxs hzs
    · exact centerMap_add_of_mem_span_left hk hF hy hy' α hα hαy hxs hzs
  · by_cases hzs : (z : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
    · exact centerMap_add_of_mem_span_right hk hF hy hy' α hα hαy hxs hzs
    · by_cases hxz : spForm k F (x : Fin k ⊕ Fin k → F) (z : Fin k ⊕ Fin k → F) = 0
      · exact centerMap_add_of_orthogonal_notMem_span hk hF hy hy' α hα hαy hxs hzs hxz
      · exact centerMap_add_of_spForm_ne_zero hk hy α hα hxz

private theorem centerMap_smul [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) (x : vecPerp y) (c : F) :
    centerMap α hα (c • x) = centerFieldEquiv hk hy α hα c • centerMap α hα x := by
  by_cases hxs : (x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxs
    have hx' : x = a • selfVecPerp y := Subtype.ext (by
      rw [Submodule.coe_smul, coe_selfVecPerp]
      exact ha.symm)
    have hcx : c • x = (c * a) • selfVecPerp y := by
      rw [hx', smul_smul]
    rw [hcx, centerMap_smul_selfVecPerp hk hF hy hy' α hα hαy (c * a), hx',
      centerMap_smul_selfVecPerp hk hF hy hy' α hα hαy a, map_mul, mul_smul]
  · exact centerMap_smul_of_notMem hk hy α hα hxs c

private theorem centerMap_isometry [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (x z : vecPerp y) :
    spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
      (centerMap α hα z : Fin k ⊕ Fin k → F) =
      centerFieldEquiv hk hy α hα (spForm k F (x : Fin k ⊕ Fin k → F)
        (z : Fin k ⊕ Fin k → F)) := by
  by_cases hxs : (x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxs
    have hfx : (centerMap α hα x : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y'} :=
      centerMap_mem_span_of_mem_span α hα hxs
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hfx
    have h1 : spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα z : Fin k ⊕ Fin k → F) = 0 := by
      rw [← hb, map_smul]
      simp [spForm_selfVecPerp_eq_zero (centerMap α hα z).2]
    have h2 : spForm k F (x : Fin k ⊕ Fin k → F) (z : Fin k ⊕ Fin k → F) = 0 := by
      rw [← ha, map_smul]
      simp [spForm_selfVecPerp_eq_zero z.2]
    rw [h1, h2, map_zero]
  by_cases hzs : (z : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y}
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzs
    have hfz : (centerMap α hα z : Fin k ⊕ Fin k → F) ∈ Submodule.span F {y'} :=
      centerMap_mem_span_of_mem_span α hα hzs
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hfz
    have h1 : spForm k F (centerMap α hα x : Fin k ⊕ Fin k → F)
        (centerMap α hα z : Fin k ⊕ Fin k → F) = 0 := by
      rw [← hb, map_smul]
      simp [mem_vecPerp.mp (centerMap α hα x).2]
    have h2 : spForm k F (x : Fin k ⊕ Fin k → F) (z : Fin k ⊕ Fin k → F) = 0 := by
      rw [← ha, map_smul]
      simp [mem_vecPerp.mp x.2]
    rw [h1, h2, map_zero]
  · exact centerMap_spForm_eq_sigma hk hy α hα

private noncomputable def centreFun {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (x : Fin k ⊕ Fin k → F) : Fin k ⊕ Fin k → F := by
  classical
  exact if hx : x ∈ vecPerp y then (centerMap α hα ⟨x, hx⟩ : Fin k ⊕ Fin k → F) else 0

private theorem centreFun_of_mem {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x : Fin k ⊕ Fin k → F} (hx : x ∈ vecPerp y) :
    centreFun α hα x = (centerMap α hα ⟨x, hx⟩ : Fin k ⊕ Fin k → F) := by
  rw [centreFun]
  split_ifs
  rfl

private theorem centreFun_add [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1)
    {x z : Fin k ⊕ Fin k → F} (hx : x ∈ vecPerp y) (hz : z ∈ vecPerp y) :
    centreFun α hα (x + z) = centreFun α hα x + centreFun α hα z := by
  have hxz := (vecPerp y).add_mem hx hz
  rw [centreFun_of_mem α hα hx, centreFun_of_mem α hα hz, centreFun_of_mem α hα hxz]
  have harg : (⟨x + z, hxz⟩ : vecPerp y) = ⟨x, hx⟩ + ⟨z, hz⟩ := Subtype.ext rfl
  rw [harg]
  exact congrArg Subtype.val (centerMap_add hk hF hy hy' α hα hαy ⟨x, hx⟩ ⟨z, hz⟩)

private theorem centreFun_smul [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1)
    {x : Fin k ⊕ Fin k → F} (hx : x ∈ vecPerp y) (c : F) :
    centreFun α hα (c • x) =
      (centerFieldEquiv hk hy α hα c) • centreFun α hα x := by
  have hcx := (vecPerp y).smul_mem c hx
  rw [centreFun_of_mem α hα hx, centreFun_of_mem α hα hcx]
  have harg : (⟨c • x, hcx⟩ : vecPerp y) = c • ⟨x, hx⟩ := Subtype.ext rfl
  rw [harg]
  have h := congrArg Subtype.val (centerMap_smul hk hF hy hy' α hα hαy ⟨x, hx⟩ c)
  calc (centerMap α hα (c • ⟨x, hx⟩) : Fin k ⊕ Fin k → F)
      = ((centerFieldEquiv hk hy α hα c) • centerMap α hα ⟨x, hx⟩ :
          vecPerp y') := h
    _ = (centerFieldEquiv hk hy α hα c) •
        (centerMap α hα ⟨x, hx⟩ : Fin k ⊕ Fin k → F) := Submodule.coe_smul _ _

private theorem centreFun_isometry [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x z : Fin k ⊕ Fin k → F} (hx : x ∈ vecPerp y) (hz : z ∈ vecPerp y) :
    spForm k F (centreFun α hα x) (centreFun α hα z) =
      centerFieldEquiv hk hy α hα (spForm k F x z) := by
  rw [centreFun_of_mem α hα hx, centreFun_of_mem α hα hz]
  exact centerMap_isometry hk hy α hα ⟨x, hx⟩ ⟨z, hz⟩

private theorem centreFun_mem_vecPerp {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x : Fin k ⊕ Fin k → F} (hx : x ∈ vecPerp y) :
    spForm k F (centreFun α hα x) y' = 0 := by
  rw [centreFun_of_mem α hα hx]
  exact mem_vecPerp.mp (centerMap α hα ⟨x, hx⟩).2

private theorem centreFun_surjective [CharP F 2] {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {x' : Fin k ⊕ Fin k → F} (hx' : x' ∈ vecPerp y') :
    ∃ x, x ∈ vecPerp y ∧ centreFun α hα x = x' := by
  obtain ⟨x, hx⟩ := centerMap_surjective α hα ⟨x', hx'⟩
  refine ⟨x, x.2, ?_⟩
  rw [centreFun_of_mem α hα x.2]
  exact congrArg Subtype.val hx

private theorem centreFun_self [CharP F 2] {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) :
    centreFun α hα y = y' := by
  have hyE : y ∈ vecPerp y := self_mem_vecPerp y
  rw [centreFun_of_mem α hα hyE]
  have harg : (⟨y, hyE⟩ : vecPerp y) = selfVecPerp y := Subtype.ext rfl
  rw [harg, centerMap_self hy α hα hαy]
  rfl

private theorem centreFun_transvection {y y' : Fin k ⊕ Fin k → F}
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : PreservesUnitTransvections α)
    {a : Fin k ⊕ Fin k → F} (ha : a ∈ vecPerp y) (p : ↥(fixing {y}))
    (hp : (p : ↥(StatedSp k F)) = spTransvection a 1) :
    (α p : ↥(StatedSp k F)) = spTransvection (centreFun α hα a) 1 := by
  by_cases ha0 : a = 0
  · subst ha0
    have hp1 : p = 1 := by
      apply Subtype.ext
      rw [hp]
      exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.spTransvection_zero_eq_one 1
    have h0E : (0 : Fin k ⊕ Fin k → F) ∈ vecPerp y := by
      rw [mem_vecPerp]
      simp
    rw [hp1, map_one, centreFun_of_mem α hα h0E]
    rw [show (⟨0, h0E⟩ : vecPerp y) = 0 from Subtype.ext rfl, centerMap_zero]
    exact (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.spTransvection_zero_eq_one 1).symm
  · have hsub : p = ⟨spTransvection a 1,
        (spTransvection_mem_fixing_singleton_iff one_ne_zero).mpr (mem_vecPerp.mp ha)⟩ :=
      Subtype.ext hp
    rw [hsub, centreFun_of_mem α hα ha]
    exact centerMap_apply α hα ⟨a, ha⟩ ha0

theorem ne_zero_of_mulEquiv_fixing {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) : y' ≠ 0 := by
  rintro rfl
  rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.spTransvection_zero_eq_one] at hαy
  have h1 : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(fixing {0})) = 1 := Subtype.ext hαy
  have h2 : (⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(fixing {y})) = 1 := α.injective (by rw [h1, map_one])
  exact hy (spTransvection_one_eq_one_iff.mp (congrArg Subtype.val h2))

theorem exists_semilinear_centreMap [Fintype F] [CharP F 2] (hk : 2 ≤ k)
    (hF : 4 ≤ Fintype.card F) {y y' : Fin k ⊕ Fin k → F} (hy : y ≠ 0)
    (α : ↥(fixing {y}) ≃* ↥(fixing {y'}))
    (hα : ∀ p : ↥(fixing {y}),
      (∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (p : ↥(StatedSp k F)) = spTransvection a 1) ↔
        ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ (α p : ↥(StatedSp k F)) = spTransvection a 1)
    (hαy : (α ⟨spTransvection y 1, spTransvection_mem_fixing_singleton y 1⟩ :
      ↥(StatedSp k F)) = spTransvection y' 1) :
    ∃ (σ : F ≃+* F) (f : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)),
      (∀ x z, spForm k F x y = 0 → spForm k F z y = 0 → f (x + z) = f x + f z) ∧
      (∀ (c : F) x, spForm k F x y = 0 → f (c • x) = σ c • f x) ∧
      (∀ x z, spForm k F x y = 0 → spForm k F z y = 0 →
        spForm k F (f x) (f z) = σ (spForm k F x z)) ∧
      (∀ x, spForm k F x y = 0 → spForm k F (f x) y' = 0) ∧
      (∀ x', spForm k F x' y' = 0 → ∃ x, spForm k F x y = 0 ∧ f x = x') ∧
      f y = y' ∧
      ∀ (a : Fin k ⊕ Fin k → F) (p : ↥(fixing {y})), spForm k F a y = 0 →
        (p : ↥(StatedSp k F)) = spTransvection a 1 →
          (α p : ↥(StatedSp k F)) = spTransvection (f a) 1 := by
  have hy' : y' ≠ 0 := ne_zero_of_mulEquiv_fixing hy α hαy
  classical
  refine ⟨centerFieldEquiv hk hy α hα, centreFun α hα, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x z hx hz
    exact centreFun_add hk hF hy hy' α hα hαy (mem_vecPerp.mpr hx) (mem_vecPerp.mpr hz)
  · intro c x hx
    exact centreFun_smul hk hF hy hy' α hα hαy (mem_vecPerp.mpr hx) c
  · intro x z hx hz
    exact centreFun_isometry hk hy α hα (mem_vecPerp.mpr hx) (mem_vecPerp.mpr hz)
  · intro x hx
    exact centreFun_mem_vecPerp α hα (mem_vecPerp.mpr hx)
  · intro x' hx'
    exact centreFun_surjective α hα (mem_vecPerp.mpr hx')
  · exact centreFun_self hy α hα hαy
  · intro a p ha hp
    exact centreFun_transvection α hα (mem_vecPerp.mpr ha) p hp

end CFSG.OddTranspositions.PartThree.ElevenSp
