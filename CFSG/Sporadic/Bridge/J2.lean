module

public import CFSG.Sporadic.Bridge.J2Check
public import CFSG.Sporadic.Bridge.J2CheckW
public import CFSG.Sporadic.Bridge.J2Native
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Sporadic.Bridge.J2

open CFSG.Certificates CFSG.Certificates.CosetEnumeration TauCeti

theorem generatorCount_eq : Sporadic.j2Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

private theorem presentation_eq : SporadicName.J2.presentation = Sporadic.j2Presentation := rfl

theorem relatorLetters_eq : Sporadic.j2Presentation.relatorLetters = [r₁L, r₂L, r₃L] := by
  simp [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.j2Presentation_transcribed, FreeGroup.invRev, r₁L, r₂L, r₃L, wL]

theorem mk_eq_wordProd (P : GroupPresentation) (w : List (Fin P.generatorCount × Bool)) :
    PresentedGroup.mk P.relatorSet (FreeGroup.mk w) =
      wordProd (presGen P) (w.map fun l => (l.1.val, l.2)) := by
  rw [← lift_mk P (presGen P) w]
  have h : PresentedGroup.mk P.relatorSet =
      FreeGroup.lift (fun i : Fin P.generatorCount => presGen P i.val) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, presGen, dite_eq_left i.isLt]
    rfl
  rw [h]

theorem wordProd_presGen_relator (P : GroupPresentation) {v : List (ℕ × Bool)}
    (hv : v ∈ P.relatorLetters) : wordProd (presGen P) v = 1 := by
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [← mk_eq_wordProd]
  exact PresentedGroup.one_of_mem (relators_mem P w hw)

noncomputable abbrev aElt : Sporadic.j2Presentation.Group := presGen Sporadic.j2Presentation 0

noncomputable abbrev bElt : Sporadic.j2Presentation.Group := presGen Sporadic.j2Presentation 1

theorem braid : aElt * bElt * aElt = bElt * aElt * bElt := by
  have h := wordProd_presGen_relator Sporadic.j2Presentation
    (show r₁L ∈ _ by rw [relatorLetters_eq]; simp)
  simp only [wordProd, r₁L, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ↓reduceIte, Bool.false_eq_true, mul_one] at h
  have h' : aElt * bElt * aElt * (bElt * aElt * bElt)⁻¹ = 1 := by
    rw [← h]; group
  exact mul_inv_eq_one.mp h'

@[expose] def gWord : List (Fin Sporadic.j2Presentation.generatorCount × Bool) :=
  [(⟨0, by simp [generatorCount_eq]⟩, true), (⟨1, by simp [generatorCount_eq]⟩, false)]

@[expose] def zWord : List (Fin Sporadic.j2Presentation.generatorCount × Bool) :=
  [(⟨0, by simp [generatorCount_eq]⟩, true), (⟨1, by simp [generatorCount_eq]⟩, true),
    (⟨0, by simp [generatorCount_eq]⟩, true), (⟨0, by simp [generatorCount_eq]⟩, true),
    (⟨1, by simp [generatorCount_eq]⟩, true), (⟨0, by simp [generatorCount_eq]⟩, true)]

noncomputable def gElt : Sporadic.j2Presentation.Group :=
  PresentedGroup.mk _ (FreeGroup.mk gWord)

noncomputable def zElt : Sporadic.j2Presentation.Group :=
  PresentedGroup.mk _ (FreeGroup.mk zWord)

theorem gElt_eq : gElt = aElt * bElt⁻¹ := by
  rw [gElt, mk_eq_wordProd]
  simp [wordProd, gWord]

theorem zElt_eq : zElt = aElt * bElt * aElt * (aElt * bElt * aElt) := by
  rw [zElt, mk_eq_wordProd]
  simp [wordProd, zWord, mul_assoc]

theorem commute_gElt_zElt : Commute gElt zElt := by
  set d := aElt * bElt * aElt with hd
  have h₁ : d * aElt = bElt * d := by
    calc d * aElt = bElt * aElt * bElt * aElt := by rw [hd, braid]
      _ = bElt * d := by rw [hd]; group
  have h₂ : d * bElt = aElt * d := by
    calc d * bElt = aElt * (bElt * aElt * bElt) := by rw [hd]; group
      _ = aElt * d := by rw [← braid, hd]
  have ca : Commute zElt aElt := by
    rw [zElt_eq, ← hd]
    show d * d * aElt = aElt * (d * d)
    rw [mul_assoc, h₁, ← mul_assoc, h₂, mul_assoc]
  have cb : Commute zElt bElt := by
    rw [zElt_eq, ← hd]
    show d * d * bElt = bElt * (d * d)
    rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]
  rw [gElt_eq]
  exact (ca.mul_right cb.inv_right).symm

noncomputable def gzVal (e : ℤ × ℤ) : Sporadic.j2Presentation.Group := gElt ^ e.1 * zElt ^ e.2

theorem weightMap_gzVal : WeightMap gzVal := ⟨fun x y => by
  simp only [gzVal, Prod.fst_add, Prod.snd_add, zpow_add]
  have h := (commute_gElt_zElt.zpow_zpow y.1 x.2).eq
  rw [mul_assoc, ← mul_assoc (gElt ^ y.1), h]
  simp only [mul_assoc]⟩

theorem codes_subWords : codes [gWord, zWord] = [[0, 3], [0, 2, 0, 0, 2, 0]] := by
  decide

theorem subWords_eval : ∀ j < [gWord, zWord].length,
    PresentedGroup.mk _ (FreeGroup.mk ([gWord, zWord].getD j [])) =
      gzVal ((J2Data.tgtG j : ℤ), (J2Data.tgtZ j : ℤ)) := by
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j
  · simp [gzVal, J2Data.tgtG, J2Data.tgtZ, gElt]
  · simp [gzVal, J2Data.tgtG, J2Data.tgtZ, zElt]

theorem gzVal_closure {f : ℕ} (hf : f < 16893) (hxy : J2Data.fxB f = J2Data.fyB f)
    (hc : J2Data.fcB f = 4) : gzVal (pairW J2Data.wtG J2Data.wtZ f) = 1 :=
  phi_eq_one_of_weights_presented (rels := Sporadic.j2Presentation.relatorSet)
    (N := 40382) (F := 16893) (fx := J2Data.fxB) (fc := J2Data.fcB) (fy := J2Data.fyB)
    (kind := J2Data.kindB) (wi := J2Data.wiB) (fs := J2Data.fsB) (ft := J2Data.ftB)
    (fo := J2Data.foB) (refs := J2Data.refsB) (pl := J2Data.pl) weightMap_gzVal
    Sporadic.j2Presentation.relators [gWord, zWord] J2Data.wordsB (relators_mem _)
    subWords_eval
    (by
      rw [codes_relators, relatorLetters_eq, generatorCount_eq]
      decide +kernel)
    (by rw [codes_subWords, generatorCount_eq]; exact J2Data.factsB_all)
    (by rw [codes_subWords]; exact J2Data.weightsG_all)
    (by rw [codes_subWords]; exact J2Data.weightsZ_all) hf hxy
    (by rw [hc, generatorCount_eq])

theorem closure_facts :
    J2Data.fxB 16890 = J2Data.fyB 16890 ∧ J2Data.fcB 16890 = 4 ∧
      pairW J2Data.wtG J2Data.wtZ 16890 = (-15, 0) ∧
    J2Data.fxB 16891 = J2Data.fyB 16891 ∧ J2Data.fcB 16891 = 4 ∧
      pairW J2Data.wtG J2Data.wtZ 16891 = (0, 2) ∧
    J2Data.fxB 16892 = J2Data.fyB 16892 ∧ J2Data.fcB 16892 = 4 ∧
      pairW J2Data.wtG J2Data.wtZ 16892 = (15, -5) := by
  decide +kernel

theorem gElt_pow : gElt ^ 15 = 1 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := closure_facts
  have h := gzVal_closure (by norm_num) h₁ h₂
  rw [h₃] at h
  simp only [gzVal, zpow_zero, mul_one, zpow_neg, inv_eq_one] at h
  exact_mod_cast h

theorem zElt_eq_one : zElt = 1 := by
  obtain ⟨-, -, -, h₁, h₂, h₃, h₄, h₅, h₆⟩ := closure_facts
  have hB := gzVal_closure (by norm_num) h₁ h₂
  have hC := gzVal_closure (by norm_num) h₄ h₅
  rw [h₃] at hB
  rw [h₆] at hC
  simp only [gzVal, zpow_zero, one_mul] at hB hC
  have hg : gElt ^ (15 : ℤ) = 1 := by exact_mod_cast gElt_pow
  rw [hg, one_mul] at hC
  calc zElt = (zElt ^ (-5 : ℤ))⁻¹ * (zElt ^ (2 : ℤ)) ^ (-2 : ℤ) := by group
    _ = 1 := by rw [hB, hC]; group

theorem index_le :
    (Subgroup.zpowers gElt).FiniteIndex ∧ (Subgroup.zpowers gElt).index ≤ 40320 := by
  have h := index_le_of_facts_presented (rels := Sporadic.j2Presentation.relatorSet)
    (H := Subgroup.zpowers gElt)
    (N := 40382) (F := 80847) (fx := J2Data.fx) (fc := J2Data.fc) (fy := J2Data.fy)
    (kind := J2Data.kind) (wi := J2Data.wi) (fs := J2Data.fs) (ft := J2Data.ft)
    (fo := J2Data.fo) (refs := J2Data.refs) (pl := J2Data.pl) (ffi := J2Data.ffi)
    (live := J2Data.live) Sporadic.j2Presentation.relators [gWord, zWord] J2Data.words
    (relators_mem _)
    (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Subgroup.mem_zpowers gElt
      · change zElt ∈ _
        rw [zElt_eq_one]
        exact Subgroup.one_mem _)
    (by
      rw [codes_relators, relatorLetters_eq, generatorCount_eq]
      decide +kernel)
    J2Data.live_zero (by norm_num)
    (by rw [codes_subWords, generatorCount_eq]; exact J2Data.facts_all)
    (by rw [generatorCount_eq]; exact J2Data.cover_all)
  rw [J2Data.liveCount_eq] at h
  exact h

theorem finite_card_le :
    Finite Sporadic.j2Presentation.Group ∧ Nat.card Sporadic.j2Presentation.Group ≤ 604800 :=
  finite_card_le_of_zpowers gElt (k := 15) (n := 40320) (by norm_num) gElt_pow index_le.1
    index_le.2

theorem tauCeti_finite_card_le :
    Finite SporadicName.J2.Group ∧ Nat.card SporadicName.J2.Group ≤ 604800 := by
  show Finite SporadicName.J2.presentation.Group ∧
    Nat.card SporadicName.J2.presentation.Group ≤ 604800
  rw [presentation_eq]
  exact finite_card_le

@[expose] noncomputable def img (i : ℕ) : ↥seedGroup := ⟨presU i, presU_mem i⟩

theorem relators_eval : ∀ v ∈ Sporadic.j2Presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd, Subgroup.coe_one,
    show (fun i => ((img i : ↥seedGroup) : GL (Fin 14) (ZMod 5))) = presU from rfl]
  rw [relatorLetters_eq] at hv
  exact presU_relator v hv

noncomputable def toNative : Sporadic.j2Presentation.Group →* ↥seedGroup :=
  presHom _ img relators_eval

theorem exists_toNative_eq (w : List (ℕ × Bool))
    (hw : ∀ l ∈ w, l.1 < Sporadic.j2Presentation.generatorCount) :
    ∃ x, ((toNative x : ↥seedGroup) : GL (Fin 14) (ZMod 5)) = wordProd presU w := by
  refine ⟨wordProd (presGen _) w, ?_⟩
  rw [toNative, presHom_wordProd _ img relators_eval w hw, coe_wordProd]
  rfl

theorem toNative_surjective : Function.Surjective toNative := by
  have key : ∀ z ∈ seedGroup, ∃ x, ((toNative x : ↥seedGroup) : GL (Fin 14) (ZMod 5)) = z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · obtain ⟨x, hx⟩ := exists_toNative_eq wA (by rw [generatorCount_eq]; decide +kernel)
        exact ⟨x, hx.trans uA_eq.symm⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨x, hx⟩ := exists_toNative_eq wB (by rw [generatorCount_eq]; decide +kernel)
        exact ⟨x, hx.trans uB_eq.symm⟩
    | one => exact ⟨1, by rw [map_one, Subgroup.coe_one]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, by rw [map_mul, Subgroup.coe_mul, ha, hb]⟩
    | inv x _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨a⁻¹, by rw [map_inv, Subgroup.coe_inv, ha]⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := key y hy
  exact ⟨x, Subtype.ext hx⟩

theorem nonempty_mulEquiv :
    Nonempty (CFSG.Blueprint.NativeSporadic.J2 ≃* TauCeti.SporadicName.J2.Group) := by
  obtain ⟨hfin, hcard⟩ := finite_card_le
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective toNative toNative_surjective hcard
    le_card_seedGroup
  show Nonempty (Blueprint.NativeSporadic.J2 ≃* SporadicName.J2.presentation.Group)
  rw [presentation_eq]
  exact ⟨nativeEquiv.trans e⟩

end CFSG.Sporadic.Bridge.J2
