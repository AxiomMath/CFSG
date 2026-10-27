module

public import CFSG.Sporadic.Bridge.J1Check
public import CFSG.Sporadic.Bridge.Common
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Bridge.J1

open CFSG.Certificates CFSG.Certificates.CosetEnumeration TauCeti CFSG.ProperTwoGeneratedCore

theorem generatorCount_eq : Sporadic.j1Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

private theorem presentation_eq : SporadicName.J1.presentation = Sporadic.j1Presentation := rfl

@[expose] def abWord : List (ℕ × Bool) := [(0, true), (1, true)]

@[expose] def repWord : List (ℕ × Bool) := [(0, true), (1, true), (0, true), (1, false)]

@[expose] def fifthBase : List (ℕ × Bool) := abWord ++ repWord ++ repWord ++ repWord

@[expose] def squareBase : List (ℕ × Bool) :=
  abWord ++ repWord ++ repWord ++ repWord ++ repWord ++ repWord ++ repWord ++
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)]

theorem relatorLetters_eq : Sporadic.j1Presentation.relatorLetters =
    [[(0, true), (0, true)], [(1, true), (1, true), (1, true)],
      abWord ++ abWord ++ abWord ++ abWord ++ abWord ++ abWord ++ abWord,
      fifthBase ++ fifthBase ++ fifthBase ++ fifthBase ++ fifthBase,
      squareBase ++ squareBase] := by
  simp [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.j1Presentation_transcribed, FreeGroup.invRev, fifthBase, squareBase, repWord, abWord]

@[expose] def subWord : List (Fin Sporadic.j1Presentation.generatorCount × Bool) :=
  [(⟨0, by simp [generatorCount_eq]⟩, true), (⟨1, by simp [generatorCount_eq]⟩, true)]

noncomputable def subElt : Sporadic.j1Presentation.Group :=
  PresentedGroup.mk _ (FreeGroup.mk subWord)

theorem subElt_pow_seven : subElt ^ 7 = 1 := by
  have hmem : abWord ++ abWord ++ abWord ++ abWord ++ abWord ++ abWord ++ abWord ∈
      Sporadic.j1Presentation.relatorLetters := by
    rw [relatorLetters_eq]
    simp
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hmem
  obtain ⟨w, hw, hwe⟩ := hmem
  have hinj : Function.Injective (List.map fun letter :
      Fin Sporadic.j1Presentation.generatorCount × Bool => (letter.1.val, letter.2)) :=
    List.map_injective_iff.mpr fun x y hxy => by
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (Fin.ext hxy.1) hxy.2
  have hw7 : w = subWord ++ subWord ++ subWord ++ subWord ++ subWord ++ subWord ++ subWord :=
    hinj (hwe.trans rfl)
  have h1 := PresentedGroup.one_of_mem (relators_mem _ w hw)
  simp only [hw7, ← FreeGroup.mul_mk, map_mul] at h1
  simp only [pow_succ, pow_zero, one_mul]
  exact h1

theorem index_le :
    (Subgroup.zpowers subElt).FiniteIndex ∧ (Subgroup.zpowers subElt).index ≤ 25080 := by
  have hc : codes [subWord] = [[0, 2]] := by decide
  have h := index_le_of_facts_presented (rels := Sporadic.j1Presentation.relatorSet)
    (H := Subgroup.zpowers subElt)
    (N := 25653) (F := 51839) (fx := J1Data.fx) (fc := J1Data.fc) (fy := J1Data.fy)
    (kind := J1Data.kind) (wi := J1Data.wi) (fs := J1Data.fs) (ft := J1Data.ft)
    (fo := J1Data.fo) (refs := J1Data.refs) (pl := J1Data.pl) (ffi := J1Data.ffi)
    (live := J1Data.live) Sporadic.j1Presentation.relators [subWord] J1Data.words
    (relators_mem _)
    (by
      intro w hw
      rw [List.mem_singleton] at hw
      subst hw
      exact Subgroup.mem_zpowers subElt)
    (by
      rw [codes_relators, relatorLetters_eq, generatorCount_eq]
      decide +kernel)
    J1Data.live_zero (by norm_num)
    (by rw [hc, generatorCount_eq]; exact J1Data.facts_all)
    (by rw [generatorCount_eq]; exact J1Data.cover_all)
  rw [J1Data.liveCount_eq] at h
  exact h

theorem finite_card_le :
    Finite Sporadic.j1Presentation.Group ∧ Nat.card Sporadic.j1Presentation.Group ≤ 175560 :=
  finite_card_le_of_zpowers subElt (k := 7) (n := 25080) (by norm_num) subElt_pow_seven
    index_le.1 index_le.2

theorem tauCeti_finite_card_le :
    Finite SporadicName.J1.Group ∧ Nat.card SporadicName.J1.Group ≤ 175560 := by
  show Finite SporadicName.J1.presentation.Group ∧
    Nat.card SporadicName.J1.presentation.Group ≤ 175560
  rw [presentation_eq]
  exact finite_card_le

noncomputable abbrev seedGroup : Subgroup (GL (Fin 7) (ZMod 11)) :=
  Subgroup.closure {j1_first_unit, j1_second_unit}

noncomputable def nativeEquiv : Blueprint.NativeSporadic.J1 ≃* seedGroup :=
  j1_exact_model_equiv.symm.trans (MulEquiv.subgroupCongr j1_canonical_subgroup_eq)

@[expose] noncomputable def unitGen (i : ℕ) : GL (Fin 7) (ZMod 11) :=
  if i = 0 then j1_first_unit else j1_second_unit

theorem unitGen_mem (i : ℕ) : unitGen i ∈ seedGroup := by
  unfold unitGen
  split
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem wordProd_mem_seedGroup (w : List (ℕ × Bool)) : wordProd unitGen w ∈ seedGroup :=
  wordProd_mem unitGen_mem w

@[expose] def letterMat (l : ℕ × Bool) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  if l.1 = 0 then j1_first_matrix else if l.2 then j1_second_matrix else j1_second_matrix ^ 2

@[expose] def matWord (w : List (ℕ × Bool)) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  (w.map letterMat).prod

theorem matWord_append (u v : List (ℕ × Bool)) :
    matWord (u ++ v) = matWord u * matWord v := by
  simp only [matWord, List.map_append, List.prod_append]

theorem first_unit_inv : j1_first_unit⁻¹ = j1_first_unit :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact Units.pow_ofPowEqOne _ _)

theorem second_unit_inv : j1_second_unit⁻¹ = j1_second_unit ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact Units.pow_ofPowEqOne _ _)

theorem val_letter (l : ℕ × Bool) :
    ((if l.2 then unitGen l.1 else (unitGen l.1)⁻¹ : GL (Fin 7) (ZMod 11)) :
      Matrix (Fin 7) (Fin 7) (ZMod 11)) = letterMat l := by
  obtain ⟨i, s⟩ := l
  unfold unitGen letterMat
  by_cases hi : i = 0 <;> cases s
  · simp only [hi, ↓reduceIte, Bool.false_eq_true, first_unit_inv]; rfl
  · simp only [hi, ↓reduceIte]; rfl
  · simp only [hi, ↓reduceIte, Bool.false_eq_true, second_unit_inv, Units.val_pow_eq_pow_val]; rfl
  · simp only [hi, ↓reduceIte]; rfl

theorem val_wordProd (w : List (ℕ × Bool)) :
    ((wordProd unitGen w : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)) =
      matWord w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordProd, matWord, List.map_cons, List.prod_cons, Units.val_mul] at ih ⊢
    rw [ih, val_letter]

@[expose] noncomputable def img (i : ℕ) : ↥seedGroup := ⟨unitGen i, unitGen_mem i⟩

@[expose] def fifthMat : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![5, 6, 4, 5, 6, 4, 1;
     5, 6, 7, 7, 10, 5, 5;
     6, 3, 8, 3, 5, 3, 6;
     4, 3, 8, 6, 6, 0, 7;
     4, 8, 6, 0, 4, 8, 6;
     10, 5, 5, 7, 5, 4, 6;
     6, 8, 0, 8, 7, 5, 7]

@[expose] def squareMat : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![8, 5, 7, 9, 4, 5, 7;
     5, 9, 6, 2, 10, 6, 7;
     7, 6, 5, 9, 4, 8, 4;
     9, 2, 9, 4, 5, 4, 3;
     4, 10, 4, 5, 0, 0, 3;
     5, 6, 8, 4, 0, 5, 0;
     7, 7, 4, 3, 3, 0, 1]

theorem matWord_fifthBase : matWord fifthBase = fifthMat := by
  decide +kernel

theorem matWord_squareBase : matWord squareBase = squareMat := by
  decide +kernel

theorem matWord_relator : ∀ v ∈ Sporadic.j1Presentation.relatorLetters, matWord v = 1 := by
  rw [relatorLetters_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl | rfl | rfl)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · simp only [matWord_append, matWord_fifthBase]
    decide +kernel
  · simp only [matWord_append, matWord_squareBase]
    decide +kernel

theorem relators_eval : ∀ v ∈ Sporadic.j1Presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd, Subgroup.coe_one]
  apply Units.ext
  rw [show (fun i => ((img i : ↥seedGroup) : GL (Fin 7) (ZMod 11))) = unitGen from rfl,
    val_wordProd, Units.val_one]
  exact matWord_relator v hv

noncomputable def toNative : Sporadic.j1Presentation.Group →* ↥seedGroup :=
  presHom _ img relators_eval

theorem toNative_surjective : Function.Surjective toNative := by
  have hgen : ∀ i < 2, img i ∈ toNative.range := fun i hi =>
    ⟨presGen _ i, presHom_presGen _ img relators_eval (by rw [generatorCount_eq]; exact hi)⟩
  intro y
  obtain ⟨y, hy⟩ := y
  suffices H : ∀ z (hz : z ∈ seedGroup), (⟨z, hz⟩ : ↥seedGroup) ∈ toNative.range from H y hy
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | hz
    · exact hgen 0 (by norm_num)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hgen 1 (by norm_num)
  | one => exact toNative.range.one_mem
  | mul x y hx hy ihx ihy => exact toNative.range.mul_mem ihx ihy
  | inv x hx ih => exact toNative.range.inv_mem ih

theorem prime_dvd_card_of_word (p : ℕ) (hp : p.Prime) (w : List (ℕ × Bool))
    (hw : matWord w ^ p = 1) (hw1 : matWord w ≠ 1) : p ∣ Nat.card seedGroup := by
  have := Fact.mk hp
  have hg : wordProd unitGen w ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, val_wordProd, Units.val_one]; exact hw)
  have hg1 : wordProd unitGen w ≠ 1 := fun h => hw1 (by rw [← val_wordProd, h, Units.val_one])
  rw [← orderOf_eq_prime hg hg1, ← Nat.card_zpowers]
  exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr (wordProd_mem_seedGroup w))

@[expose] def elevenWord : List (ℕ × Bool) :=
  [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true)]

@[expose] def involWordX : List (ℕ × Bool) :=
  [(0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
    (0, true), (1, false), (0, true), (1, true), (0, true)]

@[expose] def involWordY : List (ℕ × Bool) :=
  [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]

@[expose] def involWordZ : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]

@[expose] def involX : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![4, 6, 9, 8, 5, 8, 10;
     6, 10, 0, 6, 2, 6, 3;
     9, 0, 10, 9, 3, 9, 10;
     8, 6, 9, 0, 3, 4, 9;
     5, 2, 3, 3, 1, 5, 7;
     8, 6, 9, 4, 5, 4, 7;
     10, 3, 10, 9, 7, 7, 3]

@[expose] def involY : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![6, 5, 4, 5, 5, 4, 10;
     5, 8, 8, 3, 6, 3, 5;
     4, 8, 5, 0, 4, 3, 6;
     5, 3, 0, 8, 4, 5, 4;
     5, 6, 4, 4, 10, 6, 5;
     4, 3, 3, 5, 6, 0, 7;
     10, 5, 6, 4, 5, 7, 6]

@[expose] def involZ : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![10, 5, 9, 3, 10, 0, 4;
     5, 1, 4, 6, 9, 3, 8;
     9, 4, 0, 2, 1, 2, 7;
     3, 6, 2, 2, 3, 2, 10;
     10, 9, 1, 3, 8, 1, 8;
     0, 3, 2, 2, 1, 0, 7;
     4, 8, 7, 10, 8, 7, 0]

theorem matWord_involWord :
    matWord involWordX = involX ∧ matWord involWordY = involY ∧ matWord involWordZ = involZ := by
  decide +kernel

@[expose] def vMat (i : Fin 8) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  (if i.val % 2 = 1 then involX else 1) * (if i.val / 2 % 2 = 1 then involY else 1) *
    (if i.val / 4 % 2 = 1 then involZ else 1)

@[expose] def vWord (i : Fin 8) : List (ℕ × Bool) :=
  (if i.val % 2 = 1 then involWordX else []) ++ (if i.val / 2 % 2 = 1 then involWordY else []) ++
    (if i.val / 4 % 2 = 1 then involWordZ else [])

theorem matWord_vWord (i : Fin 8) : matWord (vWord i) = vMat i := by
  obtain ⟨hX, hY, hZ⟩ := matWord_involWord
  simp only [vWord, vMat, matWord_append, apply_ite matWord, hX, hY, hZ]
  rfl

@[expose] def vXor (i j : Fin 8) : Fin 8 := ⟨(i.val ^^^ j.val) % 8, Nat.mod_lt _ (by norm_num)⟩

theorem vMat_mul : ∀ i j : Fin 8, vMat i * vMat j = vMat (vXor i j) := by
  decide +kernel

theorem vMat_mul_self (i : Fin 8) : vMat i * vMat i = 1 := by
  rw [vMat_mul, show vXor i i = 0 by revert i; decide]
  decide +kernel

theorem vMat_injective : ∀ i j : Fin 8, vMat i = vMat j → i = j := by
  decide +kernel

@[expose] def elemAbelian : Subgroup (GL (Fin 7) (ZMod 11)) where
  carrier := {g | ∃ i, (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = vMat i}
  mul_mem' {g h} := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨vXor i j, by rw [Units.val_mul, hi, hj, vMat_mul]⟩
  one_mem' := ⟨0, by rw [Units.val_one]; decide +kernel⟩
  inv_mem' {g} := by
    rintro ⟨i, hi⟩
    have h2 : g * g = 1 := Units.ext (by rw [Units.val_mul, Units.val_one, hi, vMat_mul_self])
    exact ⟨i, by rw [inv_eq_of_mul_eq_one_right h2, hi]⟩

theorem mem_elemAbelian {g : GL (Fin 7) (ZMod 11)} :
    g ∈ elemAbelian ↔ ∃ i, (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = vMat i := Iff.rfl

theorem elemAbelian_le : elemAbelian ≤ seedGroup := by
  intro g hg
  obtain ⟨i, hi⟩ := mem_elemAbelian.mp hg
  rw [show g = wordProd unitGen (vWord i) from
    Units.ext (by rw [val_wordProd, matWord_vWord, hi])]
  exact wordProd_mem_seedGroup _

theorem card_elemAbelian : Nat.card elemAbelian = 8 := by
  let f : Fin 8 → elemAbelian := fun i =>
    ⟨⟨vMat i, vMat i, vMat_mul_self i, vMat_mul_self i⟩, mem_elemAbelian.mpr ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact vMat_injective i j (congrArg
        (fun g : elemAbelian => ((g : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))) h)
    · rintro ⟨g, hg⟩
      obtain ⟨i, hi⟩ := mem_elemAbelian.mp hg
      exact ⟨i, Subtype.ext (Units.ext hi.symm)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem le_card_native : 175560 ≤ Nat.card seedGroup := by
  have h8 : 8 ∣ Nat.card seedGroup := card_elemAbelian ▸ Subgroup.card_dvd_of_le elemAbelian_le
  have h3 := prime_dvd_card_of_word 3 (by norm_num) [(1, true)] (by decide +kernel)
    (by decide +kernel)
  have h5 := prime_dvd_card_of_word 5 (by norm_num) fifthBase
    (by rw [matWord_fifthBase]; decide +kernel) (by rw [matWord_fifthBase]; decide +kernel)
  have h7 := prime_dvd_card_of_word 7 (by norm_num) abWord (by decide +kernel) (by decide +kernel)
  have h11 := prime_dvd_card_of_word 11 (by norm_num) elevenWord (by decide +kernel)
    (by decide +kernel)
  have h19 := prime_dvd_card_of_word 19 (by norm_num) repWord (by decide +kernel)
    (by decide +kernel)
  have hd : 175560 ∣ Nat.card seedGroup := by
    have h24 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
    have h120 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 24 5) h24 h5
    have h840 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 120 7) h120 h7
    have h9240 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 840 11) h840 h11
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9240 19) h9240 h19
  exact Nat.le_of_dvd Nat.card_pos hd

theorem nonempty_mulEquiv :
    Nonempty (CFSG.Blueprint.NativeSporadic.J1 ≃* TauCeti.SporadicName.J1.Group) := by
  obtain ⟨hfin, hcard⟩ := finite_card_le
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective toNative toNative_surjective hcard le_card_native
  show Nonempty (Blueprint.NativeSporadic.J1 ≃* SporadicName.J1.presentation.Group)
  rw [presentation_eq]
  exact ⟨nativeEquiv.trans e⟩

end CFSG.Sporadic.Bridge.J1
