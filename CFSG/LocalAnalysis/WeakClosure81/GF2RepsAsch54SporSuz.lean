module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporZTwo
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.SuzRecog.LocalRFusionModel
public import CFSG.Sporadic.SuzOddCore.Outer
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.PermV
public import Certificates.Certificate75343

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporSuz

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.LocalR
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

section Words

@[expose] noncomputable def sGen (j : ℕ) : Equiv.Perm (Fin 1782) :=
  sylowGenPerm (s1Idx.getD j 0)

theorem fusionSylow_eq : fusionSylow = closure {g | ∃ j < 4, sGen j = g} := rfl

theorem s1Gens_size : s1Gens.size = 4 := Array.size_ofFn

theorem sGen_mem {j : ℕ} (hj : j < 4) : sGen j ∈ fusionSylow :=
  subset_closure ⟨j, hj, rfl⟩

theorem commT_iff {a b : Tab} {x y : Equiv.Perm (Fin 1782)} (ha : TabRep a x) (hb : TabRep b y) :
    commT a b = true ↔ x * y = y * x :=
  (ha.comp hb).beq_iff (hb.comp ha)

theorem all_s1Gens_iff {p : Tab → Bool} :
    (s1Gens.all p) = true ↔ ∀ j < 4, p s1Gens[j]! = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h j hj
    have := h j (by rw [s1Gens_size]; exact hj)
    rwa [getElem!_pos s1Gens j (by rw [s1Gens_size]; exact hj)]
  · intro h j hj
    have := h j (by rwa [s1Gens_size] at hj)
    rwa [getElem!_pos s1Gens j hj] at this

@[expose] noncomputable def wordP (f : ℕ → Equiv.Perm (Fin 1782)) (w : List Int) :
    Equiv.Perm (Fin 1782) :=
  (w.map fun z => if 0 < z then f (z.natAbs - 1) else (f (z.natAbs - 1))⁻¹).prod

theorem evalW_nil (gs gis : ℕ → Tab) : evalW gs gis [] = idTab 1782 := by
  unfold evalW
  rw [List.foldr_nil]

theorem evalW_cons (gs gis : ℕ → Tab) (z : Int) (w : List Int) :
    evalW gs gis (z :: w) =
      comp 1782 (if 0 < z then gs (z.natAbs - 1) else gis (z.natAbs - 1)) (evalW gs gis w) := by
  unfold evalW
  rw [List.foldr_cons]

theorem wordP_nil (f : ℕ → Equiv.Perm (Fin 1782)) : wordP f [] = 1 := by
  simp [wordP]

theorem wordP_cons (f : ℕ → Equiv.Perm (Fin 1782)) (z : Int) (w : List Int) :
    wordP f (z :: w) = (if 0 < z then f (z.natAbs - 1) else (f (z.natAbs - 1))⁻¹) * wordP f w := by
  simp [wordP]

theorem tabRep_evalW {gs gis : ℕ → Tab} {f : ℕ → Equiv.Perm (Fin 1782)} :
    ∀ {w : List Int}, (∀ z ∈ w, TabRep (gs (z.natAbs - 1)) (f (z.natAbs - 1))) →
      (∀ z ∈ w, TabRep (gis (z.natAbs - 1)) (f (z.natAbs - 1))⁻¹) →
        TabRep (evalW gs gis w) (wordP f w)
  | [], _, _ => by
    rw [evalW_nil, wordP_nil]
    exact TabRep.idTab
  | z :: w, hgs, hgis => by
    have ih := tabRep_evalW (w := w) (fun z' hz' => hgs z' (List.mem_cons_of_mem z hz'))
      (fun z' hz' => hgis z' (List.mem_cons_of_mem z hz'))
    rw [evalW_cons, wordP_cons]
    split_ifs
    · exact (hgs z List.mem_cons_self).comp ih
    · exact (hgis z List.mem_cons_self).comp ih

theorem wordP_mem {f : ℕ → Equiv.Perm (Fin 1782)} {H : Subgroup (Equiv.Perm (Fin 1782))}
    {w : List Int} (hf : ∀ z ∈ w, f (z.natAbs - 1) ∈ H) : wordP f w ∈ H := by
  refine list_prod_mem fun y hy => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  split_ifs
  · exact hf z hz
  · exact inv_mem (hf z hz)

@[expose] noncomputable def abF (j : ℕ) : Equiv.Perm (Fin 1782) := if j = 0 then suzB0 else suzB1

@[expose] noncomputable def cgF (g : Equiv.Perm (Fin 1782)) (j : ℕ) : Equiv.Perm (Fin 1782) :=
  if j = 0 then cPerm 2 else if j = 1 then cPerm 4 else g

@[expose] noncomputable def gPerm : Equiv.Perm (Fin 1782) := wordP abF gWord

theorem gPerm_mem : gPerm ∈ suzM := by
  refine wordP_mem fun z _ => ?_
  unfold abF
  split_ifs
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def gM : ↥suzM := ⟨gPerm, gPerm_mem⟩

theorem coe_gM : (gM : Equiv.Perm (Fin 1782)) = gPerm := rfl

@[expose] noncomputable def pairT : Subgroup ↥suzM := fusionSylow.subgroupOf suzM

theorem mem_pairT {x : ↥suzM} : x ∈ pairT ↔ (x : Equiv.Perm (Fin 1782)) ∈ fusionSylow :=
  mem_subgroupOf

theorem mul_eq_of_commutatorElement {G : Type*} [Group G] {a b c : G} (h : ⁅a, b⁆ = c) :
    a * b = c * (b * a) := by
  rw [← h, commutatorElement_def]
  group

end Words

section Checks


theorem pair_ok : sizesOK () = true ∧ lettersOK () = true ∧ inverseTabsOK () = true ∧
    s1EnumOK () = true ∧ centerOK () = true ∧ z2OK () = true ∧ gNormOK () = true ∧
    genOK () = true := by
  have h := Certificates.certificate75343
  simp only [suzPairOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem sizes_ok : sizesOK () = true := pair_ok.1

theorem letters_ok : lettersOK () = true := pair_ok.2.1

theorem inverseTabs_ok : inverseTabsOK () = true := pair_ok.2.2.1

theorem s1Enum_ok : s1EnumOK () = true := pair_ok.2.2.2.1

theorem center_ok : centerOK () = true := pair_ok.2.2.2.2.1

theorem z2_ok : z2OK () = true := pair_ok.2.2.2.2.2.1

theorem gNorm_ok : gNormOK () = true := pair_ok.2.2.2.2.2.2.1

theorem gen_ok : genOK () = true := pair_ok.2.2.2.2.2.2.2

theorem enum_size : s1Enum.tabs.size = 8192 := by
  have h := s1Enum_ok
  simp only [s1EnumOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem enum_zero : s1Enum.tabs[0]! = idTab 1782 := by
  have h := s1Enum_ok
  simp only [s1EnumOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem enum_posT : s1Enum.tabs[s1PosT]! = tTab := by
  have h := s1Enum_ok
  simp only [s1EnumOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem tabRep_one : TabRep s1Enum.tabs[0]! (1 : Equiv.Perm (Fin 1782)) := by
  rw [enum_zero]
  exact TabRep.idTab

theorem gWord_letters : ∀ z ∈ gWord, z.natAbs - 1 < 2 := by
  have h := letters_ok
  simp only [lettersOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem b0Word_letters : ∀ z ∈ b0Word, z.natAbs - 1 < 3 := by
  have h := letters_ok
  simp only [lettersOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem b1Word_letters : ∀ z ∈ b1Word, z.natAbs - 1 < 3 := by
  have h := letters_ok
  simp only [lettersOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2

end Checks

section TTab


theorem tabRep_tTab : TabRep tTab (suzInv 1) := by
  have h := sizes_ok
  simp only [sizesOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, rep_tTab⟩

theorem tabRep_posT : TabRep s1Enum.tabs[s1PosT]! (suzInv 1) := by
  rw [enum_posT]
  exact tabRep_tTab

theorem commZT_iff {a b : Tab} {x y : Equiv.Perm (Fin 1782)} (ha : TabRep a x)
    (hb : TabRep b y) : commZT a b = true ↔ x * y = suzInv 1 * (y * x) :=
  (ha.comp hb).beq_iff (tabRep_tTab.comp (hb.comp ha))

end TTab

section AB


theorem tabRep_abG {j : ℕ} (hj : j < 2) : TabRep (abG j) (abF j) := by
  have h := sizes_ok
  simp only [sizesOK, Bool.and_eq_true, beq_iff_eq] at h
  interval_cases j
  · simp only [abG, abF]
    exact ⟨h.1.1.1.2, rep_b0⟩
  · simp only [abG, abF, one_ne_zero, if_false]
    exact ⟨h.1.1.2, rep_b1⟩

theorem tabRep_abI {j : ℕ} (hj : j < 2) : TabRep (abI j) (abF j)⁻¹ := by
  have h := inverseTabs_ok
  simp only [inverseTabsOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact (tabRep_abG hj).inv (h.1 j hj).1 (h.1 j hj).2

theorem tabRep_gTab : TabRep (gTab ()) gPerm :=
  tabRep_evalW (fun z hz => tabRep_abG (gWord_letters z hz))
    (fun z hz => tabRep_abI (gWord_letters z hz))

end AB

theorem tabRep_s1Gens
    {j : ℕ} (hj : j < 4) :
    TabRep s1Gens[j]! (sGen j) := by
  rw [s1Gens_get hj]
  exact tabRep_sylowGen (s1Idx_lt hj)

section Enum


theorem exists_tab {x : Equiv.Perm (Fin 1782)} (hx : x ∈ fusionSylow) :
    ∃ k < 8192, TabRep s1Enum.tabs[k]! x := by
  obtain ⟨k, hk, h⟩ := fusionSylow_enumerates.exists_pos hx
  exact ⟨k, enum_size ▸ hk, h⟩

theorem suzInv_mem_fusionSylow : suzInv 1 ∈ fusionSylow := by
  obtain ⟨g, hg, hrep⟩ := fusionSylow_enumerates.exists_elt (k := s1PosT)
    (by rw [enum_size]; decide)
  rw [tabRep_posT.perm_eq hrep]
  exact hg

theorem eq_of_commute_sGen {x : Equiv.Perm (Fin 1782)} (hx : x ∈ fusionSylow)
    (h : ∀ j < 4, x * sGen j = sGen j * x) : x = 1 ∨ x = suzInv 1 := by
  obtain ⟨k, hk, hrep⟩ := exists_tab hx
  have htest : (s1Gens.all fun y => commT s1Enum.tabs[k]! y) = true :=
    all_s1Gens_iff.2 fun j hj => (commT_iff hrep (tabRep_s1Gens hj)).2 (h j hj)
  have hmem : k ∈ (List.range 8192).filter
      (fun i => s1Gens.all fun y => commT s1Enum.tabs[i]! y) :=
    List.mem_filter.2 ⟨List.mem_range.2 hk, htest⟩
  have hc := center_ok
  simp only [centerOK, beq_iff_eq] at hc
  rw [hc] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inl (hrep.perm_eq tabRep_one)
  · exact Or.inr (hrep.perm_eq tabRep_posT)

theorem exists_vZ2 : ∃ v ∈ fusionSylow, TabRep s1Enum.tabs[s1PosV]! v :=
  fusionSylow_enumerates.exists_elt (by rw [enum_size]; decide)

theorem exists_wZ2 : ∃ w ∈ fusionSylow, TabRep s1Enum.tabs[s1PosW]! w :=
  fusionSylow_enumerates.exists_elt (by rw [enum_size]; decide)

@[expose] noncomputable def vZ2 : Equiv.Perm (Fin 1782) := exists_vZ2.choose

@[expose] noncomputable def wZ2 : Equiv.Perm (Fin 1782) := exists_wZ2.choose

theorem vZ2_mem : vZ2 ∈ fusionSylow := exists_vZ2.choose_spec.1

theorem wZ2_mem : wZ2 ∈ fusionSylow := exists_wZ2.choose_spec.1

theorem tabRep_vZ2 : TabRep s1Enum.tabs[s1PosV]! vZ2 := exists_vZ2.choose_spec.2

theorem tabRep_wZ2 : TabRep s1Enum.tabs[s1PosW]! wZ2 := exists_wZ2.choose_spec.2

theorem z2test_iff {k : ℕ} {x : Equiv.Perm (Fin 1782)} (hx : TabRep s1Enum.tabs[k]! x) :
    (s1Gens.all fun y => commT s1Enum.tabs[k]! y || commZT s1Enum.tabs[k]! y) = true ↔
      ∀ j < 4, x * sGen j = sGen j * x ∨ x * sGen j = suzInv 1 * (sGen j * x) := by
  rw [all_s1Gens_iff]
  refine forall₂_congr fun j hj => ?_
  rw [Bool.or_eq_true, commT_iff hx (tabRep_s1Gens hj), commZT_iff hx (tabRep_s1Gens hj)]

theorem z2_iff {x : Equiv.Perm (Fin 1782)} (hx : x ∈ fusionSylow) :
    (∀ j < 4, x * sGen j = sGen j * x ∨ x * sGen j = suzInv 1 * (sGen j * x)) ↔
      x = 1 ∨ x = suzInv 1 ∨ x = vZ2 ∨ x = wZ2 := by
  have hc := z2_ok
  simp only [z2OK, beq_iff_eq] at hc
  have hmem : ∀ k, k ∈ (List.range 8192).filter (fun i => s1Gens.all fun y =>
      commT s1Enum.tabs[i]! y || commZT s1Enum.tabs[i]! y) ↔
        k = 0 ∨ k = s1PosT ∨ k = s1PosV ∨ k = s1PosW := by
    intro k
    rw [hc]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  obtain ⟨k, hk, hrep⟩ := exists_tab hx
  constructor
  · intro h
    rcases (hmem k).1 (List.mem_filter.2 ⟨List.mem_range.2 hk, (z2test_iff hrep).2 h⟩) with
      rfl | rfl | rfl | rfl
    · exact Or.inl (hrep.perm_eq tabRep_one)
    · exact Or.inr (Or.inl (hrep.perm_eq tabRep_posT))
    · exact Or.inr (Or.inr (Or.inl (hrep.perm_eq tabRep_vZ2)))
    · exact Or.inr (Or.inr (Or.inr (hrep.perm_eq tabRep_wZ2)))
  · intro h
    have key : ∀ k' < 8192, (k' = 0 ∨ k' = s1PosT ∨ k' = s1PosV ∨ k' = s1PosW) →
        ∀ y : Equiv.Perm (Fin 1782), TabRep s1Enum.tabs[k']! y →
          ∀ j < 4, y * sGen j = sGen j * y ∨ y * sGen j = suzInv 1 * (sGen j * y) :=
      fun k' _ hk'' y hy => (z2test_iff hy).1 (List.mem_filter.1 ((hmem k').2 hk'')).2
    rcases h with rfl | rfl | rfl | rfl
    · exact key 0 (by decide) (Or.inl rfl) 1 tabRep_one
    · exact key s1PosT (by decide) (Or.inr (Or.inl rfl)) _ tabRep_posT
    · exact key s1PosV (by decide) (Or.inr (Or.inr (Or.inl rfl))) _ tabRep_vZ2
    · exact key s1PosW (by decide) (Or.inr (Or.inr (Or.inr rfl))) _ tabRep_wZ2

theorem ne_of_tabRep {k k' : ℕ} (hk : k < 8192) (hk' : k' < 8192) (hne : k ≠ k')
    {x y : Equiv.Perm (Fin 1782)} (hx : TabRep s1Enum.tabs[k]! x)
    (hy : TabRep s1Enum.tabs[k']! y) : x ≠ y := by
  rintro rfl
  exact hne (fusionSylow_enumerates.pos_unique (by rw [enum_size]; exact hk)
    (by rw [enum_size]; exact hk') hx hy)

theorem z2_distinct : (1 : Equiv.Perm (Fin 1782)) ≠ suzInv 1 ∧ (1 : Equiv.Perm (Fin 1782)) ≠ vZ2 ∧
    (1 : Equiv.Perm (Fin 1782)) ≠ wZ2 ∧ suzInv 1 ≠ vZ2 ∧ suzInv 1 ≠ wZ2 ∧ vZ2 ≠ wZ2 :=
  ⟨ne_of_tabRep (by decide) (by decide) (by decide) tabRep_one tabRep_posT,
    ne_of_tabRep (by decide) (by decide) (by decide) tabRep_one tabRep_vZ2,
    ne_of_tabRep (by decide) (by decide) (by decide) tabRep_one tabRep_wZ2,
    ne_of_tabRep (by decide) (by decide) (by decide) tabRep_posT tabRep_vZ2,
    ne_of_tabRep (by decide) (by decide) (by decide) tabRep_posT tabRep_wZ2,
    ne_of_tabRep (by decide) (by decide) (by decide) tabRep_vZ2 tabRep_wZ2⟩

theorem conj_mem_of_conjInV {x : Tab} {a : Equiv.Perm (Fin 1782)} (hx : TabRep x a)
    (h : conjInV (gTab ()) x = true) :
    gPerm * a * gPerm⁻¹ = suzInv 1 ∨ gPerm * a * gPerm⁻¹ = vZ2 ∨ gPerm * a * gPerm⁻¹ = wZ2 := by
  simp only [conjInV, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h
  have key : ∀ {u : Equiv.Perm (Fin 1782)} {k : ℕ}, TabRep s1Enum.tabs[k]! u →
      (comp 1782 (gTab ()) x == comp 1782 s1Enum.tabs[k]! (gTab ())) = true →
        gPerm * a * gPerm⁻¹ = u := fun hu hk => by
    rw [((tabRep_gTab.comp hx).beq_iff (hu.comp tabRep_gTab)).1 hk, mul_inv_cancel_right]
  rcases h with h | h | h
  · exact Or.inl (key tabRep_posT h)
  · exact Or.inr (Or.inl (key tabRep_vZ2 h))
  · exact Or.inr (Or.inr (key tabRep_wZ2 h))

theorem gPerm_conj_suzInv : gPerm * suzInv 1 * gPerm⁻¹ = suzInv 1 ∨
    gPerm * suzInv 1 * gPerm⁻¹ = vZ2 ∨ gPerm * suzInv 1 * gPerm⁻¹ = wZ2 := by
  have h := gNorm_ok
  simp only [gNormOK, Bool.and_eq_true] at h
  exact conj_mem_of_conjInV tabRep_tTab h.1.1

theorem gPerm_conj_vZ2 : gPerm * vZ2 * gPerm⁻¹ = suzInv 1 ∨ gPerm * vZ2 * gPerm⁻¹ = vZ2 ∨
    gPerm * vZ2 * gPerm⁻¹ = wZ2 := by
  have h := gNorm_ok
  simp only [gNormOK, Bool.and_eq_true] at h
  exact conj_mem_of_conjInV tabRep_vZ2 h.1.2

end Enum

section CG


theorem tabRep_cgG {j : ℕ} (hj : j < 3) : TabRep (cgG j) (cgF gPerm j) := by
  interval_cases j
  · simp only [cgG, cgF]
    exact tabRep_cPerm (by norm_num)
  · simp only [cgG, cgF, one_ne_zero, if_false]
    exact tabRep_cPerm (by norm_num)
  · simp only [cgG, cgF, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false]
    exact tabRep_gTab

theorem tabRep_cgI {j : ℕ} (hj : j < 3) : TabRep (cgI j) (cgF gPerm j)⁻¹ := by
  have h := inverseTabs_ok
  simp only [inverseTabsOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact (tabRep_cgG hj).inv (h.2 j hj).1 (h.2 j hj).2

theorem suzB_eq_wordP : suzB0 = wordP (cgF gPerm) b0Word ∧ suzB1 = wordP (cgF gPerm) b1Word := by
  have h := gen_ok
  simp only [genOK, Bool.and_eq_true, beq_iff_eq] at h
  have h0 := tabRep_evalW (f := cgF gPerm) (w := b0Word)
    (fun z hz => tabRep_cgG (b0Word_letters z hz))
    (fun z hz => tabRep_cgI (b0Word_letters z hz))
  have h1 := tabRep_evalW (f := cgF gPerm) (w := b1Word)
    (fun z hz => tabRep_cgG (b1Word_letters z hz))
    (fun z hz => tabRep_cgI (b1Word_letters z hz))
  rw [h.1] at h0
  rw [h.2] at h1
  have e0 := tabRep_abG (j := 0) (by norm_num)
  have e1 := tabRep_abG (j := 1) (by norm_num)
  simp only [abG, abF, one_ne_zero, if_false] at e0 e1
  exact ⟨e0.perm_eq h0, e1.perm_eq h1⟩

end CG

section Centre


theorem suzInv_commute {p : Equiv.Perm (Fin 1782)} (hp : p ∈ fusionSylow) :
    suzInv 1 * p = p * suzInv 1 :=
  (mem_centralizer_singleton_iff.mp
    (invE_le_centM (i := 1) (by norm_num) (fusionSylow_le hp)).1).symm

theorem fusionSylow_le_suzM : fusionSylow ≤ suzM :=
  fun _ hx => (invE_le_centM (i := 1) (by norm_num) (fusionSylow_le hx)).2

@[expose] noncomputable def tM : ↥suzM :=
  ⟨suzInv 1, (invE_le_centM (i := 1) (by norm_num) suzInv_mem_invE).2⟩

theorem coe_tM : (tM : Equiv.Perm (Fin 1782)) = suzInv 1 := rfl

theorem tM_ne_one : tM ≠ 1 := fun h => suzInv_ne_one (i := 1) (by norm_num) (congrArg Subtype.val h)

theorem tM_comm : ∀ p ∈ pairT, tM * p = p * tM := fun _ hp =>
  Subtype.ext (suzInv_commute (mem_pairT.1 hp))

theorem tM_mul_self : tM * tM = 1 := Subtype.ext (suzInv_sq (i := 1) (by norm_num))

@[expose] noncomputable def pairV : Subgroup ↥suzM := zTwoOf pairT tM tM_comm tM_mul_self

@[expose] noncomputable def pairA : Subgroup ↥suzM := centralizer {tM}

@[expose] noncomputable def pairB : Subgroup ↥suzM := normalizer (pairV : Set ↥suzM)

theorem mem_pairA {x : ↥suzM} :
    x ∈ pairA ↔ (x : Equiv.Perm (Fin 1782)) * suzInv 1 = suzInv 1 * x := by
  rw [pairA, mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem card_pairA : Nat.card pairA = 3317760 := by
  have hmap : pairA.map suzM.subtype = invE 1 := by
    rw [invE_eq_centM (i := 1) (by norm_num)]
    ext y
    rw [mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.2 (mem_pairA.1 hx), x.2⟩
    · rintro ⟨hy, hyM⟩
      exact ⟨⟨y, hyM⟩, mem_pairA.2 (mem_centralizer_singleton_iff.1 hy), rfl⟩
  rw [← card_map_of_injective (K := pairA) suzM.subtype_injective, hmap,
    card_invE (i := 1) (by norm_num)]
  rfl

theorem pairT_le_pairA : pairT ≤ pairA := fun x hx =>
  mem_centralizer_singleton_iff.2 (tM_comm x hx).symm

theorem pairT_le_pairB : pairT ≤ pairB := le_normalizer_zTwoOf pairT tM tM_comm tM_mul_self

end Centre

theorem card_pairT :
    Nat.card pairT = 8192 := by
  rw [pairT, ← card_fusionSylow]
  exact Nat.card_congr (subgroupOfEquivOfLe fusionSylow_le_suzM).toEquiv

theorem isSylowIn_pairT :
    CFSG.Quasithin.IsSylowIn 2 pairT ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 13) (by rw [card_pairT]; norm_num), ?_⟩
  rw [relIndex_top_right]
  intro h
  have h1 := card_mul_index pairT
  rw [card_pairT, suzM_card] at h1
  omega

section Pair


theorem comm_mem_of_z2 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ fusionSylow)
    (h : x = 1 ∨ x = suzInv 1 ∨ x = vZ2 ∨ x = wZ2) {p : Equiv.Perm (Fin 1782)}
    (hp : p ∈ fusionSylow) : ⁅x, p⁆ = 1 ∨ ⁅x, p⁆ = suzInv 1 := by
  have hgen := (z2_iff hx).2 h
  rw [fusionSylow_eq] at hp
  refine commutatorElement_mem_pair_of_mem_closure (S := {g | ∃ j < 4, sGen j = g})
    (fun q hq => suzInv_commute hq) (suzInv_sq (i := 1) (by norm_num)) ?_ hp
  rintro _ ⟨j, hj, rfl⟩
  rcases hgen j hj with h1 | h1
  · left
    rw [commutatorElement_def, h1]
    group
  · right
    rw [commutatorElement_def, h1]
    group

theorem tM_mem : tM ∈ pairT := mem_pairT.2 suzInv_mem_fusionSylow

theorem center_pairT : ∀ x ∈ pairT, (∀ p ∈ pairT, x * p = p * x) → x = 1 ∨ x = tM := by
  intro x hx h
  rcases eq_of_commute_sGen (mem_pairT.1 hx) fun j hj => congrArg Subtype.val
    (h ⟨sGen j, fusionSylow_le_suzM (sGen_mem hj)⟩ (mem_pairT.2 (sGen_mem hj))) with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem mem_pairV {x : ↥suzM} : x ∈ pairV ↔
    (x : Equiv.Perm (Fin 1782)) = 1 ∨ (x : Equiv.Perm (Fin 1782)) = suzInv 1 ∨
      (x : Equiv.Perm (Fin 1782)) = vZ2 ∨ (x : Equiv.Perm (Fin 1782)) = wZ2 := by
  rw [pairV, mem_zTwoOf]
  constructor
  · rintro ⟨hx, h⟩
    refine (z2_iff (mem_pairT.1 hx)).1 fun j hj => ?_
    have hs : (⟨sGen j, fusionSylow_le_suzM (sGen_mem hj)⟩ : ↥suzM) ∈ pairT :=
      mem_pairT.2 (sGen_mem hj)
    rcases h _ hs with h1 | h1
    · left
      simpa using congrArg Subtype.val (mul_eq_of_commutatorElement h1)
    · exact Or.inr (congrArg Subtype.val (mul_eq_of_commutatorElement h1))
  · intro h
    have hS : (x : Equiv.Perm (Fin 1782)) ∈ fusionSylow := by
      rcases h with h | h | h | h <;> rw [h]
      · exact one_mem _
      · exact suzInv_mem_fusionSylow
      · exact vZ2_mem
      · exact wZ2_mem
    refine ⟨mem_pairT.2 hS, fun p hp => ?_⟩
    rcases comm_mem_of_z2 hS h (mem_pairT.1 hp) with h1 | h1
    · left
      apply suzM.subtype_injective
      rw [map_commutatorElement, map_one]
      exact h1
    · right
      apply suzM.subtype_injective
      rw [map_commutatorElement]
      exact h1

theorem card_pairV : Nat.card pairV = 4 := by
  obtain ⟨d01, d02, d03, d12, d13, d23⟩ := z2_distinct
  have hS : ((pairV.map suzM.subtype : Subgroup (Equiv.Perm (Fin 1782))) :
      Set (Equiv.Perm (Fin 1782))) = {1, suzInv 1, vZ2, wZ2} := by
    ext y
    rw [SetLike.mem_coe, mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_pairV.1 hx
    · intro hy
      have hyS : y ∈ fusionSylow := by
        rcases hy with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact suzInv_mem_fusionSylow
        · exact vZ2_mem
        · exact wZ2_mem
      exact ⟨⟨y, fusionSylow_le_suzM hyS⟩, mem_pairV.2 hy, rfl⟩
  have h4 : ({1, suzInv 1, vZ2, wZ2} : Set (Equiv.Perm (Fin 1782))).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [d01, d02, d03]),
      Set.ncard_insert_of_notMem (by simp [d12, d13]), Set.ncard_pair d23]
  rw [← card_map_of_injective (K := pairV) suzM.subtype_injective, ← h4, ← hS]
  exact Nat.card_coe_set_eq _

theorem wZ2_eq : wZ2 = suzInv 1 * vZ2 := by
  obtain ⟨d01, d02, -, d12, -, -⟩ := z2_distinct
  have ht : tM ∈ pairV := mem_pairV.2 (Or.inr (Or.inl rfl))
  have hv : (⟨vZ2, fusionSylow_le_suzM vZ2_mem⟩ : ↥suzM) ∈ pairV :=
    mem_pairV.2 (Or.inr (Or.inr (Or.inl rfl)))
  have h := mem_pairV.1 (mul_mem ht hv)
  change suzInv 1 * vZ2 = 1 ∨ suzInv 1 * vZ2 = suzInv 1 ∨ suzInv 1 * vZ2 = vZ2 ∨
    suzInv 1 * vZ2 = wZ2 at h
  rcases h with h | h | h | h
  · refine absurd ?_ d12
    rw [← mul_right_inj (suzInv 1), h, suzInv_sq (i := 1) (by norm_num)]
  · exact absurd (mul_left_cancel (h.trans (mul_one _).symm)).symm d02
  · exact absurd (mul_right_cancel (h.trans (one_mul _).symm)).symm d01
  · exact h.symm

@[expose] noncomputable def vZ2M : ↥suzM := ⟨vZ2, fusionSylow_le_suzM vZ2_mem⟩

theorem coe_vZ2M : (vZ2M : Equiv.Perm (Fin 1782)) = vZ2 := rfl

theorem gM_mem_pairB : gM ∈ pairB := by
  have key : ∀ u : ↥suzM, (gPerm * u * gPerm⁻¹ = suzInv 1 ∨ gPerm * u * gPerm⁻¹ = vZ2 ∨
      gPerm * u * gPerm⁻¹ = wZ2) → gM * u * gM⁻¹ ∈ pairV := fun u h => by
    rw [mem_pairV, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_gM]
    exact Or.inr h
  have ht : gM * tM * gM⁻¹ ∈ pairV := key tM (by rw [coe_tM]; exact gPerm_conj_suzInv)
  have hv : gM * vZ2M * gM⁻¹ ∈ pairV := key vZ2M (by rw [coe_vZ2M]; exact gPerm_conj_vZ2)
  have hsub : ∀ u ∈ pairV, gM * u * gM⁻¹ ∈ pairV := by
    intro u hu
    rcases mem_pairV.1 hu with h | h | h | h
    · rw [show u = 1 from Subtype.ext h, mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [show u = tM from Subtype.ext (h.trans coe_tM.symm)]
      exact ht
    · rw [show u = vZ2M from Subtype.ext (h.trans coe_vZ2M.symm)]
      exact hv
    · rw [show u = tM * vZ2M from
          Subtype.ext (by rw [h, wZ2_eq, Subgroup.coe_mul, coe_tM, coe_vZ2M]),
        show gM * (tM * vZ2M) * gM⁻¹ = gM * tM * gM⁻¹ * (gM * vZ2M * gM⁻¹) by group]
      exact mul_mem ht hv
  rw [pairB, mem_normalizer_iff]
  intro u
  refine ⟨hsub u, fun hu => ?_⟩
  let f : pairV → pairV := fun v => ⟨gM * v * gM⁻¹, hsub v v.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have h : gM * (a : ↥suzM) * gM⁻¹ = gM * b * gM⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  obtain ⟨v, hv⟩ := Finite.injective_iff_surjective.1 hf ⟨gM * u * gM⁻¹, hu⟩
  have h : gM * (v : ↥suzM) * gM⁻¹ = gM * u * gM⁻¹ := congrArg Subtype.val hv
  rw [← mul_left_cancel (mul_right_cancel h)]
  exact v.2

theorem card_pairB_dvd : Nat.card pairB ∣ 19906560 := by
  have h6 := CFSG.GH74.GLS.Stage1.Thm6.Sec13.relIndex_dvd_six card_pairV (le_refl pairB)
  have hle : centralizer (pairV : Set ↥suzM) ⊓ pairB ⊓ pairB ≤ pairA := fun x hx =>
    mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hx.1.1 tM (mem_pairV.2 (Or.inr (Or.inl rfl)))).symm
  rw [← relIndex_mul_card (H := centralizer (pairV : Set ↥suzM) ⊓ pairB) (K := pairB),
    show (19906560 : ℕ) = 6 * 3317760 by norm_num]
  exact Nat.mul_dvd_mul h6 ((card_dvd_of_le hle).trans (dvd_of_eq card_pairA))

theorem pairA_sup_pairB : pairA ⊔ pairB = ⊤ := by
  have hA : ∀ {k : ℕ}, k < 10 → cPerm k ∈ (pairA ⊔ pairB).map suzM.subtype := by
    intro k hk
    have hc := invE_le_centM (i := 1) (by norm_num) (cPerm_mem hk)
    exact ⟨⟨cPerm k, hc.2⟩,
      (le_sup_left : pairA ≤ pairA ⊔ pairB) (mem_pairA.2 (mem_centralizer_singleton_iff.1 hc.1)),
      rfl⟩
  have hlet : ∀ j, j < 3 → cgF gPerm j ∈ (pairA ⊔ pairB).map suzM.subtype := by
    intro j hj
    interval_cases j
    · exact hA (k := 2) (by norm_num)
    · exact hA (k := 4) (by norm_num)
    · exact ⟨gM, (le_sup_right : pairB ≤ pairA ⊔ pairB) gM_mem_pairB, rfl⟩
  have hM : suzM ≤ (pairA ⊔ pairB).map suzM.subtype := by
    show closure {suzB0, suzB1} ≤ _
    rw [closure_le]
    rintro _ (rfl | rfl)
    · rw [suzB_eq_wordP.1]
      exact wordP_mem fun z hz => hlet _ (b0Word_letters z hz)
    · rw [suzB_eq_wordP.2]
      exact wordP_mem fun z hz => hlet _ (b1Word_letters z hz)
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hM x.2
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

theorem pair_map (ψ : ↥suzM ≃* ↥suzM) (hψ : pairT.map ψ.toMonoidHom = pairT) :
    pairA.map ψ.toMonoidHom = pairA ∧ pairB.map ψ.toMonoidHom = pairB :=
  map_centralizer_normalizer_zTwoOf_eq tM_mem tM_ne_one tM_comm tM_mul_self center_pairT ψ hψ

end Pair

section LPair


theorem isLPair_pair : IsLPair IsCalL0 pairT pairA pairB where
  le_left := pairT_le_pairA
  le_right := pairT_le_pairB
  ne_top_left h := by
    have h1 := card_pairA
    rw [h, card_top, suzM_card] at h1
    norm_num at h1
  ne_top_right h := by
    have h1 := card_pairB_dvd
    rw [h, card_top, suzM_card] at h1
    norm_num at h1
  not_left := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 13) (N := 3317760)
    (by decide +kernel) (dvd_of_eq card_pairA)
  not_right := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 14) (N := 19906560)
    (by decide +kernel) card_pairB_dvd
  sup_eq_top := pairA_sup_pairB

end LPair

theorem card_outer_suzM_le :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥suzM) ≤ 2 := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .Suz ≃* ↥suzM := suzEquivM
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact outer_carrier_suz.1.le

end CFSG.LocalAnalysis.WeakClosure81.SporSuz

namespace CFSG.LocalAnalysis.WeakClosure81


open SporSuz in
theorem asch54SporGenAt_suz :
    Asch54SporGenAt .Suz :=
  asch54SporGenAt_of_isLPair_of_aut
    (CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.SuzOddCore.suzEquivM)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    card_outer_suzM_le isSylowIn_pairT isLPair_pair pair_map

end CFSG.LocalAnalysis.WeakClosure81

end
