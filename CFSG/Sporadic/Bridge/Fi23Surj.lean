module

public import CFSG.Sporadic.Fi23.Simple
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Presentation.Fi23
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public meta import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9111
public import Certificates.Certificate9206
public import Certificates.Certificate1012
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate9206Base

public section

namespace CFSG.Sporadic.Bridge.Fi23

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native CFSG.Sporadic.Bridge.Fi23GPL.Native TauCeti

noncomputable abbrev imgT : Array Table := imgWords.map (wordT 31671 (genTables orb))

noncomputable abbrev imgTv : Array Table := imgT.map (invT 31671)

theorem seedLetter_eq :
    seedLetter #[orb.alpha, orb.alpha, orb.beta, invT 31671 orb.beta] = genTables orb := by
  funext z
  unfold seedLetter genTables
  by_cases h1 : z = 1
  · simp [h1]
  · by_cases h2 : z = -1
    · simp [h2]
    · by_cases h3 : z = 2
      · simp [h3]
      · simp [h1, h2, h3]

theorem letters_ok :
    ∀ w ∈ surjWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10 :=
  Certificates.certificate9206.2.2.1

private theorem invT_eq_foldl (n : ℕ) (P : Table) :
    invT n P = (List.range' 0 n).foldl
      (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0) := by
  unfold invT
  simp [Id.run]
  rfl

private theorem invT_foldl_spec {n : ℕ} (P : Table) (hlt : ∀ i < n, (P[i]!).toNat < n)
    (hinj : ∀ i < n, ∀ i' < n, (P[i]!).toNat = (P[i']!).toNat → i = i') :
    ∀ m ≤ n, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0)).size = n ∧
      ∀ i < m, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i))
          (Array.replicate n 0))[(P[i]!).toNat]! = UInt32.ofNat i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨hs, hi⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [zero_add, one_mul]
    set r := (List.range' 0 m).foldl (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i))
      (Array.replicate n 0) with hr
    refine ⟨by rw [Array.size_setIfInBounds, hs], fun i hi' => ?_⟩
    have hmn : m < n := by omega
    have hPm := hlt m hmn
    have hbound : (P[m]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
      rw [Array.size_setIfInBounds, hs]; exact hPm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt' | heq
    · have hne : (P[m]!).toNat ≠ (P[i]!).toNat := fun h' => by
        have := hinj m hmn i (by omega) h'
        omega
      have hbi : (P[i]!).toNat < r.size := by rw [hs]; exact hlt i (by omega)
      have hbi' : (P[i]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
        rw [Array.size_setIfInBounds]; exact hbi
      rw [getElem!_pos (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)) (P[i]!).toNat hbi',
        Array.getElem_setIfInBounds_ne hbi hne, ← getElem!_pos r (P[i]!).toNat hbi]
      exact hi i hlt'
    · subst heq
      rw [getElem!_pos (r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (P[i]!).toNat hbound,
        Array.getElem_setIfInBounds_self]

theorem rep_invT {T : Table} {g : J} (hT : Rep 31671 T g) :
    Rep 31671 (invT 31671 T) g⁻¹ := by
  have hlt : ∀ i < 31671, (T[i]!).toNat < 31671 := by
    intro i hi
    have := hT i hi
    unfold ap at this
    rw [this]
    exact idx_lt g hi
  have hinj : ∀ i < 31671, ∀ i' < 31671, (T[i]!).toNat = (T[i']!).toNat → i = i' := by
    intro i hi i' hi' h
    have h1 := hT i hi
    have h2 := hT i' hi'
    unfold ap at h1 h2
    rw [h1, h2] at h
    have := congrArg (idx 31671 g⁻¹) h
    rwa [idx_inv_idx, idx_inv_idx] at this
  refine Rep.inv_of_invOK hT ?_
  rw [invOK, allIn_eq_true]
  intro i _ hi
  have h := (invT_foldl_spec T hlt hinj 31671 le_rfl).2 i hi
  rw [← invT_eq_foldl] at h
  rw [beq_iff_eq]
  unfold ap
  rw [h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hi.trans (by norm_num))]

@[expose] noncomputable def img
    (k : ℕ) : J := wordG genG imgWords[k]!

theorem imgT_getElem {k : ℕ} (hk : k < 10) :
    imgT[k]! = wordT 31671 (genTables orb) imgWords[k]! := by
  have hk' : k < imgWords.size := by rw [Certificates.certificate9206.1]; exact hk
  rw [getElem!_pos imgT k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
    getElem!_pos imgWords k hk']

theorem rep_img
    {k : ℕ} (hk : k < 10) : Rep 31671 imgT[k]! (img k) := by
  rw [imgT_getElem hk]
  exact Rep.wordT (by norm_num) _ fun l _ => rep_gen l

theorem rep_img_inv
    {k : ℕ} (hk : k < 10) : Rep 31671 imgTv[k]! (img k)⁻¹ := by
  have hk' : k < imgT.size := by
    rw [Array.size_map, Certificates.certificate9206.1]; exact hk
  have e : imgTv[k]! = invT 31671 imgT[k]! := by
    rw [getElem!_pos imgTv k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
      getElem!_pos imgT k hk']
  rw [e]
  exact rep_invT (rep_img hk)

@[expose] noncomputable def imgG (z : ℤ) : J :=
  if 0 < z then img (z - 1).toNat else (img (-z - 1).toNat)⁻¹

theorem rep_imgLetter
    {z : ℤ} (hz : z.natAbs ≤ 10) :
    Rep 31671 (imgLetter imgT imgTv z) (imgG z) := by
  unfold imgLetter imgG
  split_ifs with h
  · exact rep_img (by omega)
  · exact rep_img_inv (by omega)

theorem wordG_map_letterOf (v : List (ℕ × Bool)) :
    wordG imgG (v.map letterOf) = wordProd img v := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    simp only [wordProd, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b <;> simp [letterOf, imgG]

theorem letterOf_natAbs (l : ℕ × Bool) : (letterOf l).natAbs = l.1 + 1 := by
  unfold letterOf; split <;> omega

theorem eq_one_of_tupleEq {g : J} {X : Table} (hX : Rep 31671 X g)
    (h : tupleEq (apT X chainQ) chainQ = true) : g = 1 := by
  apply sep
  intro t ht
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq] at h
  have := (allIn_eq_true.1 h.2) t (Nat.zero_le _) ht
  simp only [beq_iff_eq] at this
  rw [apT_get _ _ ht, hX _ (chainQ_lt ht)] at this
  exact this

theorem eq_of_tupleEq
    {g h : J} {X Y : Table} (hX : Rep 31671 X g) (hY : Rep 31671 Y h)
    (e : tupleEq (apT X chainQ) (apT Y chainQ) = true) : g = h := by
  have : h⁻¹ * g = 1 := by
    apply sep
    intro t ht
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq, apT_size] at e
    have := (allIn_eq_true.1 e.2) t (Nat.zero_le _) ht
    simp only [beq_iff_eq] at this
    rw [apT_get _ _ ht, apT_get _ _ ht, hX _ (chainQ_lt ht), hY _ (chainQ_lt ht)] at this
    rw [idx_mul, this, idx_inv_idx]
  rw [inv_mul_eq_one] at this
  exact this.symm

private theorem presentation_eq : SporadicName.Fi23.presentation = Sporadic.fi23Presentation :=
  rfl

theorem relatorLetters_eq : Sporadic.fi23Presentation.relatorLetters = rels := by
  rw [Sporadic.fi23Presentation_relatorLetters]
  rfl

theorem generatorCount_eq : Sporadic.fi23Presentation.generatorCount = 10 := by
  simp [GroupPresentation.generatorCount]

theorem letters_lt {v : List (ℕ × Bool)} (hv : v ∈ Sporadic.fi23Presentation.relatorLetters) :
    ∀ l ∈ v, l.1 < 10 := by
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hv
  obtain ⟨w, -, rfl⟩ := hv
  intro l hl
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
  exact x.1.isLt.trans_eq generatorCount_eq

theorem mat_inv (g : J) : mat g⁻¹ = (mat g)⁻¹ := by
  change (((g : GL (Fin 253) (ZMod 3))⁻¹ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) = _
  rw [Matrix.coe_units_inv]

theorem mat_list_prod (l : List J) :
    mat l.prod = (l.map mat).prod := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.prod_cons, mat_mul, ih, List.map_cons, List.prod_cons]

theorem mat_genG (z : ℤ) : mat (genG z) =
    if z = 1 then mA else if z = -1 then mA⁻¹ else if z = 2 then mB else mB⁻¹ := by
  unfold genG
  split_ifs <;> simp only [mat_inv, mat_a, mat_b]

theorem mat_img {X : ℕ → Matrix (Fin 253) (Fin 253) (ZMod 3)}
    (hX : ∀ k < 10, X k = (imgWords[k]!.map fun z =>
      if z = 1 then mA else if z = -1 then mA⁻¹ else if z = 2 then mB else mB⁻¹).prod)
    {k : ℕ} (hk : k < 10) : mat (img k) = X k := by
  rw [hX k hk, img, wordG, mat_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z _
  exact mat_genG z

theorem relators_eval :
    ∀ v ∈ Sporadic.fi23Presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  have hlt := letters_lt hv
  rw [relatorLetters_eq] at hv
  obtain ⟨X, hX, hrel, -, -⟩ := Certificates.certificate9206.2.2.2
  apply mat_injective
  rw [mat_one, ← hrel v hv, wordProd, mat_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hk : l.1 < 10 := hlt l hl
  simp only [Function.comp_apply]
  split
  · exact mat_img hX hk
  · rw [mat_inv, mat_img hX hk]

@[expose] noncomputable def toJ :
    Sporadic.fi23Presentation.Group →* J :=
  presHom Sporadic.fi23Presentation img relators_eval

@[expose] noncomputable def presLetter (z : ℤ) : Sporadic.fi23Presentation.Group :=
  if 0 < z then presGen Sporadic.fi23Presentation (z - 1).toNat
  else (presGen Sporadic.fi23Presentation (-z - 1).toNat)⁻¹

theorem toJ_presLetter
    {z : ℤ} (hz : z.natAbs ≤ 10) :
    toJ (presLetter z) = imgG z := by
  unfold presLetter imgG toJ
  split_ifs with h
  · exact presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega)
  · rw [map_inv, presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega)]

theorem wordG_imgG_mem
    {w : List ℤ} (hw : ∀ z ∈ w, z.natAbs ≤ 10) :
    wordG imgG w ∈ toJ.range := by
  refine ⟨wordG presLetter w, ?_⟩
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact toJ_presLetter (hw z hz)

theorem surjWords_mem
    {i : ℕ} (hi : i < 2) : surjWords[i]! ∈ surjWords := by
  have hi' : i < surjWords.size := by rw [Certificates.certificate9206.2.1]; exact hi
  rw [getElem!_pos surjWords i hi']
  exact Array.getElem_mem hi'

theorem rep_surjWord
    {i : ℕ} (hi : i < 2) :
    Rep 31671 (wordT 31671 (imgLetter imgT imgTv) surjWords[i]!) (wordG imgG surjWords[i]!) :=
  Rep.wordT (by norm_num) _ fun z hz =>
    rep_imgLetter (letters_ok _ (surjWords_mem hi) z hz).2

theorem mat_wordG_imgG
    {X : ℕ → Matrix (Fin 253) (Fin 253) (ZMod 3)}
    (hX : ∀ k < 10, X k = (imgWords[k]!.map fun z =>
      if z = 1 then mA else if z = -1 then mA⁻¹ else if z = 2 then mB else mB⁻¹).prod)
    {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10) :
    mat (wordG imgG w) =
      (w.map fun z => if 0 < z then X (z - 1).toNat else (X (-z - 1).toNat)⁻¹).prod := by
  rw [wordG, mat_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  have h := hw z hz
  simp only [Function.comp_apply]
  unfold imgG
  split
  · exact mat_img hX (by omega)
  · rw [mat_inv, mat_img hX (by omega)]

theorem surjA_eq :
    wordG imgG surjWords[0]! = a := by
  obtain ⟨X, hX, -, hA, -⟩ := Certificates.certificate9206.2.2.2
  apply mat_injective
  rw [mat_wordG_imgG hX (letters_ok _ (surjWords_mem (by decide))), hA, mat_a]

theorem surjB_eq :
    wordG imgG surjWords[1]! = b := by
  obtain ⟨X, hX, -, -, hB⟩ := Certificates.certificate9206.2.2.2
  apply mat_injective
  rw [mat_wordG_imgG hX (letters_ok _ (surjWords_mem (by decide))), hB, mat_b]

theorem a_mem_range :
    a ∈ toJ.range := by
  rw [← surjA_eq]
  exact wordG_imgG_mem fun z hz => (letters_ok _ (surjWords_mem (by decide)) z hz).2

theorem b_mem_range :
    b ∈ toJ.range := by
  rw [← surjB_eq]
  exact wordG_imgG_mem fun z hz => (letters_ok _ (surjWords_mem (by decide)) z hz).2

theorem toJ_surjective :
    Function.Surjective toJ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact a_mem_range
  · exact b_mem_range

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Fi23.Group)
    (hcard : Nat.card SporadicName.Fi23.Group ≤ 4089470473293004800) :
    Nonempty (Blueprint.NativeSporadic.Fi23 ≃* SporadicName.Fi23.Group) := by
  revert hfin hcard
  show Finite SporadicName.Fi23.presentation.Group →
    Nat.card SporadicName.Fi23.presentation.Group ≤ 4089470473293004800 →
    Nonempty (Blueprint.NativeSporadic.Fi23 ≃* SporadicName.Fi23.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective toJ toJ_surjective hcard (by rw [card_J])
  exact ⟨fi23EquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Fi23 ≃* SporadicName.Fi23.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Fi23.finite_card_le.1
    Presentation.Fi23.finite_card_le.2

end CFSG.Sporadic.Bridge.Fi23
