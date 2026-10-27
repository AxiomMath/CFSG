module

public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Data.CFSGNative.Bridge.SurjD
public import Mathlib.Data.Int.Star
public import Mathlib.Order.Interval.Finset.Box

public section

namespace CFSG.Sporadic.Bridge.TableSurj

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.SurjD.Native TauCeti

variable (n : ℕ) (S : Spec) (G : Array Table)

noncomputable abbrev imgT : Array Table := S.imgWords.map (wordT n (baseLetter G))

noncomputable abbrev imgTv : Array Table := (imgT n S G).map (invT n)

structure BridgeFacts (α β : Table) : Prop where
  sizeImg : S.imgWords.size = S.m
  sizeSurj : S.surjWords.size = 2
  relsLt : ∀ r ∈ S.rels, ∀ l ∈ r, l.1 < S.m
  imgLetters : ∀ w ∈ S.imgWords, ∀ z ∈ w, 0 ≤ z ∧ z.toNat < G.size
  letters : ∀ w ∈ S.surjWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ S.m
  inv : ∀ k < S.m, invOK n (imgT n S G)[k]! (imgTv n S G)[k]! = true
  rels : ∀ r ∈ S.rels, wordT n (imgLetter (imgT n S G) (imgTv n S G)) (r.map letterOf) = idT n
  surjA : wordT n (imgLetter (imgT n S G) (imgTv n S G)) S.surjWords[0]! = α
  surjB : wordT n (imgLetter (imgT n S G) (imgTv n S G)) S.surjWords[1]! = β

variable {n S G} {α β : Table}

theorem bridge_facts (h : wordChecks n S G α β = true) : BridgeFacts n S G α β := by
  unfold wordChecks inverseChecks imageChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Array.all_eq_true,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, fun r hr l hl => h3 r hr l hl, ?_, ?_, h6, h7, h8, h9⟩
  · intro w hw z hz
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hw
    exact h4 i hi z hz
  · intro w hw z hz
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hw
    exact h5 i hi z hz

variable {J : Type*} [Group J] [MulAction J (Fin n)] (hn : n < 2 ^ 32)
  (hB : BridgeFacts n S G α β) (gG : ℕ → J) (hG : ∀ l < G.size, Rep n G[l]! (gG l))

@[expose] noncomputable def img (S : Spec) (gG : ℕ → J) (k : ℕ) : J :=
  wordG (fun z => gG z.toNat) S.imgWords[k]!

theorem imgT_getElem (hB : BridgeFacts n S G α β) {k : ℕ} (hk : k < S.m) :
    (imgT n S G)[k]! = wordT n (baseLetter G) S.imgWords[k]! := by
  have hk' : k < S.imgWords.size := by rw [hB.sizeImg]; exact hk
  rw [getElem!_pos (imgT n S G) k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
    getElem!_pos S.imgWords k hk']

include hn hB hG

theorem rep_img {k : ℕ} (hk : k < S.m) : Rep n (imgT n S G)[k]! (img S gG k) := by
  have hk' : k < S.imgWords.size := by rw [hB.sizeImg]; exact hk
  rw [imgT_getElem hB hk]
  refine Rep.wordT hn _ fun z hz => ?_
  have hz' := hB.imgLetters _ (by rw [getElem!_pos S.imgWords k hk']; exact Array.getElem_mem hk')
    z hz
  exact hG z.toNat hz'.2

theorem rep_img_inv {k : ℕ} (hk : k < S.m) : Rep n (imgTv n S G)[k]! (img S gG k)⁻¹ := by
  have hk' : k < (imgT n S G).size := by rw [Array.size_map, hB.sizeImg]; exact hk
  have e : (imgTv n S G)[k]! = invT n (imgT n S G)[k]! := by
    rw [getElem!_pos (imgTv n S G) k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
      getElem!_pos (imgT n S G) k hk']
  rw [e]
  exact Rep.inv_of_invOK (rep_img hn hB gG hG hk) (by rw [← e]; exact hB.inv k hk)

omit hn hB hG

@[expose] noncomputable def imgG (S : Spec) (gG : ℕ → J) (z : ℤ) : J :=
  if 0 < z then img S gG (z - 1).toNat else (img S gG (-z - 1).toNat)⁻¹

include hn hB hG

theorem rep_imgLetter {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ S.m) :
    Rep n (imgLetter (imgT n S G) (imgTv n S G) z) (imgG S gG z) := by
  unfold imgLetter imgG
  split_ifs with h
  · exact rep_img hn hB gG hG (by omega)
  · exact rep_img_inv hn hB gG hG (by omega)

omit hn hB hG

theorem wordG_map_letterOf (v : List (ℕ × Bool)) :
    wordG (imgG S gG) (v.map letterOf) = wordProd (img S gG) v := by
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

theorem letterOf_ne_zero (l : ℕ × Bool) : letterOf l ≠ 0 := by
  intro h
  have := letterOf_natAbs l
  rw [h] at this
  simp at this

theorem eq_of_rep_eq [FaithfulSMul J (Fin n)] {g h : J} {X : Table} (hg : Rep n X g)
    (hh : Rep n X h) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (M := J) (α := Fin n) fun i => ?_
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

include hn hB hG

theorem relators_eval [FaithfulSMul J (Fin n)] : ∀ v ∈ S.rels, wordProd (img S gG) v = 1 := by
  intro v hv
  have hlt := hB.relsLt v hv
  have hrep : Rep n (wordT n (imgLetter (imgT n S G) (imgTv n S G)) (v.map letterOf))
      (wordG (imgG S gG) (v.map letterOf)) := by
    apply Rep.wordT hn
    intro z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    exact rep_imgLetter hn hB gG hG (letterOf_ne_zero l)
      (by rw [letterOf_natAbs]; exact hlt l hl)
  rw [← wordG_map_letterOf]
  rw [hB.rels v hv] at hrep
  exact eq_of_rep_eq hrep (Rep.idT hn)

omit hn hB hG

variable (P : GroupPresentation)

@[expose] noncomputable def presLetter (z : ℤ) : P.Group :=
  if 0 < z then presGen P (z - 1).toNat else (presGen P (-z - 1).toNat)⁻¹

theorem presHom_presLetter (hm : P.generatorCount = S.m) (hrel : ∀ v ∈ P.relatorLetters,
    wordProd (img S gG) v = 1) {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ S.m) :
    presHom P (img S gG) hrel (presLetter P z) = imgG S gG z := by
  unfold presLetter imgG
  split_ifs with h
  · exact presHom_presGen _ _ _ (by rw [hm]; omega)
  · rw [map_inv, presHom_presGen _ _ _ (by rw [hm]; omega)]

theorem wordG_imgG_mem (hm : P.generatorCount = S.m) (hrel : ∀ v ∈ P.relatorLetters,
    wordProd (img S gG) v = 1) {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ S.m) :
    wordG (imgG S gG) w ∈ (presHom P (img S gG) hrel).range := by
  refine ⟨wordG (presLetter P) w, ?_⟩
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact presHom_presLetter gG P hm hrel (hw z hz).1 (hw z hz).2

variable {P}

theorem surjWords_mem (hB : BridgeFacts n S G α β) {i : ℕ} (hi : i < 2) :
    S.surjWords[i]! ∈ S.surjWords := by
  have hi' : i < S.surjWords.size := by rw [hB.sizeSurj]; exact hi
  rw [getElem!_pos S.surjWords i hi']
  exact Array.getElem_mem hi'

include hn hB hG

theorem rep_surjWord {i : ℕ} (hi : i < 2) :
    Rep n (wordT n (imgLetter (imgT n S G) (imgTv n S G)) S.surjWords[i]!)
      (wordG (imgG S gG) S.surjWords[i]!) :=
  Rep.wordT hn _ fun z hz =>
    rep_imgLetter hn hB gG hG (hB.letters _ (surjWords_mem hB hi) z hz).1
      (hB.letters _ (surjWords_mem hB hi) z hz).2

variable [FaithfulSMul J (Fin n)] {a b : J}

theorem a_mem_range (ha : Rep n α a) (hm : P.generatorCount = S.m)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (img S gG) v = 1) :
    a ∈ (presHom P (img S gG) hrel).range := by
  have hr := rep_surjWord hn hB gG hG (i := 0) (by decide)
  rw [hB.surjA] at hr
  rw [← eq_of_rep_eq hr ha]
  exact wordG_imgG_mem gG P hm hrel fun z hz => hB.letters _ (surjWords_mem hB (by decide)) z hz

theorem b_mem_range (hb : Rep n β b) (hm : P.generatorCount = S.m)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (img S gG) v = 1) :
    b ∈ (presHom P (img S gG) hrel).range := by
  have hr := rep_surjWord hn hB gG hG (i := 1) (by decide)
  rw [hB.surjB] at hr
  rw [← eq_of_rep_eq hr hb]
  exact wordG_imgG_mem gG P hm hrel fun z hz => hB.letters _ (surjWords_mem hB (by decide)) z hz

omit hB

theorem exists_surjective (ha : Rep n α a) (hb : Rep n β b)
    (hab : Subgroup.closure ({a, b} : Set J) = ⊤) (hm : P.generatorCount = S.m)
    (hrels : P.relatorLetters = S.rels) (hcheck : wordChecks n S G α β = true) :
    ∃ φ : P.Group →* J, Function.Surjective φ := by
  have hB := bridge_facts hcheck
  have hrel : ∀ v ∈ P.relatorLetters, wordProd (img S gG) v = 1 := by
    rw [hrels]; exact relators_eval hn hB gG hG
  refine ⟨presHom P (img S gG) hrel, ?_⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact a_mem_range hn hB gG hG ha hm hrel
  · exact b_mem_range hn hB gG hG hb hm hrel

theorem nonempty_mulEquiv_of_card_le (ha : Rep n α a) (hb : Rep n β b)
    (hab : Subgroup.closure ({a, b} : Set J) = ⊤) (hm : P.generatorCount = S.m)
    (hrels : P.relatorLetters = S.rels) (hcheck : wordChecks n S G α β = true) [Finite P.Group]
    {k : ℕ} (hcard : Nat.card P.Group ≤ k) (hk : k ≤ Nat.card J) : Nonempty (J ≃* P.Group) := by
  obtain ⟨φ, hφ⟩ := exists_surjective hn gG hG ha hb hab hm hrels hcheck
  exact nonempty_mulEquiv_of_surjective φ hφ hcard hk

end CFSG.Sporadic.Bridge.TableSurj
