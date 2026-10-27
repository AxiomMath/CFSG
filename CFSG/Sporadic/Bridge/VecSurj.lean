module

public import CFSG.Sporadic.HS.Chain
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Data.CFSGNative.Bridge.SurjD

public section

namespace CFSG.Sporadic.Bridge.VecSurj

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.SurjD.Native TauCeti

variable (D : VecData) (S : Spec) (G : Array Table)

noncomputable abbrev imgT : Array Table := S.imgWords.map (wordT D.n (baseLetter G))

noncomputable abbrev imgTv : Array Table := (imgT D S G).map (invT D.n)

structure BridgeFacts : Prop where
  sizeImg : S.imgWords.size = S.m
  sizeSurj : S.surjWords.size = 2
  relsLt : ∀ r ∈ S.rels, ∀ l ∈ r, l.1 < S.m
  imgLetters : ∀ w ∈ S.imgWords, ∀ z ∈ w, 0 ≤ z ∧ z.toNat < G.size
  letters : ∀ w ∈ S.surjWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ S.m
  inv : ∀ k < S.m, invOK D.n (imgT D S G)[k]! (imgTv D S G)[k]! = true
  rels : ∀ r ∈ S.rels,
    wordT D.n (imgLetter (imgT D S G) (imgTv D S G)) (r.map letterOf) = idT D.n
  surjA : wordT D.n (imgLetter (imgT D S G) (imgTv D S G)) S.surjWords[0]! = (O D).alpha
  surjB : wordT D.n (imgLetter (imgT D S G) (imgTv D S G)) S.surjWords[1]! = (O D).beta

variable {D S G}

theorem bridge_facts (h : wordChecks D.n S G (O D).alpha (O D).beta = true) :
    BridgeFacts D S G := by
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

variable {c : ℕ} (hF : Facts D c) (hB : BridgeFacts D S G) (gG : ℕ → J D)
  (hG : ∀ l < G.size, Rep D.n G[l]! (gG l))

@[expose] noncomputable def img (S : Spec) (gG : ℕ → J D) (k : ℕ) : J D :=
  wordG (fun z => gG z.toNat) S.imgWords[k]!

theorem imgT_getElem (hB : BridgeFacts D S G) {k : ℕ} (hk : k < S.m) :
    (imgT D S G)[k]! = wordT D.n (baseLetter G) S.imgWords[k]! := by
  have hk' : k < S.imgWords.size := by rw [hB.sizeImg]; exact hk
  rw [getElem!_pos (imgT D S G) k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
    getElem!_pos S.imgWords k hk']

include hF hB hG

theorem rep_img {k : ℕ} (hk : k < S.m) : Rep D.n (imgT D S G)[k]! (img S gG k) := by
  have hk' : k < S.imgWords.size := by rw [hB.sizeImg]; exact hk
  rw [imgT_getElem hB hk]
  refine Rep.wordT (n_lt_two_pow hF) _ fun z hz => ?_
  have hz' := hB.imgLetters _ (by rw [getElem!_pos S.imgWords k hk']; exact Array.getElem_mem hk')
    z hz
  exact hG z.toNat hz'.2

theorem rep_img_inv {k : ℕ} (hk : k < S.m) :
    Rep D.n (imgTv D S G)[k]! (img S gG k)⁻¹ := by
  have hk' : k < (imgT D S G).size := by rw [Array.size_map, hB.sizeImg]; exact hk
  have e : (imgTv D S G)[k]! = invT D.n (imgT D S G)[k]! := by
    rw [getElem!_pos (imgTv D S G) k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
      getElem!_pos (imgT D S G) k hk']
  rw [e]
  exact Rep.inv_of_invOK (rep_img hF hB gG hG hk) (by rw [← e]; exact hB.inv k hk)

omit hF hB hG

@[expose] noncomputable def imgG (S : Spec) (gG : ℕ → J D) (z : ℤ) : J D :=
  if 0 < z then img S gG (z - 1).toNat else (img S gG (-z - 1).toNat)⁻¹

include hF hB hG

theorem rep_imgLetter {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ S.m) :
    Rep D.n (imgLetter (imgT D S G) (imgTv D S G) z) (imgG S gG z) := by
  unfold imgLetter imgG
  split_ifs with h
  · exact rep_img hF hB gG hG (by omega)
  · exact rep_img_inv hF hB gG hG (by omega)

omit hF hB hG

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

theorem eq_of_rep_eq (hF : Facts D c) {g h : J D} {X : Table} (hg : Rep D.n X g)
    (hh : Rep D.n X h) : g = h := by
  have := faithful hF.toBaseFacts
  refine FaithfulSMul.eq_of_smul_eq_smul (M := J D) (α := Fin D.n) fun i => ?_
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

include hF hB hG

theorem relators_eval : ∀ v ∈ S.rels, wordProd (img S gG) v = 1 := by
  intro v hv
  have hlt := hB.relsLt v hv
  have hrep : Rep D.n (wordT D.n (imgLetter (imgT D S G) (imgTv D S G)) (v.map letterOf))
      (wordG (imgG S gG) (v.map letterOf)) := by
    apply Rep.wordT (n_lt_two_pow hF)
    intro z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    exact rep_imgLetter hF hB gG hG (letterOf_ne_zero l)
      (by rw [letterOf_natAbs]; exact hlt l hl)
  rw [← wordG_map_letterOf]
  rw [hB.rels v hv] at hrep
  exact eq_of_rep_eq hF hrep (Rep.idT (n_lt_two_pow hF))

omit hF hB hG

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

theorem surjWords_mem (hB : BridgeFacts D S G) {i : ℕ} (hi : i < 2) :
    S.surjWords[i]! ∈ S.surjWords := by
  have hi' : i < S.surjWords.size := by rw [hB.sizeSurj]; exact hi
  rw [getElem!_pos S.surjWords i hi']
  exact Array.getElem_mem hi'

include hF hB hG

theorem rep_surjWord {i : ℕ} (hi : i < 2) :
    Rep D.n (wordT D.n (imgLetter (imgT D S G) (imgTv D S G)) S.surjWords[i]!)
      (wordG (imgG S gG) S.surjWords[i]!) :=
  Rep.wordT (n_lt_two_pow hF) _ fun z hz =>
    rep_imgLetter hF hB gG hG (hB.letters _ (surjWords_mem hB hi) z hz).1
      (hB.letters _ (surjWords_mem hB hi) z hz).2

theorem a_mem_range (hm : P.generatorCount = S.m)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (img S gG) v = 1) :
    a D ∈ (presHom P (img S gG) hrel).range := by
  have hr := rep_surjWord hF hB gG hG (i := 0) (by decide)
  rw [hB.surjA] at hr
  rw [← eq_of_rep_eq hF hr (rep_a hF.toBaseFacts)]
  exact wordG_imgG_mem gG P hm hrel fun z hz => hB.letters _ (surjWords_mem hB (by decide)) z hz

theorem b_mem_range (hm : P.generatorCount = S.m)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (img S gG) v = 1) :
    b D ∈ (presHom P (img S gG) hrel).range := by
  have hr := rep_surjWord hF hB gG hG (i := 1) (by decide)
  rw [hB.surjB] at hr
  rw [← eq_of_rep_eq hF hr (rep_b hF.toBaseFacts)]
  exact wordG_imgG_mem gG P hm hrel fun z hz => hB.letters _ (surjWords_mem hB (by decide)) z hz

omit hB

theorem exists_surjective (hm : P.generatorCount = S.m) (hrels : P.relatorLetters = S.rels)
    (hcheck : wordChecks D.n S G (O D).alpha (O D).beta = true) :
    ∃ φ : P.Group →* J D, Function.Surjective φ := by
  have hB := bridge_facts hcheck
  have hrel : ∀ v ∈ P.relatorLetters, wordProd (img S gG) v = 1 := by
    rw [hrels]; exact relators_eval hF hB gG hG
  refine ⟨presHom P (img S gG) hrel, ?_⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab D, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact a_mem_range hF hB gG hG hm hrel
  · exact b_mem_range hF hB gG hG hm hrel

theorem nonempty_mulEquiv_of_card_le (hm : P.generatorCount = S.m)
    (hrels : P.relatorLetters = S.rels)
    (hcheck : wordChecks D.n S G (O D).alpha (O D).beta = true) [Finite P.Group] {k : ℕ}
    (hcard : Nat.card P.Group ≤ k) (hk : k ≤ Nat.card (J D)) : Nonempty (J D ≃* P.Group) := by
  obtain ⟨φ, hφ⟩ := exists_surjective hF gG hG hm hrels hcheck
  exact nonempty_mulEquiv_of_surjective φ hφ hcard hk

omit hF hG

noncomputable abbrev seedLetters (D : VecData) : Array Table :=
  #[(O D).alpha, invT D.n (O D).alpha, (O D).beta, invT D.n (O D).beta]

@[expose] noncomputable def seedG (D : VecData) (l : ℕ) : J D :=
  if l = 0 then a D else if l = 1 then (a D)⁻¹ else if l = 2 then b D else (b D)⁻¹

theorem rep_seedLetters (hF : Facts D c) : ∀ l < (seedLetters D).size,
    Rep D.n (seedLetters D)[l]! (seedG D l) := by
  intro l hl
  have hl' : l < 4 := hl
  unfold seedG
  interval_cases l
  · exact rep_a hF.toBaseFacts
  · exact Rep.inv_of_invOK (rep_a hF.toBaseFacts) hF.invA
  · exact rep_b hF.toBaseFacts
  · exact Rep.inv_of_invOK (rep_b hF.toBaseFacts) hF.invB

noncomputable abbrev chainLetters (D : VecData) : Array Table := L D

theorem rep_chainLetters (hF : Facts D c) : ∀ l < (chainLetters D).size,
    Rep D.n (chainLetters D)[l]! (CFSG.Perm.pairG (gs D) l) := by
  obtain ⟨h2, hinv, -⟩ := CFSG.Perm.chainOK_parts hF.chain
  exact CFSG.Perm.rep_pairG (rep_letters hF) h2 hinv

end CFSG.Sporadic.Bridge.VecSurj
