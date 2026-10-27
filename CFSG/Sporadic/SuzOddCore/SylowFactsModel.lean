module

public import Certificates.Certificate1379101
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SZGammaThree
public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzFacts

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SuzOddCore.SylowFacts CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

theorem getElem!_map_of_lt {α β : Type*} [Inhabited α] [Inhabited β] {A : Array α}
    {f : α → β} {i : ℕ} (hi : i < A.size) : (A.map f)[i]! = f A[i]! := by
  rw [getElem!_pos (A.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos A i hi]

def rGen (i : ℕ) : Equiv.Perm (Fin 1782) := suzWord (rWords[i]!)

def g2uGen (j : ℕ) : Equiv.Perm (Fin 1782) := suzWord (g2uWords[j]!)

def g2vGen (j : ℕ) : Equiv.Perm (Fin 1782) := suzWord (g2vWords[j]!)

def g3uGen (k : ℕ) : Equiv.Perm (Fin 1782) := suzWord (g3uWords[k]!)

def g3vGen (k : ℕ) : Equiv.Perm (Fin 1782) := suzWord (g3vWords[k]!)

def qGen (i : ℕ) : Equiv.Perm (Fin 1782) := suzWord (suzQWords[i]!)

def cGen (i : ℕ) : Equiv.Perm (Fin 1782) := suzWord (cWords[i]!)

def n2Gen (j : ℕ) : Equiv.Perm (Fin 1782) := ⁅g2uGen j, g2vGen j⁆

def n3Gen (k : ℕ) : Equiv.Perm (Fin 1782) := ⁅g3uGen k, g3vGen k⁆

def tenGen (j : ℕ) : Equiv.Perm (Fin 1782) := if j < 4 then rGen j else cGen (j - 4)

def rSet : Set (Equiv.Perm (Fin 1782)) := {g | ∃ i < 4, rGen i = g}

def n2Set : Set (Equiv.Perm (Fin 1782)) := {g | ∃ j < 7, n2Gen j = g}

def n3Set : Set (Equiv.Perm (Fin 1782)) := {g | ∃ k < 5, n3Gen k = g}

def qSet : Set (Equiv.Perm (Fin 1782)) := {g | ∃ i < 3, qGen i = g}

def R0 : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure rSet

def N2 : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure n2Set

def N3 : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure n3Set

def Q : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure qSet

def Z : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.centralizer (n3Set : Set (Equiv.Perm (Fin 1782))) ⊓ N3

theorem suzTriple_eq_bTriple : suzTriple = bTriple := rfl

theorem suzTripleInv_eq_bTripleInv : suzTripleInv = bTripleInv := rfl

theorem rep_ev {w : List ℤ} (hw : lettersOK 3 w = true) :
    Rep 1782 (ev w) (suzWord w) := by
  rw [ev, suzTriple_eq_bTriple, suzTripleInv_eq_bTripleInv]
  exact rep_suzWord hw

theorem commA_size (u v : Array ℕ) : (commA u v).size = 1782 := by
  simp [commA, compA]

theorem rep_commA {u v : Array ℕ} {x y : Equiv.Perm (Fin 1782)}
    (hu : Rep 1782 u x) (hv : Rep 1782 v y)
    (hui : Rep 1782 (invCand 1782 u) x⁻¹) (hvi : Rep 1782 (invCand 1782 v) y⁻¹) :
    Rep 1782 (commA u v) ⁅x, y⁆ := by
  rw [commutatorElement_def]
  exact rep_compA (rep_compA (rep_compA hu hv) hui) hvi

theorem rWordOK_spec (h : rWordOK () = true) :
    ∀ i < 4, lettersOK 3 (rWords[i]!) = true ∧ lettersOK 2 (rWords[i]!) = true := by
  simpa only [rWordOK, allBelow_eq_true, Bool.and_eq_true] using h

theorem g2WordOK_spec (h : g2WordOK () = true) :
    ∀ j < 7, lettersOK 3 (g2uWords[j]!) = true ∧ lettersOK 3 (g2vWords[j]!) = true := by
  simpa only [g2WordOK, allBelow_eq_true, Bool.and_eq_true] using h

theorem g3WordOK_spec (h : g3WordOK () = true) :
    ∀ k < 5, lettersOK 3 (g3uWords[k]!) = true ∧ lettersOK 3 (g3vWords[k]!) = true := by
  simpa only [g3WordOK, allBelow_eq_true, Bool.and_eq_true] using h

theorem qWordOK_spec (h : qWordOK () = true) :
    ∀ i < 3, lettersOK 3 (suzQWords[i]!) = true := by
  simpa only [qWordOK, allBelow_eq_true] using h

theorem cWordOK_spec (h : cWordOK () = true) :
    ∀ i < 6, lettersOK 3 (cWords[i]!) = true ∧ lettersOK 2 (cWords[i]!) = true := by
  simpa only [cWordOK, allBelow_eq_true, Bool.and_eq_true] using h

theorem wWordOK_spec (h : wWordOK () = true) :
    lettersOK 10 waWord = true ∧ lettersOK 10 wbWord = true := by
  simpa only [wWordOK, Bool.and_eq_true] using h

theorem rArrs_size : (rArrs ()).size = 4 := by simp only [rArrs, Array.size_ofFn]

theorem qArrs_size : (qArrs ()).size = 3 := by simp only [qArrs, Array.size_ofFn]

theorem n2Arrs_size : (n2Arrs ()).size = 7 := by simp only [n2Arrs, n2ArrOf, Array.size_ofFn]

theorem n3Arrs_size : (n3Arrs ()).size = 5 := by simp only [n3Arrs, n3ArrOf, Array.size_ofFn]

theorem tenArrs_size (r c : Array (Array Nat)) : (tenArrs r c).size = 10 := by
  simp only [tenArrs, Array.size_ofFn]

theorem rep_rArrs (i : ℕ) (hi : i < 4)
    (hw : lettersOK 3 (rWords[i]!) = true) :
    Rep 1782 ((rArrs ())[i]!) (rGen i) := by
  rw [rArrs, getElem!_ofFn_of_lt _ (by simpa using hi)]
  exact rep_ev hw

theorem rep_g2uArrs (j : ℕ) (hj : j < 7)
    (hw : lettersOK 3 (g2uWords[j]!) = true) :
    Rep 1782 ((g2uArrs ())[j]!) (g2uGen j) := by
  rw [g2uArrs, getElem!_ofFn_of_lt _ (by simpa using hj)]
  exact rep_ev hw

theorem rep_g2vArrs (j : ℕ) (hj : j < 7)
    (hw : lettersOK 3 (g2vWords[j]!) = true) :
    Rep 1782 ((g2vArrs ())[j]!) (g2vGen j) := by
  rw [g2vArrs, getElem!_ofFn_of_lt _ (by simpa using hj)]
  exact rep_ev hw

theorem rep_g3uArrs (k : ℕ) (hk : k < 5)
    (hw : lettersOK 3 (g3uWords[k]!) = true) :
    Rep 1782 ((g3uArrs ())[k]!) (g3uGen k) := by
  rw [g3uArrs, getElem!_ofFn_of_lt _ (by simpa using hk)]
  exact rep_ev hw

theorem rep_g3vArrs (k : ℕ) (hk : k < 5)
    (hw : lettersOK 3 (g3vWords[k]!) = true) :
    Rep 1782 ((g3vArrs ())[k]!) (g3vGen k) := by
  rw [g3vArrs, getElem!_ofFn_of_lt _ (by simpa using hk)]
  exact rep_ev hw

theorem rep_qArrs (i : ℕ) (hi : i < 3)
    (hw : lettersOK 3 (suzQWords[i]!) = true) :
    Rep 1782 ((qArrs ())[i]!) (qGen i) := by
  rw [qArrs, getElem!_ofFn_of_lt _ (by simpa using hi)]
  exact rep_ev hw

theorem rep_cArrs (i : ℕ) (hi : i < 6)
    (hw : lettersOK 3 (cWords[i]!) = true) :
    Rep 1782 ((cArrs ())[i]!) (cGen i) := by
  rw [cArrs, getElem!_ofFn_of_lt _ (by simpa using hi)]
  exact rep_ev hw

theorem isInvA_of_permOK {n : ℕ} {t : Array ℕ} (h : permOK n t = true) :
    isInvA n t (invCand n t) = true := by
  rw [permOK, Bool.and_eq_true] at h
  exact h.2

theorem rep_inv_rArrs (i : ℕ) (hi : i < 4)
    (hw : lettersOK 3 (rWords[i]!) = true)
    (hp : permOK 1782 ((rArrs ())[i]!) = true) :
    Rep 1782 (invCand 1782 ((rArrs ())[i]!)) (rGen i)⁻¹ :=
  rep_inv_of_isInvA (rep_rArrs i hi hw) (isInvA_of_permOK hp)

theorem rep_inv_g2uArrs (j : ℕ) (hj : j < 7)
    (hw : lettersOK 3 (g2uWords[j]!) = true)
    (hp : permOK 1782 ((g2uArrs ())[j]!) = true) :
    Rep 1782 (invCand 1782 ((g2uArrs ())[j]!)) (g2uGen j)⁻¹ :=
  rep_inv_of_isInvA (rep_g2uArrs j hj hw) (isInvA_of_permOK hp)

theorem rep_inv_g2vArrs (j : ℕ) (hj : j < 7)
    (hw : lettersOK 3 (g2vWords[j]!) = true)
    (hp : permOK 1782 ((g2vArrs ())[j]!) = true) :
    Rep 1782 (invCand 1782 ((g2vArrs ())[j]!)) (g2vGen j)⁻¹ :=
  rep_inv_of_isInvA (rep_g2vArrs j hj hw) (isInvA_of_permOK hp)

theorem rep_inv_g3uArrs (k : ℕ) (hk : k < 5)
    (hw : lettersOK 3 (g3uWords[k]!) = true)
    (hp : permOK 1782 ((g3uArrs ())[k]!) = true) :
    Rep 1782 (invCand 1782 ((g3uArrs ())[k]!)) (g3uGen k)⁻¹ :=
  rep_inv_of_isInvA (rep_g3uArrs k hk hw) (isInvA_of_permOK hp)

theorem rep_inv_g3vArrs (k : ℕ) (hk : k < 5)
    (hw : lettersOK 3 (g3vWords[k]!) = true)
    (hp : permOK 1782 ((g3vArrs ())[k]!) = true) :
    Rep 1782 (invCand 1782 ((g3vArrs ())[k]!)) (g3vGen k)⁻¹ :=
  rep_inv_of_isInvA (rep_g3vArrs k hk hw) (isInvA_of_permOK hp)

theorem rep_n2Arrs (j : ℕ) (hj : j < 7)
    (huw : lettersOK 3 (g2uWords[j]!) = true) (hvw : lettersOK 3 (g2vWords[j]!) = true)
    (hu : permOK 1782 ((g2uArrs ())[j]!) = true)
    (hv : permOK 1782 ((g2vArrs ())[j]!) = true) :
    Rep 1782 ((n2Arrs ())[j]!) (n2Gen j) := by
  rw [n2Arrs, n2ArrOf]
  rw [getElem!_ofFn_of_lt _ (by simpa using hj)]
  exact rep_commA (rep_g2uArrs j hj huw) (rep_g2vArrs j hj hvw)
    (rep_inv_g2uArrs j hj huw hu) (rep_inv_g2vArrs j hj hvw hv)

theorem rep_n3Arrs (k : ℕ) (hk : k < 5)
    (huw : lettersOK 3 (g3uWords[k]!) = true) (hvw : lettersOK 3 (g3vWords[k]!) = true)
    (hu : permOK 1782 ((g3uArrs ())[k]!) = true)
    (hv : permOK 1782 ((g3vArrs ())[k]!) = true) :
    Rep 1782 ((n3Arrs ())[k]!) (n3Gen k) := by
  rw [n3Arrs, n3ArrOf]
  rw [getElem!_ofFn_of_lt _ (by simpa using hk)]
  exact rep_commA (rep_g3uArrs k hk huw) (rep_g3vArrs k hk hvw)
    (rep_inv_g3uArrs k hk huw hu) (rep_inv_g3vArrs k hk hvw hv)

theorem rCheck_spec {rA : Array (Array Nat)} {eR : Enum} (h : rCheck rA eR = true) :
    (∀ i < 4, permOK 1782 rA[i]! = true) ∧ enumOK 1782 rA eR = true ∧
      eR.tabs.size = 8192 := by
  simp only [rCheck, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  exact h

theorem n2Check_spec {rA rI g2u g2v g2 : Array (Array Nat)} {eR : Enum}
    {ir : Std.HashMap Tab Nat} {e2 : Enum}
    (h : n2Check rA rI g2u g2v g2 eR ir e2 = true) :
    (∀ j < 7, permOK 1782 g2u[j]! = true ∧ permOK 1782 g2v[j]! = true) ∧
      (∀ j < 7, found ir eR.tabs g2u[j]! = true ∧ found ir eR.tabs g2v[j]! = true) ∧
      (∀ j < 7, permOK 1782 g2[j]! = true) ∧
      enumOK 1782 g2 e2 = true ∧ e2.tabs.size = 512 ∧
      normalOK 1782 e2.tabs rA rI g2 = true ∧
      (∀ i < 4, ∀ j < 4,
        found (indexOf e2.tabs) e2.tabs (commA rA[i]! rA[j]!) = true) := by
  simp only [n2Check, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  exact h

theorem n3Check_spec {rA rI g2 g3u g3v g3 : Array (Array Nat)} {eR e2 : Enum}
    {ir i2 : Std.HashMap Tab Nat} {e3 : Enum}
    (h : n3Check rA rI g2 g3u g3v g3 eR e2 ir i2 e3 = true) :
    (∀ k < 5, permOK 1782 g3u[k]! = true ∧ permOK 1782 g3v[k]! = true) ∧
      (∀ k < 5, found ir eR.tabs g3u[k]! = true ∧ found i2 e2.tabs g3v[k]! = true) ∧
      (∀ k < 5, permOK 1782 g3[k]! = true) ∧
      enumOK 1782 g3 e3 = true ∧ e3.tabs.size = 64 ∧
      normalOK 1782 e3.tabs rA rI g3 = true ∧
      (∀ i < 7, ∀ j < 4,
        found (indexOf e3.tabs) e3.tabs (commA g2[i]! rA[j]!) = true) := by
  simp only [n3Check, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  exact h

theorem zCheck_spec {zT : Array (Array Nat)} (h : zCheck zT = true) :
    zT.size = 16 ∧ ∀ k < zT.size, comp 1782 zT[k]! zT[k]! = idTab 1782 := by
  simp only [zCheck, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  exact h

theorem qCheck_spec {rA qA cA : Array (Array Nat)} {eR : Enum}
    {ir : Std.HashMap Tab Nat} {eQ : Enum}
    (h : qCheck rA qA cA eR ir eQ = true) :
    (∀ i < 3, permOK 1782 qA[i]! = true) ∧
      (∀ i < 3, found ir eR.tabs qA[i]! = true) ∧
      (∀ i < 3, comp 1782 qA[i]! qA[i]! = idTab 1782) ∧
      (∀ i < 3, ∀ j < 3,
        comp 1782 qA[i]! qA[j]! = comp 1782 qA[j]! qA[i]!) ∧
      enumOK 1782 qA eQ = true ∧ eQ.tabs.size = 8 ∧
      (∀ k < eQ.tabs.size, comp 1782 eQ.tabs[k]! eQ.tabs[k]! = idTab 1782) ∧
      (∀ i < 6, permOK 1782 cA[i]! = true) ∧
      (∀ i < 6, ∀ j < 3, comp 1782 qA[j]! cA[i]! = comp 1782 cA[i]! qA[j]!) := by
  simp only [qCheck, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  exact h

theorem genCheck_spec {rA cA : Array (Array Nat)} {wA wB : List Int}
    (h : genCheck rA cA wA wB = true) :
    eqA 1782 (wordA 1782 (tenArrs rA cA) ((tenArrs rA cA).map (invCand 1782)) wA) b0Arr = true ∧
      eqA 1782 (wordA 1782 (tenArrs rA cA) ((tenArrs rA cA).map (invCand 1782)) wB) b1Arr = true := by
  simp only [genCheck, Bool.and_eq_true] at h
  exact h

structure SuzModelFacts : Prop where
  wordsR : ∀ i < 4, lettersOK 3 (rWords[i]!) = true ∧ lettersOK 2 (rWords[i]!) = true
  wordsG2 : ∀ j < 7, lettersOK 3 (g2uWords[j]!) = true ∧ lettersOK 3 (g2vWords[j]!) = true
  wordsG3 : ∀ k < 5, lettersOK 3 (g3uWords[k]!) = true ∧ lettersOK 3 (g3vWords[k]!) = true
  wordsQ : ∀ i < 3, lettersOK 3 (suzQWords[i]!) = true
  wordsC : ∀ i < 6, lettersOK 3 (cWords[i]!) = true ∧ lettersOK 2 (cWords[i]!) = true
  wordsW : lettersOK 10 waWord = true ∧ lettersOK 10 wbWord = true
  rPerm : ∀ i < 4, permOK 1782 ((rArrs ())[i]!) = true
  rEnumOK : enumOK 1782 (rArrs ()) (rEnum ()) = true
  rSize : (rEnum ()).tabs.size = 8192
  n2Perm : ∀ j < 7, permOK 1782 ((g2uArrs ())[j]!) = true ∧
    permOK 1782 ((g2vArrs ())[j]!) = true
  n2InR : ∀ j < 7, found (idxR ()) (rEnum ()).tabs ((g2uArrs ())[j]!) = true ∧
    found (idxR ()) (rEnum ()).tabs ((g2vArrs ())[j]!) = true
  n2PermC : ∀ j < 7, permOK 1782 ((n2Arrs ())[j]!) = true
  n2EnumOK : enumOK 1782 (n2Arrs ()) (n2Enum ()) = true
  n2Size : (n2Enum ()).tabs.size = 512
  n2Norm : normalOK 1782 (n2Enum ()).tabs (rArrs ())
    ((rArrs ()).map (invCand 1782)) (n2Arrs ()) = true
  n2Comm : ∀ i < 4, ∀ j < 4, found (indexOf (n2Enum ()).tabs) (n2Enum ()).tabs
    (commA ((rArrs ())[i]!) ((rArrs ())[j]!)) = true
  n3Perm : ∀ k < 5, permOK 1782 ((g3uArrs ())[k]!) = true ∧
    permOK 1782 ((g3vArrs ())[k]!) = true
  n3In : ∀ k < 5, found (idxR ()) (rEnum ()).tabs ((g3uArrs ())[k]!) = true ∧
    found (idxN2 ()) (n2Enum ()).tabs ((g3vArrs ())[k]!) = true
  n3PermC : ∀ k < 5, permOK 1782 ((n3Arrs ())[k]!) = true
  n3EnumOK : enumOK 1782 (n3Arrs ()) (n3Enum ()) = true
  n3Size : (n3Enum ()).tabs.size = 64
  n3Norm : normalOK 1782 (n3Enum ()).tabs (rArrs ())
    ((rArrs ()).map (invCand 1782)) (n3Arrs ()) = true
  n3Comm : ∀ i < 7, ∀ j < 4, found (indexOf (n3Enum ()).tabs) (n3Enum ()).tabs
    (commA ((n2Arrs ())[i]!) ((rArrs ())[j]!)) = true
  zSize : (zTabs ()).size = 16
  zSq : ∀ k < (zTabs ()).size, comp 1782 ((zTabs ())[k]!) ((zTabs ())[k]!) = idTab 1782
  qPerm : ∀ i < 3, permOK 1782 ((qArrs ())[i]!) = true
  qInR : ∀ i < 3, found (idxR ()) (rEnum ()).tabs ((qArrs ())[i]!) = true
  qEnumOK : enumOK 1782 (qArrs ()) (qEnum ()) = true
  qSize : (qEnum ()).tabs.size = 8
  qSqAll : ∀ k < (qEnum ()).tabs.size,
    comp 1782 (qEnum ()).tabs[k]! (qEnum ()).tabs[k]! = idTab 1782
  cPerm : ∀ i < 6, permOK 1782 ((cArrs ())[i]!) = true
  cQ : ∀ i < 6, ∀ j < 3, comp 1782 ((qArrs ())[j]!) ((cArrs ())[i]!) =
    comp 1782 ((cArrs ())[i]!) ((qArrs ())[j]!)
  wa : eqA 1782 (wordA 1782 (tenArrs (rArrs ()) (cArrs ()))
      ((tenArrs (rArrs ()) (cArrs ())).map (invCand 1782)) waWord) b0Arr = true
  wb : eqA 1782 (wordA 1782 (tenArrs (rArrs ()) (cArrs ()))
      ((tenArrs (rArrs ()) (cArrs ())).map (invCand 1782)) wbWord) b1Arr = true

theorem suzModelFacts : SuzModelFacts := by
  have h := Certificates.certificate1379101
  unfold sylowFactsCheck at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hwR, hwG2, hwG3, hwQ, hwC, hwW, hr, hn2, hn3, hz, hq, hgen⟩ := h
  obtain ⟨hr1, hr2, hr3⟩ := rCheck_spec hr
  obtain ⟨hn21, hn22, hn23, hn24, hn25, hn26, hn27⟩ := n2Check_spec hn2
  obtain ⟨hn31, hn32, hn33, hn34, hn35, hn36, hn37⟩ := n3Check_spec hn3
  obtain ⟨hz1, hz2⟩ := zCheck_spec hz
  obtain ⟨hq1, hq2, _hq3, _hq4, hq5, hq6, hq7, hq8, hq9⟩ := qCheck_spec hq
  obtain ⟨hwa, hwb⟩ := genCheck_spec hgen
  exact
    { wordsR := rWordOK_spec hwR
      wordsG2 := g2WordOK_spec hwG2
      wordsG3 := g3WordOK_spec hwG3
      wordsQ := qWordOK_spec hwQ
      wordsC := cWordOK_spec hwC
      wordsW := wWordOK_spec hwW
      rPerm := hr1
      rEnumOK := hr2
      rSize := hr3
      n2Perm := hn21
      n2InR := hn22
      n2PermC := hn23
      n2EnumOK := hn24
      n2Size := hn25
      n2Norm := hn26
      n2Comm := hn27
      n3Perm := hn31
      n3In := hn32
      n3PermC := hn33
      n3EnumOK := hn34
      n3Size := hn35
      n3Norm := hn36
      n3Comm := hn37
      zSize := hz1
      zSq := hz2
      qPerm := hq1
      qInR := hq2
      qEnumOK := hq5
      qSize := hq6
      qSqAll := hq7
      cPerm := hq8
      cQ := hq9
      wa := hwa
      wb := hwb }

theorem size_of_permOK {n : ℕ} {t : Array ℕ} (h : permOK n t = true) : t.size = n := by
  rw [permOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem tabRep_of_permOK_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (hp : permOK n t = true) (hr : Rep n t g) : TabRep t g :=
  ⟨size_of_permOK hp, hr⟩

section Model

theorem tabRep_rArrs (i : ℕ) (hi : i < 4) : TabRep ((rArrs ())[i]!) (rGen i) :=
  tabRep_of_permOK_rep (suzModelFacts.rPerm i hi)
    (rep_rArrs i hi (suzModelFacts.wordsR i hi).1)

theorem tabRep_n2Arrs (j : ℕ) (hj : j < 7) : TabRep ((n2Arrs ())[j]!) (n2Gen j) :=
  tabRep_of_permOK_rep (suzModelFacts.n2PermC j hj)
    (rep_n2Arrs j hj (suzModelFacts.wordsG2 j hj).1 (suzModelFacts.wordsG2 j hj).2
      (suzModelFacts.n2Perm j hj).1 (suzModelFacts.n2Perm j hj).2)

theorem tabRep_n3Arrs (k : ℕ) (hk : k < 5) : TabRep ((n3Arrs ())[k]!) (n3Gen k) :=
  tabRep_of_permOK_rep (suzModelFacts.n3PermC k hk)
    (rep_n3Arrs k hk (suzModelFacts.wordsG3 k hk).1 (suzModelFacts.wordsG3 k hk).2
      (suzModelFacts.n3Perm k hk).1 (suzModelFacts.n3Perm k hk).2)

theorem tabRep_qArrs (i : ℕ) (hi : i < 3) : TabRep ((qArrs ())[i]!) (qGen i) :=
  tabRep_of_permOK_rep (suzModelFacts.qPerm i hi)
    (rep_qArrs i hi (suzModelFacts.wordsQ i hi))

theorem tabRep_cArrs (i : ℕ) (hi : i < 6) : TabRep ((cArrs ())[i]!) (cGen i) :=
  tabRep_of_permOK_rep (suzModelFacts.cPerm i hi)
    (rep_cArrs i hi (suzModelFacts.wordsC i hi).1)

theorem rEnumerates : Enumerates R0 (rEnum ()).tabs.toList := by
  refine enumerates_closure (A := rSet) (gens := rArrs ()) (E := rEnum ()) ?_ ?_
    suzModelFacts.rEnumOK
  · rintro g ⟨i, hi, rfl⟩
    exact ⟨i, by simpa [rArrs_size] using hi, tabRep_rArrs i hi⟩
  · intro j hj
    exact ⟨rGen j, ⟨j, hj, rfl⟩, tabRep_rArrs j hj⟩

theorem card_R0 : Nat.card R0 = 8192 := by
  rw [rEnumerates.card, Array.length_toList, suzModelFacts.rSize]

theorem rGen_mem_suzM (i : ℕ) (hi : i < 4) : rGen i ∈ suzM :=
  CFSG.EvenSporadicStandard.Solomon78.suzWord_mem (suzModelFacts.wordsR i hi).2

theorem R0_le_suzM : R0 ≤ suzM := by
  rw [R0, Subgroup.closure_le]
  rintro g ⟨i, hi, rfl⟩
  exact rGen_mem_suzM i hi

theorem n2Enumerates : Enumerates N2 (n2Enum ()).tabs.toList := by
  refine enumerates_closure (A := n2Set) (gens := n2Arrs ()) (E := n2Enum ()) ?_ ?_
    suzModelFacts.n2EnumOK
  · rintro g ⟨j, hj, rfl⟩
    exact ⟨j, by simpa [n2Arrs_size] using hj, tabRep_n2Arrs j hj⟩
  · intro j hj
    exact ⟨n2Gen j, ⟨j, hj, rfl⟩, tabRep_n2Arrs j hj⟩

theorem n3Enumerates : Enumerates N3 (n3Enum ()).tabs.toList := by
  refine enumerates_closure (A := n3Set) (gens := n3Arrs ()) (E := n3Enum ()) ?_ ?_
    suzModelFacts.n3EnumOK
  · rintro g ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [n3Arrs_size] using hk, tabRep_n3Arrs k hk⟩
  · intro k hk
    exact ⟨n3Gen k, ⟨k, hk, rfl⟩, tabRep_n3Arrs k hk⟩

theorem qEnumerates : Enumerates Q (qEnum ()).tabs.toList := by
  refine enumerates_closure (A := qSet) (gens := qArrs ()) (E := qEnum ()) ?_ ?_
    suzModelFacts.qEnumOK
  · rintro g ⟨i, hi, rfl⟩
    exact ⟨i, by simpa [qArrs_size] using hi, tabRep_qArrs i hi⟩
  · intro i hi
    exact ⟨qGen i, ⟨i, hi, rfl⟩, tabRep_qArrs i hi⟩

theorem card_Q : Nat.card Q = 8 := by
  rw [qEnumerates.card, Array.length_toList, suzModelFacts.qSize]

end Model

theorem mem_of_found_tabRep {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : Array Tab}
    {x : Tab} {g : Equiv.Perm (Fin n)} (hH : Enumerates H T.toList)
    (hf : found (indexOf T) T x = true) (hx : TabRep x g) : g ∈ H := by
  obtain ⟨y, hy, hyrep⟩ := hH.sound x (mem_of_found hf)
  rwa [hyrep.perm_eq hx] at hy

theorem normalizer_of_conj_generators {G : Type*} [Group G] {N : Subgroup G} {S : Set G}
    (hN : N = Subgroup.closure S) {g : G} (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ N)
    (h2 : ∀ s ∈ S, g⁻¹ * s * g ∈ N) : g ∈ Subgroup.normalizer (N : Set G) := by
  rw [hN] at h1 h2 ⊢
  have hmap1 : Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.closure S) ≤
      Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using h1 s hs
  have hmap2 : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (Subgroup.closure S) ≤
      Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using h2 s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm hmap1 ?_
  intro x hx
  have hx' : (MulAut.conj g⁻¹) x ∈ Subgroup.closure S := hmap2 (Subgroup.mem_map_of_mem _ hx)
  have hconj : MulAut.conj g ((MulAut.conj g⁻¹) x) = x := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hconj]
  exact Subgroup.mem_map_of_mem _ hx'

section Model2

theorem tabRep_g2uArrs (j : ℕ) (hj : j < 7) : TabRep ((g2uArrs ())[j]!) (g2uGen j) :=
  tabRep_of_permOK_rep (suzModelFacts.n2Perm j hj).1
    (rep_g2uArrs j hj (suzModelFacts.wordsG2 j hj).1)

theorem tabRep_g2vArrs (j : ℕ) (hj : j < 7) : TabRep ((g2vArrs ())[j]!) (g2vGen j) :=
  tabRep_of_permOK_rep (suzModelFacts.n2Perm j hj).2
    (rep_g2vArrs j hj (suzModelFacts.wordsG2 j hj).2)

theorem tabRep_g3uArrs (k : ℕ) (hk : k < 5) : TabRep ((g3uArrs ())[k]!) (g3uGen k) :=
  tabRep_of_permOK_rep (suzModelFacts.n3Perm k hk).1
    (rep_g3uArrs k hk (suzModelFacts.wordsG3 k hk).1)

theorem tabRep_g3vArrs (k : ℕ) (hk : k < 5) : TabRep ((g3vArrs ())[k]!) (g3vGen k) :=
  tabRep_of_permOK_rep (suzModelFacts.n3Perm k hk).2
    (rep_g3vArrs k hk (suzModelFacts.wordsG3 k hk).2)

theorem g2uGen_mem_R0 (j : ℕ) (hj : j < 7) : g2uGen j ∈ R0 :=
  mem_of_found_tabRep rEnumerates (suzModelFacts.n2InR j hj).1 (tabRep_g2uArrs j hj)

theorem g2vGen_mem_R0 (j : ℕ) (hj : j < 7) : g2vGen j ∈ R0 :=
  mem_of_found_tabRep rEnumerates (suzModelFacts.n2InR j hj).2 (tabRep_g2vArrs j hj)

theorem g3uGen_mem_R0 (k : ℕ) (hk : k < 5) : g3uGen k ∈ R0 :=
  mem_of_found_tabRep rEnumerates (suzModelFacts.n3In k hk).1 (tabRep_g3uArrs k hk)

theorem g3vGen_mem_N2 (k : ℕ) (hk : k < 5) : g3vGen k ∈ N2 :=
  mem_of_found_tabRep n2Enumerates (suzModelFacts.n3In k hk).2 (tabRep_g3vArrs k hk)

theorem qGen_mem_R0 (i : ℕ) (hi : i < 3) : qGen i ∈ R0 :=
  mem_of_found_tabRep rEnumerates (suzModelFacts.qInR i hi) (tabRep_qArrs i hi)

theorem N2_le_commutator : N2 ≤ ⁅R0, R0⁆ := by
  rw [N2, Subgroup.closure_le]
  rintro g ⟨j, hj, rfl⟩
  exact Subgroup.commutator_mem_commutator (g2uGen_mem_R0 j hj) (g2vGen_mem_R0 j hj)

theorem N2_le_R0 : N2 ≤ R0 := N2_le_commutator.trans (Subgroup.commutator_le_self R0)

theorem rGen_mem_normalizer_N2 (j : ℕ) (hj : j < 4) :
    rGen j ∈ Subgroup.normalizer (N2 : Set _) := by
  refine normalizer_of_conj_generators (N := N2) (S := n2Set) rfl ?_ ?_
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := hs
    exact (conj_mem_of_normalOK n2Enumerates suzModelFacts.n2Norm hj hi
      (tabRep_rArrs j hj) (tabRep_n2Arrs i hi)).1
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := hs
    exact (conj_mem_of_normalOK n2Enumerates suzModelFacts.n2Norm hj hi
      (tabRep_rArrs j hj) (tabRep_n2Arrs i hi)).2

theorem closure_rSet_le_normalizer_N2 :
    Subgroup.closure rSet ≤ Subgroup.normalizer (N2 : Set _) := by
  rw [Subgroup.closure_le]
  rintro g ⟨j, hj, rfl⟩
  exact rGen_mem_normalizer_N2 j hj

theorem comm_rGen_mem_N2 (i : ℕ) (hi : i < 4) (j : ℕ) (hj : j < 4) :
    ⁅rGen i, rGen j⁆ ∈ N2 := by
  apply mem_of_found_tabRep n2Enumerates (suzModelFacts.n2Comm i hi j hj)
  exact ⟨commA_size _ _, rep_commA (rep_rArrs i hi (suzModelFacts.wordsR i hi).1)
    (rep_rArrs j hj (suzModelFacts.wordsR j hj).1)
    (rep_inv_rArrs i hi (suzModelFacts.wordsR i hi).1 (suzModelFacts.rPerm i hi))
    (rep_inv_rArrs j hj (suzModelFacts.wordsR j hj).1 (suzModelFacts.rPerm j hj))⟩

theorem commutator_eq_N2 : ⁅R0, R0⁆ = N2 := by
  refine le_antisymm ?_ N2_le_commutator
  have hcomm : ∀ x ∈ rSet, ∀ y ∈ rSet, ⁅x, y⁆ ∈ N2 := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact comm_rGen_mem_N2 i hi j hj
  have := TauCeti.commutator_closure_closure_le (X := rSet) (Y := rSet) (N := N2)
    closure_rSet_le_normalizer_N2 closure_rSet_le_normalizer_N2 hcomm
  simpa [R0] using this

end Model2

section Model3

theorem rep_inv_n2Arrs (j : ℕ) (hj : j < 7)
    (huw : lettersOK 3 (g2uWords[j]!) = true) (hvw : lettersOK 3 (g2vWords[j]!) = true)
    (hu : permOK 1782 ((g2uArrs ())[j]!) = true)
    (hv : permOK 1782 ((g2vArrs ())[j]!) = true)
    (hp : permOK 1782 ((n2Arrs ())[j]!) = true) :
    Rep 1782 (invCand 1782 ((n2Arrs ())[j]!)) (n2Gen j)⁻¹ :=
  rep_inv_of_isInvA (rep_n2Arrs j hj huw hvw hu hv) (isInvA_of_permOK hp)

theorem rGen_mem_normalizer_N3 (j : ℕ) (hj : j < 4) :
    rGen j ∈ Subgroup.normalizer (N3 : Set _) := by
  refine normalizer_of_conj_generators (N := N3) (S := n3Set) rfl ?_ ?_
  · intro s hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact (conj_mem_of_normalOK n3Enumerates suzModelFacts.n3Norm hj hk
      (tabRep_rArrs j hj) (tabRep_n3Arrs k hk)).1
  · intro s hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact (conj_mem_of_normalOK n3Enumerates suzModelFacts.n3Norm hj hk
      (tabRep_rArrs j hj) (tabRep_n3Arrs k hk)).2

theorem closure_rSet_le_normalizer_N3 :
    Subgroup.closure rSet ≤ Subgroup.normalizer (N3 : Set _) := by
  rw [Subgroup.closure_le]
  rintro g ⟨j, hj, rfl⟩
  exact rGen_mem_normalizer_N3 j hj

theorem comm_n2Gen_rGen_mem_N3 (i : ℕ) (hi : i < 7) (j : ℕ) (hj : j < 4) :
    ⁅n2Gen i, rGen j⁆ ∈ N3 := by
  apply mem_of_found_tabRep n3Enumerates (suzModelFacts.n3Comm i hi j hj)
  exact ⟨commA_size _ _, rep_commA
    (rep_n2Arrs i hi (suzModelFacts.wordsG2 i hi).1 (suzModelFacts.wordsG2 i hi).2
      (suzModelFacts.n2Perm i hi).1 (suzModelFacts.n2Perm i hi).2)
    (rep_rArrs j hj (suzModelFacts.wordsR j hj).1)
    (rep_inv_n2Arrs i hi (suzModelFacts.wordsG2 i hi).1 (suzModelFacts.wordsG2 i hi).2
      (suzModelFacts.n2Perm i hi).1 (suzModelFacts.n2Perm i hi).2 (suzModelFacts.n2PermC i hi))
    (rep_inv_rArrs j hj (suzModelFacts.wordsR j hj).1 (suzModelFacts.rPerm j hj))⟩

theorem commutator_N2_R0_le_N3 : ⁅N2, R0⁆ ≤ N3 := by
  have hX : Subgroup.closure n2Set ≤ Subgroup.normalizer (N3 : Set _) := by
    simpa [N2] using N2_le_R0.trans closure_rSet_le_normalizer_N3
  have hcomm : ∀ x ∈ n2Set, ∀ y ∈ rSet, ⁅x, y⁆ ∈ N3 := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact comm_n2Gen_rGen_mem_N3 i hi j hj
  have := TauCeti.commutator_closure_closure_le (X := n2Set) (Y := rSet) (N := N3)
    hX closure_rSet_le_normalizer_N3 hcomm
  simpa [N2, R0] using this

theorem N3_le_commutator : N3 ≤ ⁅N2, R0⁆ := by
  rw [N3, Subgroup.closure_le]
  rintro g ⟨k, hk, rfl⟩
  have hmem : ⁅g3vGen k, g3uGen k⁆ ∈ ⁅N2, R0⁆ :=
    Subgroup.commutator_mem_commutator (g3vGen_mem_N2 k hk) (g3uGen_mem_R0 k hk)
  have heq : n3Gen k = (⁅g3vGen k, g3uGen k⁆)⁻¹ := by
    rw [n3Gen, commutatorElement_def, commutatorElement_def]
    group
  rw [heq]
  exact inv_mem hmem

theorem commutator_eq_N3 : ⁅N2, R0⁆ = N3 :=
  le_antisymm commutator_N2_R0_le_N3 N3_le_commutator

theorem zGammaThree_eq :
    CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree R0 =
      N3 ⊓ Subgroup.centralizer (N3 : Set _) := by
  rw [CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree, commutator_eq_N2,
    commutator_eq_N3]

theorem Z_eq_zGammaThree : Z = CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree R0 := by
  rw [zGammaThree_eq]
  unfold Z
  rw [inf_comm, N3, Subgroup.centralizer_closure]

end Model3

section Model4

theorem zEnumerates : Enumerates Z (zTabs ()).toList := by
  have hp : ∀ (t : Tab) (g : Equiv.Perm (Fin 1782)), TabRep t g →
      (n3Commutes (n3Arrs ()) t = true ↔ g ∈ Subgroup.centralizer (n3Set : Set _)) := by
    intro t g ht
    rw [n3Commutes, allBelow_eq_true]
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := hy
      have hgen := tabRep_n3Arrs k hk
      have hcomm : g * n3Gen k = n3Gen k * g :=
        ((ht.comp hgen).beq_iff (hgen.comp ht)).1 (h k hk)
      exact hcomm.symm
    · intro h k hk
      rw [Subgroup.mem_centralizer_iff] at h
      have hgen := tabRep_n3Arrs k hk
      have hcomm : n3Gen k * g = g * n3Gen k := h (n3Gen k) ⟨k, hk, rfl⟩
      exact ((ht.comp hgen).beq_iff (hgen.comp ht)).2 hcomm.symm
  have h := n3Enumerates.filter (n3Commutes (n3Arrs ())) hp
  simpa only [Z, zTabs, zFilter, Array.toList_filter] using h

theorem card_Z : Nat.card Z = 16 := by
  rw [zEnumerates.card, Array.length_toList, suzModelFacts.zSize]

theorem isElemTwo_Z : CFSG.ComponentClassification.GrSLit.IsElemTwo Z := by
  constructor
  · intro x hx y hy
    have hxN : x ∈ N3 := (Subgroup.mem_inf.mp hx).2
    have hxC : x ∈ Subgroup.centralizer (n3Set : Set _) := (Subgroup.mem_inf.mp hx).1
    have hxC' : x ∈ Subgroup.centralizer (N3 : Set _) := by
      rw [show N3 = Subgroup.closure n3Set from rfl, Subgroup.centralizer_closure]
      exact hxC
    exact ((Subgroup.mem_centralizer_iff.mp hxC') y (Subgroup.mem_inf.mp hy).2).symm
  · intro x hx
    obtain ⟨t, ht, htrep⟩ := zEnumerates.complete x hx
    obtain ⟨k, hk, hkt⟩ := exists_getElem!_of_mem ht
    have hsq : comp 1782 t t = idTab 1782 := by
      rw [← hkt]
      exact suzModelFacts.zSq k hk
    exact ((htrep.comp htrep).eq_iff TabRep.idTab).1 hsq

theorem isElemTwo_zGammaThree :
    CFSG.ComponentClassification.GrSLit.IsElemTwo
      (CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree R0) := by
  rw [← Z_eq_zGammaThree]
  exact isElemTwo_Z

theorem card_zGammaThree :
    Nat.card (CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree R0) = 16 := by
  rw [← Z_eq_zGammaThree, card_Z]

end Model4

section Model5

theorem Q_le_R0 : Q ≤ R0 := by
  rw [Q, Subgroup.closure_le]
  rintro g ⟨i, hi, rfl⟩
  exact qGen_mem_R0 i hi

theorem qSq (x : Equiv.Perm (Fin 1782)) (hx : x ∈ Q) : x * x = 1 := by
  obtain ⟨t, ht, htrep⟩ := qEnumerates.complete x hx
  obtain ⟨k, hk, hkt⟩ := exists_getElem!_of_mem ht
  have hsq : comp 1782 t t = idTab 1782 := by
    rw [← hkt]
    exact suzModelFacts.qSqAll k hk
  exact ((htrep.comp htrep).eq_iff TabRep.idTab).1 hsq

theorem isElemTwo_Q : CFSG.ComponentClassification.GrSLit.IsElemTwo Q := by
  constructor
  · intro x hx y hy
    have hxy : (x * y) * (x * y) = 1 := qSq (x * y) (Q.mul_mem hx hy)
    have hx1 : x * x = 1 := qSq x hx
    have hy1 : y * y = 1 := qSq y hy
    have hxinv : x⁻¹ = x := inv_eq_iff_mul_eq_one.mpr hx1
    have hyinv : y⁻¹ = y := inv_eq_iff_mul_eq_one.mpr hy1
    have hxyinv : (x * y)⁻¹ = x * y := inv_eq_iff_mul_eq_one.mpr hxy
    have h1 : (x * y)⁻¹ = y * x := by rw [mul_inv_rev, hyinv, hxinv]
    calc
      x * y = (x * y)⁻¹ := hxyinv.symm
      _ = y * x := h1
  · exact qSq

theorem cGen_mem_suzM (i : ℕ) (hi : i < 6) : cGen i ∈ suzM :=
  CFSG.EvenSporadicStandard.Solomon78.suzWord_mem (suzModelFacts.wordsC i hi).2

theorem qGen_commute_cGen (i : ℕ) (hi : i < 6) (j : ℕ) (hj : j < 3) :
    qGen j * cGen i = cGen i * qGen j := by
  have hcomm : comp 1782 ((qArrs ())[j]!) ((cArrs ())[i]!) =
      comp 1782 ((cArrs ())[i]!) ((qArrs ())[j]!) := suzModelFacts.cQ i hi j hj
  exact ((tabRep_qArrs j hj).comp (tabRep_cArrs i hi)).eq_iff
    ((tabRep_cArrs i hi).comp (tabRep_qArrs j hj)) |>.1 hcomm

theorem cGen_mem_centralizer_Q (i : ℕ) (hi : i < 6) :
    cGen i ∈ Subgroup.centralizer (Q : Set _) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hQ : Q ≤ Subgroup.centralizer ({cGen i} : Set _) := by
    rw [Q, Subgroup.closure_le]
    rintro g ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (qGen_commute_cGen i hi j hj).symm
  exact ((Subgroup.mem_centralizer_iff.mp (hQ hx)) (cGen i) (Set.mem_singleton _)).symm

end Model5

section Model6

theorem rep_tenArrs (j : ℕ) (hj : j < 10) :
    Rep 1782 ((tenArrs (rArrs ()) (cArrs ()))[j]!) (tenGen j) := by
  rw [tenArrs, getElem!_ofFn_of_lt _ hj, tenGen]
  by_cases h4 : j < 4
  · rw [if_pos h4, if_pos h4]
    exact rep_rArrs j h4 (suzModelFacts.wordsR j h4).1
  · rw [if_neg h4, if_neg h4]
    exact rep_cArrs (j - 4) (by omega) (suzModelFacts.wordsC (j - 4) (by omega)).1

theorem rep_inv_tenArrs (j : ℕ) (hj : j < 10) :
    Rep 1782 (invCand 1782 ((tenArrs (rArrs ()) (cArrs ()))[j]!)) (tenGen j)⁻¹ := by
  refine rep_inv_of_isInvA (rep_tenArrs j hj) ?_
  rw [tenArrs, getElem!_ofFn_of_lt _ hj]
  by_cases h4 : j < 4
  · rw [if_pos h4]
    exact isInvA_of_permOK (suzModelFacts.rPerm j h4)
  · rw [if_neg h4]
    exact isInvA_of_permOK (suzModelFacts.cPerm (j - 4) (by omega))

theorem rep_wa :
    Rep 1782 (wordA 1782 (tenArrs (rArrs ()) (cArrs ()))
      ((tenArrs (rArrs ()) (cArrs ())).map (invCand 1782)) waWord)
      (wordIn 10 tenGen waWord) :=
  rep_wordA (fun j hj => rep_tenArrs j hj)
    (fun j hj => by
      rw [getElem!_map_of_lt (by simpa [tenArrs_size] using hj)]
      exact rep_inv_tenArrs j hj) waWord suzModelFacts.wordsW.1

theorem rep_wb :
    Rep 1782 (wordA 1782 (tenArrs (rArrs ()) (cArrs ()))
      ((tenArrs (rArrs ()) (cArrs ())).map (invCand 1782)) wbWord)
      (wordIn 10 tenGen wbWord) :=
  rep_wordA (fun j hj => rep_tenArrs j hj)
    (fun j hj => by
      rw [getElem!_map_of_lt (by simpa [tenArrs_size] using hj)]
      exact rep_inv_tenArrs j hj) wbWord suzModelFacts.wordsW.2

theorem suzB0_eq_wa : suzB0 = wordIn 10 tenGen waWord :=
  ((eqA_iff rep_wa rep_b0).1 suzModelFacts.wa).symm

theorem suzB1_eq_wb : suzB1 = wordIn 10 tenGen wbWord :=
  ((eqA_iff rep_wb rep_b1).1 suzModelFacts.wb).symm

theorem tenGen_mem_sup (j : ℕ) (hj : j < 10) :
    tenGen j ∈ R0 ⊔ (suzM ⊓ Subgroup.centralizer (Q : Set (Equiv.Perm (Fin 1782)))) := by
  by_cases h4 : j < 4
  · rw [tenGen, if_pos h4]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, h4, rfl⟩)
  · rw [tenGen, if_neg h4]
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
      ⟨cGen_mem_suzM (j - 4) (by omega), cGen_mem_centralizer_Q (j - 4) (by omega)⟩)

theorem suzM_le_sup :
    suzM ≤ R0 ⊔ (suzM ⊓ Subgroup.centralizer (Q : Set (Equiv.Perm (Fin 1782)))) := by
  change Subgroup.closure ({suzB0, suzB1} : Set (Equiv.Perm (Fin 1782))) ≤ _
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [suzB0_eq_wa]
    exact wordIn_mem (fun j hj => tenGen_mem_sup j hj) waWord
  · rw [suzB1_eq_wb]
    exact wordIn_mem (fun j hj => tenGen_mem_sup j hj) wbWord

end Model6

theorem suz_sylow_model :
    ∃ R₀ : Subgroup (Equiv.Perm (Fin 1782)), R₀ ≤ suzM ∧ Nat.card R₀ = 8192 ∧
      CFSG.ComponentClassification.GrSLit.IsElemTwo
        (CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree R₀) ∧
      Nat.card (CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree R₀) = 16 ∧
      ∃ Q : Subgroup (Equiv.Perm (Fin 1782)), Q ≤ R₀ ∧
        CFSG.ComponentClassification.GrSLit.IsElemTwo Q ∧ Nat.card Q = 8 ∧
        suzM ≤ R₀ ⊔ (suzM ⊓
          Subgroup.centralizer (Q : Set (Equiv.Perm (Fin 1782)))) :=
  ⟨R0, R0_le_suzM, card_R0, isElemTwo_zGammaThree, card_zGammaThree,
    Q, Q_le_R0, isElemTwo_Q, card_Q, suzM_le_sup⟩

end CFSG.Sporadic.SuzOddCore
