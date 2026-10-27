module

public import Certificates.Data.CFSGNative.ExcCensus.ExtCore
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusScan
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusAmb
public import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE7

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open CFSG CFSG.Assembly Module

noncomputable section

theorem cartanOf_B_three (i j : Fin (Chk.rkN 1 3)) : cartanOf 1 3 i j = CartanMatrix.B 3 i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem cartanOf_C_three (i j : Fin (Chk.rkN 2 3)) : cartanOf 2 3 i j = CartanMatrix.C 3 i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem cartanOf_E_seven (n : ℕ) (i j : Fin 7) : cartanOf 5 n i j = CartanMatrix.E 7 i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem weylInner_cartanOf {tc n : ℕ} (h : Chk.innerTypeN tc n = true) :
    GGQ2WeylInner (Chk.rkN tc n) (cartanOf tc n) := by
  unfold Chk.innerTypeN at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  cases h with
  | inl h1 =>
    cases h1 with
    | inl h2 =>
      cases h2 with
      | inl h3 =>
        cases h3 with
        | inl hB =>
          rcases hB with ⟨rfl, rfl⟩
          have hCB : cartanOf 1 3 = CartanMatrix.B 3 := Matrix.ext fun i j => cartanOf_B_three i j
          rw [hCB]
          change GGQ2WeylInner 3 (CartanMatrix.B 3)
          exact ggQ2WeylInner_B (m := 3) (by norm_num)
        | inr hC =>
          rcases hC with ⟨rfl, rfl⟩
          have hCC : cartanOf 2 3 = CartanMatrix.C 3 := Matrix.ext fun i j => cartanOf_C_three i j
          rw [hCC]
          change GGQ2WeylInner 3 (CartanMatrix.C 3)
          exact ggQ2WeylInner_C (m := 3) (by norm_num)
      | inr hD =>
        rcases hD with ⟨⟨rfl, h5⟩, hodd⟩
        have hCD : cartanOf 3 n = CartanMatrix.D n := Matrix.ext fun i j => cartanOf_D n i j
        rw [hCD]
        change GGQ2WeylInner n (CartanMatrix.D n)
        exact ggQ2WeylInner_D_odd h5 (Nat.odd_iff.mpr hodd)
    | inr hE6 =>
      rcases hE6 with rfl
      have hCE : cartanOf 4 n = CartanMatrix.E 6 := Matrix.ext fun i j => cartanOf_E n i j
      rw [hCE]
      change GGQ2WeylInner 6 (CartanMatrix.E 6)
      exact ggQ2WeylInner_E6
  | inr hE7 =>
    rcases hE7 with rfl
    have hCE : cartanOf 5 n = CartanMatrix.E 7 := Matrix.ext fun i j => cartanOf_E_seven n i j
    rw [hCE]
    change GGQ2WeylInner 7 (CartanMatrix.E 7)
    exact ggQ2WeylInner_E7

theorem extInnerAt_of_ok {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true) {cz k : ℕ}
    {w : Chk.LinW} {L : List (ℕ × ℕ)} {B Bi : Array (Array ℤ)}
    (hn : Chk.nbrOK T m cz k w L B = true)
    (hi : Chk.invOK (Chk.rkN w.tc w.n) (Chk.cartanN w.tc w.n) Bi = true)
    (ht : Chk.innerTypeN w.tc w.n = true) :
    ExtInnerAt (excRaw m) (vec m cz) (ofMask m k) := by
  have hw : Chk.linOK T (nroots m) w = true := nbrOK_linOK hn
  refine ⟨linOf m T hT w hw, nbrLinAt_linOf hT hw hn, linOf_det_ne_zero hT hw hi,
    Chk.rkN w.tc w.n, cartanOf w.tc w.n, Equiv.refl _, ?_, weylInner_cartanOf ht⟩
  intro i j
  rfl

theorem extDetAt_of_ok {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true) {cz k : ℕ}
    {w : Chk.LinW} {L : List (ℕ × ℕ)} {B : Array (Array ℤ)} {x : Array ℤ}
    {Bc : Option (Array (Array ℤ))}
    (hn : Chk.nbrOK T m cz k w L B = true)
    (hs : Chk.singOK (Chk.rkN w.tc w.n) (Chk.cartanN w.tc w.n) x = true)
    (hc : Chk.detCondN T (dim m) w Bc = true) :
    ExtDetAt (excRaw m) (vec m cz) (ofMask m k) := by
  have hw : Chk.linOK T (nroots m) w = true := nbrOK_linOK hn
  refine ⟨linOf m T hT w hw, nbrLinAt_linOf hT hw hn, linOf_det_eq_zero hT hw hs, ?_⟩
  cases Bc with
  | none =>
    right
    simp only [Chk.detCondN] at hc
    have hd : dim m = Chk.rkN w.tc w.n + 1 := of_decide_eq_true hc
    change Module.finrank (ZMod 3) (V m) = Fintype.card (Fin (Chk.rkN w.tc w.n)) + 1
    rw [Module.finrank_fintype_fun_eq_card]
    simpa using hd
  | some Bc =>
    left
    simp only [Chk.detCondN] at hc
    exact linOf_linearIndependent hT hw hc

theorem extOutcome_of_extWitOK {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true)
    {cv cy cz : ℕ} {X : Chk.ExtWit}
    (h : Chk.extWitOK T m cv cy cz X = true) :
    TwoNodeLabels 3 (label m (ofMask m (T.zm[cv]!)))
        (label m (ofMask m (T.zm[cv]! &&& T.zm[cy]!))) ∨
      TwoNodeLabels 3 (label m (ofMask m (T.zm[cz]!)))
        (label m (ofMask m (T.zm[cv]! &&& T.zm[cy]!))) ∨
      InLLeafAt (excRaw m) (vec m cv) (vec m cz) (ofMask m (T.zm[cv]!)) (ofMask m (T.zm[cz]!)) ∨
      ExtE6At (excRaw m) (vec m cv) (vec m cz) (ofMask m (T.zm[cv]!)) (ofMask m (T.zm[cz]!)) ∨
      ExtInnerAt (excRaw m) (vec m cz) (ofMask m (T.zm[cz]!)) ∨
      ExtDetAt (excRaw m) (vec m cz) (ofMask m (T.zm[cz]!)) ∨
      ExtAmbDAt (excRaw m) (vec m cv) (vec m cz) (ofMask m (T.zm[cv]!)) (ofMask m (T.zm[cz]!)) ∨
      ExtD5At (excRaw m) (vec m cv) (vec m cz) (ofMask m (T.zm[cv]!))
        (ofMask m (T.zm[cv]! &&& T.zm[cy]!)) (ofMask m (T.zm[cz]!)) := by
  cases X <;> simp only [Chk.extWitOK, Bool.and_eq_true] at h ⊢
  · left
    simp only [labelOf_eq hT] at h
    exact (twoNodeN_encL _ _).mp h
  · right; left
    simp only [labelOf_eq hT] at h
    exact (twoNodeN_encL _ _).mp h
  · right; right; left
    exact inLLeafAt_of_leafModelOK hT h
  · right; right; right; right; left
    exact extInnerAt_of_ok hT h.1.1 h.1.2 h.2
  · right; right; right; right; right; left
    exact extDetAt_of_ok hT h.1.1 h.1.2 h.2
  · right; right; right; right; right; right; left
    exact extAmbDAt_of_ambDOK hT h
  · right; right; right; right; right; right; right
    exact extD5At_of_d5OK hT h

end

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
