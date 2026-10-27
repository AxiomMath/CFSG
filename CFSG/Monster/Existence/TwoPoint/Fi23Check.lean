module

public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.TwoPoint.Fi23Data
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

@[expose] def fiRelW (R : List (ℕ × Bool)) : List Native.Gen :=
  (R.reverse.map fun l => fiWU[l.1]!).flatten

@[expose] def fiPU : Array (List Native.PGen) := fiWU.map HS.pw

@[expose] def fiRelP (R : List (ℕ × Bool)) : List Native.PGen :=
  (R.reverse.map fun l => fiPU[l.1]!).flatten

theorem fiWU_size : fiWU.size = 10 := rfl

theorem fiPU_get {i : ℕ} (hi : i < 10) : fiPU[i]! = HS.pw fiWU[i]! := by
  have h : i < fiWU.size := by rw [fiWU_size]; exact hi
  unfold fiPU
  rw [getElem!_pos (fiWU.map HS.pw) i (by rw [Array.size_map]; exact h), Array.getElem_map,
    getElem!_pos fiWU i h]

theorem fi_pw_flatten (L : List (List Native.Gen)) :
    HS.pw L.flatten = (L.map HS.pw).flatten := by
  unfold HS.pw Native.prepWordG
  exact List.map_flatten ..

theorem fiRelP_eq {R : List (ℕ × Bool)} (hR : ∀ l ∈ R, l.1 < 10) :
    fiRelP R = HS.pw (fiRelW R) := by
  unfold fiRelP fiRelW
  rw [fi_pw_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have := hR l (List.mem_reverse.1 hl)
  exact fiPU_get this

@[expose] def fiNotTau : Native.Gen → Bool
  | .tau => false
  | _ => true

theorem fiNotTau_spec {g : Native.Gen} (h : fiNotTau g = true) : ¬ g = .tau := by
  cases g <;> simp_all [fiNotTau]

@[expose, noinline] def fiEqP (w₁ w₂ : List Native.Gen) (p₁ p₂ : List Native.PGen) : Bool :=
  (w₁ ++ w₂).all Native.Gen.validB &&
    (if (w₁ ++ w₂).all fiNotTau then checkP2 p₁ p₂ else checkP4 p₁ p₂)

theorem wordLin_eq_of_fiEqP
    {w₁ w₂ : List Native.Gen} {p₁ p₂ : List Native.PGen}
    (h : fiEqP w₁ w₂ p₁ p₂ = true) (e₁ : p₁ = HS.pw w₁) (e₂ : p₂ = HS.pw w₂) :
    wordLin w₁ = wordLin w₂ := by
  unfold fiEqP at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hv, hc⟩ := h
  subst e₁ e₂
  split_ifs at hc with ht
  · simp only [List.all_append, Bool.and_eq_true] at ht
    exact wordLin_eq_of_checkP2 (fun g hg => fiNotTau_spec (List.all_eq_true.1 ht.1 g hg))
      (fun g hg => fiNotTau_spec (List.all_eq_true.1 ht.2 g hg)) hv hc
  · exact wordLin_eq_of_checkP4 hv hc

@[expose, noinline] def fiRelCheck (R : List (ℕ × Bool)) : Bool :=
  R.all (fun l => decide (l.1 < 10)) && fiEqP (fiRelW R) [] (fiRelP R) []

@[expose] def fiRelsCheck (idx : List ℕ) : Bool := idx.all fun i => fiRelCheck rels[i]!

theorem wordLin_fiRelW
    {R : List (ℕ × Bool)} (h : fiRelCheck R = true) :
    wordLin (fiRelW R) = 1 := by
  unfold fiRelCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hR, hc⟩ := h
  have hR' : ∀ l ∈ R, l.1 < 10 := fun l hl => of_decide_eq_true (List.all_eq_true.1 hR l hl)
  have := wordLin_eq_of_fiEqP hc (fiRelP_eq hR') (rfl : ([] : List Native.PGen) = HS.pw [])
  rwa [wordLin_nil] at this

@[expose, noinline] def fiFixAt (p : List Native.PGen) (v : Native.DVec) : Bool :=
  (Native.evalPrep HS.hsCtx p v).eqv (Native.evalPrep HS.hsCtx [] v)

@[expose] def fiGuard (R : List (ℕ × Bool)) : Bool :=
  R.all (fun l => decide (l.1 < 10)) && (fiRelW R).all Native.Gen.validB

@[expose] def fiRelFixes (idx : List ℕ) (v : Native.DVec) : Bool :=
  idx.all fun i => fiGuard rels[i]! && fiFixAt (fiRelP rels[i]!) v

theorem fiRelCheck_of_fixes {R : List (ℕ × Bool)} (hg : fiGuard R = true)
    (h₁ : fiFixAt (fiRelP R) HS.axisP = true) (h₂ : fiFixAt (fiRelP R) HS.axisM = true)
    (h₃ : fiFixAt (fiRelP R) hnVecAD = true) (h₄ : fiFixAt (fiRelP R) hnVecJ = true) :
    fiRelCheck R = true := by
  unfold fiGuard at hg
  rw [Bool.and_eq_true] at hg
  unfold fiRelCheck fiEqP
  simp only [List.append_nil, hg.1, hg.2, Bool.true_and]
  split_ifs
  · unfold checkP2
    exact Bool.and_eq_true_iff.2 ⟨h₃, h₄⟩
  · unfold checkP4
    exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
      ⟨Bool.and_eq_true_iff.2 ⟨h₁, h₂⟩, h₃⟩, h₄⟩

theorem fiRelCheck_long (h₁ : fiRelFixes [55, 56] HS.axisP = true)
    (h₂ : fiRelFixes [55, 56] HS.axisM = true) (h₃ : fiRelFixes [55, 56] hnVecAD = true)
    (h₄ : fiRelFixes [55, 56] hnVecJ = true) :
    fiRelCheck rels[55]! = true ∧ fiRelCheck rels[56]! = true := by
  simp only [fiRelFixes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    at h₁ h₂ h₃ h₄
  exact ⟨fiRelCheck_of_fixes h₁.1.1 h₁.1.2 h₂.1.2 h₃.1.2 h₄.1.2,
    fiRelCheck_of_fixes h₁.2.1 h₁.2.2 h₂.2.2 h₃.2.2 h₄.2.2⟩

@[expose] def fiPAlpha : List Native.PGen := HS.pw fiWAlpha

@[expose] def fiPBeta : List Native.PGen := HS.pw fiWBeta

@[expose] def fiWAB : List Native.Gen := fiWBeta ++ fiWAlpha

@[expose] def fiPAB : List Native.PGen := fiPBeta ++ fiPAlpha

theorem fiPAB_eq : fiPAB = HS.pw fiWAB := by
  unfold fiPAB fiWAB fiPBeta fiPAlpha
  rw [HS.pw_append]

@[expose, noinline] def fiCommCheck (x : List Native.Gen) (px : List Native.PGen) (i : ℕ) : Bool :=
  decide (i < 10) &&
    fiEqP (x ++ fiWU[i]!) (fiWU[i]! ++ x) (px ++ fiPU[i]!) (fiPU[i]! ++ px)

theorem wordLin_comm_of_fiCommCheck
    {x : List Native.Gen} {px : List Native.PGen} {i : ℕ}
    (h : fiCommCheck x px i = true) (e : px = HS.pw x) :
    wordLin fiWU[i]! * wordLin x = wordLin x * wordLin fiWU[i]! := by
  unfold fiCommCheck at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  have := wordLin_eq_of_fiEqP h.2 (by rw [e, HS.pw_append, fiPU_get h.1])
    (by rw [e, HS.pw_append, fiPU_get h.1])
  rwa [wordLin_append, wordLin_append] at this

@[expose, noinline] def fiSqCheck (x : List Native.Gen) (px : List Native.PGen) : Bool :=
  fiEqP (x ++ x) [] (px ++ px) []

theorem wordLin_sq_of_fiSqCheck
    {x : List Native.Gen} {px : List Native.PGen}
    (h : fiSqCheck x px = true) (e : px = HS.pw x) : wordLin x * wordLin x = 1 := by
  unfold fiSqCheck at h
  have := wordLin_eq_of_fiEqP h (by rw [e, HS.pw_append]) (rfl : ([] : List Native.PGen) = HS.pw [])
  rwa [wordLin_append, wordLin_nil] at this

@[expose, noinline] def fiCubeCheck : Bool :=
  fiEqP (fiWAB ++ fiWAB ++ fiWAB) [] (fiPAB ++ fiPAB ++ fiPAB) []

theorem wordLin_cube_of_fiCubeCheck
    (h : fiCubeCheck = true) : (wordLin fiWAB) ^ 3 = 1 := by
  unfold fiCubeCheck at h
  have := wordLin_eq_of_fiEqP h (by rw [fiPAB_eq, HS.pw_append, HS.pw_append])
    (rfl : ([] : List Native.PGen) = HS.pw [])
  rw [wordLin_nil] at this
  rw [← this]
  simp only [wordLin_append]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

@[expose, noinline] def fiNeABCheck (i j : ℕ) : Bool :=
  fiWAB.all Native.Gen.validB &&
    hnDiffA i j (Native.evalPrep HS.hsCtx fiPAB HS.axisP) HS.axisP

theorem fi_wordLin_ab_ne_one
    {i j : ℕ} (hi : i < 24) (hj : j < 24) (h : fiNeABCheck i j = true) :
    wordLin fiWAB ≠ 1 := by
  unfold fiNeABCheck at h
  rw [Bool.and_eq_true] at h
  have hp : fiPAB = HS.pw fiWAB := fiPAB_eq
  rw [hp] at h
  exact hn_wordLin_ne_one_of_diffA (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) h.1 h.2

@[expose, noinline] def fiNeGenCheck (i a b : ℕ) : Bool :=
  decide (i < 10) && fiWU[i]!.all Native.Gen.validB &&
    hnDiffA a b (Native.evalPrep HS.hsCtx fiPU[i]! HS.axisP) HS.axisP

theorem fi_wordLin_gen_ne_one {i a b : ℕ} (ha : a < 24) (hb : b < 24)
    (h : fiNeGenCheck i a b = true) : wordLin fiWU[i]! ≠ 1 := by
  unfold fiNeGenCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hi, hv⟩, hd⟩ := h
  rw [fiPU_get hi] at hd
  exact hn_wordLin_ne_one_of_diffA (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) hv hd

@[expose, noinline] def fiMiscCheck : Bool :=
  (List.range 10).all (fiCommCheck fiWAlpha fiPAlpha) &&
    (List.range 10).all (fiCommCheck fiWBeta fiPBeta) &&
    fiSqCheck fiWAlpha fiPAlpha && fiSqCheck fiWBeta fiPBeta && fiCubeCheck && fiNeABCheck 0 0 &&
    fiNeGenCheck 3 0 0

@[expose] def fiPCAlpha : List Native.PGen := HS.pw fiCAlpha

@[expose] def fiPCThreeA : List Native.PGen := HS.pw fiCThreeA

@[expose, noinline] def fiConjCheck : Bool :=
  fiEqP (fiRhoT ++ fiCAlpha) (fiCAlpha ++ fiWAlpha) (HS.pw fiRhoT ++ fiPCAlpha)
      (fiPCAlpha ++ fiPAlpha) &&
    fiEqP (fiWAB ++ fiCThreeA) (fiCThreeA ++ wordThreeA) (fiPAB ++ fiPCThreeA)
      (fiPCThreeA ++ HS.pw wordThreeA)

theorem fiConjCheck_parts
    (h : wordLin (fiRhoT ++ fiCAlpha) = wordLin (fiCAlpha ++ fiWAlpha) ∧
      wordLin (fiWAB ++ fiCThreeA) = wordLin (fiCThreeA ++ wordThreeA)) :
    wordLin fiCAlpha * wordLin fiRhoT = wordLin fiWAlpha * wordLin fiCAlpha ∧
      wordLin fiCThreeA * wordLin fiWAB = wordLin wordThreeA * wordLin fiCThreeA := by
  obtain ⟨h1, h2⟩ := h
  rw [wordLin_append, wordLin_append] at h1 h2
  exact ⟨h1, h2⟩

end CFSG.Monster.Existence
