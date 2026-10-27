module

public import CFSG.Monster.AxisCount.HSIdentAxis
public import CFSG.Monster.AxisCount.CertData
public import CFSG.Monster.AxisCount.SchreierData0
public import CFSG.Monster.AxisCount.SchreierData1
public import CFSG.Monster.AxisCount.SchreierData2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.B.Rep4371

@[expose] def tpw : Bool → List Native.Gen
  | true => [Native.Gen.tau]
  | false => Native.Gen.tauPow 2

@[expose] def uW (i : Fin 12) (k : Nat) : List Native.Gen := (Cert.UW i)[k]!

@[expose] def xW (i : Fin 12) (r : Nat) (ε : Bool) : List Native.Gen :=
  Cert.hW i r ++ tpw ε ++ Cert.kappaW i r ε

@[expose] def so : Fin 12 → SOrbit
  | 0 => sorbit0
  | 1 => sorbit1
  | 2 => sorbit2
  | 3 => sorbit3
  | 4 => sorbit4
  | 5 => sorbit5
  | 6 => sorbit6
  | 7 => sorbit7
  | 8 => sorbit8
  | 9 => sorbit9
  | 10 => sorbit10
  | 11 => sorbit11

@[expose] def hppU (i : Fin 12) (k : Nat) : List Native.Gen := (so i).uHpp[k]!

@[expose] def bbU (i : Fin 12) (k : Nat) : Nat := (so i).uBaby[k]!

@[expose] def eIdx (ε : Bool) : Nat := if ε then 0 else 1

@[expose] def hppL (i : Fin 12) (r : Nat) (ε : Bool) : List Native.Gen :=
  (so i).lHpp[2 * r + eIdx ε]!

@[expose] def bbL (i : Fin 12) (r : Nat) (ε : Bool) : Nat := (so i).lBaby[2 * r + eIdx ε]!

@[expose] noncomputable def vv (i : Fin 12) : SpaceB := wordLin (Cert.gammaW i) aStar

@[expose] def pgam : Array (List Native.PGen) :=
  ((List.finRange 12).map fun t : Fin 12 => pw (Cert.gammaW t)).toArray

theorem pgam_spec (t : Fin 12) : pgam[(t : ℕ)]! = pw (Cert.gammaW t) := by
  unfold pgam
  rw [getElem!_finRange_map]

@[expose] def vtab : Array Native.DVec :=
  ((List.finRange 12).map fun i : Fin 12 => Native.evalPrep hsCtx pgam[(i : ℕ)]! axisP).toArray

@[expose] def vtabOK : Bool :=
  (List.finRange 12).all fun i => (Cert.gammaW i).all Native.Gen.validB

theorem gammaW_valid (h : vtabOK = true) (i : Fin 12) :
    (Cert.gammaW i).all Native.Gen.validB = true :=
  List.all_eq_true.1 h i (List.mem_finRange i)

theorem vtab_spec
    (h : vtabOK = true) (i : Fin 12) : interp vtab[(i : ℕ)]! = vv i := by
  unfold vtab
  rw [getElem!_finRange_map, pgam_spec, interp_evalPrep_pw (gammaW_valid h i), interp_axisP]
  rfl

@[expose] def stabAll : Bool := vtabOK &&
  (List.finRange 12).all fun i => (List.range 2).all fun k =>
    eqCheck hsCtx (uW i k) vtab[(i : ℕ)]! [] vtab[(i : ℕ)]!

theorem stabAll_sound (h : stabAll = true) :
    ∀ (i : Fin 12), ∀ k, k < 2 → wordLin (uW i k) (vv i) = vv i := by
  intro i k hk
  unfold stabAll at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have := eqCheck_sound (List.all_eq_true.1 (List.all_eq_true.1 h2 i (List.mem_finRange i)) k
    (List.mem_range.2 hk))
  rw [← vtab_spec h1 i]
  simpa [wordLin_nil] using this

@[expose] def e1UOrbit (i : Fin 12) : Bool :=
  (Cert.gammaW i).all Native.Gen.validB && qtabOK &&
    (let P := Native.evalWordC hsCtx (Cert.gammaW i) axisM
     (List.range 2).all fun k =>
       decide (bbU i k < 10) &&
         eqCheck hsCtx (uW i k) P (hppU i k ++ Cert.gammaW i) qtab[bbU i k]!)

theorem e1UOrbit_sound {i : Fin 12} (h : e1UOrbit i = true) :
    ∀ k, k < 2 → bbU i k < 10 ∧
      wordLin (uW i k) (wordLin (Cert.gammaW i) aStarMinus) =
        wordLin (hppU i k ++ Cert.gammaW i) (wordLin (babyW (bbU i k)) aStarMinus) := by
  intro k hk
  unfold e1UOrbit at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hg, hq⟩, h2⟩ := h
  have hv : ∀ g ∈ Cert.gammaW i, g.validB = true := fun g hg' => List.all_eq_true.1 hg g hg'
  have hP : interp (Native.evalWordC hsCtx (Cert.gammaW i) axisM) =
      wordLin (Cert.gammaW i) aStarMinus := by
    show interp (Native.evalWordC (Native.mkCtx ()) (Cert.gammaW i) axisM) = _
    rw [evalWordC_sound (Cert.gammaW i) hv, interp_axisM]
  have h3 := List.all_eq_true.1 h2 k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at h3
  have hb : bbU i k < 10 := of_decide_eq_true h3.1
  refine ⟨hb, ?_⟩
  have := eqCheck_sound h3.2
  have e : qtab[bbU i k]! = qtab[((⟨bbU i k, hb⟩ : Fin 10) : ℕ)]! := rfl
  rw [hP, e, qtab_spec hq ⟨bbU i k, hb⟩] at this
  exact this

@[expose] def e2UOrbit (i : Fin 12) : Bool :=
  (List.range 2).all fun k => eqCheck hsCtx (hppU i k) axisP [] axisP

theorem e2UOrbit_sound {i : Fin 12} (h : e2UOrbit i = true) :
    ∀ k, k < 2 → wordLin (hppU i k) aStar = aStar := by
  intro k hk
  have := eqCheck_sound (List.all_eq_true.1 h k (List.mem_range.2 hk))
  rw [interp_axisP] at this
  simpa [wordLin_nil] using this

theorem valid_tpw (ε : Bool) : (tpw ε).all Native.Gen.validB = true := by cases ε <;> rfl

@[expose] def recCheck (i : Fin 12) (P : Native.DVec) (r : Nat) : Bool :=
  (Cert.hW i r).all Native.Gen.validB &&
    (let ph := pw (Cert.hW i r)
     let a := Native.evalPrep hsCtx ph vtab[(i : ℕ)]!
     let b := Native.evalPrep hsCtx ph P
     [true, false].all fun ε =>
       (Cert.kappaW i r ε).all Native.Gen.validB && (hppL i r ε).all Native.Gen.validB &&
         decide (bbL i r ε < 10) &&
         (let rest := pw (tpw ε) ++ pw (Cert.kappaW i r ε)
          let phpp := pw (hppL i r ε)
          (Native.evalPrep hsCtx rest a).eqv vtab[Cert.tW i r ε]! &&
            (Native.evalPrep hsCtx rest b).eqv
              (Native.evalPrep hsCtx (phpp ++ pgam[Cert.tW i r ε]!) qtab[bbL i r ε]!) &&
            (Native.evalPrep hsCtx phpp axisP).eqv axisP))

@[expose] def RecSpec (i : Fin 12) (r : Nat) (ε : Bool) : Prop :=
  wordLin (xW i r ε) (vv i) = vv (Cert.tFin i r ε) ∧
    (bbL i r ε < 10 ∧ wordLin (xW i r ε) (wordLin (Cert.gammaW i) aStarMinus) =
      wordLin (hppL i r ε ++ Cert.gammaW (Cert.tFin i r ε))
        (wordLin (babyW (bbL i r ε)) aStarMinus)) ∧
    wordLin (hppL i r ε) aStar = aStar

theorem recCheck_sound
    {i : Fin 12} {P : Native.DVec} {r : Nat} (hv : vtabOK = true)
    (hq : qtabOK = true) (hP : interp P = wordLin (Cert.gammaW i) aStarMinus)
    (h : recCheck i P r = true) (ε : Bool) : RecSpec i r ε := by
  unfold recCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hh, h⟩ := h
  dsimp only at h
  have h3 := List.all_eq_true.1 h ε (mem_bool ε)
  simp only [Bool.and_eq_true] at h3
  obtain ⟨⟨⟨hk, hp⟩, hb⟩, ⟨e1, e2⟩, e3⟩ := h3
  have hb' : bbL i r ε < 10 := of_decide_eq_true hb
  have hvt : (Cert.gammaW (Cert.tFin i r ε)).all Native.Gen.validB = true := gammaW_valid hv _
  have hwa : ((Cert.hW i r ++ (tpw ε ++ Cert.kappaW i r ε))).all Native.Gen.validB = true := by
    simp only [List.all_append, Bool.and_eq_true]
    exact ⟨hh, valid_tpw ε, hk⟩
  have hX : xW i r ε = Cert.hW i r ++ (tpw ε ++ Cert.kappaW i r ε) := by
    simp [xW, List.append_assoc]
  have hL : ∀ v, Native.evalPrep hsCtx (pw (tpw ε) ++ pw (Cert.kappaW i r ε))
      (Native.evalPrep hsCtx (pw (Cert.hW i r)) v) = Native.evalPrep hsCtx
        (pw (Cert.hW i r ++ (tpw ε ++ Cert.kappaW i r ε))) v := fun v => by
    rw [← evalPrep_append, pw_append, pw_append]
  refine ⟨?_, ⟨hb', ?_⟩, ?_⟩
  · have := eqv_sound e1
    rw [hL, interp_evalPrep_pw hwa] at this
    have e : interp vtab[Cert.tW i r ε]! = vv (Cert.tFin i r ε) := vtab_spec hv (Cert.tFin i r ε)
    rw [e, vtab_spec hv i] at this
    rw [hX]
    exact this
  · have := eqv_sound e2
    rw [hL, interp_evalPrep_pw hwa, hP] at this
    have eg : pgam[Cert.tW i r ε]! = pw (Cert.gammaW (Cert.tFin i r ε)) :=
      pgam_spec (Cert.tFin i r ε)
    have hwb : (hppL i r ε ++ Cert.gammaW (Cert.tFin i r ε)).all Native.Gen.validB = true := by
      simp only [List.all_append, Bool.and_eq_true]
      exact ⟨hp, hvt⟩
    have eq : interp qtab[bbL i r ε]! = wordLin (babyW (bbL i r ε)) aStarMinus :=
      qtab_spec hq ⟨bbL i r ε, hb'⟩
    rw [eg, ← pw_append, interp_evalPrep_pw hwb, eq] at this
    rw [hX]
    exact this
  · have := eqv_sound e3
    rw [interp_evalPrep_pw hp, interp_axisP] at this
    exact this

@[expose] def recRange (i : Fin 12) (lo hi : Nat) : Bool :=
  vtabOK && qtabOK &&
    (let P := Native.evalPrep hsCtx pgam[(i : ℕ)]! axisM
     (List.range' lo (hi - lo)).all fun r => recCheck i P r)

theorem recRange_sound
    {i : Fin 12} {lo hi : Nat} (h : recRange i lo hi = true) :
    ∀ r, lo ≤ r → r < hi → ∀ ε, RecSpec i r ε := by
  intro r hlo hhi ε
  unfold recRange at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hv, hq⟩, h⟩ := h
  dsimp only at h
  have hP : interp (Native.evalPrep hsCtx pgam[(i : ℕ)]! axisM) =
      wordLin (Cert.gammaW i) aStarMinus := by
    rw [pgam_spec, interp_evalPrep_pw (gammaW_valid hv i), interp_axisM]
  exact recCheck_sound hv hq hP (List.all_eq_true.1 h r (mem_range'_iff.2 ⟨hlo, hhi⟩)) ε

@[expose] def e1UAll : Bool := (List.finRange 12).all e1UOrbit

theorem e1UAll_sound (h : e1UAll = true) (i : Fin 12) :
    ∀ k, k < 2 → bbU i k < 10 ∧
      wordLin (uW i k) (wordLin (Cert.gammaW i) aStarMinus) =
        wordLin (hppU i k ++ Cert.gammaW i) (wordLin (babyW (bbU i k)) aStarMinus) :=
  e1UOrbit_sound (List.all_eq_true.1 h i (List.mem_finRange i))

@[expose] def e2UAll : Bool := (List.finRange 12).all e2UOrbit

theorem e2UAll_sound (h : e2UAll = true) (i : Fin 12) :
    ∀ k, k < 2 → wordLin (hppU i k) aStar = aStar :=
  e2UOrbit_sound (List.all_eq_true.1 h i (List.mem_finRange i))

@[expose] def recRanges (l : List (Fin 12 × Nat × Nat)) : Bool :=
  l.all fun s => recRange s.1 s.2.1 s.2.2

theorem recRanges_sound {l : List (Fin 12 × Nat × Nat)} (h : recRanges l = true) :
    ∀ s ∈ l, recRange s.1 s.2.1 s.2.2 = true := fun s hs => List.all_eq_true.1 h s hs

@[expose] def traceAll : Bool := vtabOK &&
  (List.finRange 12).all fun i =>
    trA2N vtab[(i : ℕ)]! * 4 ^ trA2Exp i == (trA2Num i : ℤ) * 4 ^ vtab[(i : ℕ)]!.e

theorem traceAll_sound
    (h : traceAll = true) (i : Fin 12) : trA2 (vv i) = trA2Values i := by
  unfold traceAll at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := List.all_eq_true.1 h2 i (List.mem_finRange i)
  rw [beq_iff_eq] at h3
  rw [← vtab_spec h1 i, trA2_interp, trA2Values]
  have h4 : ((trA2N vtab[(i : ℕ)]! : ℤ) : ℚ) * 4 ^ trA2Exp i =
      (trA2Num i : ℚ) * 4 ^ vtab[(i : ℕ)]!.e := by exact_mod_cast h3
  rw [div_eq_div_iff (by positivity) (by positivity)]
  exact h4

end CFSG.Monster.AxisCount.HS
