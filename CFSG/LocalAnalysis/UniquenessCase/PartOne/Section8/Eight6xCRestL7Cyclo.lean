module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7Group
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7F3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWitWords
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyConjNormalizer
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.RankThree.Lattice.SteinbergBITrialityCoxeter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open scoped Matrix Polynomial

@[expose] def cycWord (eps : ℤ) : List (Fin Tag.D4.rank) :=
  if eps = 1 then [1, 2, 3, 1, 0, 2, 1, 0] else [1, 2, 1, 0]

@[expose] def cycM (eps : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  if eps = 1 then !![-1, 1, 0, 0; -1, 0, 0, 0; -1, 1, 0, -1; -1, 0, 1, -1]
  else !![0, 0, 1, -1; 0, 1, 0, -1; -1, 1, 1, -1; 0, 1, 0, 0]

private def wordMat4_l7b (l : List (Fin Tag.D4.rank)) : Matrix (Fin 4) (Fin 4) ℤ :=
  toMat 4 (lword 4 (cartanList Tag.D4) (l.map Fin.val))

private theorem wordMat4_eq_l7b (l : List (Fin Tag.D4.rank)) :
    wordMat4_l7b l = wordMat Tag.D4 l := by
  unfold wordMat4_l7b
  rw [← toMat_lword Tag.D4 (toMat_cartanList Tag.D4) l]
  change toMat 4 (lword 4 (cartanList Tag.D4) (List.map Fin.val l)) =
    toMat 4 (lword 4 (cartanList Tag.D4) (List.map Fin.val l))
  rfl

private theorem cycWord_smul_permLattice4_l7b {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (x : Fin 4 → ℤ) :
    (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps) • permLattice TwistTag.D4.perm x =
      cycM eps *ᵥ x := by
  have h1 : (coxeterSystem Tag.D4).wordProd (cycWord eps) •
      (permLattice TwistTag.D4.perm x : Fin Tag.D4.rank → ℤ) =
      wordMat Tag.D4 (cycWord eps) *ᵥ
        (permLattice TwistTag.D4.perm x : Fin Tag.D4.rank → ℤ) :=
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.D4 (cycWord eps) _
  have hP : CFSG.RankThree.Lattice.trialityPermMat *ᵥ x =
      permLattice TwistTag.D4.perm x :=
    CFSG.RankThree.Lattice.trialityPermMat_mulVec x
  have hstep0 : wordMat Tag.D4 (cycWord eps) *ᵥ
      (permLattice TwistTag.D4.perm x : Fin Tag.D4.rank → ℤ) =
      wordMat4_l7b (cycWord eps) *ᵥ (permLattice TwistTag.D4.perm x : Fin 4 → ℤ) := by
    rw [← wordMat4_eq_l7b]
    rfl
  have hstep : wordMat4_l7b (cycWord eps) *ᵥ
      (permLattice TwistTag.D4.perm x : Fin 4 → ℤ) =
      wordMat4_l7b (cycWord eps) *ᵥ (CFSG.RankThree.Lattice.trialityPermMat *ᵥ x) := by
    rw [← hP]
  have hmat : wordMat4_l7b (cycWord eps) * CFSG.RankThree.Lattice.trialityPermMat = cycM eps := by
    rcases heps with rfl | rfl <;> decide +kernel
  have hmain : (coxeterSystem Tag.D4).wordProd (cycWord eps) •
      (permLattice TwistTag.D4.perm x : Fin Tag.D4.rank → ℤ) =
      wordMat4_l7b (cycWord eps) *ᵥ (CFSG.RankThree.Lattice.trialityPermMat *ᵥ x) :=
    h1.trans (hstep0.trans hstep)
  have h2 : wordMat4_l7b (cycWord eps) *ᵥ (CFSG.RankThree.Lattice.trialityPermMat *ᵥ x) =
      (wordMat4_l7b (cycWord eps) * CFSG.RankThree.Lattice.trialityPermMat) *ᵥ x := by
    rw [← Matrix.mulVec_mulVec]
  have h3 : (wordMat4_l7b (cycWord eps) * CFSG.RankThree.Lattice.trialityPermMat) *ᵥ x =
      cycM eps *ᵥ x := by
    rw [hmat]
  exact hmain.trans (h2.trans h3)

theorem cycWord_smul_permLattice {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps) • permLattice TwistTag.D4.perm x =
      cycM eps *ᵥ x := by
  let x4 : Fin 4 → ℤ := x
  exact cycWord_smul_permLattice4_l7b heps x4

private def cycB_l7b (eps : ℤ) : List (Fin Tag.D4.rank) :=
  if eps = 1 then [2, 3] else [0, 2]

private def cycX_l7b (eps : ℤ) : List (Fin Tag.D4.rank) :=
  if eps = 1 then [0, 1, 2, 0] else [0, 3, 2, 1]

private def cycB2_l7b (eps : ℤ) : List (Fin Tag.D4.rank) :=
  (cycX_l7b eps).reverse ++ cycB_l7b eps ++ cycX_l7b eps

private def cycMover_l7b (eps : ℤ) (i : Fin 2) : List (Fin Tag.D4.rank) :=
  if i = 0 then cycB_l7b eps else cycB2_l7b eps

private def cycMoverT_l7b (eps : ℤ) (i : Fin 2) : List (Fin TwistTag.D4.tag.rank) :=
  cycMover_l7b eps i

private theorem cycM_sq_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) :
    cycM eps ^ 2 + eps • cycM eps + 1 = 0 := by
  rcases heps with rfl | rfl <;> decide +kernel

private theorem cycM_pow_six_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) :
    cycM eps ^ 6 = 1 := by
  rcases heps with rfl | rfl <;> decide +kernel

private theorem cycMover_comm_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) (i : Fin 2) :
    cycM eps * wordMat4_l7b (cycMover_l7b eps i) =
      wordMat4_l7b (cycMover_l7b eps i) * cycM eps := by
  rcases heps with rfl | rfl <;> fin_cases i <;> decide +kernel

private theorem cycMover_lpow_three_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) (i : Fin 2) :
    lpow Tag.D4.rank (lword Tag.D4.rank (cartanList Tag.D4)
      ((cycMover_l7b eps i).map Fin.val)) 3 = lid Tag.D4.rank := by
  rcases heps with rfl | rfl <;> fin_cases i <;> decide +kernel

private theorem cycMover_wordProd_pow_three_l7b
    {eps : ℤ} (heps : eps = 1 ∨ eps = -1) (i : Fin 2) :
    (coxeterSystem Tag.D4).wordProd (cycMover_l7b eps i) ^ 3 = 1 := by
  exact tw_wordProd_pow_eq_one_of_check
    (τ := Tag.D4) (cycMover_l7b eps i) 3 (cycMover_lpow_three_l7b heps i)

private theorem cyc_cover_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) :
    ∀ x : Fin 4 → ZMod 3,
      ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (eps : ZMod 3) • x →
      x ≠ 0 →
      ((wordMat4_l7b (cycMover_l7b eps 0).reverse).map
          (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x ≠ x ∨
      ((wordMat4_l7b (cycMover_l7b eps 1).reverse).map
          (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x ≠ x := by
  rcases heps with rfl | rfl
  · decide +kernel
  · decide +kernel

private theorem cycV_card_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) :
    Nat.card {x : Fin 4 → ZMod 3 |
      ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (eps : ZMod 3) • x} = 9 := by
  rcases heps with rfl | rfl
  · rw [Nat.card_eq_fintype_card]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem k1566l7b_not_nine_dvd_dZ {q : ℕ} {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (q : ZMod 3) = (eps : ZMod 3)) :
    ¬ (9 : ℤ) ∣ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1) := by
  rcases heps with rfl | rfl
  · have hq3 : q ≡ 1 [MOD 3] := by
      have h : (q : ZMod 3) = ((1 : ℕ) : ZMod 3) := by simpa using hq
      exact (ZMod.natCast_eq_natCast_iff q 1 3).mp h
    have hqmod : q % 3 = 1 := by unfold Nat.ModEq at hq3; simpa using hq3
    obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 := ⟨q / 3, by omega⟩
    intro h9
    rw [hk] at h9
    have hd : ((↑(3 * k + 1) : ℤ) ^ 2 + 1 * ↑(3 * k + 1) + 1) =
        3 * (3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1) := by
      push_cast
      ring
    rw [hd] at h9
    obtain ⟨m, hm⟩ := h9
    have hX : 3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1 =
        3 * ((k : ℤ) ^ 2 + (k : ℤ)) + 1 := by ring
    have h3 : (3 : ℤ) ∣ 3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1 := by
      refine ⟨m, ?_⟩
      linarith [hm]
    obtain ⟨m0, hm0⟩ := h3
    rw [hX] at hm0
    omega
  · have hq3 : q ≡ 2 [MOD 3] := by
      have h2 : ((-1 : ℤ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := by decide
      have h : (q : ZMod 3) = ((2 : ℕ) : ZMod 3) := h2 ▸ hq
      exact (ZMod.natCast_eq_natCast_iff q 2 3).mp h
    have hqmod : q % 3 = 2 := by unfold Nat.ModEq at hq3; simpa using hq3
    obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
    intro h9
    rw [hk] at h9
    have hd : ((↑(3 * k + 2) : ℤ) ^ 2 + (-1) * ↑(3 * k + 2) + 1) =
        3 * (3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1) := by
      push_cast
      ring
    rw [hd] at h9
    obtain ⟨m, hm⟩ := h9
    have hX : 3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1 =
        3 * ((k : ℤ) ^ 2 + (k : ℤ)) + 1 := by ring
    have h3 : (3 : ℤ) ∣ 3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1 := by
      refine ⟨m, ?_⟩
      linarith [hm]
    obtain ⟨m0, hm0⟩ := h3
    rw [hX] at hm0
    omega

private theorem k1566l7b_fixed_tuple_zpow {L : Type} [Field L] {q : ℕ}
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    {M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ}
    (hM : M ^ 2 + eps • M + 1 = 0) {b : Fin Tag.D4.rank → Lˣ}
    (hb : b ∈ CFSG.RankThree.PartOne.KE.fixedCharTuples M Fr) :
    b ^ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1) = 1 := by
  let A : ℤ[X] := Polynomial.X ^ 2 + Polynomial.C eps * Polynomial.X + 1
  have hAeval : Polynomial.aeval M A = 0 := by
    simp only [A, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_one]
    exact hM
  funext i
  let β : Fin Tag.D4.rank → ℤ := Pi.single i 1
  have h := CFSG.RankThree.PartOne.KE.rootChar_aeval_mulVec_of_mem_fixedCharTuples
    hFr hb A β
  rw [hAeval, Matrix.zero_mulVec, rootChar_zero] at h
  have hβ : rootChar b β = b i := by
    simpa [β] using CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single b i
  rw [hβ] at h
  have hAq : A.eval (q : ℤ) = (q : ℤ) ^ 2 + eps * (q : ℤ) + 1 := by
    simp [A]
  rw [hAq] at h
  exact h.symm

private theorem k1566l7b_torus_pow_dZ {L : Type} [Field L]
    [IsAlgClosed L]
    {q : ℕ} {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) {D : LangDatum TwistTag.D4.tag L}
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
    (hΦ : D.Φ = twistHom TwistTag.D4 L Fr) {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ D.torus) :
    t ^ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1) = 1 := by
  have hv : ∀ x : Fin Tag.D4.rank → ℤ,
      (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps) •
        permLattice TwistTag.D4.perm x = cycM eps *ᵥ x :=
    cycWord_smul_permLattice (eps := eps) heps
  have hM : cycM eps ^ 2 + eps • cycM eps + 1 = 0 := cycM_sq_l7b heps
  have hmap := CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedTorusOf_twistHom_eq_map
    TwistTag.D4 Fr ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)) (cycM eps) hv
  have ht' : t ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
      (twistHom TwistTag.D4 L Fr) := by
    have h : D.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L
          ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
        (twistHom TwistTag.D4 L Fr) := by
      simp [LangDatum.torus, hn, hΦ]
    rwa [h] at ht
  rw [hmap] at ht'
  obtain ⟨b, hb, rfl⟩ := ht'
  have hb' : b ∈ CFSG.RankThree.PartOne.KE.fixedCharTuples (τ := Tag.D4) (cycM eps) Fr := hb
  have h := k1566l7b_fixed_tuple_zpow hFr hM hb'
  have h' : (b : Fin TwistTag.D4.tag.rank → Lˣ) ^
      ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1) = 1 := h
  calc
    (rootDiagUnitHom TwistTag.D4.tag L b) ^ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1) =
        (rootDiagUnitHom TwistTag.D4.tag L)
          (b ^ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1)) :=
      (map_zpow (rootDiagUnitHom TwistTag.D4.tag L) b
        ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1)).symm
    _ = 1 := by simpa using congrArg (rootDiagUnitHom TwistTag.D4.tag L) h'

private theorem cycV_cardT_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) :
    Nat.card {x : Fin TwistTag.D4.tag.rank → ZMod 3 |
      ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (eps : ZMod 3) • x} = 9 :=
  cycV_card_l7b heps

private theorem cyc_coverT_l7b {eps : ℤ} (heps : eps = 1 ∨ eps = -1) :
    ∀ x : Fin TwistTag.D4.tag.rank → ZMod 3,
      ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (eps : ZMod 3) • x →
      x ≠ 0 →
      ((wordMat Tag.D4 (cycMover_l7b eps 0).reverse).map
          (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x ≠ x ∨
      ((wordMat Tag.D4 (cycMover_l7b eps 1).reverse).map
          (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x ≠ x := by
  intro x hx hx0
  have h := cyc_cover_l7b (eps := eps) heps x hx hx0
  convert h using 2 <;> rw [wordMat4_eq_l7b] <;> rfl

private def k1566l7b_W {L : Type} [Field L] [IsAlgClosed L]
    (D : LangDatum TwistTag.D4.tag L) :
    Subgroup (ModGL TwistTag.D4.tag L) where
  carrier := {t | t ∈ D.torus ∧ t ^ 3 = 1}
  mul_mem' := by
    intro a b ha hb
    refine ⟨D.torus.mul_mem ha.1 hb.1, ?_⟩
    have hcomm : Commute a b :=
      congrArg Subtype.val
        (D.isMulCommutative_torus.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
    rw [hcomm.mul_pow, ha.2, hb.2, one_mul]
  one_mem' := ⟨D.torus.one_mem, one_pow 3⟩
  inv_mem' := by
    intro a ha
    exact ⟨D.torus.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

private noncomputable abbrev k1566l7b_T (L : Type) [Field L]
    (Fr : L →+* L) (eps : ℤ) :
    Subgroup (ModGL TwistTag.D4.tag L) :=
  CFSG.RankThree.PartOne.KE.twistedTorusOf
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
    (twistHom TwistTag.D4 L Fr)

private abbrev k1566l7b_w (eps : ℤ) : WeylGroup TwistTag.D4.tag :=
  (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)

private def k1566l7b_W0 (eps : ℤ) :
    Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  wordMat Tag.D4 (cycMover_l7b eps 0).reverse

private def k1566l7b_W1 (eps : ℤ) :
    Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  wordMat Tag.D4 (cycMover_l7b eps 1).reverse

private def k1566l7b_V (eps : ℤ) : Set (Fin TwistTag.D4.tag.rank → ZMod 3) :=
  {x | ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (eps : ZMod 3) • x}

private theorem k1566l7b_card_W_surj {L : Type} [Field L]
    [IsAlgClosed L]
    {q : ℕ} {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (hq : (q : ZMod 3) = (eps : ZMod 3))
    (D : LangDatum TwistTag.D4.tag L) {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (hv : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      k1566l7b_w eps • permLattice TwistTag.D4.perm x = cycM eps *ᵥ x)
    (hDtor : D.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L (k1566l7b_w eps))
      (twistHom TwistTag.D4 L Fr)) (t : k1566l7b_W D) :
    ∃ x : Fin TwistTag.D4.tag.rank → ZMod 3,
      x ∈ k1566l7b_V eps ∧ f3Diag Tag.D4 ζ x = t.1 := by
    have htT : t.1 ∈ D.torus := t.2.1
    have ht3 : t.1 ^ 3 = 1 := t.2.2
    have htg : t.1 ∈ torusGroup Tag.D4 L :=
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 t.2.1).1
    obtain ⟨x, hx⟩ := exists_f3Diag_eq (τ := Tag.D4) hζ htg ht3
    have hxT : f3Diag Tag.D4 ζ x ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L
          ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
        (twistHom TwistTag.D4 L Fr) := by
      rw [← hx] at htT
      rw [hDtor] at htT
      exact htT
    have hxV : x ∈ k1566l7b_V eps := by
      show ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (eps : ZMod 3) • x
      have hmem := (f3Diag_mem_twistedTorusOf_iff TwistTag.D4 hζ hFr
        (v := k1566l7b_w eps)
        (M := cycM eps) hv x).1 hxT
      rw [hq] at hmem
      exact hmem
    exact ⟨x, hxV, hx⟩

private theorem k1566l7b_card_W_aux {L : Type} [Field L]
    [IsAlgClosed L]
    {q : ℕ} {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (hq : (q : ZMod 3) = (eps : ZMod 3))
    (D : LangDatum TwistTag.D4.tag L) {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (hv : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      k1566l7b_w eps • permLattice TwistTag.D4.perm x = cycM eps *ᵥ x)
    (hDtor : D.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L (k1566l7b_w eps))
      (twistHom TwistTag.D4 L Fr)) :
    Nat.card (k1566l7b_W D) = Nat.card {x // x ∈ k1566l7b_V eps} := by
  let V := k1566l7b_V eps
  let f : {x // x ∈ V} → k1566l7b_W D := fun x =>
    ⟨f3Diag Tag.D4 ζ x.1, by
      refine ⟨?_, f3Diag_pow_three (τ := Tag.D4) (by rw [← hζ, pow_orderOf_eq_one]) x.1⟩
      have hmem := (f3Diag_mem_twistedTorusOf_iff TwistTag.D4 hζ hFr
        (v := k1566l7b_w eps)
        (M := cycM eps) hv x.1).2 (by
          show ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x.1 =
            (q : ZMod 3) • x.1
          rw [hq]
          exact x.2)
      rw [hDtor]
      exact hmem⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact f3Diag_injective (τ := Tag.D4) hζ (congrArg Subtype.val hxy)
  have hf_surj : Function.Surjective f := by
    intro t
    obtain ⟨x, hxV, hx⟩ :=
      k1566l7b_card_W_surj hFr hq D hζ hv hDtor t
    exact ⟨⟨x, hxV⟩, Subtype.ext hx⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
private theorem k1566l7b_card_W {L : Type} [Field L]
    [IsAlgClosed L]
    {q : ℕ} {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (q : ZMod 3) = (eps : ZMod 3))
    (D : LangDatum TwistTag.D4.tag L)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
    (hΦ : D.Φ = twistHom TwistTag.D4 L Fr)
    {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    Nat.card (k1566l7b_W D) = 9 := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ, pow_orderOf_eq_one]
  have hv : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps) •
        permLattice TwistTag.D4.perm x = cycM eps *ᵥ x :=
    cycWord_smul_permLattice (eps := eps) heps
  have hDtor : D.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L (k1566l7b_w eps))
      (twistHom TwistTag.D4 L Fr) := by
    simp [k1566l7b_w, LangDatum.torus, hn, hΦ]
  calc
    Nat.card (k1566l7b_W D) = Nat.card {x // x ∈ k1566l7b_V eps} :=
      k1566l7b_card_W_aux hFr hq D hζ hv hDtor
    _ = 9 := cycV_cardT_l7b heps
private theorem k1566l7b_dZ_pos {q : ℕ} (hq2 : 2 ≤ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) :
    0 < (q : ℤ) ^ 2 + eps * (q : ℤ) + 1 := by
  rcases heps with rfl | rfl
  · nlinarith [sq_nonneg (q : ℤ), (by exact_mod_cast hq2 : (2 : ℤ) ≤ q)]
  · nlinarith [sq_nonneg ((q : ℤ) - 1), (by exact_mod_cast hq2 : (2 : ℤ) ≤ q)]

private theorem k1566l7b_torus_pow_d {L : Type} [Field L]
    [IsAlgClosed L]
    {q : ℕ} (hq2 : 2 ≤ q) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (D : LangDatum TwistTag.D4.tag L)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
    (hΦ : D.Φ = twistHom TwistTag.D4 L Fr) :
    ∀ t ∈ D.torus, t ^ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1).toNat = 1 := by
  have hpos : 0 < (q : ℤ) ^ 2 + eps * (q : ℤ) + 1 := k1566l7b_dZ_pos hq2 heps
  intro t ht
  rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt hpos)]
  exact k1566l7b_torus_pow_dZ hFr heps hn hΦ ht

private theorem k1566l7b_d9 {q : ℕ} (hq2 : 2 ≤ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (q : ZMod 3) = (eps : ZMod 3)) :
    ¬ 9 ∣ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1).toNat := by
  have hpos : 0 < (q : ℤ) ^ 2 + eps * (q : ℤ) + 1 := k1566l7b_dZ_pos hq2 heps
  intro h
  apply k1566l7b_not_nine_dvd_dZ heps hq
  have hz : (9 : ℤ) ∣ (((q : ℤ) ^ 2 + eps * (q : ℤ) + 1).toNat : ℤ) :=
    Int.natCast_dvd_natCast.mpr h
  rwa [Int.toNat_of_nonneg (le_of_lt hpos)] at hz

private theorem k1566l7b_cube_comm {L : Type} [Field L]
    {y : ModGL TwistTag.D4.tag L} {u : WeylGroup TwistTag.D4.tag}
    (hy_act : TwActsAs y u) (hu3 : u ^ 3 = 1) :
    ∀ t : Fin TwistTag.D4.tag.rank → Lˣ,
      Commute (y ^ 3) (rootDiagUnit TwistTag.D4.tag t) := by
  intro t
  show y ^ 3 * rootDiagUnit TwistTag.D4.tag t =
    rootDiagUnit TwistTag.D4.tag t * y ^ 3
  have h1 := hy_act t
  have h2 := hy_act (weylTuple u t)
  have h3 := hy_act (weylTuple (u * u) t)
  have hu3' : u * (u * u) = u ^ 3 := by
    rw [← mul_assoc, show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  have h3' : y * rootDiagUnit TwistTag.D4.tag (weylTuple (u * u) t) * y⁻¹ =
      rootDiagUnit TwistTag.D4.tag t := by
    rw [h3, weylTuple_weylTuple, hu3', hu3, weylTuple_one]
  have hy3 : y ^ 3 = y * y * y := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  have hcube : y ^ 3 * rootDiagUnit TwistTag.D4.tag t * (y ^ 3)⁻¹ =
      rootDiagUnit TwistTag.D4.tag t := by
    calc
      y ^ 3 * rootDiagUnit TwistTag.D4.tag t * (y ^ 3)⁻¹ =
          y * (y * (y * rootDiagUnit TwistTag.D4.tag t * y⁻¹) * y⁻¹) * y⁻¹ := by
        rw [hy3]
        group
      _ = y * (y * rootDiagUnit TwistTag.D4.tag (weylTuple u t) * y⁻¹) * y⁻¹ := by
        rw [h1]
      _ = y * rootDiagUnit TwistTag.D4.tag (weylTuple u (weylTuple u t)) * y⁻¹ := by
        rw [h2]
      _ = y * rootDiagUnit TwistTag.D4.tag (weylTuple (u * u) t) * y⁻¹ := by
        rw [weylTuple_weylTuple]
      _ = rootDiagUnit TwistTag.D4.tag t := h3'
  calc
    y ^ 3 * rootDiagUnit TwistTag.D4.tag t =
        (y ^ 3 * rootDiagUnit TwistTag.D4.tag t * (y ^ 3)⁻¹) * y ^ 3 := by group
    _ = rootDiagUnit TwistTag.D4.tag t * y ^ 3 := by rw [hcube]

private theorem k1566l7b_y3_torus {L : Type} [Field L]
    [IsAlgClosed L]
    {D : LangDatum TwistTag.D4.tag L} {y : ModGL TwistTag.D4.tag L}
    {u : WeylGroup TwistTag.D4.tag}
    (hy_mono : y ∈ monomialSubgroup TwistTag.D4.tag L)
    (hy_fixed : D.n * D.Φ y * D.n⁻¹ = y)
    (hy_act : TwActsAs y u) (hu3 : u ^ 3 = 1) :
    y ^ 3 ∈ D.torus := by
  have hyM : y ∈ D.model := tw_mem_model D hy_mono hy_fixed
  have hy3adj : y ^ 3 ∈ adjointGroup TwistTag.D4.tag L :=
    (adjointGroup TwistTag.D4.tag L).pow_mem hyM.1 3
  have hy3comm := k1566l7b_cube_comm hy_act hu3
  have hy3tor : y ^ 3 ∈ torusGroup TwistTag.D4.tag L :=
    CFSG.HardMathSupport.Timmesfeld.Torality.mem_torusGroup_of_forall_commute_rootDiagUnit
      (τ := TwistTag.D4.tag) hy3adj hy3comm
  have hy3fix : D.n * D.Φ (y ^ 3) * D.n⁻¹ = y ^ 3 := by
    rw [map_pow]
    calc
      D.n * (D.Φ y) ^ 3 * D.n⁻¹ = (D.n * D.Φ y * D.n⁻¹) ^ 3 := by
        rw [← conj_pow]
      _ = y ^ 3 := by rw [hy_fixed]
  exact CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.2 ⟨hy3tor, hy3fix⟩

private theorem k1566l7b_mover {L : Type} [Field L]
    [IsAlgClosed L]
    {q : ℕ} (hq2 : 2 ≤ q) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (D : LangDatum TwistTag.D4.tag L)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
    (hΦ : D.Φ = twistHom TwistTag.D4 L Fr) (i : Fin 2) :
    ∃ u : ModGL TwistTag.D4.tag L,
      u ∈ D.model ∧ (∀ t ∈ D.torus, u * t * u⁻¹ ∈ D.torus) ∧
        u ^ 3 ∈ D.torus ∧
          TwActsAs u ((coxeterSystem TwistTag.D4.tag).wordProd (cycMover_l7b eps i)) := by
  have hv : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps) •
        permLattice TwistTag.D4.perm x = cycM eps *ᵥ x :=
    cycWord_smul_permLattice (eps := eps) heps
  have hcomm4 : cycM eps * wordMat4_l7b (cycMover_l7b eps i) =
      wordMat4_l7b (cycMover_l7b eps i) * cycM eps :=
    cycMover_comm_l7b (eps := eps) heps i
  rw [wordMat4_eq_l7b] at hcomm4
  have hu : (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps) *
      weylTwist TwistTag.D4
        ((coxeterSystem TwistTag.D4.tag).wordProd (cycMover_l7b eps i)) =
      (coxeterSystem TwistTag.D4.tag).wordProd (cycMover_l7b eps i) *
        (coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps) :=
    tw_comm_of_word_matrix
      (t := TwistTag.D4) (lw := cycWord eps) (la := cycMover_l7b eps i)
      (M := cycM eps) hv hcomm4
  obtain ⟨y, hy_mono, hy_fixed, hy_act⟩ :=
    tw_exists_lift
      (t := TwistTag.D4) D hq2 hFr hΦ hn hv (by norm_num : (6 : ℕ) ≠ 0)
      (cycM_pow_six_l7b heps) hu
  have hyM : y ∈ D.model :=
    tw_mem_model
      D hy_mono hy_fixed
  have hyT : ∀ t ∈ D.torus, y * t * y⁻¹ ∈ D.torus := fun t ht =>
    tw_conj_mem_torus
      D hy_mono hy_fixed ht
  have hu3 : (coxeterSystem TwistTag.D4.tag).wordProd (cycMover_l7b eps i) ^ 3 = 1 :=
    cycMover_wordProd_pow_three_l7b heps i
  have hy3T : y ^ 3 ∈ D.torus :=
    k1566l7b_y3_torus (D := D) (y := y) hy_mono hy_fixed hy_act hu3
  exact ⟨y, hyM, hyT, hy3T, hy_act⟩

private theorem k1566l7b_cover_words {eps : ℤ} :
    (∀ z : Fin TwistTag.D4.tag.rank → ℤ,
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycMoverT_l7b eps 0))⁻¹ • z =
        k1566l7b_W0 eps *ᵥ z) ∧
    (∀ z : Fin TwistTag.D4.tag.rank → ℤ,
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycMoverT_l7b eps 1))⁻¹ • z =
        k1566l7b_W1 eps *ᵥ z) := by
  constructor
  · intro z
    rw [← CoxeterSystem.wordProd_reverse,
      CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec,
      show wordMat TwistTag.D4.tag (cycMoverT_l7b eps 0).reverse = k1566l7b_W0 eps from rfl]
  · intro z
    rw [← CoxeterSystem.wordProd_reverse,
      CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec,
      show wordMat TwistTag.D4.tag (cycMoverT_l7b eps 1).reverse = k1566l7b_W1 eps from rfl]

private theorem k1566l7b_cover {L : Type} [Field L]
    [IsAlgClosed L]
    {q : ℕ} {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (q : ZMod 3) = (eps : ZMod 3))
    (D : LangDatum TwistTag.D4.tag L) {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (hv : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      k1566l7b_w eps • permLattice TwistTag.D4.perm x = cycM eps *ᵥ x)
    (hDtor : D.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L (k1566l7b_w eps))
      (twistHom TwistTag.D4 L Fr))
    {u₁ u₂ : ModGL TwistTag.D4.tag L}
    (hu₁ : TwActsAs u₁ ((coxeterSystem TwistTag.D4.tag).wordProd (cycMover_l7b eps 0)))
    (hu₂ : TwActsAs u₂ ((coxeterSystem TwistTag.D4.tag).wordProd (cycMover_l7b eps 1))) :
    ∀ t ∈ k1566l7b_W D, t ≠ 1 →
      u₁ * t * u₁⁻¹ ≠ t ∨ u₂ * t * u₂⁻¹ ≠ t := by
  obtain ⟨hW0, hW1⟩ := k1566l7b_cover_words (eps := eps)
  intro t ht ht1
  obtain ⟨htT, ht3⟩ := ht
  have htg : t ∈ torusGroup TwistTag.D4.tag L :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 htT).1
  obtain ⟨x, hx⟩ := exists_f3Diag_eq (τ := TwistTag.D4.tag) hζ htg ht3
  have hxT : f3Diag TwistTag.D4.tag ζ x ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L (k1566l7b_w eps))
      (twistHom TwistTag.D4 L Fr) := by
    rwa [← hx, hDtor] at htT
  have hxV : ((cycM eps).map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (eps : ZMod 3) • x := by
    have hmem := (f3Diag_mem_twistedTorusOf_iff TwistTag.D4 hζ hFr
      (v := k1566l7b_w eps)
      (M := cycM eps) hv x).1 hxT
    rwa [hq] at hmem
  have hx0 : x ≠ 0 := by
    intro hx0
    apply ht1
    rw [← hx, hx0, f3Diag_zero]
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ, pow_orderOf_eq_one]
  rcases cyc_coverT_l7b (eps := eps) heps x hxV hx0 with h | h
  · left
    intro hfix
    have hact := f3Diag_conj_of_twActsAs (τ := TwistTag.D4.tag) hζ3 hu₁ hW0 x
    rw [← hx, hact] at hfix
    exact h (f3Diag_injective (τ := TwistTag.D4.tag) hζ hfix)
  · right
    intro hfix
    have hact := f3Diag_conj_of_twActsAs (τ := TwistTag.D4.tag) hζ3 hu₂ hW1 x
    rw [← hx, hact] at hfix
    exact h (f3Diag_injective (τ := TwistTag.D4.tag) hζ hfix)

theorem movingE9_cyc {L : Type} [Field L] [IsAlgClosed L]
    (h3 : (3 : L) ≠ 0) {q : ℕ} (hq2 : 2 ≤ q) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ q) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (q : ZMod 3) = (eps : ZMod 3))
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L Fr g0 = g0 * canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps))) :
    ∃ W : Subgroup (ModGL TwistTag.D4.tag L),
      MovingE9 (LangDatum.ofTwist TwistTag.D4 Fr q hFr _ hg0C hg0).model W := by
  obtain ⟨ζ, hζ⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (n := 3) (by simpa using h3)
  let D : LangDatum TwistTag.D4.tag L := LangDatum.ofTwist TwistTag.D4 Fr q hFr
    ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)) hg0C hg0
  have hmem : ∀ t, t ∈ k1566l7b_W D ↔ t ∈ D.torus ∧ t ^ 3 = 1 := fun _ => Iff.rfl
  have hW9 : Nat.card (k1566l7b_W D) = 9 :=
    k1566l7b_card_W hFr heps hq D rfl rfl hζ
  have hd : ∀ t ∈ D.torus, t ^ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1).toNat = 1 :=
    k1566l7b_torus_pow_d hq2 hFr heps D rfl rfl
  have hd9 : ¬ 9 ∣ ((q : ℤ) ^ 2 + eps * (q : ℤ) + 1).toNat :=
    k1566l7b_d9 hq2 heps hq
  obtain ⟨u₁, hu₁M, hu₁T, hu₁3, hu₁act⟩ :=
    k1566l7b_mover hq2 hFr heps D rfl rfl (0 : Fin 2)
  obtain ⟨u₂, hu₂M, hu₂T, hu₂3, hu₂act⟩ :=
    k1566l7b_mover hq2 hFr heps D rfl rfl (1 : Fin 2)
  have hv : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      k1566l7b_w eps • permLattice TwistTag.D4.perm x = cycM eps *ᵥ x :=
    cycWord_smul_permLattice (eps := eps) heps
  have hDtor : D.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L (k1566l7b_w eps))
      (twistHom TwistTag.D4 L Fr) := by
    simp [k1566l7b_w, LangDatum.torus]
    rfl
  have hcover : ∀ t ∈ k1566l7b_W D, t ≠ 1 →
      u₁ * t * u₁⁻¹ ≠ t ∨ u₂ * t * u₂⁻¹ ≠ t :=
    k1566l7b_cover hFr heps hq D hζ hv hDtor hu₁act hu₂act
  exact ⟨k1566l7b_W D,
    movingE9_of_cover D.torus_le_model D.isMulCommutative_torus hd hd9 hmem hW9
      hu₁M hu₂M hu₁T hu₂T hu₁3 hu₂3 hcover⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7
