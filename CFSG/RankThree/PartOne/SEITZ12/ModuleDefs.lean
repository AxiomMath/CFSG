module

public import CFSG.LieType.Ree.LargeReeInvolutionCoordinates

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

@[expose] noncomputable def phi4ml_vt (m : ℕ) (K : Type) [Field K] (e k l g i : K) :
    ModGL F4.tag K :=
  sylowD m K 0 e * sylowF m K 0 g * sylowH m K 0 i * sylowK m K k * sylowL m K l

@[expose] def phi4ml_vtWord (pe pse pg psg pi psi pk psk pl psl : Poly) : Word :=
  [(36, pe), (39, pse), (43, pg), (46, psg), (44, pi), (47, psi), (38, pk), (42, psk), (41, pl),
    (45, psl)]

theorem phi4ml_wordEval_vtWord (σ : K →+* K) (hσ : ∀ c, σ c = largeReeSigma m c) (x : ℕ → K)
    (pe pse pg psg pi psi pk psk pl psl : Poly) (hse : polyEval x pse = σ (polyEval x pe))
    (hsg : polyEval x psg = σ (polyEval x pg)) (hsi : polyEval x psi = σ (polyEval x pi))
    (hsk : polyEval x psk = σ (polyEval x pk)) (hsl : polyEval x psl = σ (polyEval x pl)) :
    wordEval K x (phi4ml_vtWord pe pse pg psg pi psi pk psk pl psl) =
      phi4ml_vt m K (polyEval x pe) (polyEval x pk) (polyEval x pl) (polyEval x pg)
        (polyEval x pi) := by
  simp only [wordEval, phi4ml_vtWord, phi4ml_vt, sylowD, sylowF, sylowH, sylowK, sylowL, sylowX,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hse, hsg, hsi, hsk, hsl,
    ← hσ, map_zero, pinnedX_zero, zero_pow two_ne_zero, zero_mul, add_zero, one_mul, mul_assoc]

theorem phi4ml_wordEval_reverse (x : ℕ → K) (w : Word) :
    wordEval K x w.reverse = (wordEval K x w)⁻¹ := by
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  induction w with
  | nil => simp [wordEval_nil]
  | cons f w ih =>
    have h1 : wordEval K x [f] =
        pinnedX F4.tag K (orbitCertRoot F4.tag f.1) (polyEval x f.2) := by
      simp [wordEval_cons, wordEval_nil]
    rw [List.reverse_cons, wordEval_append, ih, h1, wordEval_cons, mul_inv_rev, pinnedX_neg,
      CharTwo.neg_eq]

theorem phi4ml_vt_e (e : K) : phi4ml_vt m K e 0 0 0 0 = sylowD m K 0 e := by
  simp [phi4ml_vt, sylowF, sylowH, sylowK, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem phi4ml_vt_k (k : K) : phi4ml_vt m K 0 k 0 0 0 = sylowK m K k := by
  simp [phi4ml_vt, sylowD, sylowF, sylowH, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem phi4ml_vt_g (g : K) : phi4ml_vt m K 0 0 0 g 0 = sylowF m K 0 g := by
  simp [phi4ml_vt, sylowD, sylowH, sylowK, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem phi4ml_vt_i (i : K) : phi4ml_vt m K 0 0 0 0 i = sylowH m K 0 i := by
  simp [phi4ml_vt, sylowD, sylowF, sylowK, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem phi4ml_vt_zero : phi4ml_vt m K 0 0 0 0 0 = 1 := by
  simp [phi4ml_vt, sylowD, sylowF, sylowH, sylowK, sylowL, sylowX, largeReeSigma_zero,
    pinnedX_zero]

end CFSG.RankThree.PartOne.SEITZ12
