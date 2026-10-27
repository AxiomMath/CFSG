module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Gen
public import Certificates.Data.G2GenCheck
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.K7bX
import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.CGT.PushingUpLit.CGT6.EmbG23 Certificates.G2Gen Certificates.G2ThreeMax
open CFSG.CGT.PushingUpLit.CGT6.EmbModule
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

section CertificateInputs


private theorem g2GenIn_ne_one_of_diag {x : G3} {a : Array ℕ} {p : ℕ} (hx : mt x = M a)
    (hp : p / 14 = p % 14) (hpl : p < 196) (h : a[p]! % 3 = 2) : x ≠ 1 := by
  intro hx1
  have h1 : M a = 1 := by rw [← hx, hx1, mt_one, M_idArr]
  have hr : p / 14 < 14 := by omega
  have hc : p % 14 < 14 := by omega
  have h2 : M a ⟨p / 14, hr⟩ ⟨p % 14, hc⟩ = 1 := by
    have h2 := congrFun (congrFun h1 ⟨p / 14, hr⟩) ⟨p % 14, hc⟩
    simpa [Matrix.one_apply, Fin.ext_iff, hp] using h2
  simp only [M, Matrix.of_apply] at h2
  rw [Nat.div_add_mod] at h2
  have h3 : a[p]! % 3 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' (a[p]!) 1 3).1 h2
    simpa [Nat.ModEq] using this
  omega

private theorem g2GenIn_genGood_of_check (hchk : g2GenCheck = true) :
    ∀ t : G3, t * t = 1 → t ≠ 1 → IsGenGood (MulAut.conj t) := by
  intro t ht ht1
  have h := hchk
  simp only [Certificates.G2Gen.g2GenCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  let d : G3 := wordElem gensG dW
  let g : G3 := wordElem gensG gW
  let gi : G3 := wordElem gensG giW
  let y : G3 := wordElem gensG yInW
  have hd : mt d = M (wordArr dW) := mt_word dW (by decide)
  have hg : mt g = M (wordArr gW) := mt_word gW (by decide)
  have hgi : mt gi = M (wordArr giW) := mt_word giW (by decide)
  have hy : mt y = M (wordArr yInW) := mt_word yInW (by decide)
  have hd2 : d * d = 1 := eq_of_beq3 (mt_mul' hd hd) mt_one (beq_iff_eq.mpr h1)
  have hd1 : d ≠ 1 := g2GenIn_ne_one_of_diag (p := 45) hd (by decide) (by decide) h2
  have hggi : g * gi = 1 := eq_of_beq3 (mt_mul' hg hgi) mt_one (beq_iff_eq.mpr h3)
  have hginv : g⁻¹ = gi := inv_eq_of_mul_eq_one_right hggi
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hyunfold : y = gi * d * g * d := by
    simp only [y, yInW, d, g, gi, wordElem, List.map_append, List.prod_append]
  have hyeq2 : g⁻¹ * (MulAut.conj d) g = gi * d * g * d := by
    rw [MulAut.conj_apply, hginv, hdinv]
    group
  have hyeq : y = g⁻¹ * (MulAut.conj d) g := hyunfold.trans hyeq2.symm
  have hpow : ∀ n, mt (y ^ n) = M (mpowArr (wordArr yInW) n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, mt_one]; rfl
    | succ n ih => rw [pow_succ', mt_mul' hy ih]; rfl
  have hy13 : y ^ 13 = 1 := eq_of_beq3 (hpow 13) mt_one (beq_iff_eq.mpr h4)
  have hyne : y ≠ 1 := ne_one_of_nz hy (by decide) (by decide) h5
  have hyord : orderOf y = 13 := by
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact orderOf_eq_prime hy13 hyne
  have hdparam : 3 * (1 + 1) < dParam 13 := by
    have hord : dParam 13 = 12 := by
      show orderOf (2 : ZMod 13) = 12
      rw [orderOf_eq_iff (by norm_num : 0 < 12)]
      refine ⟨by decide, ?_⟩
      intro k hk _
      interval_cases k <;> decide
    rw [hord]; norm_num
  have hgen : IsGenGood (MulAut.conj d) := by
    refine ⟨1, fun _ => g, y, 13, by norm_num, hyord, ?_, hdparam⟩
    refine Subgroup.subset_closure ⟨0, ?_⟩
    exact hyeq.symm
  obtain ⟨h, hh⟩ :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.g2_involutions_conj (K := ZMod 3)
      (by rw [Nat.card_zmod]; decide) hd2 ht hd1 ht1
  have hσ : MulAut.conj t = MulAut.conj h * MulAut.conj d * (MulAut.conj h)⁻¹ := by
    rw [← hh]
    simp only [map_mul, map_inv]
  exact IsGenGood.conj hσ hgen

end CertificateInputs

theorem g23_inner_genGood_of_check (hchk : g2GenCheck = true) :
    ∀ t : G23, t * t = 1 → t ≠ 1 → IsGenGood (MulAut.conj t) := by
  intro t ht ht1
  exact g2GenIn_genGood_of_check hchk (show G3 from t) ht ht1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
