module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynClassical

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem kgUni_holds :
    KGSimpleOn FamUni := by
  intro p hp hp2 S _ _ lab α K hF hlab hcen hin hαp hα1 hK k f hk hlabK
  exfalso
  rw [CFSG.StandardType.TCJ.tcj_ggFixSub_eq_fixSubgroup] at hK
  have hKopen : CFSG.Open.IsComponentOf K (fixSubgroup α) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hK
  classical
  obtain ⟨F, hF', hFf, d, τ, hτ, hτQ, hcardF, hd, hd3, A, u, e, hA, hαu, hu⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.innDiag_unitary_data hcen hF hin
  have h2 : (2 : F) = 0 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.two_eq_zero_of_card
    (n := 2 * lab.n) (by rw [hcardF, ← pow_mul, Nat.mul_comm])
  generalize hQdef : 2 ^ lab.n = Q at *
  have hdQ : (d, Q) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2'⟩ := Prod.mk.inj h
    have hn2 := hd3 h1
    have : 4 ≤ Q := by
      rw [← hQdef]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hue : MulAut.congr e α = u := by
    ext z
    obtain ⟨l, rfl⟩ := e.surjective z
    show e (α (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply]
    exact hαu l
  have hpow : u ^ p = 1 := by rw [← hue, ← map_pow, hαp, map_one]
  have hord := CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.compType_uni_scalar
    h2 hτ hτQ A hA hp hp2 hcardF hd hdQ u hu hpow
  rcases CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.compType_uni_decomp
      hτ hτQ hcardF hA hord hu hue hKopen with
    ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨eM⟩⟩ |
    ⟨b, e', E, hE, hEfin, hb2, hcardE, ⟨eM⟩⟩
  · letI := hE
    have hpw : Q ^ dd = 2 ^ (lab.n * dd) := by rw [← hQdef, ← pow_mul]
    rw [hpw] at hτ'Q hcardE
    exact kg_false_of_quot_su hKopen.2.2 τ' hτ' ha2 hτ'Q hcardE ⟨eM⟩ hk hlabK
  · letI := hE
    have hpw : Q ^ (2 * e') = 2 ^ (lab.n * (2 * e')) := by rw [← hQdef, ← pow_mul]
    rw [hpw] at hcardE
    exact kg_false_of_quot_sl hKopen.2.2 hb2 hcardE ⟨eM⟩ hk hlabK

end CFSG.StandardType.KG
