module

public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaDefs
import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaUniComp
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem innDiagAllEnnolaUni_of_pieces (hScal : UniScalar) (hP3 : UniLabelDict) :
    InnDiagAllEnnolaOn FamUni := by
  intro S _ _ p α J labK labJ hFam hp hp2 hrow hcen hin hα hlabJ hJ
  have hpq : p ∣ 2 ^ labK.n + 1 := by
    rcases hrow with h | ⟨-, -, h⟩
    · exact ggRowP_E.dvd h
    · exact h
  obtain ⟨K, hK, hKf, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    innDiag_unitary_data hcen hFam hin
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hJ' : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom) (fixSubgroup u) := by
    rw [← hMEq]
    exact tcjLin_component_transport e α hJ
  have hlabJ' : HasLabel ↥(J.map e.toMonoidHom) (fun l : GLALabel => l = labJ) :=
    hasLabel_transport e hlabJ
  have hdQ : (d, 2 ^ labK.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ labK.n := hd3n hd
    have : 2 ^ 2 ≤ 2 ^ labK.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  have hcanK : (canonLabel labK).n = labK.n := by
    rcases hFam with ht | ⟨ht, hr⟩
    · simp [canonLabel, ht]
    · simp [canonLabel, ht, hr]
  obtain ⟨a, dd, E, hE, hEf, τ', hτ', ha2, hddp, hτ'Q, hcardE, ⟨φ⟩⟩ :=
    tcjUniEnnola_component_psu_fixed hScal hτ hτq hcard ⟨labK.n, rfl⟩ (by omega) hdQ A hA hp hp2
      hpq u hgraph hpow (J.map e.toMonoidHom) hJ'
  have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (labK.n * dd) := by
    intro x
    rw [pow_mul]
    exact hτ'Q x
  have hcardm : Nat.card E = (2 ^ (labK.n * dd)) ^ 2 := by
    rw [pow_mul]
    exact hcardE
  have hlab : (canonLabel labJ).n = labK.n * dd :=
    hP3 ↥(J.map e.toMonoidHom) labJ a (labK.n * dd) E τ' hτ' ha2 hτ'm hcardm hlabJ' ⟨φ⟩
  have hodd : Odd dd := by
    rcases (Nat.dvd_prime hp).mp hddp with h1 | h1
    · rw [h1]
      exact odd_one
    · rw [h1]
      exact hp.odd_of_ne_two hp2
  exact ⟨dd, hodd, by rw [hlab, hcanK, mul_comm]⟩

theorem innDiagAllEnnolaUni :
    InnDiagAllEnnolaOn FamUni :=
  innDiagAllEnnolaUni_of_pieces uniScalar_holds uniLabelDict_holds

end CFSG.StandardType.TCJ

end
