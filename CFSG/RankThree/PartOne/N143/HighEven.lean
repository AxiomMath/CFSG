module

public import CFSG.RankThree.PartOne.N143.HighEvenA
public import CFSG.RankThree.PartOne.N143.HighEvenU
public import CFSG.RankThree.PartOne.N143.SectionListLie
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG TauCeti CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.Census
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

theorem noOddCentralCoverFor_highEven : NoOddCentralCoverFor IsLieHighEvenIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  have hloc : ∀ {m : ℕ}, m + 1 ≤ localRank 3 Y → 3 ≤ m → False := by
    intro m hm hm3
    have := hm.trans (CFSG.RankThree.OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num))
    omega
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      obtain ⟨h5, h3r, hq3, hq2⟩ : 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 ∧ q.p = 2 := hi
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq2
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
      let eP : S ≃* PSL(r' + 2 + 1, GaloisField q.p q.exponent) :=
        e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (r' + 2) q hv)
      let φ' : Y →* PSL(r' + 2 + 1, GaloisField q.p q.exponent) := eP.toMonoidHom.comp φ
      have hφ' : Function.Surjective φ' := eP.surjective.comp hφ
      have hkerφ : φ'.ker = φ.ker := by
        ext x
        simp [φ', MonoidHom.mem_ker]
      have hcard : 3 ∣ Nat.card (GaloisField q.p q.exponent)ˣ := by
        rw [Nat.card_units, GaloisField.card _ _ q.exponent_pos.ne']
        simpa [PrimePower.card_def] using hq3
      obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' 3 hcard
      have hζ : ζ ^ 3 = 1 := by rw [← hζo, pow_orderOf_eq_one]
      exact hloc (succ_le_localRank_psl_even hζo hζ φ' hφ' (hkerφ ▸ hcent) (hkerφ ▸ h3dvd))
        (by omega)
    | twistedA r q =>
      obtain ⟨h5, h3r, hq3, hq2⟩ : 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card + 1 ∧ q.p = 2 := hi
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hU := unitaryFieldData_galoisField q.p q.exponent q.exponent_pos
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
      have eT : (CFSGIndex.lie ⟨.twistedA (r' + 2) q, hv⟩).Group ≃*
          StatedProj (StatedSU (r' + 2 + 1) (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent))) :=
        CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj (r' + 2) q hv
      let ψ : S ≃* unitaryPSU hU (r' + 2 + 1) :=
        (e.trans eT).trans (unitaryPSUEquiv hU (n := r' + 2 + 1) (by omega)).symm
      let φ' : Y →* unitaryPSU hU (r' + 2 + 1) := ψ.toMonoidHom.comp φ
      have hφ' : Function.Surjective φ' := ψ.surjective.comp hφ
      have hkerφ : φ'.ker = φ.ker := by
        ext x
        simp [φ', MonoidHom.mem_ker]
      have hpq : 3 ∣ q.p ^ q.exponent + 1 := by
        simpa [PrimePower.card_def] using hq3
      exact hloc (succ_le_localRank_unitary_even hU hq2 hpq (r := r') (n := r' + 2 + 1)
        (by omega) φ' hφ' (hkerφ ▸ hcent) (hkerφ ▸ h3dvd)) (by omega)
    | B r q => exact hi.elim
    | C r q => exact hi.elim
    | D r q => exact hi.elim
    | twistedD r q => exact hi.elim
    | E6 q => exact hi.elim
    | E7 q => exact hi.elim
    | E8 q => exact hi.elim
    | F4 q => exact hi.elim
    | G2 q => exact hi.elim
    | twistedE6 q => exact hi.elim
    | trialityD4 q => exact hi.elim
    | suzuki m => exact hi.elim
    | reeG2 m => exact hi.elim
    | reeF4 m => exact hi.elim
    | tits => exact hi.elim

end CFSG.RankThree.PartOne.N143
