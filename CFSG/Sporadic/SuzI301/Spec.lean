module

public import Certificates.Certificate810302
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
public import CFSG.Sporadic.SuzI301.SpecAux

public noncomputable section

namespace CFSG.Sporadic.SuzI301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.HardMathSupport.Dickson.I271

@[expose] def hP : Equiv.Perm (Fin 1782) := permOfArr 1782 (sH ())

@[expose] def dP : Equiv.Perm (Fin 1782) := permOfArr 1782 (sD ())

@[expose] def b2P : Equiv.Perm (Fin 1782) := permOfArr 1782 (sB2 ())

@[expose] def b3P : Equiv.Perm (Fin 1782) := permOfArr 1782 (sB3 ())

@[expose] def mP : Equiv.Perm (Fin 1782) := permOfArr 1782 (sM ())

@[expose] def tauP : Equiv.Perm (Fin 1782) := suzV * mP

@[expose] def B1 : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure {dP, b2P, b3P}

@[expose] def tabP (t : Array ℕ) : Equiv.Perm (Fin 64) := permOfArr 64 t

@[expose] def oGens : Array (Array ℕ) := matTabs.push (mat64 (sTau ()))

section Facts


theorem hP_mem : hP ∈ suzM := SpecAux.hP_mem

theorem dP_eq : dP = hP * fuseXA * hP⁻¹ := SpecAux.dP_eq

theorem gens_mem : dP ∈ invE 1 ∧ b2P ∈ invE 1 ∧ b3P ∈ invE 1 ∧ mP ∈ suzM := SpecAux.gens_mem

theorem commute_facts : Commute dP b2P ∧ Commute dP b3P ∧ Commute b2P b3P ∧
    Commute (suzInv 1) tauP := SpecAux.commute_facts

theorem pow_facts : dP ^ 3 = 1 ∧ b2P ^ 3 = 1 ∧ b3P ^ 3 = 1 := SpecAux.pow_facts

theorem indep_facts : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → dP ^ i * b2P ^ j * b3P ^ k = 1 →
    i = 0 ∧ j = 0 ∧ k = 0 := SpecAux.indep_facts

theorem conj_qVec_facts :
    (∀ v < 64, (mat64 (sD ()))[v]! < 64 ∧ ∃ a < 2,
      dP * qVec v * dP⁻¹ = qVec (mat64 (sD ()))[v]! * suzInv 1 ^ a) ∧
    (∀ v < 64, (mat64 (sB2 ()))[v]! < 64 ∧ ∃ a < 2,
      b2P * qVec v * b2P⁻¹ = qVec (mat64 (sB2 ()))[v]! * suzInv 1 ^ a) ∧
    (∀ v < 64, (mat64 (sB3 ()))[v]! < 64 ∧ ∃ a < 2,
      b3P * qVec v * b3P⁻¹ = qVec (mat64 (sB3 ()))[v]! * suzInv 1 ^ a) ∧
    (∀ v < 64, (mat64 (sTau ()))[v]! < 64 ∧ ∃ a < 2,
      tauP * qVec v * tauP⁻¹ = qVec (mat64 (sTau ()))[v]! * suzInv 1 ^ a) ∧
    (∀ t ∈ [mat64 (sD ()), mat64 (sB2 ()), mat64 (sB3 ()), mat64 (sTau ())],
      Rep 64 t (tabP t)) := SpecAux.conj_qVec_facts

theorem six4_facts :
    ∀ g ∈ Subgroup.closure (Set.range fun j : Fin 11 => tabP oGens[(j : ℕ)]!), g * g = 1 →
      g ≠ 1 → ∃ y ∈ ({tabP (mat64 (sD ())) * tabP (mat64 (sB2 ())) * tabP (mat64 (sB3 ())) ^ 2,
        tabP (mat64 (sB2 ())) ^ 2 * tabP (mat64 (sB3 ())) ^ 2} : Set (Equiv.Perm (Fin 64))),
        ¬ Commute g (y * g * y⁻¹) := SpecAux.six4_facts

theorem tau_not_mem_omega : tabP (mat64 (sTau ())) ∉
    Subgroup.closure (Set.range fun j : Fin 10 => tabP matTabs[(j : ℕ)]!) :=
  SpecAux.tau_not_mem_omega

theorem omega_cent_facts : ∀ g ∈ Subgroup.closure (Set.range fun j : Fin 10 =>
    tabP matTabs[(j : ℕ)]!), Commute g (tabP (mat64 (sD ()))) → g ^ 12 = 1 :=
  SpecAux.omega_cent_facts

theorem r0_facts :
    (∀ v < 64, ∀ a < 2, Commute dP (qVec v * suzInv 1 ^ a) ↔ (mat64 (sD ()))[v]! = v) ∧
    ∀ v < 64, v ≠ 0 → (mat64 (sD ()))[v]! = v → ∃ w < 64, (mat64 (sD ()))[w]! = w ∧
      (gammaBit v w + gammaBit w v) % 2 = 1 := SpecAux.r0_facts

theorem r0_card : ((Finset.range 64).filter fun v => (mat64 (sD ()))[v]! = v).card = 16 :=
  SpecAux.r0_card

end Facts

end CFSG.Sporadic.SuzI301
