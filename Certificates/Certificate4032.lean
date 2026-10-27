module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSevenInputs
import Certificates.Kernel.LocalQT.Small.C4032

public section

namespace Certificates

open CFSG.KD.LQT.C4032 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.AltSeven in
open Equiv Equiv.Perm CFSG.Open CFSG.QuasithinUnique in
theorem certificate4032 : (∀ σ : Perm (Fin 7), σ * σ = 1 → σ ≠ 1 →
          CFSG.QuasithinUnique.Ch1.AltSeven.fixCount σ = 1 ∨ CFSG.QuasithinUnique.Ch1.AltSeven.fixCount σ = 3 ∨ CFSG.QuasithinUnique.Ch1.AltSeven.fixCount σ = 5)
    ∧ (∀ σ : Perm (Fin 7), σ * σ = 1 → CFSG.QuasithinUnique.Ch1.AltSeven.fixCount σ = 3 → P22 σ)
    ∧ (∀ σ : Perm (Fin 7), σ * σ = 1 → CFSG.QuasithinUnique.Ch1.AltSeven.fixCount σ = 5 → Q2 σ)
    ∧ (∀ σ : Perm (Fin 7), σ * σ = 1 → CFSG.QuasithinUnique.Ch1.AltSeven.fixCount σ = 5 →
          ∃ c : Perm (Fin 7), Perm.sign c = 1 ∧ c ≠ 1 ∧ σ * c = c * σ)
    ∧ (∀ τ : Perm (Fin 7), τ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * τ →
          τ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * τ →
          τ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * τ →
          τ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * τ →
          τ * (swap 4 5 * swap 5 6) = (swap 4 5 * swap 5 6) * τ → τ = 1) :=
  ⟨fun σ h1 h2 => by simpa using CFSG.KC.LQT.S.s4032a ta σ h1 h2,
    (CFSG.KC.LQT.S.s4032bc cb allb cc allc).1, (CFSG.KC.LQT.S.s4032bc cb allb cc allc).2,
    CFSG.KC.LQT.S.s4032d td, fun τ h1 h2 h3 h4 h5 => CFSG.KC.LQT.S.s4032e _ hts te τ (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> assumption)⟩

end Certificates
