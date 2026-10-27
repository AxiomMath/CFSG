module

public import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofQL
import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9L
import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9U
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
public import CFSG.RankThree.PartTwo.Sec15.Item15Steps
public import Certificates.Certificate8166
public import Certificates.Certificate8169
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace Proof166Res6

theorem transport_fourGroup {T T₀ : Type*} [Group T] [Group T₀] (e : T ≃* T₀)
    (h : ∀ E₀ : Subgroup (MulAut T₀), IsPGroup 3 E₀ → ∃ S : Subgroup T₀, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      ∀ σ ∈ E₀, S.map (σ : T₀ →* T₀) = S)
    (E : Subgroup (MulAut T)) (hE : IsPGroup 3 E) :
    ∃ S : Subgroup T, S ≠ ⊥ ∧ IsPGroup 2 S ∧ ∀ σ ∈ E, S.map (σ : T →* T) = S := by
  obtain ⟨S₀, hS₀, h2, hfix⟩ := h (E.map (MulAut.congr e).toMonoidHom) (hE.map _)
  refine ⟨S₀.map e.symm.toMonoidHom, ?_, h2.map _, fun σ hσ => ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective]
    exact hS₀
  · have hσ' := hfix (MulAut.congr e σ) ⟨σ, hσ, rfl⟩
    have hcomp : (σ : T →* T).comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp ((MulAut.congr e σ : MulAut T₀) : T₀ →* T₀) := by
      ext x
      simp [MulAut.congr_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hσ']

theorem two_ne_zero_of_charP {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h0
  have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff K p] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h1)

end Proof166Res6

open Proof166Res6 CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
theorem ksl3OddE9Aut : KSL3OddE9Aut := by
  intro T _ _ p e _ hp2 he hiso E hEab _
  have hE : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hEab.2 x x.2)⟩
  rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · obtain ⟨ψ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField p e)
    have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_of_charP hp2
    have hK : Nat.card (GaloisField p e) % 3 = 1 := by
      rw [GaloisField.card p e (by omega)]
      exact hq
    exact transport_fourGroup (φ.trans ψ)
      (fun E₀ hE₀ => exists_fixed_fourGroup_projectiveSL h2 hK E₀ hE₀) E hE
  · have hU : UnitaryFieldData p e (GaloisField p (2 * e)) :=
      ⟨Fact.out, he, GaloisField.card p (2 * e) (by omega)⟩
    obtain ⟨ψ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
    have h2 : (2 : GaloisField p (2 * e)) ≠ 0 := two_ne_zero_of_charP hp2
    have hq2 : 2 < p ^ e := by
      have hp3 : 3 ≤ p := by
        have := (Fact.out : p.Prime).two_le
        omega
      calc 2 < 3 := by norm_num
        _ ≤ p := hp3
        _ ≤ p ^ e := Nat.le_self_pow (by omega) p
    exact transport_fourGroup (φ.trans ψ.symm)
      (fun E₀ hE₀ => exists_fixed_fourGroup_unitaryPSU hU h2 hq2 hq
        (card_unitarySU_galoisField hU) E₀ hE₀) E hE

end CFSG.RankThree.PartTwo.Sec16
