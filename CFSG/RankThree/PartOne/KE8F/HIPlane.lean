module

public import CFSG.RankThree.PartOne.KE8F.HIAssembly
public import CFSG.RankThree.PartOne.KE8F.PlaneToralE8
public import CFSG.RankThree.PartOne.KE.NativeCyclicLocalCore
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter
public import CFSG.RankThree.PartOne.KE.NativeCyclicEndpoint

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE (ordinary_E_outer_derived_subgroup_odd localCoreTrivialOn_noninner_E
  OddEndpoint cycloVal oddEndpoint_E8_of_native)

theorem planeLocalCoreOdd_E8_phi4_big
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp10 : 10 < p)
    (hpf : p ∣ Nat.card K * Nat.card K + 1) :
    PlaneLocalCoreOdd p (adjointGroup .E8 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨F⟩ := exists_e8P4Frame K hf hK hp (by omega) hpf L
  have hout := (ordinary_E_outer_derived_subgroup_odd .E8 (Or.inr (Or.inr rfl)) K).1
  have hcore := localCoreTrivialOn_noninner_E .E8 (Or.inr (Or.inr rfl)) K hp (by omega)
  exact planeLocalCoreOdd16 hp hp10 center_adjointGroup_eq_bot (hV_E8 F hf hK hp hp10 hpf) hout
    hcore (hI_E8 F hf hK hp hp10 hpf center_adjointGroup_eq_bot)

theorem oddEndpoint_E8_phi4_big
    : OddEndpoint .E8 fun p ℓ f => 5 < p ∧ (p : ℤ) ∣ cycloVal 4 ℓ f := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨hp5, hpc⟩ := hc
  have hpf : p ∣ Nat.card K * Nat.card K + 1 := by
    have h : (p : ℤ) ∣ ((Nat.card K : ℤ) * (Nat.card K : ℤ) + 1) := by
      have h1 : (p : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ) := by
        simpa [cycloVal, hK] using hpc
      have e4 : (exhaustionPhi 4).eval (Nat.card K : ℤ) = (Nat.card K : ℤ) ^ 2 + 1 := by
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one]
      rw [e4] at h1
      simpa [sq] using h1
    exact_mod_cast h
  have hp10 : 10 < p := by
    by_contra hle
    have hle' : p ≤ 10 := by omega
    have h7 : p = 7 := by
      interval_cases p <;> first | rfl | (exfalso; norm_num at hp)
    subst h7
    have h0 := (ZMod.natCast_eq_zero_iff (Nat.card K * Nat.card K + 1) 7).2 hpf
    push_cast at h0
    have key : ∀ x : ZMod 7, x * x + 1 ≠ 0 := by decide
    exact key _ h0
  exact planeLocalCoreOdd_E8_phi4_big K hℓ hf hK hp hp10 hpf

end CFSG.RankThree.PartOne.KE8F
