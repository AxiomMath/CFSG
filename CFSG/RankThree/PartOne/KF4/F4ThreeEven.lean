module

public import CFSG.RankThree.PartOne.KF4.F4ThreeData
public import CFSG.RankThree.PartOne.KF4.EvenCore

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open scoped Matrix


theorem planeLocalCoreOdd_F4_three_six_even (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 3).eval (Nat.card K : ℤ) ∨
      (p : ℤ) ∣ (exhaustionPhi 6).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup .F4 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have hout := F4_outer_commutator_odd K
  have hcore := localCoreTrivialOn_noninner_F4 K hp hp3
  have hstep : F4CoreStep K p L := f4_even_core_step K hf hK hp L
  rcases hpf with h3 | h6
  ·
    have h3' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 := by
      simpa [exhaustionPhi] using h3
    have hΦ3 : ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
        p).2 h3'
      simpa using this
    have hcm := canonicalRep_mem_monomialSubgroup L f4W3
    have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W3, hcm⟩ = f4W3 :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep f4W3)
    have hnW : ∀ u, weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W3, hcm⟩ • u =
        ((1 : ℤ) • weylMatrix f4W3) *ᵥ u := fun u => by
      rw [hπ, one_smul, weylMatrix_mulVec]
    have h := f4_three_main K hf hK 1 (Or.inl rfl) (fun h => absurd h (by decide)) hp hp3
      (f4Three_hΦ_one _ hΦ3) L _ hcm hnW hstep
    exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore
      h.2
  ·
    have h6' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
      simpa [exhaustionPhi] using h6
    have hΦ6 : ((Nat.card K : ℕ) : ZMod p) ^ 2 - ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
        p).2 h6'
      simpa using this
    have hq2 : 2 < 2 ^ f := by
      by_contra hle
      have hf1 : f = 1 := by
        by_contra hne
        have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hf1
      have hKc : (Nat.card K : ℤ) = 2 := by exact_mod_cast hK
      rw [hKc] at h6'
      have h3' : (p : ℤ) ∣ 3 := by simpa using h6'
      have := Int.le_of_dvd (by norm_num) h3'
      omega
    have hcm := canonicalRep_mem_monomialSubgroup L (f4Cox ^ 10)
    have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L (f4Cox ^ 10), hcm⟩ =
        f4Cox ^ 10 := weylQuotientHom_eq (mapsRootLines_canonicalRep (f4Cox ^ 10))
    have hnW : ∀ u, weylQuotientHom .F4 L
        ⟨canonicalRep (coxeterSystem .F4) L (f4Cox ^ 10), hcm⟩ • u =
          ((-1 : ℤ) • weylMatrix f4W3) *ᵥ u := fun u => by
      rw [hπ, ← weylMatrix_mulVec, weylMatrix_f4Cox_ten, neg_one_smul]
    have h := f4_three_main K hf hK (-1) (Or.inr rfl) (fun _ => hq2) hp hp3
      (f4Three_hΦ_neg _ hΦ6) L _ hcm hnW hstep
    exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore
      h.2

theorem oddEndpoint_F4_evenPhi3 :
    OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 3 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨rfl, hc2⟩ := hc
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_F4_three_six_even K hf hK hp hp3
      (Or.inl (by simpa [cycloVal, hK] using hc2)))).1

theorem oddEndpoint_F4_evenPhi6 :
    OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 6 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨rfl, hc2⟩ := hc
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_F4_three_six_even K hf hK hp hp3
      (Or.inr (by simpa [cycloVal, hK] using hc2)))).1

end CFSG.RankThree.PartOne.KF4
