module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryVec
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public section

namespace CFSG.StandardType.SympMinus

open Polynomial Matrix Multiplicative CFSG.StandardType.TorC CFSG.StandardType.SpJoin
open CFSG.RankThree.Classical (spEnd)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] {p m : ℕ}

@[expose] noncomputable def smuQuad (t : K) : K[X] := X ^ 2 + C t * X + 1

theorem smuQuad_monic (t : K) : (smuQuad t).Monic := by
  rw [smuQuad]
  monicity!

theorem smuQuad_natDegree (t : K) : (smuQuad t).natDegree = 2 := by
  rw [smuQuad]
  compute_degree!

theorem smuQuad_coeff_zero (t : K) : (smuQuad t).coeff 0 = 1 := by
  simp [smuQuad]

theorem smuQuad_ne_X_sub_one (t : K) : smuQuad t ≠ X - 1 := by
  intro h
  have h1 : (X - 1 : K[X]).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_sub_C (1 : K)
  have h2 := congrArg Polynomial.natDegree h
  rw [smuQuad_natDegree, h1] at h2
  norm_num at h2

theorem reciprocalPolynomial_smuQuad (t : K) : reciprocalPolynomial (smuQuad t) = smuQuad t := by
  rw [reciprocalPolynomial, smuQuad_coeff_zero t, inv_one, C_1, one_mul]
  ext n
  rw [Polynomial.coeff_reverse, smuQuad_natDegree]
  by_cases hn : n ≤ 2
  · rw [Polynomial.revAt_le hn]
    interval_cases n <;>
      simp [smuQuad, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_one, Polynomial.coeff_X]
  · have hlt : (smuQuad t).natDegree < n := by rw [smuQuad_natDegree]; omega
    rw [Polynomial.revAt_eq_self_of_lt (by omega : 2 < n),
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

theorem sq_add_smul_add_one_eq (Z : SpecialLinearGroup (Fin 2) K) (t : K) :
    (Z : Matrix (Fin 2) (Fin 2) K) ^ 2 + t • (Z : Matrix (Fin 2) (Fin 2) K) + 1 =
      ((Z : Matrix (Fin 2) (Fin 2) K).trace + t) • (Z : Matrix (Fin 2) (Fin 2) K) := by
  have h := add_inv_eq_trace_smul Z
  have hinv : (Z : Matrix (Fin 2) (Fin 2) K) * ((Z⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hCH : (Z : Matrix (Fin 2) (Fin 2) K) * (Z : Matrix (Fin 2) (Fin 2) K) + 1 =
      (Z : Matrix (Fin 2) (Fin 2) K).trace • (Z : Matrix (Fin 2) (Fin 2) K) := by
    calc (Z : Matrix (Fin 2) (Fin 2) K) * (Z : Matrix (Fin 2) (Fin 2) K) + 1
        = (Z : Matrix (Fin 2) (Fin 2) K) *
            ((Z : Matrix (Fin 2) (Fin 2) K) + ((Z⁻¹ : SpecialLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)) := by
          rw [Matrix.mul_add, hinv]
      _ = (Z : Matrix (Fin 2) (Fin 2) K) * ((Z : Matrix (Fin 2) (Fin 2) K).trace • 1) := by
          rw [h]
      _ = (Z : Matrix (Fin 2) (Fin 2) K).trace • (Z : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
  rw [pow_two, add_right_comm, hCH, add_smul]

theorem trace_inv_eq (Z : SpecialLinearGroup (Fin 2) K) :
    ((Z⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
      (Z : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp [add_comm]

theorem irreducible_smuQuad [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {c : Multiplicative (ZMod p)} (hc : c ≠ 1) :
    Irreducible (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Z : SpecialLinearGroup (Fin 2) K := ζ c with hZdef
  set t : K := (Z : Matrix (Fin 2) (Fin 2) K).trace with ht
  have hZ1 : Z ≠ 1 := fun h => hc (hζ (h.trans (map_one ζ).symm))
  have hZp : Z ^ p = 1 := by
    rw [hZdef, ← map_pow]
    have : c ^ p = 1 := by
      obtain ⟨z, rfl⟩ : ∃ z : ZMod p, ofAdd z = c := ⟨toAdd c, rfl⟩
      rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
    rw [this, map_one]
  have htr : t ≠ 0 := trace_ne_zero_of_pow_eq_one hZ1 (hp.odd_of_ne_two hp2) hZp
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcop : Nat.Coprime p (Nat.card K - 1) := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have h1 : p ∣ Nat.card K + 1 - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
    rw [h3] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hroot : ∀ r : K, r ^ 2 + t * r + 1 ≠ 0 := by
    intro r hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    have hdet : ((Z : Matrix (Fin 2) (Fin 2) K) - r • 1).det = 0 := by
      have hZdet : (Z : Matrix (Fin 2) (Fin 2) K).det = 1 := Z.2
      rw [Matrix.det_fin_two] at hZdet ⊢
      rw [ht, Matrix.trace_fin_two] at hr
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
        ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, smul_eq_mul, mul_one,
        mul_zero, sub_zero, Fin.one_eq_zero_iff, one_ne_zero]
      linear_combination hr + hZdet + (-((Z : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (Z : Matrix (Fin 2) (Fin 2) K) 1 1) * r) * h2
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hZv : (Z : Matrix (Fin 2) (Fin 2) K) *ᵥ v = r • v := by
      have h1 := hv
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
      exact sub_eq_zero.mp h1
    have hpowv : ∀ n : ℕ, ((Z : Matrix (Fin 2) (Fin 2) K) ^ n) *ᵥ v = r ^ n • v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hZv, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
    have hZpm : (Z : Matrix (Fin 2) (Fin 2) K) ^ p = 1 := by
      have := congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hZp
      simpa using this
    have hsp : r ^ p = 1 := by
      have h1 := hpowv p
      rw [hZpm, Matrix.one_mulVec] at h1
      have h2' : (r ^ p - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2').resolve_right hv0)
    have hsq : r ^ (Nat.card K - 1) = 1 := by
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one r hr0
    have hr1 : r = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hsp, hsq⟩
    subst hr1
    exact htr (by linear_combination hr - h2)
  have hne : smuQuad t ≠ 0 := (smuQuad_monic t).ne_zero
  rw [(smuQuad_monic t).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [smuQuad_natDegree]) (by rw [smuQuad_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def] at hr
  apply hroot r
  simpa [smuQuad] using hr

section Torus

variable (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
  (f₀ : Fin m → Multiplicative (ZMod p))

private theorem smuPoly_planeMat_add {m : ℕ} (A B : Fin m → Matrix (Fin 2) (Fin 2) K) :
    WitSpNs.planeMat A + WitSpNs.planeMat B = WitSpNs.planeMat (fun x => A x + B x) := by
  ext a b
  simp only [Matrix.add_apply, WitSpNs.planeMat_apply]
  split_ifs <;> simp

private theorem smuPoly_planeMat_smul {m : ℕ} (c : K)
    (A : Fin m → Matrix (Fin 2) (Fin 2) K) :
    c • WitSpNs.planeMat A = WitSpNs.planeMat (fun x => c • A x) := by
  ext a b
  simp only [Matrix.smul_apply, WitSpNs.planeMat_apply]
  split_ifs <;> simp

theorem aeval_smuQuad_spEnd_apply (t : K) (v : Fin m ⊕ Fin m → K) :
    aeval (spEnd (spPlaneTorus m ζ f₀)) (smuQuad t) v =
      WitSpNs.planeMat (fun x => (((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).trace + t) •
          ((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v := by
  set g : StatedSp m K := spPlaneTorus m ζ f₀ with hg
  let M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := (g : GL (Fin m ⊕ Fin m) K)
  let A : Fin m → Matrix (Fin 2) (Fin 2) K := fun x => (ζ (f₀ x) : Matrix (Fin 2) (Fin 2) K)
  have hM : M = WitSpNs.planeMat A := by
    dsimp only [M, A]
    exact coe_spPlaneTorus m ζ f₀
  have h_aeval : aeval (spEnd g) (smuQuad t) = (spEnd g) ^ 2 + t • (spEnd g) + 1 := by
    simp only [smuQuad, map_add, map_mul, map_one, map_pow, aeval_X, aeval_C, Algebra.smul_def]
  have h_apply : ∀ w, aeval (spEnd g) (smuQuad t) w = (M * M + t • M + 1) *ᵥ w := by
    intro w
    rw [h_aeval]
    show (spEnd g) ((spEnd g) w) + t • (spEnd g) w + w = (M * M + t • M + 1) *ᵥ w
    rw [CFSG.RankThree.Classical.spEnd_apply, CFSG.RankThree.Classical.spEnd_apply]
    dsimp only [M]
    rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [h_apply v, hM]
  congr 1
  rw [WitSpNs.planeMat_mul, smuPoly_planeMat_smul, ← WitSpNs.planeMat_one,
    smuPoly_planeMat_add, smuPoly_planeMat_add]
  congr 1
  funext x
  rw [← pow_two]
  dsimp only [A]
  exact sq_add_smul_add_one_eq (ζ (f₀ x)) t

variable {ζ f₀}

private theorem smuPoly_block_eq_zero [CharP K 2] {S : Finset (Fin m)}
    {c : Multiplicative (ZMod p)} (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) {x : Fin m}
    (hx : x ∈ S) :
    (((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace +
      ((ζ c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace) •
        ((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 0 := by
  have htr : ((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
      ((ζ c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
    rcases (hS x).mp hx with h | h
    · rw [h]
    · rw [h, map_inv]
      exact trace_inv_eq (ζ c)
  rw [htr, CharTwo.add_self_eq_zero, zero_smul]

theorem aeval_smuQuad_suppIn [CharP K 2] {S : Finset (Fin m)} {c : Multiplicative (ZMod p)}
    (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) {v : Fin m ⊕ Fin m → K} (hv : SmuSuppIn S v) :
    aeval (spEnd (spPlaneTorus m ζ f₀))
      (smuQuad ((ζ c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace) v = 0 := by
  rw [aeval_smuQuad_spEnd_apply]
  funext r
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [WitSpNs.planeMat_apply]
  by_cases hps : WitSpNs.plane r = WitSpNs.plane s
  · rw [if_pos hps]
    by_cases hx : WitSpNs.plane r ∈ S
    · have hx' : WitSpNs.plane s ∈ S := hps ▸ hx
      rw [smuPoly_block_eq_zero (ζ := ζ) hS hx']
      simp
    · rw [hv s (hps ▸ hx), mul_zero]
  · rw [if_neg hps, zero_mul]

theorem aeval_smuQuad_suppOff [CharP K 2] {S : Finset (Fin m)} {c : Multiplicative (ZMod p)}
    (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) (v : Fin m ⊕ Fin m → K) :
    SmuSuppOff S (aeval (spEnd (spPlaneTorus m ζ f₀))
      (smuQuad ((ζ c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace) v) := by
  intro r hr
  rw [aeval_smuQuad_spEnd_apply]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [WitSpNs.planeMat_apply]
  by_cases hps : WitSpNs.plane r = WitSpNs.plane s
  · have hr' : WitSpNs.plane s ∈ S := hps ▸ hr
    rw [if_pos hps, smuPoly_block_eq_zero (ζ := ζ) hS hr']
    simp
  · rw [if_neg hps, zero_mul]

end Torus

end CFSG.StandardType.SympMinus

end
