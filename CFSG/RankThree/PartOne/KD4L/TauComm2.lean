module

public import CFSG.RankThree.PartOne.KD4L.TauComm
public import CFSG.RankThree.PartOne.KD4L.TauCert

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.Monster.B.Classical.E6Adjoint
open scoped Pointwise

section PrimePow

variable {ℓ f : ℕ} [Fact ℓ.Prime]

theorem eq_two_of_pow_eq_two (hq : ℓ ^ f = 2) : ℓ = 2 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hd : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ hf0
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) Nat.prime_two).1 hd

end PrimePow

section CharTwo

variable {L : Type} [Field L] [CharP L 2]

theorem sum_pow_units_four {K : Type} [Field K] [Fintype K] [DecidableEq K] (ι : K →+* L)
    (hK : Fintype.card K = 4) (m : ℕ) :
    (∑ x : Kˣ, (ι (x : K)) ^ m) = if 3 ∣ m then 1 else 0 := by
  have h : ∑ x : Kˣ, (x : K) ^ m = if 3 ∣ m then -1 else 0 := by
    have := FiniteField.sum_pow_units K m
    rwa [hK] at this
  have h' := congrArg ι h
  rw [map_sum] at h'
  simp only [map_pow] at h'
  rw [h']
  split_ifs
  · rw [map_neg, map_one, CharTwo.neg_eq]
  · exact map_zero ι

omit [CharP L 2] in
theorem pairClassEnd_eq_sum (A₁ A₂ : Fin 78) (r : ℕ) :
    pairClassEnd (R := L) A₁ A₂ r = ∑ t : Fin 3 × Fin 3,
      if ((t.1 : ℕ) + 2 * (t.2 : ℕ)) % 3 = r then coeffEnd A₁ t.1 * coeffEnd A₂ t.2 else 0 := by
  classical
  rw [pairClassEnd, pairClass, ← List.sum_toFinset _ (nodup_pairList.filter _)]
  rw [show (pairList.filter fun t : Fin 3 × Fin 3 =>
      ((t.1 : ℕ) + 2 * (t.2 : ℕ)) % 3 == r).toFinset =
      Finset.univ.filter fun t : Fin 3 × Fin 3 => ((t.1 : ℕ) + 2 * (t.2 : ℕ)) % 3 = r from by
    ext t
    simp [mem_pairList]]
  rw [Finset.sum_filter]

theorem commute_pairClassEnd_of_expand {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (ι : K →+* L) (hK : Fintype.card K = 4) {X : Module.End L (RootModule Tag.E6 L)}
    (A₁ A₂ : Fin 78) (Y : L → Module.End L (RootModule Tag.E6 L))
    (hexp : ∀ a : L, Y a = ∑ t : Fin 3 × Fin 3, (a ^ (t.1 : ℕ) * ((a ^ 2) ^ (t.2 : ℕ))) •
      (coeffEnd (R := L) A₁ t.1 * coeffEnd A₂ t.2))
    (hterm : ∀ x : Kˣ, Commute X (Y (ι (x : K))))
    (r : ℕ) (hr : r < 3) : Commute X (pairClassEnd (R := L) A₁ A₂ r) := by
  classical
  set w : ℕ := (3 - r) % 3 with hw
  have key : (∑ x : Kˣ, ((ι (x : K)) ^ w) • Y (ι (x : K))) = pairClassEnd (R := L) A₁ A₂ r := by
    rw [pairClassEnd_eq_sum]
    simp_rw [hexp, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_smul]
    have hs : ∑ x : Kˣ, (ι (x : K)) ^ w * ((ι (x : K)) ^ (t.1 : ℕ) *
        (((ι (x : K)) ^ 2) ^ (t.2 : ℕ))) =
        ∑ x : Kˣ, (ι (x : K)) ^ (w + (t.1 : ℕ) + 2 * (t.2 : ℕ)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← pow_mul, ← pow_add, ← pow_add]
      ring_nf
    rw [hs, sum_pow_units_four ι hK]
    have hdiv : (3 ∣ w + (t.1 : ℕ) + 2 * (t.2 : ℕ)) ↔
        ((t.1 : ℕ) + 2 * (t.2 : ℕ)) % 3 = r := by
      rw [hw]
      interval_cases r <;> omega
    by_cases hc : ((t.1 : ℕ) + 2 * (t.2 : ℕ)) % 3 = r
    · rw [ite_eq_left (hdiv.2 hc), ite_eq_left hc, one_smul]
    · rw [ite_eq_right (mt hdiv.1 hc), ite_eq_right hc, zero_smul]
  rw [← key]
  exact Commute.sum_right _ _ _ fun x _ => (hterm x).smul_right _

theorem commute_pairClassEnd_of_terms {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (ι : K →+* L) (hK : Fintype.card K = 4) {X : Module.End L (RootModule Tag.E6 L)}
    (hterm : ∀ x : Kˣ, Commute X (xOp Tag.E6 L 4 (ι (x : K)) *
      xOp Tag.E6 L 2 ((ι (x : K)) ^ 2)))
    (r : ℕ) (hr : r < 3) : Commute X (pairClassEnd (R := L) 10 8 r) :=
  commute_pairClassEnd_of_expand ι hK 10 8 (fun a => xOp Tag.E6 L 4 a * xOp Tag.E6 L 2 (a ^ 2))
    (fun a => by
      rw [xOp_eq_lab (R := L) (4 : Fin Tag.E6.rank) a, xOp_eq_lab (R := L) (2 : Fin Tag.E6.rank)]
      exact pair_expand _ _ _ _ _ _) hterm r hr

theorem commute_pairClassEnd_neg_of_terms {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (ι : K →+* L) (hK : Fintype.card K = 4) {X : Module.End L (RootModule Tag.E6 L)}
    (hterm : ∀ x : Kˣ, Commute X (yOp Tag.E6 L 4 (ι (x : K)) *
      yOp Tag.E6 L 2 ((ι (x : K)) ^ 2)))
    (r : ℕ) (hr : r < 3) : Commute X (pairClassEnd (R := L) 20 16 r) :=
  commute_pairClassEnd_of_expand ι hK 20 16 (fun a => yOp Tag.E6 L 4 a * yOp Tag.E6 L 2 (a ^ 2))
    (fun a => by
      rw [yOp_eq_lab (R := L) (4 : Fin Tag.E6.rank) a, yOp_eq_lab (R := L) (2 : Fin Tag.E6.rank)]
      exact pair_expand _ _ _ _ _ _) hterm r hr

theorem commute_of_two_aux {X : Module.End L (RootModule Tag.E6 L)}
    (hP : ∀ r < 3, Commute X (pairClassEnd (R := L) 10 8 r))
    (hQ : ∀ r < 3, Commute X (pairClassEnd (R := L) 20 16 r))
    (hx1 : Commute X (xOp Tag.E6 L 1 1)) (hy1 : Commute X (yOp Tag.E6 L 1 1))
    (hx3 : Commute X (xOp Tag.E6 L 3 1)) (hy3 : Commute X (yOp Tag.E6 L 3 1))
    {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) (c : L) :
    Commute X (xOp Tag.E6 L j c) ∧ Commute X (yOp Tag.E6 L j c) := by
  have hlab : ∀ (A : ℕ) (hA : A < 78) (g : Module.End L (RootModule Tag.E6 L)),
      g = 1 + ad L (Finsupp.single (lab ⟨A, hA⟩) 1) + formTensor L (Finsupp.single (lab ⟨A, hA⟩) 1) →
        Commute X g → Commute X (ad L (Finsupp.single (lab ⟨A, hA⟩) 1) +
          formTensor L (Finsupp.single (lab ⟨A, hA⟩) 1)) := by
    intro A hA g hg hc
    have e : ad L (Finsupp.single (lab ⟨A, hA⟩) 1) + formTensor L (Finsupp.single (lab ⟨A, hA⟩) 1) =
        g - 1 := by rw [hg]; abel
    rw [e]
    exact hc.sub_right (Commute.one_right X)
  have hM₁ : Commute X (ad L (Finsupp.single (lab 7) 1) + formTensor L (Finsupp.single (lab 7) 1)) := by
    refine hlab 7 (by decide) (xOp Tag.E6 L 1 1) ?_ hx1
    have h := xOp_eq_lab (R := L) (1 : Fin Tag.E6.rank) 1
    simp only [one_smul, one_pow] at h
    exact h
  have hN₁ : Commute X (ad L (Finsupp.single (lab 14) 1) + formTensor L (Finsupp.single (lab 14) 1)) := by
    refine hlab 14 (by decide) (yOp Tag.E6 L 1 1) ?_ hy1
    have h := yOp_eq_lab (R := L) (1 : Fin Tag.E6.rank) 1
    simp only [one_smul, one_pow] at h
    exact h
  have hM₃ : Commute X (ad L (Finsupp.single (lab 9) 1) + formTensor L (Finsupp.single (lab 9) 1)) := by
    refine hlab 9 (by decide) (xOp Tag.E6 L 3 1) ?_ hx3
    have h := xOp_eq_lab (R := L) (3 : Fin Tag.E6.rank) 1
    simp only [one_smul, one_pow] at h
    exact h
  have hN₃ : Commute X (ad L (Finsupp.single (lab 18) 1) + formTensor L (Finsupp.single (lab 18) 1)) := by
    refine hlab 18 (by decide) (yOp Tag.E6 L 3 1) ?_ hy3
    have h := yOp_eq_lab (R := L) (3 : Fin Tag.E6.rank) 1
    simp only [one_smul, one_pow] at h
    exact h
  obtain ⟨hj0, hj5⟩ : j ≠ 0 ∧ j ≠ 5 := hj
  have hj0' : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
  have hj5' : (j : ℕ) ≠ 5 := fun h => hj5 (Fin.ext h)
  have hjlt : (j : ℕ) < 6 := j.2
  have hm : (j : ℕ) - 1 < 4 := by omega
  have hcomm := commute_of_tauCert tauLettersOK_two tauTargetsOK_two hP hQ hM₁ hN₁ hM₃ hN₃
    ((j : ℕ) - 1) hm c
  have hjeq : (⟨(j : ℕ) - 1 + 1, show (j : ℕ) - 1 + 1 < 6 by omega⟩ : Fin Tag.E6.rank) = j :=
    Fin.ext (by simp only; omega)
  rw [hjeq] at hcomm
  exact hcomm

end CharTwo

section Two

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

theorem card_orbitField_pair_of_two (hq : ℓ ^ f = 2) :
    Nat.card ((tauDatum L ℓ f hf).orbitField
      ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ))) = 4 := by
  have hO := orbit24_mem (L := L) (ℓ := ℓ) (f := f) hf
  obtain ⟨hc, -⟩ := pair_data hf rfl hO
  rw [(tauDatum L ℓ f hf).card_orbitField hO, hc]
  change (ℓ ^ f) ^ 2 = 4
  rw [hq]
  norm_num

theorem commute_pairClassEnd (hq : ℓ ^ f = 2) {X : Module.End L (RootModule Tag.E6 L)}
    (hX : X ∈ e6Commutant ((tauDatum L ℓ f hf).orbitGroup : Set (ModGL Tag.E6 L)))
    (r : ℕ) (hr : r < 3) : Commute X (pairClassEnd (R := L) 10 8 r) := by
  classical
  obtain rfl : ℓ = 2 := eq_two_of_pow_eq_two hq
  set D := tauDatum L 2 f hf with hD
  have hO := orbit24_mem (L := L) (ℓ := 2) (f := f) hf
  set K := D.orbitField ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ)) with hK
  have hKcard : Nat.card K = 4 := card_orbitField_pair_of_two hf hq
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  let _ : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hKcard]
  have hterm : ∀ x : Kˣ, Commute X (xOp Tag.E6 L 4 ((x : K) : L) *
      xOp Tag.E6 L 2 (((x : K) : L) ^ 2)) := by
    intro x
    have := hX _ (orbitX_mem_orbitGroup D hO (x : K))
    rwa [orbitX_pair (L := L) (ℓ := 2) hf, Units.val_mul, coe_xUnit, coe_xUnit, hq] at this
  exact commute_pairClassEnd_of_terms (Subfield.subtype K) hKc hterm r hr

theorem commute_pairClassEnd_neg (hq : ℓ ^ f = 2)
    {X : Module.End L (RootModule Tag.E6 L)}
    (hX : X ∈ e6Commutant ((tauDatum L ℓ f hf).orbitGroup : Set (ModGL Tag.E6 L)))
    (r : ℕ) (hr : r < 3) : Commute X (pairClassEnd (R := L) 20 16 r) := by
  classical
  obtain rfl : ℓ = 2 := eq_two_of_pow_eq_two hq
  set D := tauDatum L 2 f hf with hD
  have hO := orbit24_mem (L := L) (ℓ := 2) (f := f) hf
  set K := D.orbitField ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ)) with hK
  have hKcard : Nat.card K = 4 := card_orbitField_pair_of_two hf hq
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  let _ : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hKcard]
  have hterm : ∀ x : Kˣ, Commute X (yOp Tag.E6 L 4 ((x : K) : L) *
      yOp Tag.E6 L 2 (((x : K) : L) ^ 2)) := by
    intro x
    have := hX _ (orbitY_mem_orbitGroup D hO (x : K))
    rwa [orbitY_pair (L := L) (ℓ := 2) hf, Units.val_mul, coe_yUnit, coe_yUnit, hq] at this
  exact commute_pairClassEnd_neg_of_terms (Subfield.subtype K) hKc hterm r hr

theorem commute_of_two (hq : ℓ ^ f = 2) {X : Module.End L (RootModule Tag.E6 L)}
    (hX : X ∈ e6Commutant ((tauDatum L ℓ f hf).orbitGroup : Set (ModGL Tag.E6 L)))
    {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) (c : L) :
    Commute X (xOp Tag.E6 L j c) ∧ Commute X (yOp Tag.E6 L j c) := by
  classical
  obtain rfl : ℓ = 2 := eq_two_of_pow_eq_two hq
  set D := tauDatum L 2 f hf with hD
  have hsingle : ∀ {i : Fin Tag.E6.rank},
      ({Pi.single i 1} : Set (Fin Tag.E6.rank → ℤ)) ∈ D.orbits →
      Commute X (xOp Tag.E6 L i 1) ∧ Commute X (yOp Tag.E6 L i 1) := by
    intro i hO
    have h1 : GenFixedRootDatum.orbitCard ({Pi.single i 1} : Set (Fin Tag.E6.rank → ℤ)) = 1 :=
      Set.ncard_singleton _
    have hr := orbitRoot_single hf hO rfl
    have hx := hX _ (orbitX_mem_orbitGroup D hO 1)
    have hy := hX _ (orbitY_mem_orbitGroup D hO 1)
    rw [orbitX_eq_xUnit D h1 hr, coe_xUnit] at hx
    rw [orbitY_eq_yUnit D h1 hr, coe_yUnit] at hy
    exact ⟨by simpa using hx, by simpa using hy⟩
  obtain ⟨hx1, hy1⟩ := hsingle (orbit1_mem (L := L) (ℓ := 2) (f := f) hf)
  obtain ⟨hx3, hy3⟩ := hsingle (orbit3_mem (L := L) (ℓ := 2) (f := f) hf)
  exact commute_of_two_aux (fun r hr => commute_pairClassEnd hf hq hX r hr)
    (fun r hr => commute_pairClassEnd_neg hf hq hX r hr) hx1 hy1 hx3 hy3 hj c

theorem e6Commutant_tauLayer {X : Module.End L (RootModule Tag.E6 L)}
    (hX : X ∈ e6Commutant ((tauDatum L ℓ f hf).orbitGroup : Set (ModGL Tag.E6 L))) :
    X ∈ e6Commutant ((subsystemGroup Tag.E6 L d4Support : Subgroup (ModGL Tag.E6 L)) :
      Set (ModGL Tag.E6 L)) := by
  have hq2 : 2 ≤ ℓ ^ f := by
    have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
    calc 2 ≤ ℓ := hℓ
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right (by omega) hf
  refine mem_e6Commutant_subsystemGroup (fun j hj c => ?_) (fun j hj c => ?_)
  · by_cases hq : 3 ≤ ℓ ^ f
    · exact (commute_of_three_le hf hq hX hj c).1
    · exact (commute_of_two hf (by omega) hX hj c).1
  · by_cases hq : 3 ≤ ℓ ^ f
    · exact (commute_of_three_le hf hq hX hj c).2
    · exact (commute_of_two hf (by omega) hX hj c).2

end Two

end CFSG.RankThree.PartOne.KD4L
