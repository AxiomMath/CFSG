module

public import CFSG.RankThree.PartTwo.Census.Spin.RootOp
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessOdd

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {R : RootData K N ι} {H : Subgroup R.G}
  {L : Subfield K}

theorem commutator_one_add_sandwich {A B : Matrix N N K} (hA : A * A = 0) (hB : B * B = 0)
    (hABA : A * B * A = 0) (a b : K) :
    (1 + a • A) * (1 + b • B) * (1 - a • A) * (1 - b • B) =
      1 + (a * b) • (A * B - B * A) + (a * b * b) • (B * A * B) := by
  have hABA' : A * (B * A) = 0 := by rw [← mul_assoc, hABA]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_sub, mul_assoc, hA, hB, hABA', smul_zero, mul_zero, zero_mul,
    smul_smul]
  module

theorem sandwich_product {A B : Matrix N N K} (hA : A * A = 0) (hB : B * B = 0)
    (hABA : A * B * A = 0) (a : K) :
    (1 + a • (A * B - B * A) + a • (B * A * B)) *
        (1 + (-a) • (A * B - B * A) + a • (B * A * B)) =
      1 + (2 * a) • (B * A * B) := by
  have hM : (A * B - B * A) * (A * B - B * A) = 0 := by
    have e : (A * B - B * A) * (A * B - B * A) =
        A * B * A * B - A * (B * B) * A - B * (A * A) * B + B * (A * B * A) := by noncomm_ring
    rw [e, hABA, hA, hB]
    simp
  have hMN : (A * B - B * A) * (B * A * B) = 0 := by
    have e : (A * B - B * A) * (B * A * B) = A * (B * B) * A * B - B * (A * B * A) * B := by
      noncomm_ring
    rw [e, hB, hABA]
    simp
  have hNM : (B * A * B) * (A * B - B * A) = 0 := by
    have e : (B * A * B) * (A * B - B * A) = B * (A * B * A) * B - B * A * (B * B) * A := by
      noncomm_ring
    rw [e, hB, hABA]
    simp
  have hN : (B * A * B) * (B * A * B) = 0 := by
    have e : (B * A * B) * (B * A * B) = B * A * (B * B) * A * B := by noncomm_ring
    rw [e, hB]
    simp
  generalize A * B - B * A = M at hM hMN hNM ⊢
  generalize B * A * B = P at hM hMN hNM hN ⊢
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hM, hMN, hNM, hN,
    smul_zero, add_zero]
  module

theorem RootOp.sandwich (h2 : (2 : K) ≠ 0) {A B : Matrix N N K} {wA wB : ι → ℤ}
    (hA : R.RootOp H L A wA) (hB : R.RootOp H L B wB) (hABA : A * B * A = 0) :
    R.RootOp H L (B * A * B) (wA + wB + wB) where
  sq := by
    have e : B * A * B * (B * A * B) = B * A * (B * B) * A * B := by noncomm_ring
    rw [e, hB.sq]
    simp
  mem u := by
    obtain ⟨g, hg⟩ := hA.mem (u / 2)
    obtain ⟨g₁, hg₁⟩ := hB.mem 1
    obtain ⟨g₂, hg₂⟩ := hB.mem (-1)
    refine ⟨⁅g, g₁⁆ * ⁅g, g₂⁆, ?_⟩
    rw [mat_mul, commutatorElement_def, commutatorElement_def, mat_mul, mat_mul, mat_mul,
      mat_mul, mat_mul, mat_mul, mat_inv_one_add_smul R hA.sq hg,
      mat_inv_one_add_smul R hB.sq hg₁, mat_inv_one_add_smul R hB.sq hg₂, hg, hg₁, hg₂,
      commutator_one_add_sandwich hA.sq hB.sq hABA, commutator_one_add_sandwich hA.sq hB.sq hABA]
    simp only [mul_one, mul_neg, neg_neg]
    rw [sandwich_product hA.sq hB.sq hABA, mul_div_cancel₀ u h2]
  torus s := by
    calc R.mat (R.torus s) * (B * A * B) = R.mat (R.torus s) * B * A * B := by
          simp only [mul_assoc]
      _ = ((∏ j, s j ^ wB j : Kˣ) : K) • (B * (R.mat (R.torus s) * A) * B) := by
          rw [hB.torus]
          simp only [smul_mul_assoc, mul_assoc]
      _ = ((∏ j, s j ^ wB j : Kˣ) : K) • (((∏ j, s j ^ wA j : Kˣ) : K) •
            (B * A * (R.mat (R.torus s) * B))) := by
          rw [hA.torus]
          simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = ((∏ j, s j ^ (wA + wB + wB) j : Kˣ) : K) • (B * A * B * R.mat (R.torus s)) := by
          rw [hB.torus, mul_smul_comm, smul_smul, smul_smul]
          congr 1
          · rw [← Units.val_mul, ← Units.val_mul, ← Finset.prod_mul_distrib,
              ← Finset.prod_mul_distrib]
            congr 1
            exact Finset.prod_congr rfl fun j _ => by
              rw [Pi.add_apply, Pi.add_apply, zpow_add, zpow_add]
              group
          · simp only [mul_assoc]
  memD u hu := by
    have h2L : (2 : K) ∈ L := by
      have := L.add_mem L.one_mem L.one_mem
      rwa [one_add_one_eq_two] at this
    obtain ⟨g, hgD, hg⟩ := hA.memD (u / 2) (L.div_mem hu h2L)
    obtain ⟨g₁, hgD₁, hg₁⟩ := hB.memD 1 L.one_mem
    obtain ⟨g₂, hgD₂, hg₂⟩ := hB.memD (-1) (L.neg_mem L.one_mem)
    refine ⟨⁅g, g₁⁆ * ⁅g, g₂⁆, Subgroup.mul_mem _
      (Subgroup.commutator_mem_commutator (commutator_le_self H hgD)
        (commutator_le_self H hgD₁))
      (Subgroup.commutator_mem_commutator (commutator_le_self H hgD)
        (commutator_le_self H hgD₂)), ?_⟩
    rw [mat_mul, commutatorElement_def, commutatorElement_def, mat_mul, mat_mul, mat_mul,
      mat_mul, mat_mul, mat_mul, mat_inv_one_add_smul R hA.sq hg,
      mat_inv_one_add_smul R hB.sq hg₁, mat_inv_one_add_smul R hB.sq hg₂, hg, hg₁, hg₂,
      commutator_one_add_sandwich hA.sq hB.sq hABA, commutator_one_add_sandwich hA.sq hB.sq hABA]
    simp only [mul_one, mul_neg, neg_neg]
    rw [sandwich_product hA.sq hB.sq hABA, mul_div_cancel₀ u h2]

theorem rootOp_witness_h {σ : K →+* K} {F : R.G →* R.G} (hR : R.RootsInCommutator σ F)
    (h2 : (2 : K) ≠ 0) {p f : ℕ} [CharP K p] (hcard : Nat.card (fixedField σ) = p ^ f)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {X Y : κ → Matrix N N K} {w wY : κ → ι → ℤ}
    (hX : ∀ a, R.RootOp (fixedSubgroup F) (fixedField σ) (X a) (w a))
    (hY : ∀ a, R.RootOp (fixedSubgroup F) (fixedField σ) (Y a) (wY a))
    (hpair : ∀ a, SqZeroPair (X a) (Y a)) (hne : ∀ a, X a ≠ 0)
    (hXX : ∀ a b, a ≠ b → Commute (X a) (X b)) (hXY : ∀ a b, a ≠ b → Commute (X b) (Y a))
    (z : ι) (hz : ∀ a, Even (w a z)) (j₀ : ι) (hj₀ : Odd (R.CM z j₀)) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) p (f * Fintype.card κ) := by
  have hm1 : ((-1 : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_neg, Units.val_one]
    exact (fixedField σ).neg_mem (fixedField σ).one_mem
  have htD : R.torus (Pi.mulSingle z (-1)) ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
    refine torus_mem_commutator_of R hR fun j => ?_
    by_cases hj : j = z
    · subst hj
      rw [Pi.mulSingle_eq_same]
      exact hm1
    · rw [Pi.mulSingle_eq_of_ne hj, Units.val_one]
      exact (fixedField σ).one_mem
  have hneg1 : (-1 : Kˣ) ≠ 1 := fun h => h2 (by
    have h3 := congrArg (fun v : Kˣ => (v : K)) h
    simp only [Units.val_neg, Units.val_one] at h3
    rw [← one_add_one_eq_two]
    nth_rewrite 1 [← h3]
    exact neg_add_cancel 1)
  have hprod : ∀ v : ι → ℤ, (∏ j, (Pi.mulSingle z (-1 : Kˣ)) j ^ v j) = (-1 : Kˣ) ^ v z :=
    fun v => by
      rw [Finset.prod_eq_single z (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
        (fun h => absurd (Finset.mem_univ _) h), Pi.mulSingle_eq_same]
  refine R.rootOp_witness hcard hX hY hpair hne hXX hXY (Pi.mulSingle z (-1)) ?_ htD
    (fun a => by rw [hprod, (hz a).neg_one_zpow]) j₀ ?_ (hR j₀ 1 (fixedField σ).one_mem).1
  · rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]
  · rw [hprod, hj₀.neg_one_zpow]
    exact hneg1

end RootData

end CFSG.RankThree.PartTwo.Census.Spin
