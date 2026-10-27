module

public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite
public import CFSG.Quasithin.Vol2.Ch11SecOE7C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

include hJ hf hcard hfixed in
theorem rootU_sup_conjSub_eq_top {x : ProjectiveSpecialUnitaryMatrixGroup J}
    (hx : A1b.conjSub x (rootU J hJ) ≠ rootU J hJ) :
    rootU J hJ ⊔ A1b.conjSub x (rootU J hJ) = ⊤ := by
  obtain ⟨-, -, -, -, -, rho, -, -, hΩ, -, hstab, -, hnormal, -, hUT, -, -, -, -, hUcard, hreg,
    -⟩ := unitary_three_point_structure J f hf hcard hfixed hJ
  set U := rootU J hJ with hUdef
  set B := unitaryCoordinateStabilizer J 0 with hBdef
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide) with hαdef
  have hmemB : ∀ g, g ∈ B ↔ rho g α = α := fun g => by
    rw [← hstab, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  have hUB : U ≤ B := hUT ▸ le_sup_left
  have hBN : B ≤ Subgroup.normalizer (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hnormal
  have hconjB : ∀ b ∈ B, A1b.conjSub b U = U := fun b hb =>
    A1b.conjSub_eq_iff_mem_normalizer.mpr (hBN hb)
  have hxα : rho x α ≠ α := fun h => hx (hconjB x ((hmemB x).mpr h))
  have hrho : ∀ (g h : ProjectiveSpecialUnitaryMatrixGroup J) (p : unitaryIsotropicPoints J),
      rho (g * h) p = rho g (rho h p) := fun g h p => by
    rw [map_mul, Equiv.Perm.mul_apply]
  set H := U ⊔ A1b.conjSub x U with hH
  have hUH : U ≤ H := le_sup_left
  have hU'H : A1b.conjSub x U ≤ H := le_sup_right
  have hreg' : ∀ b c : unitaryIsotropicPoints J, b ≠ rho x α → c ≠ rho x α →
      ∃ u ∈ A1b.conjSub x U, rho u b = c := by
    intro b c hb hc
    have hinv : ∀ p, rho x (rho x⁻¹ p) = p := fun p => by
      rw [← hrho, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
    have hb' : rho x⁻¹ b ≠ α := fun h => hb (by rw [← h, hinv])
    have hc' : rho x⁻¹ c ≠ α := fun h => hc (by rw [← h, hinv])
    obtain ⟨⟨u, hu⟩, hu1, -⟩ := hreg (rho x⁻¹ b) (rho x⁻¹ c) hb' hc'
    refine ⟨x * u * x⁻¹, ?_, ?_⟩
    · rw [A1b.mem_conjSub_iff, show x⁻¹ * (x * u * x⁻¹) * x = u by group]
      exact hu
    · rw [hrho, hrho, hu1, hinv]
  have htrans : ∀ p : unitaryIsotropicPoints J, ∃ h ∈ H, rho h α = p := by
    intro p
    by_cases hp : p = rho x α
    · obtain ⟨w, hw1, hw2⟩ : ∃ w : unitaryIsotropicPoints J, w ≠ α ∧ w ≠ rho x α := by
        by_contra hcon
        push Not at hcon
        have hsurj : Function.Surjective
            (fun b : Bool => if b then α else rho x α) := fun w => by
          by_cases hw : w = α
          · exact ⟨true, by simp [hw]⟩
          · exact ⟨false, by simp [hcon w hw]⟩
        have h1 := Nat.card_le_card_of_surjective _ hsurj
        have hb : Nat.card Bool = 2 := by simp
        rw [hb, hΩ] at h1
        have h2 : 2 ≤ (2 ^ f) ^ 3 := by
          calc 2 ≤ 2 ^ f := by
                calc 2 = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
        omega
      obtain ⟨u', hu', hu'1⟩ := hreg' α w (Ne.symm hxα) hw2
      obtain ⟨⟨u, hu⟩, hu1, -⟩ := hreg w p hw1 (hp ▸ Ne.symm (Ne.symm hxα))
      exact ⟨u * u', H.mul_mem (hUH hu) (hU'H hu'), by rw [hrho, hu'1, hu1]⟩
    · obtain ⟨u', hu', hu'1⟩ := hreg' α p (Ne.symm hxα) hp
      exact ⟨u', hU'H hu', hu'1⟩
  have hconj : ∀ g, A1b.conjSub g U ≤ H := by
    intro g
    obtain ⟨h, hh, hhg⟩ := htrans (rho g α)
    have hb : h⁻¹ * g ∈ B := by
      rw [hmemB, hrho, ← hhg, ← hrho, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
    have hg : g = h * (h⁻¹ * g) := by group
    rw [hg, A1b.conjSub_mul, hconjB _ hb]
    rintro _ ⟨u, hu, rfl⟩
    exact H.mul_mem (H.mul_mem hh (hUH hu)) (H.inv_mem hh)
  have hq : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := CFSG.UnitaryThreeRecognition.Model.isSimpleGroup_psu J (2 ^ f) hcard hfixed hq
  have hN : Subgroup.normalClosure (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ H := by
    refine Subgroup.closure_le H |>.mpr fun y hy => ?_
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hay
    exact hconj c ⟨a, ha, rfl⟩
  have hU1 : U ≠ ⊥ := by
    intro h
    have h1 : Nat.card U = 1 := by rw [h, Subgroup.card_bot]
    rw [hUcard] at h1
    have : 1 < (2 ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have : (Subgroup.normalClosure (U : Set (ProjectiveSpecialUnitaryMatrixGroup J))).Normal :=
    Subgroup.normalClosure_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure (U : Set (ProjectiveSpecialUnitaryMatrixGroup J))) with h | h
  · exact absurd (le_bot_iff.mp (h ▸ Subgroup.subset_normalClosure)) hU1
  · exact eq_top_iff.mpr (h ▸ hN)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
