module

public import CFSG.RankThree.PartOne.KE6.Phi3A2A2Case
public import CFSG.CharacterTheory.BrauerLinearThree.LocalRecognition

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_split)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

namespace NonsplitLayers

theorem dvd_card_SL_three_of_dvd_phiThree {K : Type} [Field K] [Finite K] {p : ℕ}
    (h : p ∣ Nat.card K ^ 2 + Nat.card K + 1) : p ∣ Nat.card (SL(3, K)) := by
  rw [CFSG.BrauerLinearThree.card_SL_three]
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have h1 : Nat.card K ^ 3 - 1 = (Nat.card K - 1) * (Nat.card K ^ 2 + Nat.card K + 1) := by
    have h3 : 1 ≤ Nat.card K ^ 3 := Nat.one_le_pow _ _ hq
    zify [hq, h3]
    ring
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
  rw [h1]
  exact Dvd.dvd.mul_left h _


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem phi3_A2_layer_card {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support13) :
    Nat.card ↥(rootSpan Tag.E6 Ω S ⊓ (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)) =
      Nat.card (SL(3, K)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hT : ∀ β ∈ parabolicRoots Tag.E6 support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support13 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨π, hπ⟩ := exists_positive_of_conj hL hLT hT
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π i) (π j)) (e * Fr c) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w
      (chainRoot13_mem_parabolicRoots hij).1
    refine ⟨e, he, fun c => ?_⟩
    rw [h, hπ]
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_permuting_of_theta hFrs
    (phi3ThetaConj Ω Fr w) (phi3ThetaConj_injective w) π hθ
  obtain ⟨-, ⟨H', hH'⟩, -, -, -, -, -, -⟩ := sl3_root_permuting_frobenius_fixed_split hℓ hf hK
    π Φ b (fun i j hij t => by rw [hΦt, hFr])
  set P := rootSpan Tag.E6 Ω S ⊓ (phi3Theta Ω Fr).eqLocus (MonoidHom.id _) with hPdef
  obtain ⟨e, -⟩ := exists_mulEquiv_fixSubgroup_gen (phi3Theta Ω Fr) (phi3ThetaConj Ω Fr w)
    (phi3ThetaConj_conj w) hQ hmaps Φ hΦ₀
  rw [Nat.card_congr e.toEquiv]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun Y : SL(3, K) => (⟨H' * Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y * H'⁻¹,
      (hH' _).2 ⟨Y, rfl⟩⟩ : ↥(fixSubgroup Φ))) ⟨fun Y Z h => ?_, fun X => ?_⟩)).symm
  · have h1 := congrArg Subtype.val h
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact specialLinearGroup_map_injective (algebraMap K Ω).injective h2
  · obtain ⟨Y, hY⟩ := (hH' X).1 X.2
    exact ⟨Y, Subtype.ext hY.symm⟩

theorem phi3_A2_layer_card₂ {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support56) :
    Nat.card ↥(rootSpan Tag.E6 Ω S ⊓ (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)) =
      Nat.card (SL(3, K)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω support56 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hT : ∀ β ∈ parabolicRoots Tag.E6 support56,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support56 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨π, hπ⟩ := exists_positive_of_conj₂ hL hLT hT
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 (π i) (π j)) (e * Fr c) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w
      (chainRoot56_mem_parabolicRoots hij).1
    refine ⟨e, he, fun c => ?_⟩
    rw [h, hπ]
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_permuting_of_theta₂ hFrs
    (phi3ThetaConj Ω Fr w) (phi3ThetaConj_injective w) π hθ
  obtain ⟨-, ⟨H', hH'⟩, -, -, -, -, -, -⟩ := sl3_root_permuting_frobenius_fixed_split hℓ hf hK
    π Φ b (fun i j hij t => by rw [hΦt, hFr])
  set P := rootSpan Tag.E6 Ω S ⊓ (phi3Theta Ω Fr).eqLocus (MonoidHom.id _) with hPdef
  obtain ⟨e, -⟩ := exists_mulEquiv_fixSubgroup_gen₂ (phi3Theta Ω Fr) (phi3ThetaConj Ω Fr w)
    (phi3ThetaConj_conj w) hQ hmaps Φ hΦ₀
  rw [Nat.card_congr e.toEquiv]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun Y : SL(3, K) => (⟨H' * Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y * H'⁻¹,
      (hH' _).2 ⟨Y, rfl⟩⟩ : ↥(fixSubgroup Φ))) ⟨fun Y Z h => ?_, fun X => ?_⟩)).symm
  · have h1 := congrArg Subtype.val h
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact specialLinearGroup_map_injective (algebraMap K Ω).injective h2
  · obtain ⟨Y, hY⟩ := (hH' X).1 X.2
    exact ⟨Y, Subtype.ext hY.symm⟩

end NonsplitLayers

end CFSG.RankThree.PartOne.KE6
