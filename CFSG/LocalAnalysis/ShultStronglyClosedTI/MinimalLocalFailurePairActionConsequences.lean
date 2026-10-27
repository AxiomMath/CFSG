module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionQuotient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSimple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G]

theorem minimalLocalFailurePairAction_normalCore_eq_bot [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
    H.normalCore = ⊥ := by
  rcases minimalLocalFailure_normal_eq_bot_or_top h H.normalCore with hbot | htop
  · exact hbot
  · exact False.elim (h.local_datum.proper (top_le_iff.mp (htop ▸ H.normalCore_le)))

theorem minimalLocalFailurePairAction_normal_pair_subgroup_eq_bot [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (hdoubly : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    (W : Subgroup G) (hWB : W ≤ pairPointStabilizer H beta)
    (hWnormal : (W.subgroupOf H).Normal) : W = ⊥ := by
  have hWH : W ≤ H := hWB.trans (pairPointStabilizer_le_point H beta)
  have hHN : H ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mp hWnormal
  have hfix : ∀ w ∈ W, ∀ gamma : rightCosetSpace H,
      rightCosetTranslate H gamma w = gamma := by
    intro w hw gamma
    by_cases hgamma : gamma = rightCosetMk H 1
    · rw [hgamma]
      exact (mem_rightCosetStabilizer_iff H _ w).mp (hWB hw).1
    · obtain ⟨a, habase, hbgamma⟩ := hdoubly (rightCosetMk H 1) beta
        (rightCosetMk H 1) gamma (Ne.symm hbeta) (Ne.symm hgamma)
      have haH : a ∈ H := by
        rw [← rightCosetStabilizer_base H]
        exact (mem_rightCosetStabilizer_iff H _ a).mpr habase
      have hconj : a * w * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hHN haH) w).mp hw
      have hbetafix : rightCosetTranslate H beta (a * w * a⁻¹) = beta :=
        (mem_rightCosetStabilizer_iff H beta _).mp (hWB hconj).2
      rw [← hbgamma]
      calc
        rightCosetTranslate H (rightCosetTranslate H beta a) w =
            rightCosetTranslate H beta (a * w) := rightCosetTranslate_mul H beta a w
        _ = rightCosetTranslate H
            (rightCosetTranslate H beta (a * w * a⁻¹)) a := by
          rw [rightCosetTranslate_mul]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
        _ = rightCosetTranslate H beta a := by rw [hbetafix]
  have hcore : W ≤ H.normalCore := by
    intro w hw g
    have hmem : w ∈ rightConjugate H g := by
      rw [← rightCosetStabilizer_mk H g]
      exact (mem_rightCosetStabilizer_iff H _ w).mpr (hfix w hw _)
    exact (mem_right_conjugate_iff H g w).mp hmem
  rw [minimalLocalFailurePairAction_normalCore_eq_bot h] at hcore
  exact le_antisymm hcore bot_le

theorem minimalLocalFailurePairAction_classCommutators_eq_bot_of_doubly_transitive
    [Finite G] {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (hdoubly : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    (hWJ : minimalLocalFailureProperPairClassCommutators H z ≤ pairOddCore H beta) :
    minimalLocalFailureProperPairClassCommutators H z = ⊥ := by
  apply minimalLocalFailurePairAction_normal_pair_subgroup_eq_bot h hbeta hdoubly
    (minimalLocalFailureProperPairClassCommutators H z)
    (hWJ.trans (Subgroup.map_subtype_le _))
  exact minimalLocalFailureProperPairClassCommutators_normal_in_point H
    h.local_datum.distinguished_mem

theorem minimalLocalFailurePairActionPointHull_le_properPairHull [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    minimalLocalFailurePairActionPointHull H z ≤ minimalLocalFailureProperPairHull H z beta t :=
  (Subgroup.closure_le _).mpr fun _ ha =>
    (minimalLocalFailureProperPair_class_subset h.local_datum h.central_sylow hbeta ht ha).2

theorem minimalLocalFailurePairActionPointHull_inf_pair_eq_bot [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hQ : IsElemAbelian 2 (minimalLocalFailurePairActionPointHull H z)) :
    minimalLocalFailurePairActionPointHull H z ⊓ pairPointStabilizer H beta = ⊥ := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let M := H.subgroupOf K
  let tK : K := ⟨t, minimalLocalFailureProperPair_flip_mem H z beta t⟩
  let D := M ⊓ M.map (MulAut.conj tK⁻¹).toMonoidHom
  have htM : tK ∉ M := by
    change t ∉ H
    exact pair_flip_not_mem_point hbeta ht
  have hDodd : Odd (Nat.card D) :=
    (minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper).2.2
      tK htM
  have hQK := minimalLocalFailurePairActionPointHull_le_properPairHull h hbeta ht
  have hQH := minimalLocalFailurePairActionPointHull_le_point H h.local_datum.distinguished_mem
  have hbetaeq : beta = rightCosetMk H t := by
    simpa only [rightCosetTranslate_mk, one_mul] using ht.2.symm
  apply le_antisymm _ bot_le
  intro a ha
  let aK : K := ⟨a, hQK ha.1⟩
  have haM : aK ∈ M := hQH ha.1
  have haConjH : t * a * t⁻¹ ∈ H := by
    have haStab := ha.2.2
    rw [hbetaeq, rightCosetStabilizer_mk] at haStab
    exact (mem_right_conjugate_iff H t a).mp haStab
  have haD : aK ∈ D := by
    refine ⟨haM, Subgroup.mem_map.mpr ⟨tK * aK * tK⁻¹, haConjH, ?_⟩⟩
    change tK⁻¹ * (tK * aK * tK⁻¹) * tK⁻¹⁻¹ = aK
    group
  have hsquare : (⟨aK, haD⟩ : D) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hQ.2 a ha.1
  exact Subgroup.mem_bot.mpr (congrArg (fun x : D => ((x : K) : G))
    (square_one_eq_one_of_odd_card hDodd hsquare))

theorem minimalLocalFailurePairAction_triple_eq_pair_centralizer [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hQ : IsElemAbelian 2 (minimalLocalFailurePairActionPointHull H z)) :
    triplePointStabilizer H z beta =
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) := by
  have hdisjoint := minimalLocalFailurePairActionPointHull_inf_pair_eq_bot h hbeta ht hproper hQ
  have hznorm := triple_stabilizer_normalized_by_distinguished h.local_datum beta
  apply le_antisymm _ (pair_z_centralizer_le_triple H z beta)
  intro e he
  refine ⟨he.1, ?_⟩
  have heH : e ∈ H := pairPointStabilizer_le_point H beta he.1
  let c := z⁻¹ * e⁻¹ * z * e
  let Q := minimalLocalFailurePairActionPointHull H z
  have hcQ : c ∈ Q := by
    have hzQ : z ∈ Q := Subgroup.subset_closure ⟨1, by simp⟩
    have hzeQ : e⁻¹ * z * e ∈ Q := Subgroup.subset_closure ⟨⟨e, heH⟩, rfl⟩
    simpa only [c, mul_assoc] using Q.mul_mem (Q.inv_mem hzQ) hzeQ
  have hcE : c ∈ triplePointStabilizer H z beta := by
    have hconj := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (triplePointStabilizer H z beta : Set G)).inv_mem hznorm) e⁻¹).mp
      ((triplePointStabilizer H z beta).inv_mem he)
    simpa only [inv_inv, c] using (triplePointStabilizer H z beta).mul_mem hconj he
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hdisjoint ▸ (show c ∈
    Q ⊓ pairPointStabilizer H beta from ⟨hcQ, hcE.1⟩))
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hh : (e * z)⁻¹ * (z * e) = 1 := by
    simpa only [c, mul_inv_rev, mul_assoc] using hc1
  exact inv_mul_eq_one.mp hh

end CFSG.ShultStronglyClosedTI
