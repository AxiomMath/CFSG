module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HTup
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HTits

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenF4QPlus CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section Qv

variable {Ω : Type} [Field Ω] [CharP Ω 2] {ζ : Ωˣ}

theorem single_mem_survivingRoots (hζ : orderOf ζ = 3) {i : Fin TwistTag.D4.tag.rank}
    (hi : i = 1 ∨ i = 2) :
    (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ survivingRoots (tup ζ gT) ∧
      (-Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ survivingRoots (tup ζ gT) := by
  have hζ3 := pow_three_of_orderOf hζ
  have hs : ∀ j : Fin TwistTag.D4.tag.rank, (j = 1 ∨ j = 2) →
      (∑ k, (((Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) k : ℤ) : ZMod 3) * gT k) = 0 ∧
      (∑ k, (((-Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) k : ℤ) : ZMod 3) * gT k) = 0 := by
    decide +revert
  obtain ⟨h1, h2⟩ := hs i hi
  refine ⟨⟨IsRoot.basis i, ?_⟩, ⟨IsRoot.neg (IsRoot.basis i), ?_⟩⟩
  · rw [rootChar_tup hζ3, h1, ZMod.val_zero, pow_zero]
  · rw [rootChar_tup hζ3, h2, ZMod.val_zero, pow_zero]

theorem weylElt_mem_Qv (hζ : orderOf ζ = 3) {i : Fin TwistTag.D4.tag.rank}
    (hi : i = 1 ∨ i = 2) : weylElt TwistTag.D4.tag Ω i 1 ∈ d4A2Qv Ω vT := by
  obtain ⟨h1, h2⟩ := single_mem_survivingRoots (ζ := ζ) hζ hi
  rw [d4A2Qv_eq_rootSpan]
  have hx : xUnit TwistTag.D4.tag Ω i 1 ∈
      rootSpan Tag.D4 Ω ((fun α => vT • α) '' d4A2Sigma) := by
    refine rootSpan_mono ?_ (xUnit_mem_rootSpan_single i 1)
    rw [survivingRoots_tup_gT hζ]
    exact Set.singleton_subset_iff.2 h1
  have hy : yUnit TwistTag.D4.tag Ω i (-(((1 : Ωˣ)⁻¹ : Ωˣ) : Ω)) ∈
      rootSpan Tag.D4 Ω ((fun α => vT • α) '' d4A2Sigma) := by
    refine rootSpan_mono ?_ (yUnit_mem_rootSpan_neg_single i _)
    rw [survivingRoots_tup_gT hζ]
    exact Set.singleton_subset_iff.2 h2
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem hx hy) hx

theorem nwT_mem_Qv (hζ : orderOf ζ = 3) : nw Ω wT ∈ d4A2Qv Ω vT := by
  have h1 := weylElt_mem_Qv (Ω := Ω) hζ (i := 1) (Or.inl rfl)
  have h2 := weylElt_mem_Qv (Ω := Ω) hζ (i := 2) (Or.inr rfl)
  have : nw Ω wT = weylElt TwistTag.D4.tag Ω 1 1 * weylElt TwistTag.D4.tag Ω 2 1 := by
    simp [nw, wT]
  rw [this]
  exact mul_mem h1 h2

theorem d4A2TorusElt_pow_eq (hζ3 : ζ ^ 3 = 1) (a b : ZMod 3) :
    d4A2TorusElt (ζ ^ a.val) (ζ ^ b.val) = rootDiagUnit TwistTag.D4.tag (tup ζ (fun j =>
      a * ((Tag.D4.cartan 0 j : ℤ) : ZMod 3) + b * ((Tag.D4.cartan 2 j : ℤ) : ZMod 3))) := by
  unfold d4A2TorusElt
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, tup]
  rw [pow_val_zpow hζ3, pow_val_zpow hζ3, pow_val_add hζ3]

theorem cE_mem_Qv (hζ : orderOf ζ = 3) :
    rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈ d4A2Qv Ω vT := by
  have hζ3 := pow_three_of_orderOf hζ
  have hs : d4A2TorusElt (ζ ^ (2 : ZMod 3).val) (ζ ^ (1 : ZMod 3).val) =
      rootDiagUnit TwistTag.D4.tag (tup ζ ![0, 2, 0, 2]) := by
    rw [d4A2TorusElt_pow_eq hζ3]
    congr 2
    funext j
    fin_cases j <;> decide
  have hsT : d4A2TorusElt (ζ ^ (2 : ZMod 3).val) (ζ ^ (1 : ZMod 3).val) ∈
      subsystemTorus Tag.D4 Ω d4SuppA2 :=
    mem_subsystemTorus_d4A2.2 ⟨_, _, rfl⟩
  have hnv : canonicalRep (coxeterSystem Tag.D4) Ω vT = nw Ω [0, 2, 1] :=
    (nw_eq_canonicalRep [0, 2, 1]).symm
  refine Subgroup.mem_map.2 ⟨_, subsystemTorus_le_subsystemGroup hsT, ?_⟩
  show canonicalRep (coxeterSystem Tag.D4) Ω vT *
    d4A2TorusElt (ζ ^ (2 : ZMod 3).val) (ζ ^ (1 : ZMod 3).val) *
      (canonicalRep (coxeterSystem Tag.D4) Ω vT)⁻¹ = _
  have h := nw_conj_rootDiagUnit (Ω := Ω) hζ3 [0, 2, 1] (![0, 2, 0, 2] : Exp3)
  have hw : wordExp [0, 2, 1] (![0, 2, 0, 2] : Exp3) = gT := by decide
  rw [hw] at h
  rw [hnv, hs]
  exact h

theorem Qv_le_and_derived [IsAlgClosed Ω] (hζ : orderOf ζ = 3) :
    d4A2Qv Ω vT ≤ toralCentralizer TwistTag.D4.tag Ω (tup ζ gT) ∧
      ⁅toralCentralizer TwistTag.D4.tag Ω (tup ζ gT),
        toralCentralizer TwistTag.D4.tag Ω (tup ζ gT)⁆ = d4A2Qv Ω vT := by
  have hpK : ringChar Ω ≠ 3 := by
    rw [ringChar.eq Ω 2]
    decide
  obtain ⟨-, -, hQM, -, -, -, hMder, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω 3 Nat.prime_three (by decide) hpK
      (tup ζ gT) (orderOf_rootDiagUnit_tup_gT hζ) vT (survivingRoots_tup_gT hζ).symm
  exact ⟨hQM, hMder⟩

end Qv

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
