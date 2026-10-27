module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix
open CFSG.RankThree.GF2n.Stroth80

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

private abbrev s16t3_ce_quot (L : Subgroup (MulAut W)) : Type _ :=
  W ⧸ modFix L (⊤ : Subgroup W)

private noncomputable def s16t3_ce_range (L : Subgroup (MulAut W)) :
    Subgroup (MulAut (s16t3_ce_quot L)) :=
  (MulDistribMulAction.toMulAut ↥L (s16t3_ce_quot L)).range

private theorem s16t3_ce_realizes_quotient {D : FFModel} {U : Subgroup W}
    (h : D.Realizes L U (fixV L)) :
    D.Realizes (s16t3_ce_range L)
      (U.map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) ⊥ := by
  let ρ := QuotientGroup.mk' (modFix L (⊤ : Subgroup W))
  let θ : ↥L →* ↥(s16t3_ce_range L) :=
    (MulDistribMulAction.toMulAut ↥L (s16t3_ce_quot L)).rangeRestrict
  have hker : ρ.ker ≤ fixV L := by
    rw [QuotientGroup.ker_mk']
    exact (CFSG.Quasithin.SmithD391.modFix_top_eq L).le
  have hR := s16k_realizes_map h ρ hker θ (MonoidHom.rangeRestrict_surjective _)
    (fun _ _ => rfl)
  have hbot : (fixV L).map ρ = ⊥ := by
    rw [← CFSG.Quasithin.SmithD391.modFix_top_eq L]
    exact (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge
  rwa [hbot] at hR

private theorem s16t3_ce_quotient_binaryNaturalSL {n a : ℕ} {U : Subgroup W}
    (h : BinaryNaturalSL L U (fixV L) n a) :
    BinaryNaturalSL (s16t3_ce_range L)
      (U.map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) ⊥ n a := by
  obtain ⟨K, hK, hKf, hK2, hR⟩ := h
  exact ⟨K, hK, hKf, hK2, s16t3_ce_realizes_quotient hR⟩

private theorem s16t3_ce_quotient_natSpn {n a : ℕ} {U : Subgroup W}
    (h : NatSpn L U (fixV L) n a) :
    NatSpn (s16t3_ce_range L)
      (U.map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) ⊥ n a := by
  obtain ⟨he, K, hK, hKf, hK2, hR⟩ := h
  exact ⟨he, K, hK, hKf, hK2, s16t3_ce_realizes_quotient hR⟩

private theorem s16t3_ce_quotient_natOmegaPlus {n a : ℕ} {U : Subgroup W}
    (h : NatOmegaPlus L U (fixV L) n a) :
    NatOmegaPlus (s16t3_ce_range L)
      (U.map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) ⊥ n a := by
  obtain ⟨he, K, hK, hKf, hK2, hR⟩ := h
  exact ⟨he, K, hK, hKf, hK2, s16t3_ce_realizes_quotient hR⟩

private theorem s16t3_ce_quotient_natOmegaMinus {n a : ℕ} {U : Subgroup W}
    (h : NatOmegaMinus L U (fixV L) n a) :
    NatOmegaMinus (s16t3_ce_range L)
      (U.map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) ⊥ n a := by
  obtain ⟨he, K, hK, hKf, b, c, hK2, hirr, hR⟩ := h
  exact ⟨he, K, hK, hKf, b, c, hK2, hirr, s16t3_ce_realizes_quotient hR⟩

private theorem s16t3_ce_quotient_alternatingNatural {n : ℕ} {U : Subgroup W}
    (h : AlternatingNatural L U (fixV L) n) :
    AlternatingNatural (s16t3_ce_range L)
      (U.map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) ⊥ n :=
  s16t3_ce_realizes_quotient h

private theorem s16t3_ce_abs_two_cases {F : Type} [Field F] (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · refine Or.inr ?_
    have hu : Nat.card Fˣ = 1 := by
      have h := Nat.card_units (α := F)
      omega
    haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc) 1)

private theorem s16t3_ce_abs_comm_id {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (hF : Nat.card F = 2) (i0 : ι) {X : Subgroup (GL ι F)} (hX : AddCommutantScalar X)
    (g : (ι → F) ≃+ (ι → F))
    (hg : ∀ γ ∈ X, ∀ v : ι → F,
      g ((γ : Matrix ι ι F) *ᵥ v) = (γ : Matrix ι ι F) *ᵥ g v) (v : ι → F) : g v = v := by
  obtain ⟨c, hc⟩ := hX g.toAddMonoidHom hg
  rcases s16t3_ce_abs_two_cases hF c with rfl | rfl
  · exfalso
    have h0 : g (Pi.single i0 1) = g 0 := by
      rw [map_zero]
      exact (hc _).trans (zero_smul _ _)
    have h1 := congrFun (g.injective h0) i0
    simp at h1
  · exact (hc v).trans (one_smul _ _)

private theorem s16t3_ce_endUnits_omegaMinus {H : Subgroup (MulAut W)} {I : Subgroup W} {n : ℕ}
    (hn : 4 ≤ n) (h : NatOmegaMinus H I ⊥ n 1) : Z391.EndUnitsTrivial H I := by
  obtain ⟨-, F, hF, hFf, b, c, hF2, hirr, hreal⟩ := h
  letI := hF
  haveI : Finite F := hFf
  have hF2' : Nat.card F = 2 := by simpa using hF2
  exact s15k_abs_endUnits_of_comm
    (fun g hg v => s16t3_ce_abs_comm_id hF2' (Sum.inr (Sum.inr 0))
      (addCommutantScalar_statedOmegaMinus (m := n / 2) (by omega) hirr) g hg v) hreal

private theorem s16t3_ce_endUnitsTrivial_range (hq : CFSG.Open.IsQuasisimple ↥L)
    {I : Subgroup W} (hnat : SumOfNatShape L I (fixV L) 1) :
    Z391.EndUnitsTrivial (s16t3_ce_range L)
      (I.map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) := by
  obtain ⟨n, hcases⟩ := hnat
  rcases hcases with ⟨hSL, hsum⟩ | ⟨hSp, hsum⟩ | ⟨hOP, hsum⟩ | ⟨hOM, hsum⟩ | ⟨hAlt, hsum⟩
  · obtain hN := s16t3_sumOfNat_one hsum
    exact s16c167_endUnits_ln (s16k_three_le_of_isSLn hq hSL)
      (s16t3_ce_quotient_binaryNaturalSL hN)
  · obtain hN := s16t3_sumOfNat_one hsum
    exact s15k_abs_endUnits_sp (s16k_six_le_of_isSpn hq hSp)
      (s16t3_ce_quotient_natSpn hN)
  · obtain hN := s16t3_sumOfNat_one hsum
    exact s15k_abs_endUnits_omegaPlus (s16k_six_le_of_isOmegaPlus hq hOP)
      (s16t3_ce_quotient_natOmegaPlus hN)
  · obtain hN := s16t3_sumOfNat_one hsum
    exact s16t3_ce_endUnits_omegaMinus (s16k_four_le_of_isOmegaMinus hq hOM)
      (s16t3_ce_quotient_natOmegaMinus hN)
  · obtain hN := s16t3_sumOfNat_one hsum
    exact s16c167_endUnits_alt (s16k_five_le_of_isAlt hq hAlt)
      (s16t3_ce_quotient_alternatingNatural hN)

private theorem s16t3_ce_of_surjective {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {H : Subgroup (MulAut Q)} {P : Subgroup Q}
    (θ : Γ →* ↥H) (hθ : Function.Surjective θ)
    (hact : ∀ (g : Γ) (q : Q), ((θ g : ↥H) : MulAut Q) q = g • q)
    (h : Z391.EndUnitsTrivial H P) :
    Z391.EndUnitsTrivial (⊤ : Subgroup Γ) P := by
  intro φ hφ
  refine h φ ?_
  intro m x y hxy
  obtain ⟨g, rfl⟩ := hθ m
  have hm : ∀ z : Q, (θ g : ↥H) • z = (⟨g, Subgroup.mem_top g⟩ : ↥(⊤ : Subgroup Γ)) • z := by
    intro z
    show ((θ g : ↥H) : MulAut Q) z = g • z
    exact hact g z
  have hxy' : (⟨g, Subgroup.mem_top g⟩ : ↥(⊤ : Subgroup Γ)) • (x : Q) = (y : Q) := by
    rw [← hm (x : Q)]
    exact hxy
  rw [hm ((φ x : ↥P) : Q)]
  exact hφ ⟨g, Subgroup.mem_top g⟩ x y hxy'

theorem s16t3_endUnitsTrivial_tilde (hq : CFSG.Open.IsQuasisimple ↥L) {I : Subgroup W}
    (hnat : SumOfNatShape L I (fixV L) 1) :
    Z391.EndUnitsTrivial (⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) I) := by
  have hE := s16t3_ce_endUnitsTrivial_range hq hnat
  exact s16t3_ce_of_surjective
    (θ := (MulDistribMulAction.toMulAut ↥L (s16t3_ce_quot L)).rangeRestrict)
    (MonoidHom.rangeRestrict_surjective _) (fun _ _ => rfl) hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
