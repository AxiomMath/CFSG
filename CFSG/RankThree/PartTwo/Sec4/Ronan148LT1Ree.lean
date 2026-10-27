module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Ree
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Comp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)


theorem three_dvd_ordTwistedF4 (b : ℕ) : 3 ∣ CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) := by
  unfold CFSG.Open.ordTwistedF4
  have h : 3 ∣ (2 ^ (2 * b + 1)) ^ 4 - 1 := by
    have h15 : (16 - 1 : ℕ) ∣ 16 ^ (2 * b + 1) - 1 := Nat.sub_one_dvd_pow_sub_one 16 (2 * b + 1)
    have h16 : (2 ^ (2 * b + 1)) ^ 4 = 16 ^ (2 * b + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h16]
    exact (show (3 : ℕ) ∣ 16 - 1 by norm_num).trans h15
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _) _

theorem three_dvd_card_statedSU_three {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ (2 * f)) :
    3 ∣ Nat.card (CFSG.Open.StatedSU 3 (2 ^ f) F) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, hf, hF⟩
  have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 3) (by norm_num)
  have h3 : (3 : ℤ) ∣ (Nat.card (CFSG.Open.StatedSU 3 (2 ^ f) F) : ℤ) := by
    rw [hc]
    have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
    rw [hIcc, Finset.prod_pair (by norm_num)]
    have h2 : (3 : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 := by
      have h4 : (3 : ℕ) ∣ (2 ^ f) ^ 2 - 1 := by
        have h15 : (4 - 1 : ℕ) ∣ 4 ^ f - 1 := Nat.sub_one_dvd_pow_sub_one 4 f
        have h16 : (2 ^ f) ^ 2 = 4 ^ f := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [h16]
        exact h15
      have hle : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have := (Int.natCast_dvd_natCast.2 h4)
      push_cast [Nat.cast_sub hle] at this
      simpa using this
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  exact_mod_cast h3

section Ree


theorem reeF4_noSz {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ β : MulAut (ReeTag.F4.reeGamma K a), β ^ 3 = 1 →
      ∀ C Y : Subgroup (ReeTag.F4.reeGamma K a), (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
        (Y.subgroupOf C).IsSubnormal → Group.IsPerfect ↥Y → ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  classical
  intro β hβ C Y hC hYC hsub hp h3
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial a K hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hβ1 : β = 1
  ·
    subst hβ1
    have hCtop : C = ⊤ := Subgroup.ext fun z => by simp [hC]
    subst hCtop
    have hS : IsSimpleGroup (ReeTag.F4.reeGamma K a) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 ha hK
    have h3S : 3 ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
      rw [Sec8.Item86ResProof.card_of_mulEquiv_reeGamma a K hK (MulEquiv.refl _)]
      exact three_dvd_ordTwistedF4 a
    exact eq_bot_of_equiv_simple Subgroup.topEquiv hS h3S hYC hsub h3
  by_cases hin : ∃ g : ReeTag.F4.reeGamma K a, β = MulAut.conj g
  ·
    obtain ⟨g, hg⟩ := hin
    obtain ⟨y, hy, hy3, hy1⟩ :=
      CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ ⟨g, hg.symm⟩ hβ hβ1
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    obtain ⟨eU⟩ := Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hyo
    have hCeq : C = Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) := by
      ext z
      rw [hC, hy, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
      constructor
      · intro h
        calc z * y = y * z * y⁻¹ * y := by rw [h]
          _ = y * z := by group
      · intro h
        rw [← h]
        group
    subst hCeq
    have hF'card : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
      rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
    have hF'card' : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = 2 ^ (2 * (2 * a + 1)) :=
      GaloisField.card 2 _ (by omega)
    have hq := (Sec8.Item87Proof.isQuasisimple_statedSU_three
      (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hF'card (by omega)).1
    exact eq_bot_of_equiv_quasisimple eU hq
      (three_dvd_card_statedSU_three (by omega) hF'card') hYC hsub hp h3
  ·
    push Not at hin
    obtain ⟨g, σ, hσ, hg⟩ := SeitzOuterCube.Exc.reeF4_stdDescent_odd ha hK Nat.prime_three β
      ⟨orderOf_eq_prime hβ hβ1, hin⟩
    obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ := exists_fixSubgroup_fieldAut_equiv hK Nat.prime_three
      (by norm_num) σ hσ
    haveI := hchar
    haveI : Finite (fixSubfield σ) := Subtype.finite
    haveI : Finite (ModGL ReeTag.F4.tag (fixSubfield σ)) := finite_modGL
    haveI : Finite ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) := Subtype.finite
    set δ := ReeTag.F4.reeGammaFieldAut K a σ with hδ
    have hCeq : C = Sec4.autFix (MulAut.conj g * δ * (MulAut.conj g)⁻¹) :=
      Subgroup.ext fun z => (hC z).trans (by rw [hg]; exact Sec4.mem_autFix.symm)
    have hfix : Sec4.autFix δ = fixSubgroup δ := Subgroup.ext fun _ => Iff.rfl
    let eCδ : ↥C ≃* ReeTag.F4.reeGamma (fixSubfield σ) b :=
      (((MulEquiv.subgroupCongr hCeq).trans
        (RonanK429Lie.autFixConjEquiv (MulAut.conj g) δ)).trans
          (MulEquiv.subgroupCongr hfix)).trans eC
    rcases Nat.eq_zero_or_pos b with rfl | hb
    ·
      have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
      have hv : LieTypeIndex.tits.Valid := by
        refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
        · simp [LieTypeIndex.inStandardRange_iff]
        · simp [LieTypeIndex.isDuplicateRepresentative_iff]
      let eR : ↥C ≃* ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0) :=
        eCδ.trans (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm
      have hT := (CFSG.LieType.Simplicity.titsData (fixSubfield σ) hk2).isQuasisimple hk2
      obtain ⟨eT⟩ := nonempty_commutator_reeFixed_equiv_cat_tits hk2 hv
      haveI : Finite ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0) := Subtype.finite
      have h3T : 3 ∣ Nat.card ↥(commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0)) := by
        haveI : Finite ↥(commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0)) := Subtype.finite
        exact three_dvd_card_of_lie lieOrderBridge_holds ⟨.tits, hv⟩
          (fun m h => by cases h) ⟨eT⟩
      refine eq_bot_of_equiv_comm eR hT h3T (fun x y => ?_) hYC hsub hp h3
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    ·
      have hs : IsSimpleGroup ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
      have h3S : 3 ∣ Nat.card ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) := by
        rw [Sec8.Item86ResProof.card_of_mulEquiv_reeGamma b (fixSubfield σ) hkcard
          (MulEquiv.refl _)]
        exact three_dvd_ordTwistedF4 b
      exact eq_bot_of_equiv_simple eCδ hs h3S hYC hsub h3

theorem kT1_seven_F4 (m : ℕ) (hm : (LieTypeIndex.reeF4 m).Valid) :
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group := by
  intro S _ _ hs hna ⟨e0⟩ _
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hm e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  have hOut : Group.IsSolvable (Outer S) := (ReeTag.large_Ree_model_Schreier S 2 (2 * m + 1) hR).2.2.1
  refine row143_of_inner_kgroup hs hna
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOut P hPp)
    fun β hβ Y hY hsn _ hp h3Y => ?_
  exact sp4R148_bot_of_mulEquiv e (reeF4_noSz ha hK) β hβ (Sec4.autFix β) Y (fun z => Iff.rfl)
    hY hsn hp h3Y

end Ree

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
