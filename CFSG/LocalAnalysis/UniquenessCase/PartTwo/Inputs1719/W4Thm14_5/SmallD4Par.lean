module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOne
import CFSG.Quasithin.MS93.FFOrders
import CFSG.Quasithin.Vol2.Ch11L2Q5cNot3
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.SteinbergBNLinearTwoOuterInvolutionRigidity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.A5.G3
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Blueprint (LieModel)


theorem center_eq_bot_of_is3D4 {X : Type} [Group X] {f : ℕ} (h : Is3D4 X f) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, K, _, _, σ, -, -, ⟨φ⟩⟩ :=
    exists_mulEquiv_triality_model (LieModel.chevalleyExceptionalModel h (by decide))
  have h1 : (Subgroup.center X).map φ.toMonoidHom =
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Subgroup.map_center_eq φ
  rw [center_graphFixedRootGroup_eq_bot σ.surjective] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h1

theorem not_nParamSingle_of_is3D4 {X : Type} [Group X] {f n : ℕ} (h : Is3D4 X f) :
    ¬ NParamSingle X n := by
  have hZ := center_eq_bot_of_is3D4 h
  have hX := LieModel.chevalleyExceptionalModel h (by decide)
  have hf : 1 ≤ f := hX.1.2.1
  have hcard : Nat.card X = ordTrialityD4 (2 ^ f) := card_chevalleyExceptionalModel_two hX
  have hlow : LowOrder (Nat.card X) (f * 12) := by
    rw [hcard]
    refine lowOrder_of_profile (profile_ordTrialityD4 hf) (by omega) (fun j hj => ?_) ?_
    · rcases hj with ⟨hd, -⟩ | hd | hd
      · exact (Nat.le_of_dvd (by positivity) hd).trans (by omega)
      · exact (Nat.le_of_dvd (by positivity) hd).trans (by omega)
      · exact (Nat.le_of_dvd (by positivity) hd).trans (by omega)
    · rw [ordTrialityD4]
      exact Dvd.dvd.mul_left (CFSG.Quasithin.Vol2.Ch11.SecB.three_dvd_two_pow_sq_sub_one f) _
  have hq : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
    rw [hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv
  refine not_nParamSingle_of_lowOrder hlow (fun _ => by rw [hZ, Subgroup.card_bot]; exact odd_one)
    (fun g hg hX => ?_) (fun g hg hX => ?_)
  · exact CFSG.Quasithin.MS93.ordA_two_ne_ordTrialityD4 hg hf (hX.symm.trans (hq.trans hcard))
  · exact ordTrialityD4_ne_ordBC_two hf hg (hcard.symm.trans hX)

theorem nParam_eq_of_is3D4_parabolic {G : Type} [Group G] [Finite G] {L P : Subgroup G} {e n : ℕ}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hS : Is3D4 ↥L e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n) :
    n = e ∨ n = 3 * e := by
  classical
  obtain ⟨he1, K, hKf, hKfin, σ, hK, hσ, ⟨φ⟩⟩ :=
    exists_mulEquiv_triality_model (LieModel.chevalleyExceptionalModel hS (by decide))
  let : Field K := hKf
  let : Finite K := hKfin
  have hK3 : Nat.card K = 2 ^ (3 * e) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Pa : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (P.subgroupOf L).map φ.toMonoidHom with hPa
  have hPa' : P.subgroupOf L = Pa.map φ.symm.toMonoidHom := by
    rw [hPa, Subgroup.map_map]
    have hid : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id ↥L :=
      MonoidHom.ext fun x => φ.symm_apply_apply x
    rw [hid, Subgroup.map_id]
  obtain ⟨χ₁⟩ := nonempty_bar2_hinf_subgroupOf hPL
  obtain ⟨χ₂⟩ := nonempty_bar2_hinf_map_mulEquiv φ (P.subgroupOf L)
  have hL2 : ∀ m, IsL2 (Bar2 (Hinf Pa)) m → n = m := fun m h =>
    kNshape_holds G (Hinf P) n m hN
      (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv (χ₂.trans χ₁.symm) h))
  have hbotP : perfectCore Pa = ⊥ → False := fun hbot => by
    apply hinf
    have hPinf : Hinf P = (Hinf (P.subgroupOf L)).map L.subtype := by
      rw [Hinf_map L.subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPL]
    rw [hPinf, hPa', Hinf_map_eq_bot φ.symm Pa (by rw [Hinf_eq_perfectCore]; exact hbot),
      Subgroup.map_bot]
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU := isSylowTwoOf_subgroupOf_top hUsyl
  have hparA : IsParabolic2 (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) Pa := by
    obtain ⟨S, hSN⟩ := hpar.map φ.toMonoidHom φ.surjective
    exact ⟨le_top, S, CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S, inf_le_right.trans hSN⟩
  by_cases htop : Pa = ⊤
  ·
    exfalso
    have hPL' : P = L := by
      refine le_antisymm hPL (Subgroup.subgroupOf_eq_top.mp ?_)
      rw [hPa', htop, Subgroup.map_top_of_surjective _ φ.symm.surjective]
    rw [hPL'] at hN
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
    have hsimpL : IsSimpleGroup ↥L :=
      ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_is3D4 hS)).trans
        QuotientGroup.quotientBot).symm.isSimpleGroup
    have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfL
    have hO2 : CFSG.pCore 2 ↥L = ⊥ := by
      rcases (CFSG.pCore_normal (p := 2) (G := ↥L)).eq_bot_or_eq_top with hbot | htop'
      · exact hbot
      · exact absurd ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_equiv
          ((MulEquiv.subgroupCongr htop').trans Subgroup.topEquiv)).isNilpotent
          (Group.IsPerfect.not_isNilpotent ↥L)
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq rfl hperf hO2
    have hD4 : Is3D4 (Bar2 (Hinf L)) e := CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hS
    have hqb : CFSG.Open.IsQuasisimple (Bar2 (Hinf L)) := (CFSG.Open.IsQuasisimple.congr χ).mpr hq
    exact not_nParamSingle_of_is3D4 hD4 (nParamSingle_of_nParam_of_isQuasisimple hN hqb)
  · rcases perfectCore_parabolic_cases hU (triality_residualOvergroupsAt σ) hparA htop with
      hbot | ⟨j, ⟨ebar⟩⟩
    · exact (hbotP hbot).elim
    ·
      have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ e) ^ 1) := fun c => by
        rw [pow_one]
        exact hσ c
      have hLa : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom (d4Index j)) =
          (2 ^ e) ^ (TwistTag.D4.orbit (d4Index j)).card :=
        card_orbitField_D4_orientation Nat.prime_two he1 hK (Or.inl rfl) hσ' (d4Index j)
      have horb : ∀ a : Fin TwistTag.D4.foldedTag.rank,
          (TwistTag.D4.orbit a).card = 1 ∨ (TwistTag.D4.orbit a).card = 3 := by
        decide
      by_cases h4 : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom (d4Index j))
      ·
        have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom (d4Index j)),
            s.card = 4 := exists_finset_card_four h4
        obtain ⟨g, hg, hker⟩ := exists_levi_hom_fixed σ (d4Index j) hUsyl.2.1 hL4
        have : IsSimpleGroup (SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom (d4Index j))) :=
          sl2_isSimple hL4
        have hnab := sl2_nonabelian hL4
        have hm : n = e * (TwistTag.D4.orbit (d4Index j)).card := by
          apply hL2
          rw [Hinf_eq_perfectCore]
          refine KTabD.isL2_of_mulEquiv_sl2 ?_ (by rw [hLa, ← pow_mul])
            ((nonempty_bar2_equiv_of_mulEquiv ebar).some.trans (modO2EquivOfHom hnab g hg hker))
          by_contra hlt
          push Not at hlt
          have hle : (2 ^ e) ^ (TwistTag.D4.orbit (d4Index j)).card ≤ 2 ^ 1 := by
            rw [← pow_mul]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rcases horb (d4Index j) with h1 | h3
        · exact Or.inl (by rw [hm, h1, mul_one])
        · exact Or.inr (by rw [hm, h3, mul_comm])
      ·
        exfalso
        have hm2 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom (d4Index j)) = 2 := by
          rw [hLa, ← pow_mul] at h4 ⊢
          have hc1 : 1 ≤ (TwistTag.D4.orbit (d4Index j)).card := by
            rcases horb (d4Index j) with h | h <;> omega
          have hc : e * (TwistTag.D4.orbit (d4Index j)).card = 1 := by
            by_contra hne
            have h2 : 2 ≤ e * (TwistTag.D4.orbit (d4Index j)).card := by
              have := Nat.mul_le_mul he1 hc1
              omega
            exact h4 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h2))
          rw [hc, pow_one]
        obtain ⟨R, hVN, hNV, hsup, hRV, hker⟩ := fixed_structure σ (d4Index j)
        have hVU : graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom (d4Index j) ≤
            graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := graphFixedSimpleComplement_le _
        have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom (d4Index j)) :=
          IsPGroup.of_injective hUsyl.2.1 (Subgroup.inclusion hVU)
            (Subgroup.inclusion_injective hVU)
        have hVs : Group.IsSolvable
            ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom (d4Index j)) := by
          have := hV2.isNilpotent
          infer_instance
        have hsolvSL :
            Group.IsSolvable (SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom (d4Index j))) := by
          refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
          rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hm2]
          norm_num
        have hMs : Group.IsSolvable ↥R.range :=
          Group.isSolvable_of_surjective (f := R.rangeRestrict)
            (MonoidHom.rangeRestrict_surjective R)
        have hNs : Group.IsSolvable ↥(fixedPosWeylGroup TwistTag.D4 K σ.toRingHom (d4Index j)) :=
          isSolvable_of_levi hVN hNV hsup hVs hMs
        have hpcN : perfectCore (fixedPosWeylGroup TwistTag.D4 K σ.toRingHom (d4Index j)) = ⊥ :=
          (isSolvable_iff_perfectCore_eq_bot _).mp hNs
        have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} ≤
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedParabolic_le _ _ _ _
        have hpc0 : perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom
            {d4Index j}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = ⊥ := by
          apply Subgroup.map_injective
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective
          rw [perfectCore_map_subgroupOf hPC, fixed_perfectCore_eq σ (d4Index j), hpcN,
            Subgroup.map_bot]
        apply hbotP
        have : Subsingleton ↥(perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom
            {d4Index j}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
          rw [hpc0]
          infer_instance
        have : Subsingleton ↥(perfectCore Pa) := ebar.toEquiv.subsingleton
        exact Subgroup.eq_bot_of_subsingleton _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
