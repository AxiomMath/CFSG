module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Label
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroupHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOne
import CFSG.Quasithin.MS93.FFOrders
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOrders
public import CFSG.LieType.Ree.Duality
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.A5.G3
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Blueprint (LieModel)

theorem eq_of_nParamSingle_of_isSz {X : Type} [Group X] [Finite X] {k j : ℕ}
    (h : NParamSingle X k) (hSz : IsSz X j) : k = j := by
  obtain ⟨a, ha, rfl⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_eq_two_mul_add_one_of_lieModel_twistedB2 hSz
  have hcard : Nat.card X = ordSuzuki (2 ^ (2 * a + 1)) := by
    rw [S19.card_of_isSz_two_pow hSz, ordSuzuki]
    ring
  have hZcard : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
    rw [FourteenEight.center_eq_bot_of_isSz hSz]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv
  rcases h with hSz' | hL2 | hSU3 | hSL3 | hSp4
  · obtain ⟨b, hb, rfl⟩ :=
      CFSG.LocalAnalysis.EvenBN.GMSK.exists_eq_two_mul_add_one_of_lieModel_twistedB2 hSz'
    have hcard' : Nat.card X = ordSuzuki (2 ^ (2 * b + 1)) := by
      rw [S19.card_of_isSz_two_pow hSz', ordSuzuki]
      ring
    obtain ⟨r, hr, hmr⟩ := (profile_ordSuzuki (f := 2 * b + 1) (by omega)).two
    obtain ⟨s, hs, hms⟩ := (profile_ordSuzuki (f := 2 * a + 1) (by omega)).two
    have := eq_of_two_pow_mul_odd hr hs (hmr.symm.trans (hcard'.symm.trans (hcard.trans hms)))
    omega
  · exact (FourteenEight.not_lieModel_psl_two_of_isSz hSz hL2).elim
  · exact (FourteenEight.not_isSU3_of_isSz hSz hSU3).elim
  · obtain ⟨-, hL3⟩ := hSL3
    have hk : 1 ≤ k := hL3.admissible.2.1
    have hL3card : Nat.card (X ⧸ Subgroup.center X) = ordA 2 (2 ^ k) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL3.card_eq_lieOrd (by norm_num)
    exact absurd (hcard.symm.trans (hZcard.symm.trans hL3card))
      (CFSG.RankThree.PartTwo.Sec8.Item8ModelProof.ordSuzuki_ne_ordA_two (by omega) hk)
  · have hk : 1 ≤ k := hSp4.admissible.2.1
    have hSp4card : Nat.card X = ordBC 2 (2 ^ k) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hSp4.card_eq_lieOrd (by norm_num)
    exact absurd (hcard.symm.trans hSp4card) (ordSuzuki_ne_ordBC_two ⟨a, rfl⟩ hk)

theorem nParam_eq_of_isSz_bar2 {G : Type} [Group G] [Finite G] {H : Subgroup G} {n j : ℕ}
    (hN : NParam H n) (hSz : IsSz (Bar2 H) j) : n = j :=
  eq_of_nParamSingle_of_isSz (nParamSingle_of_nParam_of_isQuasisimple hN
    (uc22p20g_qs_Sz (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz)
      hSz).1) hSz

theorem not_nParamSingle_of_twistedF4 {X : Type} [Group X] {f n : ℕ}
    (h : LieModel X .twistedF4 0 2 f) : ¬ NParamSingle X n := by
  obtain ⟨-, hR⟩ := CFSG.Blueprint.LieModel.reeTitsModel h (by decide)
  obtain ⟨k, hk, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel hR
  obtain ⟨a, K, _, _, _, -, hfa, hK, ⟨ε⟩⟩ := exists_mulEquiv_largeRee_model hR
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hZ : Subgroup.center X = ⊥ := by
    have h1 : (Subgroup.center X).map ε.toMonoidHom = Subgroup.center ↥(F4.reeGamma K a) :=
      Subgroup.map_center_eq ε
    rw [large_Ree_fixed_group_center_trivial a K hK'] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ ε.injective).1 h1
  have h3 : 3 ∣ ordTwistedF4 (2 ^ (2 * k + 1)) := by
    have h15 : 16 - 1 ∣ 16 ^ (2 * k + 1) - 1 ^ (2 * k + 1) :=
      Nat.sub_dvd_pow_sub_pow (x := 16) (y := 1) (n := 2 * k + 1)
    have h16 : (2 ^ (2 * k + 1)) ^ 4 = 16 ^ (2 * k + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h4 : 3 ∣ (2 ^ (2 * k + 1)) ^ 4 - 1 := by
      rw [h16]
      rw [one_pow] at h15
      exact dvd_trans (by norm_num) h15
    unfold ordTwistedF4
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h4 _) _) _
  have hlow : LowOrder (Nat.card X) ((2 * k + 1) * 12) := by
    rw [hcard]
    refine lowOrder_of_profile (profile_ordTwistedF4 (by omega)) (by omega) (fun j hj => ?_) h3
    rcases hj with ⟨hd, -⟩ | hd | ⟨hd, -⟩ | hd
    · exact (Nat.le_of_dvd (by positivity) hd).trans (by omega)
    · exact (Nat.le_of_dvd (by positivity) hd).trans (by omega)
    · exact (Nat.le_of_dvd (by positivity) hd).trans (by omega)
    · exact (Nat.le_of_dvd (by positivity) hd).trans (by omega)
  have hq : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
    rw [hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv
  refine not_nParamSingle_of_lowOrder hlow (fun _ => by rw [hZ, Subgroup.card_bot]; exact odd_one)
    (fun g hg hX => ?_) (fun g hg hX => ?_)
  · exact CFSG.Quasithin.MS93.ordA_two_ne_ordTwistedF4 hg (by omega)
      (hX.symm.trans (hq.trans hcard))
  · exact ordTwistedF4_ne_ordBC_two (by omega) hg (hcard.symm.trans hX)

theorem nParam_eq_of_twistedF4_parabolic
    {G : Type} [Group G] [Finite G] {L P : Subgroup G} {e n : ℕ}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hS : LieModel ↥L .twistedF4 0 2 e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n) :
    n = e := by
  obtain ⟨-, hR⟩ := CFSG.Blueprint.LieModel.reeTitsModel hS (by decide)
  obtain ⟨a, K, _, _, _, ha, hea, -, -⟩ := exists_mulEquiv_largeRee_model hR
  obtain ⟨S, hSN⟩ := hpar
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥L) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨Pj, hRT, hSL, hSz⟩ := CFSG.Quasithin.CLG2.rankTwoParG_f4_labelled (f := e) hR hU
  have hparA : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) :=
    ⟨le_top, S, hU, inf_le_right.trans hSN⟩
  obtain ⟨χ₁⟩ := nonempty_bar2_hinf_subgroupOf hPL
  have hL2 : IsL2 (Bar2 (Hinf (P.subgroupOf L))) e → n = e := fun h =>
    kNshape_holds G (Hinf P) n e hN (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv χ₁.symm h))
  have hSzP : IsSz (Bar2 (Hinf (P.subgroupOf L))) e → n = e := fun h =>
    nParam_eq_of_isSz_bar2 hN (CFSG.Blueprint.LieModel.of_mulEquiv χ₁.symm h)
  by_cases htop : P.subgroupOf L = ⊤
  ·
    have hPL' : P = L := le_antisymm hPL (Subgroup.subgroupOf_eq_top.mp htop)
    rw [hPL'] at hN
    have hsimpL : IsSimpleGroup ↥L := uc22p22r_lieModel_isSimple_twistedF4 hS
    have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfL
    have hO2 : CFSG.pCore 2 ↥L = ⊥ := by
      rcases (CFSG.pCore_normal (p := 2) (G := ↥L)).eq_bot_or_eq_top with hbot | htop'
      · exact hbot
      · exact absurd ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_equiv
          ((MulEquiv.subgroupCongr htop').trans Subgroup.topEquiv)).isNilpotent
          (Group.IsPerfect.not_isNilpotent ↥L)
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq rfl hperf hO2
    have hF4 : LieModel (Bar2 (Hinf L)) .twistedF4 0 2 e :=
      CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hS
    have hqb : CFSG.Open.IsQuasisimple (Bar2 (Hinf L)) := (CFSG.Open.IsQuasisimple.congr χ).mpr hq
    exact absurd (nParamSingle_of_nParam_of_isQuasisimple hN hqb)
      (not_nParamSingle_of_twistedF4 hF4)
  · rcases perfectCore_parabolic_cases hU hRT.res hparA htop with hbot | ⟨j, ⟨ebar⟩⟩
    ·
      refine absurd ?_ hinf
      have hPinf : Hinf P = (Hinf (P.subgroupOf L)).map L.subtype := by
        rw [Hinf_map L.subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPL]
      rw [hPinf, Hinf_eq_perfectCore, hbot, Subgroup.map_bot]
    ·
      obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      ·
        apply hL2
        rw [Hinf_eq_perfectCore]
        exact CFSG.Blueprint.LieModel.of_mulEquiv (nonempty_bar2_equiv_of_mulEquiv ebar).some.symm
          (CFSG.Quasithin.CLG2.LeviDataSL.lieModel_quotient hSL (by omega)
            (by rw [hea]; exact odd_two_mul_add_one a)).1
      ·
        apply hSzP
        rw [Hinf_eq_perfectCore]
        exact CFSG.Blueprint.LieModel.of_mulEquiv (nonempty_bar2_equiv_of_mulEquiv ebar).some.symm
          (CFSG.Quasithin.CLG2.LeviDataSz.lieModel_quotient hSz).1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
