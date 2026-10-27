module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenPiCV
import CFSG.LocalAnalysis.EvenBN.G2.G2LieModelFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOne
import CFSG.CGT.T75G.Sec68Insp
import CFSG.LocalAnalysis.SteinbergBNLinearTwoOuterInvolutionRigidity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.A5.G3
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.Blueprint (LieModel)


theorem not_nParamSingle_of_isG2 {X : Type} [Group X] {k n : ℕ} (h : IsG2 X k) :
    ¬ NParamSingle X n := by
  have hk : 2 ≤ k := (CFSG.LocalAnalysis.EvenBN.G2.lieModel_G2_params h).2
  have hcard : Nat.card X = ordG2 (2 ^ k) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (LieModel.chevalleyExceptionalModel h (by decide))
  have hZ : CFSG.Open.IsQuasisimple X → Odd (Nat.card (Subgroup.center X)) := fun _ => by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.center_eq_bot_of_isG2 h,
      Subgroup.card_bot]
    exact odd_one
  have hlow : LowOrder (Nat.card X) (k * 6) := by
    rw [hcard]
    refine lowOrder_of_profile (CFSG.Timmesfeld.Orders.profile_ordG2 (by omega)) ?_ ?_ ?_
    · omega
    · intro j hj
      obtain ⟨a, ha, hdvd⟩ := hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · exact Nat.le_of_dvd (by positivity) hdvd
      · exact (Nat.le_of_dvd (by positivity) hdvd).trans (by omega)
    · rw [ordG2]
      simpa [mul_assoc] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_two_pow_sq_sub_one k)
        ((2 ^ k) ^ 6 - 1)) ((2 ^ k) ^ 6)
  refine not_nParamSingle_of_lowOrder hlow hZ (fun f hf hX => ?_) (fun f hf hX => ?_)
  · have hq : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
      rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.center_eq_bot_of_isG2 h]
      exact Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv
    exact (CFSG.CGT.T75G.ordA_two_ne_ordG2 hf (by omega)) (hX.symm.trans (hq.trans hcard))
  · exact (CFSG.Timmesfeld.Orders.ordG2_ne_ordBC_two hk hf) (hcard.symm.trans hX)

theorem isL2_bar2_perfectCore_parabolic_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (j : Fin 2) :
    IsL2 (Bar2 (perfectCore ((CFSG.LieType.Chevalley.parabolicSubgroup .G2 K
      {CFSG.QuasithinUnique.Setup.X6.g2Index j}).subgroupOf
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)))) n := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab := sl2_nonabelian (K := K) hK4
  have hsimple : IsSimpleGroup (SL2 K) := sl2_isSimple (K := K) hK4
  obtain ⟨g, hg, hker⟩ :=
    exists_levi_hom_adjoint (τ := .G2) (K := K) hK hn (CFSG.QuasithinUnique.Setup.X6.g2Index j)
  have hmodel : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  let e : Bar2 (perfectCore ((CFSG.LieType.Chevalley.parabolicSubgroup .G2 K
      {CFSG.QuasithinUnique.Setup.X6.g2Index j}).subgroupOf
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K))) ≃*
      StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab g hg hker).trans sl2EquivStatedProj
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n)
    e.symm hmodel

theorem nParam_eq_of_isG2_parabolic {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    {e n : ℕ} (hS : IsG2 ↥L e) (hPL : P ≤ L) (hpar : IsParabolicTwo ↥L (P.subgroupOf L))
    (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n) : n = e := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.exists_adjoint_of_isG2 hS
  have he : 2 ≤ e := (CFSG.LocalAnalysis.EvenBN.G2.lieModel_G2_params hS).2
  let : Field K := hKf
  let : Finite K := hKfin
  have hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hmodGL : Finite (ModGL .G2 K) := finite_modGL
  set ψ : ↥L ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := φ with hψ
  set Pa : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    (P.subgroupOf L).map ψ.toMonoidHom with hPa
  have hPa' : P.subgroupOf L = Pa.map ψ.symm.toMonoidHom := by
    rw [hPa, Subgroup.map_map]
    ext x
    simp
  obtain ⟨χ₁⟩ := nonempty_bar2_hinf_subgroupOf hPL
  obtain ⟨χ₂⟩ := nonempty_bar2_hinf_map_mulEquiv ψ (P.subgroupOf L)
  have hL2 : IsL2 (Bar2 (Hinf Pa)) e → n = e := fun h =>
    kNshape_holds G (Hinf P) n e hN
      (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv (χ₂.trans χ₁.symm) h))
  have hparA : IsParabolic2 (⊤ : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) Pa := by
    obtain ⟨S, hSN⟩ := hpar.map ψ.toMonoidHom ψ.surjective
    exact ⟨le_top, S, CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S,
      inf_le_right.trans hSN⟩
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent .G2 K).subgroupOf (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := .G2) (K := K) 2).1)
  by_cases htop : Pa = ⊤
  ·
    have hPL' : P = L := by
      refine le_antisymm hPL (Subgroup.subgroupOf_eq_top.mp ?_)
      rw [hPa', htop, Subgroup.map_top_of_surjective _ ψ.symm.surjective]
    rw [hPL'] at hN
    have hsimpleL : IsSimpleGroup ↥L := uc22p22r_lieModel_isSimple_G2 hS
    have hqAdj : CFSG.IsQuasisimple
        ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
      refine CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (K := K) ?_
      rw [hKcard]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have hqL : CFSG.IsQuasisimple ↥L := CFSG.IsQuasisimple.of_mulEquiv φ hqAdj
    have hperfL : Group.IsPerfect ↥L := hqL.1
    have hqL' : CFSG.Open.IsQuasisimple ↥L := ⟨hqL.1.commutator_eq_top, hqL.2.1⟩
    have hperf : ⁅L, L⁆ = L := isPerfect_iff.mp hperfL
    have hO2 : CFSG.pCore 2 ↥L = ⊥ := by
      have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases (CFSG.pCore_normal (p := 2) (G := ↥L)).eq_bot_or_eq_top with hbot | htop'
      · exact hbot
      · exact absurd ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_equiv
          ((MulEquiv.subgroupCongr htop').trans Subgroup.topEquiv)).isNilpotent
          (Group.IsPerfect.not_isNilpotent ↥L)
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq rfl hperf hO2
    have hG2 : IsG2 (Bar2 (Hinf L)) e := CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hS
    have hq : CFSG.Open.IsQuasisimple (Bar2 (Hinf L)) :=
      (CFSG.Open.IsQuasisimple.congr χ).mpr hqL'
    exact absurd (nParamSingle_of_nParam_of_isQuasisimple hN hq)
      (not_nParamSingle_of_isG2 hG2)
  · rcases perfectCore_parabolic_cases hU (G2_residualOvergroupsAt (K := K)) hparA htop with
      hbot | ⟨j, ⟨ebar⟩⟩
    ·
      refine absurd ?_ hinf
      have hPinf : Hinf P = (Hinf (P.subgroupOf L)).map L.subtype := by
        rw [Hinf_map L.subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPL]
      rw [hPinf, hPa',
        Hinf_map_eq_bot ψ.symm Pa (by rw [Hinf_eq_perfectCore]; exact hbot), Subgroup.map_bot]
    ·
      apply hL2
      rw [Hinf_eq_perfectCore]
      exact CFSG.Blueprint.LieModel.of_mulEquiv (nonempty_bar2_equiv_of_mulEquiv ebar).some.symm
        (isL2_bar2_perfectCore_parabolic_g2 hKcard he j)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
