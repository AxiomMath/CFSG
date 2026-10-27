module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusChar2b
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusL37
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusE16Alt
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL
public import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
public import CFSG.CGT.PushingUpLit.NineContent
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.GF2Type.Smith1980Orth.S3GoodLin
public import CFSG.GF2Type.Smith1980Orth.W4Lin
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.Components
public import CFSG.GH74.E2.OddRankG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.GLRMain
public import CFSG.LargeExtraspecial.S111ADisj
public import CFSG.LargeExtraspecial.S3cOddCore
public import CFSG.LargeExtraspecial.S3cSix
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S4Three
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeSylow
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusSpor
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.Timmesfeld.ARS.CaseHConnected
public import CFSG.Timmesfeld.ARS.CaseHU33
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Walter.J1Props
public import Certificates.Certificate5007

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)

section Final

set_option linter.unusedSectionVars false


theorem olRow_two_SL (p e : ℕ) [Fact p.Prime] (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField p e))) := by
  intro X _ _ P L Q hcfg ⟨φ⟩
  have hp : p.Prime := Fact.out
  have hLN := hcfg.card_dvd φ
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
  rw [GaloisField.card p e (by omega)] at hc
  have h3 : (p ^ e) ^ 3 ∣ Nat.card (projSL 3 (GaloisField p e)) := by
    have h' : (p ^ e) ^ 3 ∣ Nat.card (projSL 3 (GaloisField p e)) * Nat.gcd 3 (p ^ e - 1) := by
      rw [hc]; exact dvd_mul_right _ _
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e - 1)) := by
      rw [← pow_mul]
      exact coprime_pow_of_dvd hp (Nat.gcd_dvd_left 3 _) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h; omega)
    exact hcop.dvd_of_dvd_mul_right h'
  obtain ⟨rfl, rfl⟩ := eq_seven_of_cube_dvd hp hp3 he1 (h3.trans hLN)
  exact olRow_two_SL_seven X P L Q hcfg ⟨φ⟩

theorem olRow_two_eps (p e : ℕ) [Fact p.Prime] (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    OLRow (fun T _ => IsSLThreeEpsAt T (p ^ e)) := by
  intro X _ _ P L Q hcfg ⟨K, _, _, h⟩
  have hp : p.Prime := Fact.out
  rcases h with ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩
  · have hLN := hcfg.card_dvd φ
    have hc := CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 3) (by norm_num)
    rw [hK, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
      Finset.prod_pair (by norm_num)] at hc
    have h3 : (p ^ e) ^ 3 ∣ 1382446517760 := by
      have : (p ^ e) ^ 3 ∣ Nat.card (StatedSL 3 K) := by
        rw [hc]; exact dvd_mul_right _ _
      exact this.trans hLN
    obtain ⟨rfl, rfl⟩ := eq_seven_of_cube_dvd hp hp3 he1 h3
    exact olRow_two_statedSL_seven (by rw [hK]; norm_num) X P L Q hcfg ⟨φ⟩
  · have hLN := hcfg.card_dvd φ
    have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K :=
      ⟨hp, he1, by rw [hK, ← pow_mul, mul_comm]⟩
    have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hu (n := 3) (by norm_num)
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)] at hc
    have h3 : (p ^ e) ^ 3 ∣ 1382446517760 := by
      have : (((p ^ e) ^ 3 : ℕ) : ℤ) ∣ (Nat.card (StatedSU 3 (p ^ e) K) : ℤ) := by
        rw [hc]; push_cast; exact dvd_mul_right _ _
      exact (Int.natCast_dvd_natCast.mp this).trans hLN
    obtain ⟨rfl, rfl⟩ := eq_seven_of_cube_dvd hp hp3 he1 h3
    have h43 : ((43 : ℕ) : ℤ) ∣ (Nat.card (StatedSU 3 (7 ^ 1) K) : ℤ) := by
      rw [hc]; norm_num
    have := (Int.natCast_dvd_natCast.mp h43).trans hLN
    norm_num at this

theorem olRow_four_alt (n : ℕ) (hn : n ≤ 9) :
    OLRow (fun T _ => Nonempty (T ≃* alternatingGroup (Fin n))) := by
  rcases (by omega : n ≤ 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9) with
    h | rfl | rfl | rfl | rfl | rfl
  · exact olRow_alt_le_four h
  · exact olRow_alt_five
  · exact olRow_alt_six
  · exact olRow_alt_seven
  · exact olRow_of_E16 _ exists_E16_alt_eight
  · exact olRow_of_E16 _ exists_E16_alt_nine


theorem olRow_five_spor : ∀ s ∈ sporadics46,
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier s)) := by
  intro s hs
  simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact olRow_spor_M11
  · exact olRow_spor_M12
  · exact olRow_spor_M22
  · exact olRow_spor_M23
  · exact olRow_spor_M24
  · exact olRow_spor_J1
  · exact olRow_spor_J2
  · exact olRow_spor_J3
  · exact olRow_spor_J4
  · exact olRow_spor_McL
  · exact olRow_spor_HS
  · exact olRow_spor_He
  · exact olRow_spor_Ru

theorem olRow_five_cover : ∀ s ∈ sporadicCovers46,
    OLRow (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) := by
  intro s hs
  simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact olRow_cover_M22
  · exact olRow_cover_J3
  · exact olRow_cover_McL
  · exact olRow_cover_ON


theorem olRows_holds : OLRows where
  one := fun p e _ hp2 he => olRow_one p e hp2 he
  two_eps := fun p e _ hp3 he1 he2 => olRow_two_eps p e hp3 he1 he2
  two_SL := fun p e _ hp3 he1 he2 => olRow_two_SL p e hp3 he1 he2
  two_SU := fun p e _ hp3 he1 _ => olRow_two_SU p e hp3 he1
  three_G2 := fun p _ hp3 => olRow_three_G2 p hp3
  three_Sp := fun p _ hp3 => olRow_three_Sp p hp3
  three_SU := fun p _ hp3 _ => olRow_three_SU p hp3
  three_SL := fun p _ hp3 _ => olRow_three_SL p hp3
  four_alt := olRow_four_alt
  four_A6 := olRow_four_A6
  four_A7 := olRow_four_A7
  five_spor := olRow_five_spor
  five_cover := olRow_five_cover
  six_model := olRow_six_model
  six_SL3 := olRow_six_SL3
  seven_SL52 := olRow_seven_SL52
  seven_Sp62 := olRow_of_E16 _ exists_E16_projSp_three_two
  seven_SU54 := olRow_seven_SU54
  eight_SL3 := olRow_eight_SL3
  eight_SU3 := olRow_eight_SU3
  eight_SL43 := olRow_eight_SL43
  eight_cover := olRow_eight_cover

theorem kf148OneLineComp_holds : KF148OneLineComp :=
  kf148OneLineComp_of_rows olRows_holds

end Final

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
