module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.RankThree.PartTwo.Sec13.Item131a

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

namespace L227

theorem eight_dvd_pow_three_mul_sq_sub_one (q : ℕ) : 8 ∣ q ^ 3 * (q ^ 2 - 1) := by
  rcases Nat.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    exact Dvd.dvd.mul_right ⟨k ^ 3, by ring⟩ _
  · subst hk
    obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    refine Dvd.dvd.mul_left ⟨m, ?_⟩ _
    have h : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega

theorem eight_dvd_card_of_isSLThreePi {X : Type} [Group X] (hX : Sec4.IsSLThreePi X) :
    8 ∣ Nat.card X := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  rcases hcase with ⟨hK, -, ⟨e⟩⟩ | ⟨hK, -, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three]
    exact Dvd.dvd.mul_right (eight_dvd_pow_three_mul_sq_sub_one _) _
  · rw [Nat.card_congr e.toEquiv,
      CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK]
    exact Dvd.dvd.mul_right (eight_dvd_pow_three_mul_sq_sub_one _) _

theorem eight_dvd_card_projSL_three (K : Type) [Field K] [Finite K] :
    8 ∣ Nat.card (projSL 3 K) := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd K
  have h8 : 8 ∣ Nat.card (projSL 3 K) * Nat.gcd 3 (Nat.card K - 1) := by
    rw [h, ← mul_assoc]
    exact Dvd.dvd.mul_right (eight_dvd_pow_three_mul_sq_sub_one _) _
  exact (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) (by norm_num)).dvd_of_dvd_mul_right
    h8

theorem eight_dvd_card_projSU_three (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    8 ∣ Nat.card (projSU 3 p f) := by
  have h := KFacts.KS14.card_projSU_three_mul_gcd p f hf
  have h8 : 8 ∣ Nat.card (projSU 3 p f) * Nat.gcd 3 (p ^ f + 1) := by
    rw [h, ← mul_assoc]
    exact Dvd.dvd.mul_right (eight_dvd_pow_three_mul_sq_sub_one _) _
  exact (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) (by norm_num)).dvd_of_dvd_mul_right
    h8

theorem eight_dvd_card_of_equiv_prod {X S : Type} [Group X] [Group S] (h8 : 8 ∣ Nat.card S)
    (e : X ≃* Multiplicative (ZMod 3) × S) : 8 ∣ Nat.card X := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  exact Dvd.dvd.mul_left h8 _

theorem eight_dvd_card_of_isZ3LThreePi {X : Type} [Group X] (hX : Sec8.IsZ3LThreePi X) :
    8 ∣ Nat.card X := by
  obtain ⟨p, e, hp, he, h | h⟩ := hX
  · obtain ⟨-, ⟨φ⟩⟩ := h
    exact eight_dvd_card_of_equiv_prod (eight_dvd_card_projSL_three _) φ
  · obtain ⟨-, ⟨φ⟩⟩ := h
    exact eight_dvd_card_of_equiv_prod (eight_dvd_card_projSU_three p e he) φ

theorem eight_dvd_card_of_isZ3PGLThreePi {X : Type} [Group X] (hX : Sec8.IsZ3PGLThreePi X) :
    8 ∣ Nat.card X := by
  obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hX
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have h1 := card_projImage_slPi_mul_three hK hq
  have h8 : 8 ∣ Nat.card (projImage (Sec4.slPi π 3 (p ^ f) K)) * 3 := by
    rw [h1]
    exact Dvd.dvd.mul_right (eight_dvd_pow_three_mul_sq_sub_one _) _
  have h8' : 8 ∣ Nat.card (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h8
  have hle : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  exact eight_dvd_card_of_equiv_prod (h8'.trans (Subgroup.card_dvd_of_le hle)) φ

theorem eight_dvd_card_of_isSLThreePiTwo {X : Type} [Group X] (hX : Sec4.IsSLThreePiTwo X) :
    8 ∣ Nat.card X := by
  obtain ⟨L₀, -, -, -, hSL, -⟩ := hX
  exact (eight_dvd_card_of_isSLThreePi hSL).trans (Subgroup.card_subgroup_dvd_card L₀)

theorem eight_dvd_card_of_isTripleCover {Q S : Type} [Group Q] [Group S] (h8 : 8 ∣ Nat.card S)
    (h : Sec4.IsTripleCover Q S) : 8 ∣ Nat.card Q := by
  obtain ⟨-, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q),
    Nat.card_congr e.toEquiv]
  exact Dvd.dvd.mul_right h8 _

theorem eight_dvd_card_alternating_seven : 8 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  norm_num

theorem eight_dvd_card_M22 : 8 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M22 := by
  rw [KFacts.KS14.card_nativeM22]
  norm_num

theorem eight_dvd_card_M12 : 8 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M12 := by
  rw [KFacts.KS14.card_nativeM12]
  norm_num

theorem eight_dvd_card_J2 : 8 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
  rw [KFacts.KS14.card_nativeJ2]
  norm_num

theorem eight_dvd_card_thetaQuot_of_dvd_lBarA {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    {c : G} (hD : Sec13Data G A c L) (h8 : 8 ∣ Nat.card (lBarA c L A)) :
    8 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
  have hΛn : ((Sec12.lBar c L).subgroupOf (lBarA c L A)).Normal := lBar_normal hD
  have hΛcard : Nat.card ((Sec12.lBar c L).subgroupOf (lBarA c L A)) =
      Nat.card (L ⧸ aschbacherSolvableCore 3 L) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).toEquiv).trans
      (Nat.card_congr η.toEquiv).symm
  have hidx : ((Sec12.lBar c L).subgroupOf (lBarA c L A)).index ∣ 27 := by
    have hR : Nat.card (aBarHom hD).range = 27 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective hD)).toEquiv, hD.card_eq]
    have h1 : ((Sec12.lBar c L).subgroupOf (lBarA c L A)).relIndex (aBarHom hD).range =
        ((Sec12.lBar c L).subgroupOf (lBarA c L A)).index := by
      rw [← Subgroup.relIndex_sup_right, sup_comm, lBar_sup_range_aBarHom hD,
        Subgroup.relIndex_top_right]
    have h2 := Subgroup.relIndex_dvd_card
      (H := (Sec12.lBar c L).subgroupOf (lBarA c L A)) (K := (aBarHom hD).range)
    rwa [h1, hR] at h2
  have hmul := Subgroup.card_mul_index ((Sec12.lBar c L).subgroupOf (lBarA c L A))
  have hcop : Nat.Coprime 8 ((Sec12.lBar c L).subgroupOf (lBarA c L A)).index :=
    Nat.Coprime.coprime_dvd_right hidx (by norm_num)
  rw [← hΛcard]
  rw [← hmul] at h8
  exact hcop.dvd_of_dvd_mul_right h8

theorem card_projSL_two_galoisField_three_three :
    Nat.card (projSL 2 (GaloisField 3 3)) = 9828 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Sec11.KSListsProof.card_projSL_two_mul (GaloisField 3 3)
  rw [GaloisField.card 3 3 (by norm_num)] at h
  norm_num at h
  omega

theorem not_eight_dvd_card_thetaQuot {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) [(solvableRadical Y).Normal]
    (e : Y ⧸ solvableRadical Y ≃* projSL 2 (GaloisField 3 3)) :
    ¬ 8 ∣ Nat.card (Y ⧸ aschbacherSolvableCore 3 Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₁⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := Y) hq
  have hθ : aschbacherSolvableCore 3 (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ :=
    (theta_quotient_core_and_ranks (G := Y)).1
  have hZ : IsPGroup 3 (Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)) :=
    Sec10.Sec10XProof.isPGroup_center_of_theta_eq_bot hθ
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hquot : Nat.card ((Y ⧸ aschbacherSolvableCore 3 Y) ⧸
      Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)) = 9828 := by
    rw [Nat.card_congr (e₁.trans e).toEquiv, card_projSL_two_galoisField_three_three]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)), hquot, hk]
  intro h8
  have hcop : Nat.Coprime 8 (3 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have := hcop.dvd_of_dvd_mul_right h8
  norm_num at this

end L227

theorem pieceL227_holds (h131a : Item131a) : PieceL227 := by
  intro G _ _ A c L E F a b R Y hY hL
  haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨e₂⟩ := hL
  have hD : Sec13Data G F b Y := hY.hD
  have hq : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  refine L227.not_eight_dvd_card_thetaQuot hq e₂ ?_
  rcases h131a G F b Y hD with ⟨h, -⟩ | ⟨h, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
    h | ⟨-, h | h | h⟩
  · exact L227.eight_dvd_card_thetaQuot_of_dvd_lBarA hD
      (L227.eight_dvd_card_of_isZ3LThreePi h)
  · exact L227.eight_dvd_card_thetaQuot_of_dvd_lBarA hD
      (L227.eight_dvd_card_of_isZ3PGLThreePi h)
  · exact L227.eight_dvd_card_thetaQuot_of_dvd_lBarA hD
      (L227.eight_dvd_card_of_equiv_prod L227.eight_dvd_card_alternating_seven e)
  · exact L227.eight_dvd_card_thetaQuot_of_dvd_lBarA hD
      (L227.eight_dvd_card_of_equiv_prod L227.eight_dvd_card_M22 e)
  · exact L227.eight_dvd_card_thetaQuot_of_dvd_lBarA hD
      (L227.eight_dvd_card_of_equiv_prod L227.eight_dvd_card_M12 e)
  · exact L227.eight_dvd_card_thetaQuot_of_dvd_lBarA hD
      (L227.eight_dvd_card_of_equiv_prod L227.eight_dvd_card_J2 e)
  · exact L227.eight_dvd_card_thetaQuot_of_dvd_lBarA hD
      (L227.eight_dvd_card_of_isSLThreePiTwo h)
  · exact L227.eight_dvd_card_of_isSLThreePi h
  · exact L227.eight_dvd_card_of_isTripleCover L227.eight_dvd_card_alternating_seven h
  · exact L227.eight_dvd_card_of_isTripleCover L227.eight_dvd_card_M22 h

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
