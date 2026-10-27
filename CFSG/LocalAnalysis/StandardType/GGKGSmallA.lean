module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGKGOrd
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import all CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F

private theorem kgsa_two_adic {N a m b : ℕ} (hN : N = 2 ^ a * m) (hm : Odd m)
    (hb : 2 ^ b ∣ N) : b ≤ a := by
  rw [hN] at hb
  have hcop : Nat.Coprime (2 ^ b) m := Nat.Coprime.pow_left b (Odd.coprime_two_left hm)
  have h2 : 2 ^ b ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hb
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2

private theorem kgsa_odd_two_pow_sub_one {f : ℕ} (hf : 0 < f) : Odd (2 ^ f - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow
    (even_iff_two_dvd.mpr (dvd_pow_self 2 hf.ne')) odd_one

private theorem kgsa_odd_two_pow_add_one {f : ℕ} (hf : 0 < f) : Odd (2 ^ f + 1) :=
  Even.add_odd (even_iff_two_dvd.mpr (dvd_pow_self 2 hf.ne')) odd_one

private theorem kgsa_ordSuzuki_eq (n : ℕ) :
    ordSuzuki (2 ^ n) = 2 ^ (2 * n) * ((2 ^ (2 * n) + 1) * (2 ^ n - 1)) := by
  rw [ordSuzuki]
  have h : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm n 2]
  rw [h, mul_assoc]

private theorem kgsa_ordG2_eq (n : ℕ) :
    ordG2 (2 ^ n) = 2 ^ (6 * n) * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) := by
  rw [ordG2]
  have h6 : (2 ^ n) ^ 6 = 2 ^ (6 * n) := by rw [← pow_mul, Nat.mul_comm n 6]
  have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm n 2]
  rw [h6, h2, mul_assoc]

private theorem kgsa_g2der_eq {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hg : lab.tag = .G2der) : lab = ⟨.G2der, 0, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hg
  subst hg
  simp only [LargeEvenInLambda2] at hl
  obtain ⟨-, hr, hn⟩ := hl
  subst hr hn
  rfl

theorem kgSmallA_holds :
    KGSimpleOn fun lab : GLALabel =>
      lab.tag = .twB2 ∨ lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der := by
  intro p hp hp2 S _ _ lab α K hFam hlab hcen hin hαp hα1 hK k f hk hlabK
  exfalso
  have hS : HasLabel S (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hM : MarkedModel lab (S ⧸ Subgroup.center S) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨labJ, hJlam, hJdvd, hJhas⟩ :=
    CFSG.StandardType.TCJ.tcjSimple_holds p hp hp2 S lab α K hlab hcen hin hαp hK
  have hrigid := kg_rigid_C hk hlabK hJlam hJhas
  have hnf : lab.n ∣ f := by rw [← hrigid.2.2]; exact hJdvd
  have hn1 : 1 ≤ lab.n := hlab.1
  have hf1 : 1 ≤ f := (kg_inLambda2_C hk hlabK).1
  have hnlef : lab.n ≤ f := Nat.le_of_dvd (by omega) hnf
  have hcardSbot : Nat.card S = Nat.card (S ⧸ Subgroup.center S) := by
    rw [hcen]
    exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm
  rcases hFam with htwB2 | hG2 | hG2der | htwF4der
  ·
    have hE : IsExcLab lab := by simp [IsExcLab, htwB2]
    have hLM := lieModel_of_mark_two hM (markChar_two_of_exc hE)
    have hcardZ : Nat.card (S ⧸ Subgroup.center S) = ordSuzuki (2 ^ lab.n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hLM,
        evenLieOrder_of_excLab hlab hE, htwB2]
      rfl
    have hdvdK : 2 ^ (f * k ^ 2) ∣ Nat.card (K ⧸ Subgroup.center K) := by
      rw [kg_card_BC (lab := ⟨.C, k, f⟩) (kg_inLambda2_C hk hlabK) (Or.inr rfl) hlabK]
      exact dvd_mul_right _ _
    have hdvdS : 2 ^ (f * k ^ 2) ∣ Nat.card S :=
      hdvdK.trans ((Subgroup.card_quotient_dvd_card (Subgroup.center K)).trans
        (Subgroup.card_subgroup_dvd_card K))
    have hN : Nat.card S =
        2 ^ (2 * lab.n) * ((2 ^ (2 * lab.n) + 1) * (2 ^ lab.n - 1)) := by
      rw [hcardSbot, hcardZ, kgsa_ordSuzuki_eq]
    have hodd : Odd ((2 ^ (2 * lab.n) + 1) * (2 ^ lab.n - 1)) :=
      (kgsa_odd_two_pow_add_one (by omega)).mul (kgsa_odd_two_pow_sub_one (by omega))
    have hb := kgsa_two_adic hN hodd hdvdS
    have hk2 : 9 ≤ k ^ 2 := by
      have h := Nat.pow_le_pow_left hk 2
      norm_num at h
      exact h
    have h9 : lab.n * 9 ≤ f * k ^ 2 := Nat.mul_le_mul hnlef hk2
    omega
  ·
    have hE : IsExcLab lab := by simp [IsExcLab, hG2]
    have hLM := lieModel_of_mark_two hM (markChar_two_of_exc hE)
    have hcardZ : Nat.card (S ⧸ Subgroup.center S) = ordG2 (2 ^ lab.n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hLM,
        evenLieOrder_of_excLab hlab hE, hG2]
      rfl
    have hdvdK : 2 ^ (f * k ^ 2) ∣ Nat.card (K ⧸ Subgroup.center K) := by
      rw [kg_card_BC (lab := ⟨.C, k, f⟩) (kg_inLambda2_C hk hlabK) (Or.inr rfl) hlabK]
      exact dvd_mul_right _ _
    have hdvdS : 2 ^ (f * k ^ 2) ∣ Nat.card S :=
      hdvdK.trans ((Subgroup.card_quotient_dvd_card (Subgroup.center K)).trans
        (Subgroup.card_subgroup_dvd_card K))
    have hN : Nat.card S =
        2 ^ (6 * lab.n) * ((2 ^ (6 * lab.n) - 1) * (2 ^ (2 * lab.n) - 1)) := by
      rw [hcardSbot, hcardZ, kgsa_ordG2_eq]
    have hodd : Odd ((2 ^ (6 * lab.n) - 1) * (2 ^ (2 * lab.n) - 1)) :=
      (kgsa_odd_two_pow_sub_one (by omega)).mul (kgsa_odd_two_pow_sub_one (by omega))
    have hb := kgsa_two_adic hN hodd hdvdS
    have hk2 : 9 ≤ k ^ 2 := by
      have h := Nat.pow_le_pow_left hk 2
      norm_num at h
      exact h
    have h9 : lab.n * 9 ≤ f * k ^ 2 := Nat.mul_le_mul hnlef hk2
    omega
  ·
    have hlab_eq : lab = ⟨.G2der, 0, 1⟩ := kgsa_g2der_eq hlab hG2der
    have hM' : MarkedModel (⟨.G2der, 0, 1⟩ : LargeEvenLabel) (S ⧸ Subgroup.center S) := by
      simpa [hlab_eq] using hM
    have hcardZ : Nat.card (S ⧸ Subgroup.center S) = 6048 := card_of_G2der hM'
    have h5K : 5 ∣ Nat.card (K ⧸ Subgroup.center K) := kg_five_dvd_card_C hk hlabK
    have h5S : 5 ∣ Nat.card S :=
      h5K.trans ((Subgroup.card_quotient_dvd_card (Subgroup.center K)).trans
        (Subgroup.card_subgroup_dvd_card K))
    have h5Z : 5 ∣ Nat.card (S ⧸ Subgroup.center S) := by rwa [hcardSbot] at h5S
    rw [hcardZ] at h5Z
    norm_num at h5Z
  ·
    have hE : IsExcLab lab := by simp [IsExcLab, htwF4der]
    have hLM := lieModel_of_mark_two hM (markChar_two_of_exc hE)
    have hcardZ : Nat.card (S ⧸ Subgroup.center S) = ordTits := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hLM,
        evenLieOrder_of_excLab hlab hE, htwF4der]
      rfl
    have h7K : 7 ∣ Nat.card (K ⧸ Subgroup.center K) := kg_seven_dvd_card_C hk hlabK
    have h7S : 7 ∣ Nat.card S :=
      h7K.trans ((Subgroup.card_quotient_dvd_card (Subgroup.center K)).trans
        (Subgroup.card_subgroup_dvd_card K))
    have h7Z : 7 ∣ Nat.card (S ⧸ Subgroup.center S) := by rwa [hcardSbot] at h7S
    rw [hcardZ] at h7Z
    rw [ordTits] at h7Z
    exact absurd h7Z (by decide)

end CFSG.StandardType.KG
