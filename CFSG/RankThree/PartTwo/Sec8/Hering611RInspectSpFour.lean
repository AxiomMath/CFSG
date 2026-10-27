module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectBridge
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSixSp
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectA6

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.RankThree.PartTwo.Sec8

theorem false_of_inner_sp4 {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    [CharP F 2] (ψ : X ≃* StatedSp 2 F) {P : Subgroup X} (hP : IsA6Sub P) {g : X}
    (hg3 : g ^ 3 = 1) (hgP : ∀ p ∈ P, p * g = g * p) (hg1 : g ≠ 1) : False := by
  obtain ⟨R, hRP, hR, hR9, -⟩ := hP.exists_elemAbelian_nine
  have hgR : g ∉ R := fun hgR =>
    hg1 (hP.eq_one_of_commute (hRP hgR) hgP
      (by rw [show 9 = 3 * 3 from rfl, pow_mul, hg3, one_pow]))
  obtain ⟨hF, hFcard⟩ := Sec6.isElemAbelian_sup_zpowers_three hR hgR hg3
    (fun k hk => hgP k (hRP hk))
  have hle := Sec19.Item19Res2Proof.card_le_nine_of_elemAbelian_sp4
    (Sec4.isElemAbelian_map ψ.toMonoidHom hF)
  rw [Subgroup.card_map_of_injective ψ.injective, hFcard, hR9] at hle
  omega

section Main


theorem spFour611 {G : Type} [Group G] [Finite G] {K : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    {n : ℕ} (hn : Odd n) (φ : K ⧸ aschbacherSolvableCore 3 K ≃* projSp 2 (GaloisField 2 n))
    (hA6 : HasA6Cent K c) :
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSp 2 (GaloisField 2 3)) ∧
      KFacts.InducesStdKind K c .field := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero n := ⟨hn.pos.ne'⟩
  obtain ⟨hcN, hα3, hα1, P, hP, ⟨e6⟩⟩ := hA6
  have hPsub : IsA6Sub P := ⟨isPerfect_of_mem_thetaComponentsIn hP, ⟨e6⟩⟩
  set α := Item426.thetaAut K hcN with hα
  have hPC : P ≤ Item426.fixSub α := le_of_mem_thetaComponentsIn hP
  by_cases hin : KFacts.IsInnerAut α
  ·
    exfalso
    obtain ⟨g, hg⟩ := hin
    let ψ : K ⧸ aschbacherSolvableCore 3 K ≃* StatedSp 2 (GaloisField 2 n) :=
      φ.trans (KFacts.statedSpEquivProjSpOfCharTwo (GaloisField 2 n)).symm
    have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ := by
      have h := CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := GaloisField 2 n)
        (by norm_num : 1 ≤ 2)
      rw [eq_bot_iff]
      intro z hz
      have hz' : ψ z ∈ Subgroup.center (StatedSp 2 (GaloisField 2 n)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := (Subgroup.mem_center_iff.mp hz) (ψ.symm y)
        calc y * ψ z = ψ (ψ.symm y * z) := by simp
          _ = ψ (z * ψ.symm y) := by rw [this]
          _ = ψ z * y := by simp
      rw [h, Subgroup.mem_bot] at hz'
      exact Subgroup.mem_bot.mpr (ψ.injective (by rw [hz', map_one]))
    have hg3 : g ^ 3 = 1 := by
      have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, hg, hα3]
      have h2 : g ^ 3 ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := congrArg (fun γ : MulAut (K ⧸ aschbacherSolvableCore 3 K) => γ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc y * g ^ 3 = g ^ 3 * y * (g ^ 3)⁻¹ * g ^ 3 := by rw [this]
          _ = g ^ 3 * y := by group
      rwa [hZ, Subgroup.mem_bot] at h2
    have hg1 : g ≠ 1 := by
      rintro rfl
      apply hα1
      rw [← hg, map_one]
    have hgP : ∀ p ∈ P, p * g = g * p := by
      intro p hp
      have h1 : α p = p := hPC hp
      rw [← hg, MulAut.conj_apply] at h1
      calc p * g = g * p * g⁻¹ * g := by rw [h1]
        _ = g * p := by group
    exact false_of_inner_sp4 ψ hPsub hg3 hgP hg1
  ·
    have hout : InducesOuterTheta c K := ⟨hcN, hin⟩
    have key : ∃ k, n = 3 * k := by
      let e : K ⧸ aschbacherSolvableCore 3 K ≃* StatedProj (StatedSp 2 (GaloisField 2 n)) :=
        φ.trans (PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))
      obtain ⟨-, σ, -, hcardσ, -⟩ := KFacts.exists_barCentralizer_mulEquiv_sp4 hc3 hout e
      have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn.pos.ne'
      have hdvd : Nat.card (GH74.GLS.IVK.fixedField σ) ∣ 2 ^ n := by
        rw [← hFcard, ← hcardσ]
        exact dvd_pow_self _ (by norm_num)
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      refine ⟨k, ?_⟩
      have h1 : (2 ^ k) ^ 3 = 2 ^ n := by rw [← hk, hcardσ, hFcard]
      rw [← pow_mul] at h1
      have := Nat.pow_right_injective (le_refl 2) h1
      omega
    obtain ⟨k, rfl⟩ := key
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := hn.pos
      omega
    obtain ⟨hfield, ⟨eC⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp hk0 hc3 hout ⟨φ⟩
    by_cases hk1 : k = 1
    · subst hk1
      exact ⟨⟨φ⟩, hfield⟩
    · exfalso
      have hk2 : 2 ≤ k := by omega
      haveI hsimp := Sec8.Hering418.isSimpleGroup_projSp_two hk2
      have hbar : Sec8.barCentralizer (Subgroup.zpowers c) K = Item426.fixSub α := by
        ext y
        rw [KFacts.mem_barCentralizer_zpowers_iff hcN y]
        exact Iff.rfl
      let eF : Item426.fixSub α ≃* projSp 2 (GaloisField 2 k) :=
        (MulEquiv.subgroupCongr hbar).symm.trans eC
      haveI : IsSimpleGroup ↥(Item426.fixSub α) := eF.isSimpleGroup
      have hsn : (P.subgroupOf (Item426.fixSub α)).IsSubnormal :=
        (mem_thetaComponentsIn_iff.mp hP).2.2.1
      have hPbot : P ≠ ⊥ := hPsub.ne_bot
      have htop : P.subgroupOf (Item426.fixSub α) = ⊤ := by
        rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsn with hb | ht
        · exact absurd ((Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hPC) hPbot
        · exact ht
      have hPeq : P = Item426.fixSub α :=
        le_antisymm hPC (Subgroup.subgroupOf_eq_top.mp htop)
      haveI hPsimple : IsSimpleGroup ↥P := (MulEquiv.subgroupCongr hPeq).isSimpleGroup
      have hP360 : Nat.card P = 360 := hPsub.card_eq_of_isSimpleGroup
      have hPC2 : Nat.card P = Nat.card (projSp 2 (GaloisField 2 k)) := by
        rw [Nat.card_congr (MulEquiv.subgroupCongr hPeq).toEquiv, Nat.card_congr eF.toEquiv]
      have hcardK : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k hk0
      rw [PGLModel.card_projSp_of_charTwo, hcardK,
        show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from by decide,
        Finset.prod_pair (by norm_num)] at hPC2
      have hq4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      generalize 2 ^ k = q at hq4 hPC2
      have h2 : 16 ≤ q ^ 2 := by nlinarith
      have h4 : 256 ≤ q ^ 4 := by nlinarith
      have h2' : 15 ≤ q ^ (2 * 1) - 1 := by simp; omega
      have h4' : 255 ≤ q ^ (2 * 2) - 1 := by
        have : q ^ (2 * 2) = q ^ 4 := by norm_num
        omega
      have hbig : 360 < q ^ (2 ^ 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) := by
        calc 360 < 256 * (15 * 255) := by norm_num
          _ ≤ q ^ (2 ^ 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) :=
            Nat.mul_le_mul (by norm_num [h4]) (Nat.mul_le_mul h2' h4')
      omega

end Main

end CFSG.RankThree.PartTwo.Sec8.Hering611R
