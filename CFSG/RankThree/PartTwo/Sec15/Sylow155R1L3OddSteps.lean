module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res5ProofNorm
public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofLA7
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofRead
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem mem_scriptY4_L_of_not22 (h135 : Item135Simple) (h142 : Concl142R) (h138 : Item138N)
    (hgen : KS1517Gen) (h : Sec15R G A c L) {Y : Subgroup G} (hctx : Ctx1514 A (lB A) c L Y)
    (h22 : ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2) :
    L ∈ scriptY4 A (lB A) := by
  obtain ⟨p, e, hp, he, hiso, hprod, -⟩ := hctx.concl1515
  have hLc := h.mem_thetaComponentsAt
  have hsimp := Proof1514.isSimpleGroup_of_isoLThreePi hLc he hiso
  have hperf : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc).1
  obtain ⟨hAbE, hAb9⟩ := Proof1517.isElemAbelian_card_aBar h hctx
  have hgL := Proof1517.le_sSup_of_gen h hctx (hgen _ p e he hiso hperf
    (not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he hiso hprod) h22 _ hAbE hAb9)
  have hLΔ := Proof1517.le_delta_of_le_sSup h142 h hgL
  obtain ⟨-, h9, -⟩ := Proof1517.point_facts h hctx
  have h3 : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  refine ⟨⟨fun htop => ?_, h.le_normalizer⟩,
    Sec16.eq_oPrimeResidualOf_of_isSimpleGroup (Sec6.isPerfect_of_mem_thetaComponentsAt hLc)
      hsimp h3,
    le_antisymm hLΔ (delta_le L), h135 G A c L h.toSec13Data (Or.inl ⟨p, e, hp, he, hiso⟩)⟩
  refine centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian h.toSec13Data.ne_one ?_
  rw [eq_top_iff, ← htop]
  exact h.toSec13Data.le_centralizer

theorem step1517Y0_at (h135 : Item135Simple) (h142 : Concl142R) (h138 : Item138N)
    (hgen : KS1517Gen) (h152 : Item152 A (lB A)) (h : Sec15R G A c L)
    (h22 : ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2) {Y : Subgroup G}
    (hctx : Ctx1514 A (lB A) c L Y) :
    ∀ X ∈ scriptY2 A, L ≤ X → ∃ Y₀ ∈ scriptY0Star A (lB A), L ≤ Y₀ := by
  intro X hX hLX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL4 := mem_scriptY4_L_of_not22 h135 h142 h138 hgen h hctx h22
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) with hM
  have hM2 : M ∈ scriptY2 A :=
    Sec16.normalizer_pCoreOf_mem_scriptY2 h.isSimpleGroup h.nonabelian hX
  have hLM : L ≤ M := hLX.trans (Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX.2
  have hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hloc)
  obtain ⟨J, -, hLJ, hJ0⟩ := h152 L hL4 M hM2 hLM hF
  obtain ⟨Y₀, hJY₀, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hJ0
  exact ⟨Y₀, hY₀, hLJ.trans hJY₀⟩

theorem step1517Con_at (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) (hq0 : Step1517Q0) (h : Sec15R G A c L) {Y : Subgroup G}
    (hctx : Ctx1514 A (lB A) c L Y) :
    ∀ Y₀ ∈ scriptY0Star A (lB A), Y₀ ≠ Y → ¬ L ≤ Y₀ := by
  intro Y₀ hY₀ _ hLY₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, hS₀Y₀⟩ := Sec16.exists_qStar_le_normalizer h153 hobs hY₀
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hOQ : O ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hq0 G A c L h Y hctx, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two O).mpr hO2⟩
  obtain ⟨w, hw, hOw⟩ := Sec16.exists_conj_le_normalizer h1411 hS₀ hS₀Y₀ hOQ
  set Y₁ := Y₀.map (MulAut.conj w).toMonoidHom with hY₁def
  have hY₁ : Y₁ ∈ scriptY0Star A (lB A) := Sec16.map_conj_mem_scriptY0Star hw hY₀
  obtain ⟨-, -, -, -, -, -, hYL, -, hΩ⟩ := hctx.concl1515
  obtain ⟨-, h9, -⟩ := Proof1517.point_facts h hctx
  have h3 : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3 (normalizer_le_of_omegaA_eq hΩ hw)
  have hLY₁ : L ≤ Y₁ := by
    rw [← Late.map_conj_eq_of_mem_normalizer hwL, hY₁def]
    exact Subgroup.map_mono hLY₀
  have hYN : Y ≤ Subgroup.normalizer (Y₁ : Set G) := by
    rw [hYL]
    exact sup_le (inf_le_left.trans (hLY₁.trans Subgroup.le_normalizer)) hOw
  have hYY₁ : Y ≤ Y₁ :=
    Proof1517.le_of_le_normalizer_of_cover hctx.mem_y0Star.prop.1.2.1 hYL hLY₁ hYN
  have hYeq : Y = Y₁ := hctx.mem_y0Star.eq_of_le hY₁.prop hYY₁
  exact hctx.not_le (hYeq ▸ hLY₁)

theorem step1517_at (h135 : Item135Simple) (h142 : Concl142R) (h138 : Item138N)
    (hgen : KS1517Gen) (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A))
    (hobs : Claim153Obs A (lB A)) (h1411 : Item1411_1 A (lB A)) (hq0 : Step1517Q0)
    (hsimp : Step1517Simple) (h : Sec15R G A c L)
    (h22 : ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2) :
    Step1517 A (lB A) c L := by
  intro Y hctx
  have hno : ∀ X ∈ scriptY2 A, ¬ L ≤ X := by
    intro X hX hLX
    obtain ⟨Y₀, hY₀, hLY₀⟩ := step1517Y0_at h135 h142 h138 hgen h152 h h22 hctx X hX hLX
    by_cases hYY : Y₀ = Y
    · exact hctx.not_le (hYY ▸ hLY₀)
    · exact step1517Con_at h153 hobs h1411 hq0 h hctx Y₀ hY₀ hYY hLY₀
  exact ⟨hno, hsimp G A c L h Y hctx hno⟩

theorem step1516_at (h : Sec15R G A c L) (h153 : Item153Main A (lB A))
    (hobs : Claim153Obs A (lB A)) (h149 : Item149 A (lB A)) (h1411 : Item1411_1 A (lB A))
    (hloc : Claim1411Local A (lB A)) : Step1516 A (lB A) c L := by
  intro Y hctx
  obtain ⟨-, -, -, -, -, -, -, -, hΩ⟩ := hctx.concl1515
  exact Proof1515Res.step1516_of_mem h h153 hobs h149 h1411 hloc hctx.mem_y0Star hΩ

theorem step1518_at (h1516 : Step1516 A (lB A) c L) (h1517 : Step1517 A (lB A) c L)
    (hTL : Step1518TL) (hN : KS1518Norm) (h : Sec15R G A c L) : Step1518 A (lB A) c L := by
  intro Y hctx p e _ he hiso
  by_contra hp2
  obtain ⟨hno, hs, -⟩ := h1517 Y hctx
  obtain ⟨he2, hLY⟩ := step1518Read G A c L h Y hctx hno hs p e he hiso hp2
  subst he2
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)))
    (Proof1514.bot_mem_scriptQPi_two A (lB A) _)
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hS.prop.1.2
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hT := h1516 Y hctx S hS
  have hTY := hTL G A c L h Y hctx hno hs p 2 he hiso hp2 _ hT
  apply hTY
  have hθ := Proof1520.theta_eq_bot_of_isSimpleGroup h.mem_thetaComponentsAt hs
  have hisoL : Sec4.IsoLThreePi ↥L p 2 := Proof1520.isoLThreePi_of_theta_eq_bot hθ hiso
  have hM : IsLThreeEpsAt ↥((L ⊓ Y).subgroupOf L) p 1 :=
    IsLThreeEpsAt.of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm hLY
  have hT2 : IsPGroup 2 ↥(S ⊓ H) := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hT.prop.2
  have hU2 : IsPGroup 2 ↥((S ⊓ H ⊓ L).subgroupOf L) :=
    (hT2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hUN : (S ⊓ H ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (((L ⊓ Y).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxY : (x : G) ∈ Subgroup.normalizer (Y : Set G) := hSY hx.1.1
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨-, hyY⟩
      exact ⟨(x * y * x⁻¹).2, (Subgroup.mem_normalizer_iff.mp hxY y).mp hyY⟩
    · rintro ⟨-, hyY⟩
      exact ⟨y.2, (Subgroup.mem_normalizer_iff.mp hxY y).mpr hyY⟩
  have hle := hN ↥L p hp2 hisoL ((L ⊓ Y).subgroupOf L) hM ((S ⊓ H ⊓ L).subgroupOf L) hU2 hUN
  intro z hz
  have hzL : z ∈ L := hz.2
  have hz' : (⟨z, hzL⟩ : ↥L) ∈ (S ⊓ H ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hz
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hle hz'))).2

theorem not_isoLThreePi_two_two_of_ne_two {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) : ¬ Sec4.IsoLThreePi X 2 2 := by
  intro h22
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := Sec19.Step1917EqProof.eq_of_isoLThreePi he (by norm_num) hiso h22
  have hp : p.Prime := Fact.out
  have h2 : 2 ∣ p ^ e := by rw [hq]; norm_num
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd
