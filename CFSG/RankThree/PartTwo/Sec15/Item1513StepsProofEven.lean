module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1511Meta
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511 CFSG.RankThree.PartTwo.Sec15.Proof1513

@[expose] noncomputable def Step1513EvenType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Ctx1513 G A c L a K →
      ∀ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 →
        Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9 →
        (∀ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ → w ∉ Subgroup.normalizer (T : Set G)) →
          (∃ m : ℕ, 1 ≤ m ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m) ∧
            ∃ m : ℕ, 1 ≤ m ∧ Sec4.IsoLThreePi (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 m

@[expose] noncomputable def Step1513EvenTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ 2 ∣ Nat.card (xA A) →
      ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      (∃ m : ℕ, 1 ≤ m ∧ Sec4.IsoLThreePi (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) 2 m) →
        TransOn A (lB A) (xA A) (Subgroup.centralizer ({b} : Set G))

namespace Proof1513Steps

variable {G : Type} [Group G] [Finite G]

theorem not_two_dvd_card_xA {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hw3 : w ^ 3 = 1)
    (hT : ∀ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ → w ∉ Subgroup.normalizer (T : Set G)) :
    ¬ 2 ∣ Nat.card (xA A) := by
  intro h2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set X := xA A with hX
  have hX3 : ¬ 3 ∣ Nat.card X :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hA3 : IsPGroup 3 A := isPGroup_of_sec13Data hD
  set R := Subgroup.zpowers w ⊔ A with hR
  have hR3 : IsPGroup 3 R := IsPGroup.to_sup_of_normal_right'
    (isPGroup_zpowers_of_pow_three hw3) hA3 (Subgroup.zpowers_le.mpr hwA)
  have hAW : A ≤ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer
  have hRX : R ≤ Subgroup.normalizer (X : Set G) :=
    (sup_le (Subgroup.zpowers_le.mpr hwA) hAW).trans (normalizer_le_normalizer_xA A)
  obtain ⟨S, hS, -, hRS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hR3 hX3 hRX bot_le IsPGroup.of_bot
    (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun y => by simp)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
  have hS1 : S ≠ ⊥ := by
    intro hS0
    have hxp : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
    have h1 := hS.2.2 (Subgroup.zpowers (x : G)) (Subgroup.zpowers_le.mpr x.2) hxp
      (by rw [hS0]; exact bot_le)
    have hx1 : (x : G) = 1 := by
      have := Subgroup.mem_zpowers (x : G)
      rw [h1, hS0, Subgroup.mem_bot] at this
      exact this
    have : orderOf x = 1 := by rw [← Subgroup.orderOf_coe, hx1, orderOf_one]
    omega
  have hSX : S ≤ X := hS.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := le_sup_right.trans hRS
  have hS3 : ¬ 3 ∣ Nat.card S := fun h3 => hX3 (h3.trans (Subgroup.card_dvd_of_le hSX))
  have hSQ : S ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three S).mpr hS3, hAS⟩,
      fun B _ => (inf_le_left.trans hSX).trans (le_sup_right.trans le_sup_left)⟩, le_top⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS.2.1⟩
  exact hT S hSQ hS1 (hRS (Subgroup.mem_sup_left (Subgroup.mem_zpowers w)))


theorem ctx1513_point (h131 : Item131) (h133 : Item133) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) {A L K : Subgroup G} {c a : G} (hctx : Ctx1513 G A c L a K)
    {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) (hbc : Subgroup.zpowers b ≠ Subgroup.zpowers c)
    {Lb : Subgroup G} (hLb : Lb ∈ lA A b) : Ctx1513 G A c L b Lb := by
  have h := hctx.toSec15R
  have hDb := (sec15R_point h hb hLb).toSec13Data
  obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  have htype : Sec8.IsZ3PGLThreePi (lBarA b Lb A) ∨
      Nonempty (lBarA b Lb A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) := by
    rcases type_of_point h133 h hctx.irreducible hctx.card_inf hctx.normalizer_le hb hbc hLb with
      h1 | h1 | ⟨⟨φ⟩⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hDb hJ2p hJ2z φ
      exact ((not_j2_of_irreducible h131 h134 h48 h415 h hctx.irreducible hctx.card_inf hb
        hLb).false ψ).elim
  exact ⟨h, hctx.scriptY0_nonempty, hctx.irreducible, hctx.card_inf, hctx.normalizer_le, hb, hbc,
    hLb, htype⟩

theorem false_of_acts (h131 : Item131) (hnt : Step1513NoTransv) (hmeets : Step1513Meets)
    (hmax : Step1513Max) {A L K : Subgroup G} {c a : G} (hctx : Ctx1513 G A c L a K)
    (h1511 : Item1511Star A (lB A) c L) (h1411 : Item1411_1 A (lB A))
    (h153 : Item153Main A (lB A)) (hnorm : Claim153Normal A (lB A)) {w : G}
    (hwKW : w ∈ K ⊓ Subgroup.normalizer (A : Set G)) (hw3 : w ^ 3 = 1)
    (hwC9 : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9)
    (hT : ∃ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ ∧ w ∈ Subgroup.normalizer (T : Set G)) :
    False := by
  have h := hctx.toSec15R
  have hD := h.toSec13Data
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hwKW.2
  have hWH := hctx.normalizer_le
  have hwC : w ∉ Subgroup.centralizer (A : Set G) := by
    intro hwc
    have hAC : A ⊓ Subgroup.centralizer ({w} : Set G) = A := inf_of_le_left fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwc x hx)
    rw [hAC, hD.card_eq] at hwC9
    norm_num at hwC9
  obtain ⟨-, htypes⟩ := cases_of_irreducible h131 h hctx.card_inf hctx.irreducible
  obtain ⟨p, e, hp, he, hL3⟩ : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rcases htypes with h1 | h1 | h1
    · exact h1
    · exact (hnt G A c L h (Or.inr h1) w ⟨hWH hwA, hwA⟩ hw3 hwC9).elim
    · exact (hnt G A c L h (Or.inl h1) w ⟨hWH hwA, hwA⟩ hw3 hwC9).elim
  obtain ⟨Y₁, hY₁⟩ := hctx.scriptY0_nonempty
  obtain ⟨Y, -, hY⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hY₁
  have hYmeet := hmeets G A c L a K hctx Y hY
  obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_S0 h153 hnorm hY
  obtain ⟨S, hS, hwS⟩ := hmax G A c L a K hctx w hwKW hw3 hwC9 hT
  obtain ⟨u, ⟨huA, -⟩, hSu⟩ := h1411 S hS S₀ hS₀
  set w' := u * w * u⁻¹ with hw'
  have hw'A : w' ∈ Subgroup.normalizer (A : Set G) := mul_mem (mul_mem huA hwA) (inv_mem huA)
  have hwS' : S.map (MulAut.conj w).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hwS
  have hw'S : w' ∈ Subgroup.normalizer (S₀ : Set G) := by
    have h1 : S₀.map (MulAut.conj w').toMonoidHom = S₀ := by
      rw [hSu, Late.map_conj_map_conj, hw',
        show u * w * u⁻¹ * u = u * w by group, ← Late.map_conj_map_conj, hwS']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hw'3 : w' ^ 3 = 1 := by rw [hw', conj_pow, hw3, mul_one, mul_inv_cancel]
  have hw'C : w' ∉ Subgroup.centralizer (A : Set G) := by
    intro hw'c
    apply hwC
    have h1 : w = u⁻¹ * w' * u⁻¹⁻¹ := by rw [hw']; group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_centralizer A (inv_mem huA)) w').mp hw'c
  exact false_of_mem_normalizer_Y h h1511 he hL3 hWH hY hYmeet hw'A
    (hS₀Y (mem_normalizer_sup hw'A hw'S)) hw'3 hw'C

theorem type_two_of_point (h131 : Item131) (h133 : Item133) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hnt : Step1513NoTransv) (htv : Step1513Transv)
    (hmeets : Step1513Meets) (hmax : Step1513Max) (htype : Step1513EvenType)
    {A L K : Subgroup G} {c a : G} (hctx : Ctx1513 G A c L a K)
    (h1511 : Item1511Star A (lB A) c L) (h1411 : Item1411_1 A (lB A))
    (h153 : Item153Main A (lB A)) (hnorm : Claim153Normal A (lB A)) {w : G}
    (hwKW : w ∈ K ⊓ Subgroup.normalizer (A : Set G)) (hw3 : w ^ 3 = 1)
    (hwC9 : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9)
    (hT : ∀ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ → w ∉ Subgroup.normalizer (T : Set G))
    {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) {Lb : Subgroup G} (hLb : Lb ∈ lA A b) :
    ∃ m : ℕ, 1 ≤ m ∧ Sec4.IsoLThreePi (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) 2 m := by
  have h := hctx.toSec15R
  have hD := h.toSec13Data
  by_cases hbc : Subgroup.zpowers b = Subgroup.zpowers c
  ·
    have hLbc : Lb ∈ lA A c := lA_eq_of_zpowers_eq hbc ▸ hLb
    obtain ⟨f, hfA, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers
      hctx.card_inf
    have hLbL : Lb = L := eq_of_mem_lA_of_mem hD.mem_thetaComponentsAt hLbc hfA hfL hfc
    rw [hLbL]
    exact (htype _ A c L a K hctx w hwKW hw3 hwC9 hT).1
  · have hctxb := ctx1513_point h131 h133 h134 h48 h415 hctx hb hbc hLb
    obtain ⟨wb, hwbKW, hwb3, hwbC9⟩ := htv _ A c L b Lb hctxb
    by_cases hTb : ∃ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ ∧
        wb ∈ Subgroup.normalizer (T : Set G)
    · exact (false_of_acts h131 hnt hmeets hmax hctxb h1511 h1411 h153 hnorm hwbKW hwb3 hwbC9
        hTb).elim
    · push Not at hTb
      exact (htype _ A c L b Lb hctxb wb hwbKW hwb3 hwbC9 hTb).2

end Proof1513Steps

open Proof1513Steps

theorem step1513Even_of
    (h131 : Item131) (h133 : Item133) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hset : Item13SetupAt)
    (hnt : Step1513NoTransv) (htv : Step1513Transv) (hmeets : Step1513Meets)
    (hmax : Step1513Max) (h1511 : Item1511StarR) (h1411 : Item1411_1R) (h153 : Item153MainR)
    (hnorm : Claim153NormalR) (htype : Step1513EvenType) (htrans : Step1513EvenTrans) :
    Step1513Even := by
  intro G _ _ A c L a K hctx w hwKW hw3 hwC9 hT b hb
  have h := hctx.toSec15R
  obtain ⟨Lb, hLb⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
    h.not_mem_partTwoT b hb
  exact htrans G A c L h (not_two_dvd_card_xA h hwKW.2 hw3 hT) b Lb hb hLb
    (type_two_of_point h131 h133 h134 h48 h415 hnt htv hmeets hmax htype hctx (h1511 G A c L h)
      (h1411 G A c L h) (h153 G A c L h) (hnorm G A c L h) hwKW hw3 hwC9 hT hb hLb)

end CFSG.RankThree.PartTwo.Sec15
