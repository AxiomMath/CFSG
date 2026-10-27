module

public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofTools
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Item1511Meta
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec15.Item1510ProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Late.Transitivity
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511 CFSG.RankThree.PartTwo.Sec15.Proof1513
open CFSG.Assembly.RankThreeEven (projSL projSU)

structure Ctx1513 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (K : Subgroup G) : Prop extends Sec15R G A c L where
  scriptY0_nonempty : (scriptY0 A (lB A)).Nonempty
  irreducible : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L))
  card_inf : Nat.card (A ⊓ L : Subgroup G) = 9
  normalizer_le :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  zpowers_a_mem : Subgroup.zpowers a ∈ omegaA A
  zpowers_a_ne : Subgroup.zpowers a ≠ Subgroup.zpowers c
  mem_lA_a : K ∈ lA A a
  type_a : Sec8.IsZ3PGLThreePi (lBarA a K A) ∨
    Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12)

@[expose] noncomputable def Step1513HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Sec15R G A c L → (scriptY0 A (lB A)).Nonempty →
    Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) →
    Nat.card (A ⊓ L : Subgroup G) = 9 →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Subgroup.zpowers a ∈ omegaA A → Subgroup.zpowers a ≠ Subgroup.zpowers c → K ∈ lA A a →
      IsEmpty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)

@[expose] noncomputable def Step1513Meets : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Ctx1513 G A c L a K →
      ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y

@[expose] noncomputable def Step1513Transv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Ctx1513 G A c L a K →
      ∃ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 ∧
        Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9

@[expose] noncomputable def Step1513NoTransv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) →
      ∀ w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G),
        w ^ 3 = 1 → Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) ≠ 9

@[expose] noncomputable def Step1513Max : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Ctx1513 G A c L a K →
      ∀ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 →
        Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9 →
        (∃ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ ∧ w ∈ Subgroup.normalizer (T : Set G)) →
          ∃ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), w ∈ Subgroup.normalizer (S : Set G)

@[expose] noncomputable def Step1513Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Ctx1513 G A c L a K →
      ∀ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 →
        Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9 →
        (∀ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ → w ∉ Subgroup.normalizer (T : Set G)) →
          ∀ b : G, Subgroup.zpowers b ∈ omegaA A →
            TransOn A (lB A) (xA A) (Subgroup.centralizer ({b} : Set G))

section Proof


variable {G : Type} [Group G] [Finite G]

namespace Proof1513

theorem false_of_normalizer_le (h133 : Item133) (hset : Item13SetupAt) (hHJ : Step1513HJ)
    (hmeets : Step1513Meets) (htv : Step1513Transv) (hnt : Step1513NoTransv)
    (hmax : Step1513Max) (heven : Step1513Even) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h1511 : Item1511Star A (lB A) c L) (h1411 : Item1411_1 A (lB A))
    (hloc : Claim1411Local A (lB A)) (h153 : Item153Main A (lB A))
    (hnorm : Claim153Normal A (lB A)) (hY0 : (scriptY0 A (lB A)).Nonempty)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hne : omegaA A ≠ {Subgroup.zpowers c})
    (htypes : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    False := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨a, ha, hac⟩ : ∃ a : G, Subgroup.zpowers a ∈ omegaA A ∧
      Subgroup.zpowers a ≠ Subgroup.zpowers c := by
    by_contra hall
    push Not at hall
    apply hne
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨h.zpowers_mem_omegaA, fun F hF => ?_⟩
    obtain ⟨-, -, b, hb, -⟩ := id hF
    subst hb
    exact hall b hF
  obtain ⟨K, hK⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
    h.not_mem_partTwoT a ha
  have hDa := (sec15R_point h ha hK).toSec13Data
  have htype : Sec8.IsZ3PGLThreePi (lBarA a K A) ∨
      Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2) := by
    rcases h133 G A a K hDa h.hypS_or_hypT with hWa | ⟨-, -, -, htra, -⟩ |
        ⟨-, -, -, -, -, hΩa, -, -, -⟩ | h4 | h4 | h4
    · exact (hac (Proof1510.zpowers_eq_of_le_normalizer hD hcL h9 hirr hDa.mem_A
        hDa.card_zpowers (inf_le_right.trans hWa))).elim
    · obtain ⟨w, hw, hcw⟩ := htra _ h.zpowers_mem_omegaA
      exact (hac (Proof1510.eq_of_eq_map_conj hcw (hWH hw))).elim
    · have hc' := h.zpowers_mem_omegaA
      rw [hΩa] at hc'
      obtain ⟨w, hw, hcw⟩ := hc'
      exact (hac (Proof1510.eq_of_eq_map_conj hcw (hWH hw))).elim
    · exact Or.inl h4
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr h4)
  have htype' : Sec8.IsZ3PGLThreePi (lBarA a K A) ∨
      Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) := by
    rcases htype with h1 | h1 | ⟨⟨φ⟩⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · exact ((hHJ G A c L a K h hY0 hirr h9 hWH ha hac hK).false φ).elim
  have hctx : Ctx1513 G A c L a K := ⟨h, hY0, hirr, h9, hWH, ha, hac, hK, htype'⟩
  obtain ⟨w, hwKW, hw3, hwC9⟩ := htv G A c L a K hctx
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hwKW.2
  have hwC : w ∉ Subgroup.centralizer (A : Set G) := by
    intro hwc
    have hAC : A ⊓ Subgroup.centralizer ({w} : Set G) = A := inf_of_le_left fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwc x hx)
    rw [hAC, hD.card_eq] at hwC9
    norm_num at hwC9
  obtain ⟨p, e, hp, he, hL3⟩ : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rcases htypes with h1 | h1 | h1
    · exact h1
    · exact (hnt G A c L h (Or.inr h1) w ⟨hWH hwA, hwA⟩ hw3 hwC9).elim
    · exact (hnt G A c L h (Or.inl h1) w ⟨hWH hwA, hwA⟩ hw3 hwC9).elim
  obtain ⟨Y₁, hY₁⟩ := hY0
  obtain ⟨Y, -, hY⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hY₁
  have hYmeet := hmeets G A c L a K hctx Y hY
  have hfalse : ∀ w' ∈ Subgroup.normalizer (A : Set G),
      w' ∈ Subgroup.normalizer (Y : Set G) → w' ^ 3 = 1 →
        w' ∉ Subgroup.centralizer (A : Set G) → False :=
    fun w' hw'A hw'Y hw'3 hw'C =>
      false_of_mem_normalizer_Y h h1511 he hL3 hWH hY hYmeet hw'A hw'Y hw'3 hw'C
  obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_S0 h153 hnorm hY
  by_cases hT : ∃ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ ∧
      w ∈ Subgroup.normalizer (T : Set G)
  ·
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
    exact hfalse w' hw'A (hS₀Y (mem_normalizer_sup hw'A hw'S)) hw'3 hw'C
  ·
    push Not at hT
    have htrb := heven G A c L a K hctx w hwKW hw3 hwC9 hT
    have htrX : TransOn A (lB A) (xA A) ⊤ :=
      rank3II_14_11_2_of h.toSec14Std hloc htrb
    obtain ⟨w'', hw''N, hw''3, hw''C⟩ :=
      exists_mem_of_le_sup (normalizer_le_sup_of_transOn htrX hS₀) hwA hw3 hwC
    exact hfalse w'' hw''N.1 (hS₀Y (mem_normalizer_sup hw''N.1 hw''N.2)) hw''3 hw''C

end Proof1513

theorem rank3II_15_13_of (h131 : Item131) (h132 : Item132) (h133 : Item133)
    (hset : Item13SetupAt) (hBr : Sec16.Step169TwoBridge) (hHJ : Step1513HJ)
    (hmeets : Step1513Meets) (htv : Step1513Transv) (hnt : Step1513NoTransv)
    (hmax : Step1513Max) (heven : Step1513Even) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (h159 : Item159 A c L) (h1510 : Item1510 A)
    (h1511 : Item1511Star A (lB A) c L) (h1411 : Item1411_1 A (lB A))
    (hloc : Claim1411Local A (lB A)) (h153 : Item153Main A (lB A))
    (hnorm : Claim153Normal A (lB A)) : Item1513 A (lB A) c L := by
  intro hY0 hirr h9
  by_contra hcon
  have hne1 : ¬ (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
      WStarS4 A ∧ Sec21.IsIrreducibleOn (wStar A) ∧ TransOmegaThree A c) :=
    fun h1 => hcon (Or.inl h1)
  have hne2 : omegaA A ≠ {Subgroup.zpowers c} := fun h2 => hcon (Or.inr h2)
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨f, hfA, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers h9
  obtain ⟨hprod, htypes⟩ := cases_of_irreducible h131 h h9 hirr
  rcases h133 G A c L hD h.hypS_or_hypT with hWH | ⟨hW4, ⟨e7⟩, h3, htr, -⟩ |
      ⟨-, -, -, -, -, hΩ3, hn9, -, -⟩ | hPGL | ⟨⟨e12⟩⟩ | ⟨⟨eJ⟩⟩
  · exact Proof1513.false_of_normalizer_le h133 hset hHJ hmeets htv hnt hmax heven h h1511 h1411
      hloc h153 hnorm hY0 hirr h9 hWH hne2 htypes
  ·
    apply hne1
    obtain ⟨hS7, hZ7⟩ := isPerfect_center_alt7
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hS7 hZ7 e7
    have hcB : c ∉ A ⊓ L := fun h1 => hcL h1.2
    have hAa := eq_sup_of_card_nine hD h9 hcB
    rcases h132 G A c L hD h.hypS_or_hypT c hD.mem_A hD.ne_one L hD.mem_thetaComponentsAt hAa
        hcB hirr with ⟨-, -, -, -, -, -, h9', -⟩ | hWc | ⟨hirrW, -⟩
    · omega
    · exfalso
      have hΩ : omegaA A = {Subgroup.zpowers c} := by
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨h.zpowers_mem_omegaA, fun F hF => ?_⟩
        obtain ⟨w, hw, rfl⟩ := htr F hF
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWc hw)
      rw [hΩ, Set.ncard_singleton] at h3
      omega
    · exact ⟨⟨ψ⟩, hW4, hirrW, h3, htr⟩
  ·
    rcases h159 hirr h9 with h1 | ⟨-, -, hT⟩ | ⟨⟨χ⟩, -⟩
    · have := ncard_omegaA_eq_one_of_le hΩ3 h1
      omega
    · have := hT.1
      omega
    · exact false_of_orbit_quot hD h1510 (fun F hF => by rw [hΩ3] at hF; exact hF)
        hfA hfL hfc (hBr G A c L h ⟨χ⟩ hprod)
  · exact Proof1514.false_of_prod_of_isZ3PGLThreePi hD hcL hprod hPGL
  ·
    obtain ⟨-, ⟨hM12p, hM12z⟩, -⟩ := sporadicModels131
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z e12
    rcases htypes with ⟨p, e, hp, -, hL3⟩ | ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · exact KFacts.KS14.not_isoLThreePi_M12 p e (isoLThreePi_of_mulEquiv ψ hL3)
    · exact (Proof1514.isEmpty_mulEquiv_M12_of_A7 χ).false ψ
    · exact (Proof1514.isEmpty_mulEquiv_M12_of_M22 χ).false ψ
  ·
    obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z eJ
    obtain ⟨hJL, hJA, hJM⟩ := KFacts.KS14.ks17J2NotList
    rcases htypes with ⟨p, e, hp, -, hL3⟩ | ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · exact hJL p e (isoLThreePi_of_mulEquiv ψ hL3)
    · exact hJA.false (ψ.symm.trans χ)
    · exact hJM.false (ψ.symm.trans χ)

end Proof

theorem item1513R_of
    (h131 : Item131) (h132 : Item132) (h133 : Item133)
    (hset : Item13SetupAt) (h159 : Item159R) (h1510 : Item1510R)
    (hBr : Sec16.Step169TwoBridge) (h1511 : Item1511StarR) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h153 : Item153MainR) (hnorm : Claim153NormalR)
    (hHJ : Step1513HJ) (hmeets : Step1513Meets) (htv : Step1513Transv)
    (hnt : Step1513NoTransv) (hmax : Step1513Max) (heven : Step1513Even) : Item1513R :=
  fun G _ _ A c L h => rank3II_15_13_of h131 h132 h133 hset hBr hHJ hmeets htv hnt hmax heven h
    (h159 G A c L h) (h1510 G A c L h) (h1511 G A c L h) (h1411 G A c L h) (hloc G A c L h)
    (h153 G A c L h) (hnorm G A c L h)

end CFSG.RankThree.PartTwo.Sec15
