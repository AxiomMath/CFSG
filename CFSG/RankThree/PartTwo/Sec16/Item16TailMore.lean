module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

theorem false_of_l34 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2))
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L))
    (h1510 : Item1510 A) (hBr : Step169TwoBridge) : False := by
  obtain ⟨c', L', hL', hc', hempty⟩ := h1510
  rw [hΩ, Set.mem_singleton_iff] at hc'
  have hL'c : L' ∈ lA A c := lA_eq_of_zpowers_eq hc' ▸ hL'
  have h3L : 3 ∣ Nat.card L := by
    have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 20160 := by
      have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 2)
      rw [GaloisField.card 2 2 (by norm_num)] at hc
      norm_num at hc
      rw [Nat.card_congr φ.toEquiv]
      omega
    have h2 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
    rw [h1] at h2
    exact (show 3 ∣ 20160 by norm_num).trans h2
  have hLL' : L = L' := (h.chosen136.2 c h.zpowers_mem_omegaA L' hL'c).2 L h.mem_lA.1 h3L
  subst hLL'
  exact hempty.false (hBr G A c L h ⟨φ⟩ hprod).some

theorem mem_scriptQ_of_le_of_normal {A : Subgroup G} {a : G}
    (ha : a ∈ A) {R Θ : Subgroup G} (hRΘ : R ≤ Θ)
    (hΘC : Θ ≤ Subgroup.centralizer ({a} : Set G))
    (hCΘ : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Θ : Set G))
    (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    R ∈ scriptQ A (lB A) := by
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hΘ3 (h3.trans (Subgroup.card_dvd_of_le hRΘ))
  refine ⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩, fun B hB => ?_⟩
  unfold qBound
  by_cases haB : a ∈ B
  · have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hcop : Nat.Coprime 3 (Nat.card (Θ ⊓ Subgroup.centralizer (B : Set G) : Subgroup G)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
        hΘ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hle : Θ ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
      le_pPrimeCoreOf inf_le_right (le_normalizer_inf (hCB.trans hCΘ) Subgroup.le_normalizer)
        hcop
    exact ((inf_le_inf_right _ hRΘ).trans hle).trans (le_sup_left.trans le_sup_left)
  · have hAM := le_zpowers_sup_of_not_mem hB ha haB
    have hCAB : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.centralizer_le hB.1
    have hCACa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
    have hleA : R ⊓ Subgroup.centralizer (B : Set G) ≤ Θ ⊓ Subgroup.centralizer (A : Set G) := by
      rintro x ⟨hxR, hxB⟩
      refine ⟨hRΘ hxR, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hsub : Subgroup.zpowers a ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (hΘC (hRΘ hxR))).symm
        · intro z hz
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hxB z hz)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsub (hAM hy))
    have hcop : Nat.Coprime 3 (Nat.card (Θ ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
        hΘ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hle : Θ ⊓ Subgroup.centralizer (A : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
      le_pPrimeCoreOf inf_le_right (le_normalizer_inf (hCACa.trans hCΘ) Subgroup.le_normalizer)
        hcop
    exact (hleA.trans hle).trans (le_sup_right.trans le_sup_left)

theorem para1612_of :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Ctx169 G A c L → ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≠ ⊥ := by
  intro G _ _ A c L h S hS hS1
  obtain ⟨a, haA, ha1, hev⟩ : ∃ a ∈ A, a ≠ 1 ∧ 2 ∣ Nat.card (thetaCen ({a} : Set G)) := by
    by_contra hall
    push Not at hall
    have hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (thetaCen ({a} : Set G))) := fun a ha ha1 =>
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (hall a ha ha1))
    have hmem : A ∈ partTwoS G := by
      refine ⟨h.mem_partTwoF, fun a ha ha1 => ?_, fun B hBA hB9 => ?_⟩
      · have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx ha)
        have hAθ : A ≤ Subgroup.normalizer ((thetaCen ({a} : Set G) : Subgroup G) : Set G) :=
          hAC.trans (Proof169.centralizer_le_normalizer_thetaCen _)
        exact (hodd a ha ha1).of_dvd_nat
          (Subgroup.card_dvd_of_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hAθ))
      · have hBne : B ≠ ⊥ := by
          intro hbot
          rw [hbot, Subgroup.card_bot] at hB9
          omega
        obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
        have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
        exact (hodd b (hBA hb) hb1').of_dvd_nat
          (Subgroup.card_dvd_of_le (thetaT_le_thetaCen hb hb1'))
    rw [h.partTwoS_eq] at hmem
    simp at hmem
  set Θ := thetaCen ({a} : Set G) with hΘ
  obtain ⟨-, -, hc3, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer ({a} : Set G))) Nat.prime_three
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    change ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({a} : Set G))).map (Subgroup.centralizer ({a} : Set G)).subtype)
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hc3
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx haA)
  have hAθ : A ≤ Subgroup.normalizer (Θ : Set G) :=
    hAC.trans (Proof169.centralizer_le_normalizer_thetaCen _)
  obtain ⟨T, hAT, hT1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two A Θ h.isE27.isPGroup hAθ
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hΘ3) hev
  set R := (T : Subgroup ↥Θ).map Θ.subtype with hR
  have hRQ : R ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le_of_normal haA (Subgroup.map_subtype_le _)
      (Subgroup.map_subtype_le _) (Proof169.centralizer_le_normalizer_thetaCen _) hΘ3 hAT
  have hR2 : IsPGroup 2 R := T.isPGroup'.map _
  have hRQ2 : R ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hRQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩
  subst hS1
  exact hT1 (le_bot_iff.mp (hS.2 hRQ2 bot_le))

@[expose] noncomputable def Step1619One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2))

@[expose] noncomputable def Step1619Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ Y ∈ scriptY3 A (lB A), Group.IsSolvable ↥Y

theorem step1619One_of (h1614 : Step1614) (h1616 : Step1616) (h1510 : Item1510R)
    (hBr : Step169TwoBridge) : Step1619One := by
  intro G _ _ A c L h
  refine ⟨fun φ => ?_⟩
  obtain ⟨n, -, -, hprod⟩ := h1616 G A c L h
  exact false_of_l34 h.toSec15R φ (h1614 G A c L h) hprod (h1510 G A c L h.toSec15R) hBr

theorem step1619_of (h1 : Step1619One) (h2 : Step1619Two) : Step1619 :=
  fun G _ _ A c L h => ⟨h1 G A c L h, h2 G A c L h⟩

theorem two_lt_of_isZ3LThreeTwo {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec13Data G A c L) {n : ℕ} (hn : IsZ3LThreeTwo A c L n)
    (h34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2))) :
    2 < n := by
  obtain ⟨hn1, hiso, -⟩ := hn
  by_contra hle
  have hn12 : n = 1 ∨ n = 2 := by omega
  rcases hn12 with rfl | rfl
  ·
    rcases hiso with ⟨h3, -⟩ | ⟨-, ⟨φ⟩⟩
    · norm_num at h3
    · have hq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
        Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
      have := isSolvable_projSU_two
      have hsol : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
        obtain ⟨x, y, hxy⟩ := hq.2.2
        by_contra hntr
        rw [not_nontrivial_iff_subsingleton] at hntr
        apply hxy
        have : Subsingleton ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
            Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
          QuotientGroup.mk_surjective.subsingleton
        exact Subsingleton.elim _ _
      have := hq.1
      exact Group.IsPerfect.not_isSolvable _ hsol
  · rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨h3, -⟩
    · exact h34.false φ
    · norm_num at h3

@[expose] noncomputable def Step1620Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → omegaA A = {Subgroup.zpowers c} →
    ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      ∀ X ∈ collectionIn (scriptQ A (lB A)) P, X ≠ ⊥ →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2),
        Subgroup.normalizer (A : Set G) ≤
          (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G)) ⊔
            Subgroup.centralizer (A : Set G) →
        oPrimeResidualOf 3 (⨆ w ∈ Subgroup.normalizer (A : Set G) ⊓
            Subgroup.normalizer (S : Set G), X.map (MulAut.conj w).toMonoidHom) ≠ ⊥

theorem bot_mem_omega168 {A : Subgroup G} (hG : Nontrivial G)
    (hs : ∀ Y ∈ scriptY3 A (lB A), Y ∈ scriptYs A (lB A)) :
    (⊥ : Subgroup G) ∈ Sec17.omega168 A (lB A) := by
  refine ⟨?_, ⟨?_, fun a _ => Subgroup.mem_normalizer_iff.mpr fun y => by
    constructor <;> intro hy <;> simp_all⟩, fun Y hY _ => hs Y hY⟩
  · refine le_antisymm bot_le ?_
    have h0 : deltaZero A (lB A) ⊥ = ⊥ := le_bot_iff.mp (deltaZero_le ⊥)
    rw [h0]
    exact Subgroup.map_subtype_le _
  · intro htop
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have : x ∈ (⊥ : Subgroup G) := htop ▸ Subgroup.mem_top x
    exact hx (Subgroup.mem_bot.mp this)

end CFSG.RankThree.PartTwo.Sec16
