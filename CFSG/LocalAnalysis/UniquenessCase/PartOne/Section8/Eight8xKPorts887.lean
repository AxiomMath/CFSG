module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarKernel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63J2Tits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsSpor Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R71 R72 Sec7Hyp ImageModK QuotK7 PPrimeCoreIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

private theorem r887_card_eq_of_isSpor_J2
    {X : Type} [Group X] [Finite X]
    (hJ2 : IsSpor X .J2) : Nat.card X = 604800 := by
  obtain ⟨e⟩ := hJ2
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.J2.card_J2

private theorem r887_pRank_five_mulAut_le_two
    {X : Type} [Group X] [Finite X] (hJ2 : IsSpor X .J2) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_five ?_
  have hout : ¬ 5 ∣ Nat.card (Outer X) := not_five_dvd_card_outer_of_isSpor_J2 hJ2
  have hinner_dvd : Nat.card (inner X) ∣ Nat.card X :=
    Subgroup.card_dvd_of_surjective (f := (MulAut.conj : X →* MulAut X).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hnot3 : ¬ 5 ^ 3 ∣ Nat.card (inner X) := by
    intro h
    have h' : 5 ^ 3 ∣ Nat.card X := h.trans hinner_dvd
    rw [r887_card_eq_of_isSpor_J2 hJ2] at h'
    norm_num at h'
  have hcard : Nat.card (MulAut X) = Nat.card (Outer X) * Nat.card (inner X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (inner X)
  rw [hcard]
  intro h
  have hcop0 : Nat.Coprime 5 (Nat.card (Outer X)) :=
    (Nat.prime_five.coprime_iff_not_dvd).2 hout
  have hcop : Nat.Coprime (5 ^ 3) (Nat.card (Outer X)) := hcop0.pow_left 3
  exact hnot3 (hcop.dvd_of_dvd_mul_left h)

private theorem r887_centOverO2_pRank_ge_one
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hLM : M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2)
    (hM5 : 3 ≤ CFSG.Open.pRank 5 M) :
    1 ≤ CFSG.Open.pRank 5 (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let ρ : ↥M →* MulAut (Bar2 L) := (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
    (Subgroup.inclusion hLM)
  have hineq := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map (G := ↥M)
    (H := MulAut (Bar2 L)) Nat.prime_five ρ (⊤ : Subgroup ↥M)
  have htop : CFSG.Open.pRank 5 (⊤ : Subgroup ↥M) = CFSG.Open.pRank 5 M :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup M).symm
  have himg : CFSG.Open.pRank 5 ((⊤ : Subgroup ↥M).map ρ) ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans (r887_pRank_five_mulAut_le_two hJ2)
  have hker : CFSG.Open.pRank 5 (⊤ ⊓ ρ.ker) =
      CFSG.Open.pRank 5 (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L) := by
    have hcomap : ρ.ker = (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L).comap
        M.subtype := by
      rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.centOverO2_eq_ker_map hLM]
      exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm
    rw [top_inf_eq, hcomap]
    have hsub : (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L).comap M.subtype =
        (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L).subgroupOf M := rfl
    rw [hsub]
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup
          ((CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L).subgroupOf M),
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup
          (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L)]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5)
      (Subgroup.subgroupOfEquivOfLe (fun x hx =>
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hx).1))
  have : CFSG.Open.pRank 5 M ≤
      CFSG.Open.pRank 5 (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L) + 2 := by
    calc CFSG.Open.pRank 5 M = CFSG.Open.pRank 5 (⊤ : Subgroup ↥M) := htop.symm
      _ ≤ CFSG.Open.pRank 5 (⊤ ⊓ ρ.ker) + CFSG.Open.pRank 5 ((⊤ : Subgroup ↥M).map ρ) := hineq
      _ ≤ CFSG.Open.pRank 5 (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L) + 2 :=
          Nat.add_le_add hker.le himg
  omega

private theorem r887_exists_five_mem_centOverO2
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hLM : M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2)
    (hM5 : 3 ≤ CFSG.Open.pRank 5 M) :
    ∃ f : G, f ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L ∧ orderOf f = 5 := by
  have h1 := r887_centOverO2_pRank_ge_one hLM hJ2 hM5
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5)
      (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L)
  have h5le : 5 ≤ Nat.card E := by
    rw [hEcard]
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ CFSG.Open.pRank 5
          (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L) :=
          Nat.pow_le_pow_right (by norm_num) h1
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h5le
    omega
  obtain ⟨f, hfne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
  refine ⟨(f : G), hE f.2, orderOf_eq_prime (hEel.2 (f : G) f.2) ?_⟩
  intro h
  exact hfne (Subtype.ext h)

private theorem r887_centOverO2_le_centralizerBar {G : Type} [Group G] [Finite G]
    (M L : Subgroup G) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 M L ≤ centralizerBar M L := by
  intro x hx
  obtain ⟨hxM, hxc⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hx
  exact ⟨hxM, hxc⟩

private theorem r887_exists_five_mem_centralizerBar
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hMN : M ≤ normalizer (L : Set G)) (hJ : IsSpor (Bar2 L) .J2)
    (hM5 : 3 ≤ CFSG.Open.pRank 5 M) :
    ∃ f : G, f ∈ centralizerBar M L ∧ orderOf f = 5 := by
  obtain ⟨f, hf, hf5⟩ := r887_exists_five_mem_centOverO2 hMN hJ hM5
  exact ⟨f, r887_centOverO2_le_centralizerBar M L hf, hf5⟩

private theorem r887_center_eq_bot_of_isSpor_J2
    {X : Type} [Group X] [Finite X] (hJ : IsSpor X .J2) : Subgroup.center X = ⊥ := by
  have hcard := r887_card_eq_of_isSpor_J2 hJ
  obtain ⟨e⟩ := hJ
  have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X)).resolve_right fun ht => ?_
  have hprime : (Nat.card X).Prime :=
    (@Group.is_simple_iff_prime_card X _ (Subgroup.center_eq_top_iff.1 ht)).1 inferInstance
  rw [hcard] at hprime
  norm_num at hprime

private theorem r887_not_threeCover_of_isSpor_J2
    {X : Type} [Group X] [Finite X] (hJ : IsSpor X .J2) :
    ¬ (IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) := by
  have h1 : Nat.card (Subgroup.center X) = 1 := by
    rw [r887_center_eq_bot_of_isSpor_J2 hJ, Subgroup.card_bot]
  rintro (⟨-, h3, -⟩ | ⟨-, h3, -⟩ | ⟨-, h3, -⟩) <;> omega

theorem r887_commutator_zpow_mem {G : Type} [Group G] {O : Subgroup G} {a f : G}
    (haN : a ∈ normalizer (O : Set G)) (hfN : f ∈ normalizer (O : Set G))
    (hcomm : f * a * f⁻¹ * a⁻¹ ∈ O) (i j : ℤ) :
    f ^ i * a ^ j * (f ^ i)⁻¹ * (a ^ j)⁻¹ ∈ O := by
  have : (O.subgroupOf (normalizer (O : Set G))).Normal := Subgroup.normal_in_normalizer
  let π : ↥(normalizer (O : Set G)) →* ↥(normalizer (O : Set G)) ⧸
      O.subgroupOf (normalizer (O : Set G)) := QuotientGroup.mk' _
  have hc1 : ⁅π ⟨f, hfN⟩, π ⟨a, haN⟩⁆ = 1 := by
    rw [← map_commutatorElement]
    refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    simpa [commutatorElement_def] using hcomm
  have hc : Commute (π ⟨f, hfN⟩) (π ⟨a, haN⟩) := commutatorElement_eq_one_iff_mul_comm.mp hc1
  have hc3 : ⁅π ⟨f, hfN⟩ ^ i, π ⟨a, haN⟩ ^ j⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hc.zpow_zpow i j)
  have h4 : π ⁅(⟨f, hfN⟩ : ↥(normalizer (O : Set G))) ^ i,
      (⟨a, haN⟩ : ↥(normalizer (O : Set G))) ^ j⁆ = 1 := by
    rw [map_commutatorElement, map_zpow, map_zpow]
    exact hc3
  have h5 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h4)
  simpa [commutatorElement_def] using h5

private theorem r887_pCoreOf_le_centralizerBar {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hLM : L ≤ M) :
    CFSG.Open.pCoreOf 2 L ≤ centralizerBar M L := by
  intro o ho
  have hOL : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLN : L ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  refine mem_centralizerBar_iff.mpr ⟨hLM (hOL ho), ?_⟩
  intro y hy
  have h1 : y * o⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.1 (hLN hy) o⁻¹).1 ((CFSG.Open.pCoreOf 2 L).inv_mem ho)
  have h2 : ⁅o, y⁆ = o * (y * o⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact (CFSG.Open.pCoreOf 2 L).mul_mem ho h1

theorem r887_centralizing_five_of_mem_centralizerBar {G : Type} [Group G] [Finite G]
    {M L Z : Subgroup G} {f₀ : G} (hLM : L ≤ M) (hMN : M ≤ normalizer (L : Set G))
    (hZL : Z ≤ L) (hZ : IsPGroup 3 Z) (hf₀ : f₀ ∈ centralizerBar M L) (hf₀5 : orderOf f₀ = 5) :
    ∃ f : G, f ∈ centralizerBar M L ∧ f ∈ centralizer (Z : Set G) ∧ orderOf f = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hO : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hLN : L ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hMN' : M ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L (hMN hx)
  have hAcard : Nat.card (Subgroup.zpowers f₀) = 5 := by
    rw [Nat.card_zpowers, hf₀5]
  have hA : IsPGroup 5 (Subgroup.zpowers f₀) := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hAcb : Subgroup.zpowers f₀ ≤ centralizerBar M L := Subgroup.zpowers_le.2 hf₀
  have hAN : Subgroup.zpowers f₀ ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    fun x hx => hMN' (centralizerBar_le M L (hAcb hx))
  have hZN : Z ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) := fun x hx => hLN (hZL hx)
  have hcomm : ∀ e ∈ Z, ∀ a ∈ Subgroup.zpowers f₀,
      e * a * e⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro e he a ha
    have h := (mem_centralizerBar_iff.1 (hAcb ha)).2 e (hZL he)
    have h2 : e * a * e⁻¹ * a⁻¹ = ⁅a, e⁆⁻¹ := by
      rw [commutatorElement_inv, commutatorElement_def]
    rw [h2]
    exact (CFSG.Open.pCoreOf 2 L).inv_mem h
  obtain ⟨A', hA'Z, hA'AO, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_centralizing_copy (ℓ := 3) (p := 5)
      Nat.prime_three (by norm_num) Nat.prime_five (by norm_num) (CFSG.Open.pCoreOf 2 L)
      (Subgroup.zpowers f₀) Z hO hAN hZN hA hZ hcomm
  have hA'card : Nat.card A' = 5 := by
    rw [Nat.card_congr φ.toEquiv, hAcard]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A') 5 (dvd_of_eq hA'card.symm)
  refine ⟨(x : G), ?_, hA'Z x.2, ?_⟩
  · exact (sup_le hAcb (r887_pCoreOf_le_centralizerBar hLM)) (hA'AO x.2)
  · rw [Subgroup.orderOf_coe, hx]

private theorem r887_mem_normalizer_inf {G : Type} [Group G] {O C : Subgroup G} {x : G}
    (hxC : x ∈ C) (hxO : x ∈ normalizer (O : Set G)) :
    x ∈ normalizer ((O ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hxO ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hxO h]
  refine and_congr Iff.rfl ⟨fun hh => C.mul_mem (C.mul_mem hxC hh) (C.inv_mem hxC), fun hh => ?_⟩
  have h1 := C.mul_mem (C.mul_mem (C.inv_mem hxC) hh) hxC
  have h2 : x⁻¹ * (x * h * x⁻¹) * x = h := by group
  rwa [h2] at h1

open scoped Pointwise in
private theorem r887_mem_zpowers_sup_iff {G : Type} [Group G] {y : G} {K : Subgroup G}
    (hy : y ∈ normalizer (K : Set G)) {x : G} :
    x ∈ Subgroup.zpowers y ⊔ K ↔ ∃ (i : ℤ), ∃ k ∈ K, x = y ^ i * k := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y) K
    (Subgroup.zpowers_le.2 hy)
  constructor
  · intro hx
    have hx' : x ∈ ((Subgroup.zpowers y : Subgroup G) : Set G) * (K : Set G) := by
      rw [← h]
      exact hx
    obtain ⟨u, hu, k, hk, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact ⟨i, k, hk, rfl⟩
  · rintro ⟨i, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers y i) hk

private theorem r887_exists_zpow_eq_self_of_not_dvd {G : Type} [Group G] {a : G}
    (ha : orderOf a = 5) {j : ℤ} (h5 : ¬ ((5 : ℕ) : ℤ) ∣ j) : ∃ k : ℤ, a ^ (j * k) = a := by
  have h5a : a ^ (5 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha] at h
    simpa using h
  have hj5 : j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
  have hex : ∃ k m : ℤ, j * k = 1 + 5 * m := by
    rcases hj5 with h | h | h | h
    · exact ⟨1, (j - 1) / 5, by omega⟩
    · exact ⟨3, (3 * j - 1) / 5, by omega⟩
    · exact ⟨2, (2 * j - 1) / 5, by omega⟩
    · exact ⟨4, (4 * j - 1) / 5, by omega⟩
  obtain ⟨k, m, hm⟩ := hex
  refine ⟨k, ?_⟩
  rw [hm, zpow_add, zpow_one, zpow_mul, h5a, one_zpow, mul_one]

theorem r887_exists_commuting_five_independent {G : Type} [Group G] [Finite G]
    {O C : Subgroup G} {a f : G} (hO : IsPGroup 2 O) (haC : a ∈ C) (hfC : f ∈ C)
    (haN : a ∈ normalizer (O : Set G)) (hfN : f ∈ normalizer (O : Set G))
    (ha : orderOf a = 5) (hf : orderOf f = 5) (hcomm : f * a * f⁻¹ * a⁻¹ ∈ O)
    (hind : ∀ (i : ℤ), ∀ o ∈ O, a ≠ f ^ i * o) :
    ∃ a' : G, a' ∈ C ∧ orderOf a' = 5 ∧ Commute f a' ∧ a' ∉ Subgroup.zpowers f := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hO' : IsPGroup 2 ↥(O ⊓ C) := hO.to_inf_left
  have haN' : a ∈ normalizer ((O ⊓ C : Subgroup G) : Set G) := r887_mem_normalizer_inf haC haN
  have hfN' : f ∈ normalizer ((O ⊓ C : Subgroup G) : Set G) := r887_mem_normalizer_inf hfC hfN
  have hcomm' : f * a * f⁻¹ * a⁻¹ ∈ O ⊓ C :=
    ⟨hcomm, C.mul_mem (C.mul_mem (C.mul_mem hfC haC) (C.inv_mem hfC)) (C.inv_mem haC)⟩
  have hcz : ∀ e ∈ Subgroup.zpowers f, ∀ b ∈ Subgroup.zpowers a,
      e * b * e⁻¹ * b⁻¹ ∈ O ⊓ C := by
    intro e he b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact r887_commutator_zpow_mem haN' hfN' hcomm' i j
  have hacard : Nat.card (Subgroup.zpowers a) = 5 := by rw [Nat.card_zpowers, ha]
  have hfcard : Nat.card (Subgroup.zpowers f) = 5 := by rw [Nat.card_zpowers, hf]
  have hApG : IsPGroup 5 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by simpa using hacard)
  have hEpG : IsPGroup 5 (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by simpa using hfcard)
  obtain ⟨A', hA'c, hA'sup, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_centralizing_copy (ℓ := 5) (p := 5)
      Nat.prime_five (by norm_num) Nat.prime_five (by norm_num) (O ⊓ C) (Subgroup.zpowers a)
      (Subgroup.zpowers f) hO' (Subgroup.zpowers_le.2 haN') (Subgroup.zpowers_le.2 hfN')
      hApG hEpG hcz
  have hA'card : Nat.card A' = 5 := by rw [Nat.card_congr φ.toEquiv, hacard]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A') 5 (dvd_of_eq hA'card.symm)
  have hxsup : (x : G) ∈ Subgroup.zpowers a ⊔ (O ⊓ C) := hA'sup x.2
  have hxC : (x : G) ∈ C :=
    (sup_le (Subgroup.zpowers_le.2 haC) inf_le_right : Subgroup.zpowers a ⊔ (O ⊓ C) ≤ C) hxsup
  have hx5 : orderOf (x : G) = 5 := by rw [Subgroup.orderOf_coe, hx]
  refine ⟨(x : G), hxC, hx5, Subgroup.mem_centralizer_iff.1 (hA'c x.2) f
    (Subgroup.mem_zpowers f), ?_⟩
  intro hxf
  obtain ⟨j, o', ho', hj⟩ := (r887_mem_zpowers_sup_iff haN').1 hxsup
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hxf
  have hoO : o' ∈ O := ho'.1
  by_cases h5 : ((5 : ℕ) : ℤ) ∣ j
  · have haj : a ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [ha]; exact h5)
    have hxo : (x : G) = o' := by rw [hj, haj, one_mul]
    obtain ⟨k, hk⟩ := hO ⟨o', hoO⟩
    have h1 : orderOf (x : G) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hxo]
      simpa using congrArg Subtype.val hk
    rw [hx5] at h1
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h1
    omega
  · obtain ⟨k, hk⟩ := r887_exists_zpow_eq_self_of_not_dvd ha h5
    have h1 : a ^ j = f ^ i * o'⁻¹ := by
      rw [hi, hj]
      group
    have hajmem : a ^ j ∈ Subgroup.zpowers f ⊔ O := by
      rw [h1]
      exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers f i) (O.inv_mem hoO)
    have hamem : a ∈ Subgroup.zpowers f ⊔ O := by
      have h2 : (a ^ j) ^ k = a := by
        rw [← zpow_mul]
        exact hk
      rw [← h2]
      exact zpow_mem hajmem k
    obtain ⟨m, o, ho, hao⟩ := (r887_mem_zpowers_sup_iff hfN).1 hamem
    exact hind m o ho hao

private theorem r887_mem_normalizer_zpowers {K : Type} [Group K] {g y : K}
    (hg : g * y = y * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup K) : Set K) := by
  have hc : Commute g y := hg
  have hfix : ∀ s ∈ Subgroup.zpowers y, g * s * g⁻¹ = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (hc.zpow_right k).mul_inv_cancel
  have hfix' : ∀ s ∈ Subgroup.zpowers y, g⁻¹ * s * g = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (hc.zpow_right k).inv_mul_cancel
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hfix h hh]
    exact hh
  · intro hh
    have h2 : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g * h * g⁻¹ := hfix' _ hh
    rw [h2]
    exact hh

private theorem r887_exists_fixed_mod_two_group {H : Type} [Group H] [Finite H] {O : Subgroup H}
    [O.Normal] (hO : IsPGroup 2 O) {E : Subgroup H} (hE : IsPGroup 3 E) {y : H}
    (hy : ∀ e ∈ E, QuotientGroup.mk' O e * QuotientGroup.mk' O y =
      QuotientGroup.mk' O y * QuotientGroup.mk' O e) :
    ∃ c : H, c ∈ Subgroup.centralizer (E : Set H) ∧
      QuotientGroup.mk' O c = QuotientGroup.mk' O y := by
  let B : Subgroup H := (Subgroup.zpowers (QuotientGroup.mk' O y)).comap (QuotientGroup.mk' O)
  have hOB : O ≤ B := by
    intro o ho
    show QuotientGroup.mk' O o ∈ Subgroup.zpowers (QuotientGroup.mk' O y)
    have h1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    rw [h1]
    exact one_mem _
  have hyB : y ∈ B := Subgroup.mem_zpowers (QuotientGroup.mk' O y)
  have hcomm : ∀ e ∈ E, ∀ b ∈ B, QuotientGroup.mk' O e * QuotientGroup.mk' O b =
      QuotientGroup.mk' O b * QuotientGroup.mk' O e := by
    intro e he b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← hk]
    exact Commute.zpow_right (hy e he) k
  have hcommB : ∀ e ∈ E, ∀ b ∈ B, e * b * e⁻¹ * b⁻¹ ∈ O := by
    intro e he b hb
    have h2 : QuotientGroup.mk' O (e * b * e⁻¹ * b⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm e he b hb]
      group
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hEB : E ≤ Subgroup.normalizer (B : Set H) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have hn := Subgroup.mem_normalizer_iff.1 (r887_mem_normalizer_zpowers (hy e he))
      (QuotientGroup.mk' O b)
    show QuotientGroup.mk' O b ∈ Subgroup.zpowers (QuotientGroup.mk' O y) ↔
      QuotientGroup.mk' O (e * b * e⁻¹) ∈ Subgroup.zpowers (QuotientGroup.mk' O y)
    rw [map_mul, map_mul, map_inv]
    exact hn
  have hEO : E ≤ Subgroup.normalizer (O : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨c, -, hcE, hcy⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_fixed_in_coset
    (ℓ := 3) Nat.prime_three (by norm_num) O B E hO hOB hEO hEB hE hcommB y hyB
  refine ⟨c, hcE, ?_⟩
  have h1 : QuotientGroup.mk' O (c * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hcy
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

private theorem r887_map_centralizer_le_centralizer_map {G : Type} [Group G]
    {L Z : Subgroup G} :
    ((L ⊓ centralizer (Z : Set G)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤
      centralizer ((((Z.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (Bar2 L)) : Set (Bar2 L))) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have hxc : (x : G) ∈ centralizer (Z : Set G) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2
  have h := Subgroup.mem_centralizer_iff.1 hxc (u : G) (Subgroup.mem_subgroupOf.1 hu)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem r887_map_centralizer_eq_centralizer_map {G : Type} [Group G] [Finite G]
    {L Z : Subgroup G} (hZL : Z ≤ L) (hZ : IsPGroup 3 Z) :
    ((L ⊓ centralizer (Z : Set G)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      centralizer ((((Z.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (Bar2 L)) : Set (Bar2 L))) := by
  refine le_antisymm r887_map_centralizer_le_centralizer_map ?_
  intro yb hyb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) yb
  have hE : IsPGroup 3 (Z.subgroupOf L) := hZ.comap_subtype
  have hy : ∀ e ∈ Z.subgroupOf L, QuotientGroup.mk' (CFSG.pCore 2 ↥L) e *
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) y =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) y * QuotientGroup.mk' (CFSG.pCore 2 ↥L) e := by
    intro e he
    exact Subgroup.mem_centralizer_iff.1 hyb _ (Subgroup.mem_map_of_mem _ he)
  obtain ⟨c, hcE, hcπ⟩ := r887_exists_fixed_mod_two_group CFSG.pCore_isPGroup hE hy
  refine ⟨c, ?_, hcπ⟩
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨c.2, Subgroup.mem_centralizer_iff.2 ?_⟩)
  intro z hz
  have h := Subgroup.mem_centralizer_iff.1 hcE ⟨z, hZL hz⟩ (Subgroup.mem_subgroupOf.2 hz)
  exact congrArg Subtype.val h

theorem r887_exists_five_centralizerBar_inf_centralizer
    {G : Type} [Group G] [Finite G] {M L Z : Subgroup G} (hLM : L ≤ M)
    (hMN : M ≤ normalizer (L : Set G)) (hZL : Z ≤ L) (hZ : IsPGroup 3 Z)
    (hJ : IsSpor (Bar2 L) .J2) (hM5 : 3 ≤ CFSG.Open.pRank 5 M) :
    ∃ f : G, f ∈ centralizerBar M L ∧ f ∈ centralizer (Z : Set G) ∧ orderOf f = 5 := by
  obtain ⟨f₀, hf₀, hf₀5⟩ := r887_exists_five_mem_centralizerBar hMN hJ hM5
  exact r887_centralizing_five_of_mem_centralizerBar hLM hMN hZL hZ hf₀ hf₀5

theorem r887_pRank_two_of_commuting_mod_two_group {G : Type} [Group G] [Finite G]
    {O C : Subgroup G} {a f : G} (hO : IsPGroup 2 O) (haC : a ∈ C) (hfC : f ∈ C)
    (haN : a ∈ normalizer (O : Set G)) (hfN : f ∈ normalizer (O : Set G))
    (ha : orderOf a = 5) (hf : orderOf f = 5) (hcomm : f * a * f⁻¹ * a⁻¹ ∈ O)
    (hind : ∀ (i : ℤ), ∀ o ∈ O, a ≠ f ^ i * o) :
    2 ≤ CFSG.Open.pRank 5 C := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a', ha'C, ha'5, hcomm', hind'⟩ :=
    r887_exists_commuting_five_independent hO haC hfC haN hfN ha hf hcomm hind
  exact CFSG.GroupTheory.two_le_pRank_of_commute hfC ha'C hf ha'5 hcomm' hind'

private theorem r887_card_of_isA6Z3 {Y : Type} [Group Y] (h : IsA6Z3 Y) : Nat.card Y = 1080 := by
  obtain ⟨-, hz, e⟩ := h
  have hq : Nat.card (Y ⧸ Subgroup.center Y) = 360 := by
    obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
  rw [hq, hz] at hcard
  omega

private theorem r887_exists_five_mem_inf_centralizer {G : Type} [Group G] [Finite G]
    {L Z : Subgroup G} (hZL : Z ≤ L) (hZ : IsPGroup 3 Z)
    (hA6 : IsA6Z3 ↥(centralizer ((((Z.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (Bar2 L)) : Set (Bar2 L))))) :
    ∃ a : G, a ∈ L ⊓ centralizer (Z : Set G) ∧ orderOf a = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card ↥(centralizer ((((Z.subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) : Set (Bar2 L)))) := by
    rw [r887_card_of_isA6Z3 hA6]
    norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hymem : (y : Bar2 L) ∈ ((L ⊓ centralizer (Z : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [r887_map_centralizer_eq_centralizer_map hZL hZ]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hymem
  have hdvd : 5 ∣ orderOf x := by
    have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) ∣ orderOf x := orderOf_map_dvd _ x
    have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) = 5 := by
      rw [hxy, Subgroup.orderOf_coe, hy]
    rwa [h2] at h1
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨((x ^ (orderOf x / 5) : ↥L) : G), ?_, ?_⟩
  · have hxG : (x : G) ∈ L ⊓ centralizer (Z : Set G) := Subgroup.mem_subgroupOf.mp hx
    exact (L ⊓ centralizer (Z : Set G)).pow_mem hxG _
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div hx0 hdvd

theorem r887_pRank_centralizer_ge_two
    {G : Type} [Group G] [Finite G] {M L Z : Subgroup G} (hLM : L ≤ M)
    (hMN : M ≤ normalizer (L : Set G)) (hZL : Z ≤ L) (hZ : IsPGroup 3 Z)
    (hJ : IsSpor (Bar2 L) .J2) (hM5 : 3 ≤ CFSG.Open.pRank 5 M)
    (hA6 : IsA6Z3 ↥(centralizer ((((Z.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (Bar2 L)) : Set (Bar2 L))))) :
    2 ≤ CFSG.Open.pRank 5 (M ⊓ centralizer (Z : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfC, hfZ, hf5⟩ :=
    r887_exists_five_centralizerBar_inf_centralizer hLM hMN hZL hZ hJ hM5
  obtain ⟨a, haLZ, ha5⟩ := r887_exists_five_mem_inf_centralizer hZL hZ hA6
  obtain ⟨haL, haZ⟩ := Subgroup.mem_inf.mp haLZ
  have hfM : f ∈ M := centralizerBar_le M L hfC
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hOL : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have haN : a ∈ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L
      (Subgroup.le_normalizer haL)
  have hfN : f ∈ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L (hMN hfM)
  have hcomm : f * a * f⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    have h := (mem_centralizerBar_iff.mp hfC).2 a haL
    rwa [commutatorElement_def] at h
  have hind : ∀ (i : ℤ), ∀ o ∈ CFSG.Open.pCoreOf 2 L, a ≠ f ^ i * o := by
    intro i o ho hao
    have hfiL : f ^ i ∈ L := by
      have h : f ^ i = a * o⁻¹ := by rw [hao]; group
      rw [h]
      exact L.mul_mem haL (L.inv_mem (hOL ho))
    have hfiC : f ^ i ∈ centralizerBar M L := zpow_mem hfC i
    have hfiO : f ^ i ∈ CFSG.Open.pCoreOf 2 L :=
      inf_centralizerBar_le_pCore_of_center_bar2 (P := M)
        (r887_center_eq_bot_of_isSpor_J2 hJ) ⟨hfiC, hfiL⟩
    have haO : a ∈ CFSG.Open.pCoreOf 2 L := by
      rw [hao]
      exact (CFSG.Open.pCoreOf 2 L).mul_mem hfiO ho
    obtain ⟨k, hk⟩ := hO2 ⟨a, haO⟩
    have h1 : orderOf a ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [ha5] at h1
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h1
    omega
  have haC : a ∈ M ⊓ centralizer (Z : Set G) := ⟨hLM haL, haZ⟩
  have hfC' : f ∈ M ⊓ centralizer (Z : Set G) := ⟨hfM, hfZ⟩
  exact r887_pRank_two_of_commuting_mod_two_group hO2 haC hfC' haN hfN ha5 hf5 hcomm hind

theorem r887_sec7Hyp_normalizer {G : Type} [Group G] [Finite G] (D : Data G) {Z : Subgroup G}
    (hsp : IsStronglyPEmbedded 5 D.M) (hZc : Nat.card Z = 3)
    (hH : ¬ normalizer (Z : Set G) ≤ D.M)
    (hrank : 2 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer (Z : Set G))) :
    Sec7Hyp D 5 (normalizer (Z : Set G)) := by
  refine ⟨Nat.prime_five, by norm_num, hsp, ?_, hH, ?_⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_ne_top_of_card_prime_uc6
      D.standing.simple D.standing.nonab Nat.prime_three hZc
  · have hle : D.M ⊓ centralizer (Z : Set G) ≤ normalizer (Z : Set G) ⊓ D.M :=
      fun x hx => ⟨Subgroup.centralizer_le_normalizer (Z : Set G) hx.2, hx.1⟩
    have h2 := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) hle
    omega

theorem r887_exists_section_of_hom {C S Q : Type} [Group C] [Finite C] [Group S] [Group Q]
    [IsSimpleGroup Q] (φ : C →* S) (f : C →* Q) (hf : Function.Surjective f)
    (hodd : ¬ 2 ∣ Nat.card φ.ker) (hQ : 2 ∣ Nat.card Q) :
    ∃ (A : Subgroup S) (V : Subgroup ↥A) (_ : V.Normal), Nonempty ((↥A ⧸ V) ≃* Q) := by
  have hker : φ.ker ≤ f.ker := by
    have : (φ.ker.map f).Normal := Subgroup.Normal.map inferInstance f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map f) with hbot | htop
    · intro x hx
      have hmem : f x ∈ φ.ker.map f := Subgroup.mem_map_of_mem f hx
      rw [hbot] at hmem
      simpa using hmem
    · exfalso
      have hQdvd : 2 ∣ Nat.card (φ.ker.map f) := by
        rw [htop, Subgroup.card_top]
        exact hQ
      exact hodd (hQdvd.trans (Subgroup.card_map_dvd φ.ker f))
  let π : C →* ↥φ.range := φ.rangeRestrict
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective φ
  have hπker : π.ker ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let g : ↥φ.range →* Q :=
    (π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)) ⟨f, hπker⟩
  have hg : ∀ c : C, g (π c) = f c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨f, hπker⟩ c
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨c, rfl⟩ := hf q
    exact ⟨π c, hg c⟩
  exact ⟨φ.range, g.ker, inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective g hgs⟩⟩

theorem r887_alt6_section_image {G : Type} [Group G] [Finite G] {M L Z H : Subgroup G} {p : ℕ}
    (hLM : L ≤ M) (hZL : Z ≤ L) (hZ : IsPGroup 3 Z) (hCH : centralizer (Z : Set G) ≤ H)
    (hA6 : IsA6Z3 ↥(centralizer ((((Z.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (Bar2 L)) : Set (Bar2 L)))))
    (hK : ¬ 2 ∣ Nat.card (PPrimeCoreIn p H)) :
    ∃ (A : Subgroup ↥(ImageModK p H (H ⊓ M))) (V : Subgroup ↥A) (_ : V.Normal),
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (↥A ⧸ V) 6 := by
  classical
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup (Bar2 L), Y = centralizer ((((Z.subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) : Set (Bar2 L))) := ⟨_, rfl⟩
  rw [← hYdef] at hA6
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : Subgroup G, C₀ = L ⊓ centralizer (Z : Set G) := ⟨_, rfl⟩
  have hC₀L : C₀ ≤ L := hC₀def ▸ inf_le_left
  have hC₀H : C₀ ≤ H := hC₀def ▸ (inf_le_right.trans hCH)
  have hC₀M : C₀ ≤ M := hC₀L.trans hLM
  let ρ : ↥C₀ →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hC₀L)
  have hρ : ρ.range = Y := by
    rw [hYdef, MonoidHom.range_comp, Subgroup.inclusion_range, hC₀def]
    exact r887_map_centralizer_eq_centralizer_map hZL hZ
  let ρY : ↥C₀ →* ↥Y := (MulEquiv.subgroupCongr hρ).toMonoidHom.comp ρ.rangeRestrict
  have hρY : Function.Surjective ρY :=
    (MulEquiv.subgroupCongr hρ).surjective.comp (MonoidHom.rangeRestrict_surjective ρ)
  let f : ↥C₀ →* ↥Y ⧸ Subgroup.center ↥Y := (QuotientGroup.mk' (Subgroup.center ↥Y)).comp ρY
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hρY
  let qH : ↥H →* QuotK7 p H := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)
  let φ₀ : ↥C₀ →* QuotK7 p H := qH.comp (Subgroup.inclusion hC₀H)
  have hφ₀ : ∀ c : ↥C₀, φ₀ c ∈ ImageModK p H (H ⊓ M) := by
    intro c
    refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hC₀H c, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨hC₀H c.2, hC₀M c.2⟩
  let φ : ↥C₀ →* ↥(ImageModK p H (H ⊓ M)) := φ₀.codRestrict _ hφ₀
  have hodd : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C₀.subtype ≤ PPrimeCoreIn p H := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : φ x = 1 := hx
      have hx2 : φ₀ x = 1 := congrArg Subtype.val hx1
      have hx3 : Subgroup.inclusion hC₀H x ∈ CFSG.pPrimeCore p ↥H :=
        (QuotientGroup.eq_one_iff _).mp hx2
      exact Subgroup.mem_map_of_mem H.subtype hx3
    have hcardmap : Nat.card (φ.ker.map C₀.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective C₀.subtype_injective
    have hdvd : Nat.card φ.ker ∣ Nat.card (PPrimeCoreIn p H) := by
      rw [← hcardmap]
      exact Subgroup.card_dvd_of_le hle
    exact fun h => hK (h.trans hdvd)
  have hQsimple : IsSimpleGroup (↥Y ⧸ Subgroup.center ↥Y) := hA6.1.2.1
  have hQ2 : 2 ∣ Nat.card (↥Y ⧸ Subgroup.center ↥Y) := by
    have h360 : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 360 := by
      obtain ⟨e⟩ := hA6.2.2
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
    rw [h360]
    norm_num
  obtain ⟨A, V, hV, ⟨e⟩⟩ := r887_exists_section_of_hom φ f hf hodd hQ2
  obtain ⟨e'⟩ := hA6.2.2
  exact ⟨A, V, hV, ⟨e.trans e'⟩⟩

private theorem r887_pRank_subgroupOf_eq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K D : Subgroup G} (h : K ≤ D) :
    CFSG.Open.pRank p (K.subgroupOf D) = CFSG.Open.pRank p K := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (K.subgroupOf D),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv
    (Fact.out : p.Prime).one_lt (Subgroup.subgroupOfEquivOfLe h)

private theorem r887_imageModK_opp_normal {G : Type} [Group G] [Finite G] {p : ℕ}
    {H : Subgroup G} : (ImageModK p H (Opp p H)).Normal := by
  have hOppH : ((Opp p H).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (Opp p H : Set G) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.mem_normalizer_Opp_uc6
        (Subgroup.le_normalizer g.2) p
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have h := hOppH.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    (QuotientGroup.mk'_surjective _)
  simpa [ImageModK] using h

theorem r887_of_inputs
    {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h71 : R71 D) (h72 : R72 D) (h882 : R882 D) (h885 : R885 D) (h886 : R886 D)
    (hAlt6 : FiveEmbeddedNoAlt6) : R887 D := by
  intro L P hS
  by_contra hH
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hJ, hsig, -⟩ := h885 L P hS
  obtain ⟨hZc, -, -, hA6⟩ := h886 L P hS
  have hLM : L ≤ D.M := hS.mem.1.le
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hS.mem
  have h5 : (5 : ℕ) ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 5
  have hsp : IsStronglyPEmbedded 5 D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns h5
  have hM5 : 3 ≤ CFSG.Open.pRank 5 D.M := hSg.three_le 5 h5
  have hnorm : D.M ≤ normalizer (L : Set G) :=
    (h882 L P hS).resolve_right fun h => r887_not_threeCover_of_isSpor_J2 hJ h.1
  have hZL : ZOf (P ⊓ L) ≤ L := inf_le_left.trans inf_le_right
  have hZ3 : IsPGroup 3 (ZOf (P ⊓ L)) := IsPGroup.of_card (n := 1) (by simpa using hZc)
  have hrank := r887_pRank_centralizer_ge_two hLM hnorm hZL hZ3 hJ hM5 hA6
  have hSec := r887_sec7Hyp_normalizer D hsp hZc hH hrank
  set H : Subgroup G := normalizer (ZOf (P ⊓ L) : Set G) with hHdef
  have hCH : centralizer (ZOf (P ⊓ L) : Set G) ≤ H := Subgroup.centralizer_le_normalizer _
  obtain ⟨hodd, -, -⟩ := h71 5 H hSec
  have hK : ¬ 2 ∣ Nat.card (PPrimeCoreIn 5 H) := by
    intro h
    have := Nat.odd_iff.mp hodd
    omega
  obtain ⟨hFstar, hlist⟩ := h72 5 H hSec
  have hrankH : 2 ≤ CFSG.Open.pRank 5 (H ⊓ D.M) := by
    have := hSec.2.2.2.2.2
    omega
  have hNstrong : IsStronglyPEmbedded 5 (ImageModK 5 H (H ⊓ D.M)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.isStronglyPEmbedded_map_quotient_pPrimeCore
      Nat.prime_five hsp hSec.2.2.2.2.1 hrankH
  have hnot5K : ¬ 5 ∣ Nat.card (CFSG.pPrimeCore 5 ↥H) :=
    (Nat.prime_five.coprime_iff_not_dvd).mp
      (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := 5))
  have hrk : 1 < CFSG.Open.pRank 5 (ImageModK 5 H (H ⊓ D.M)) := by
    have h1 : CFSG.Open.pRank 5 (ImageModK 5 H (H ⊓ D.M)) =
        CFSG.Open.pRank 5 ((H ⊓ D.M).subgroupOf H) :=
      CFSG.pRank_map_eq_of_not_dvd_card_ker (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H))
        (QuotientGroup.mk'_surjective _) Nat.prime_five
        (by rw [QuotientGroup.ker_mk']; exact hnot5K) ((H ⊓ D.M).subgroupOf H)
    have h2 : CFSG.Open.pRank 5 ((H ⊓ D.M).subgroupOf H) = CFSG.Open.pRank 5 (H ⊓ D.M) :=
      r887_pRank_subgroupOf_eq inf_le_left
    omega
  refine hAlt6 (QuotK7 5 H) (ImageModK 5 H (Opp 5 H)) (ImageModK 5 H (H ⊓ D.M))
    r887_imageModK_opp_normal hFstar ?_ hNstrong hrk
    (r887_alt6_section_image hLM hZL hZ3 hCH hA6 hK)
  rcases hlist with h | h | ⟨h3, -⟩ | ⟨-, h | h | h | h⟩ | ⟨h11, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · omega
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
