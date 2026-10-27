module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R876
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7M
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelSmallOrders
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OutRows
import CFSG.RankThree.PartTwo.Sec5.Bender.Core
import CFSG.GroupTheory.OppositeRadicals
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Fstar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsL3 IsSpor IsAlt Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (QuotK7 ImageModK LKQuot7 IsAutSz IsReeType)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def HasL34Section {Q : Type} [Group Q] (X : Subgroup Q) : Prop :=
  ∃ Y : Subgroup Q, Y ≤ X ∧ ∃ (N : Subgroup ↥Y) (_ : N.Normal), IsL3 (↥Y ⧸ N) 2

@[expose] def S7ListL34 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (p : ℕ) (Y : Subgroup Q), p.Prime → 5 ≤ p → p ≠ 7 →
    genFittingFStar Q ≤ Y → CFSG.pPrimeCore p Q = ⊥ →
    ((∃ m : ℕ, LieModel ↥Y .PSL 2 p m) ∨ (∃ m : ℕ, LieModel ↥Y .PSU 3 p m) ∨
      (p = 3 ∧ (IsReeType ↥Y 1 ∨ IsSpor ↥Y .M11 ∨ IsL3 ↥Y 2)) ∨
      (p = 5 ∧ (IsAutSz ↥Y 5 ∨ LieModel ↥Y .Tits 0 2 1 ∨ IsSpor ↥Y .McL ∨ IsAlt ↥Y 10)) ∨
      (p = 11 ∧ IsSpor ↥Y .J4)) →
    HasL34Section (⊤ : Subgroup Q) → (p = 5 ∧ IsSpor ↥Y .McL) ∨ (p = 11 ∧ IsSpor ↥Y .J4)

@[expose] def S7J4Rank : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (Y : Subgroup Q), genFittingFStar Q ≤ Y →
    IsSpor ↥Y .J4 → CFSG.Open.pRank 11 (⊤ : Subgroup Q) ≤ 2

private theorem s7crk_prime_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ 241920) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)))

private theorem s7crk_pow_dvd {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ k ∣ 241920) :
    k ≤ 1 ∧ (11 ≤ p → k = 0) := by
  refine ⟨?_, fun h11 => ?_⟩
  · by_contra hk
    have h2 : p ^ 2 ∣ 241920 := (pow_dvd_pow p (by omega : 2 ≤ k)).trans h
    have hp1 : p ∣ 241920 := (dvd_pow_self p two_ne_zero).trans h2
    rcases s7crk_prime_dvd hp hp1 with rfl | rfl | rfl | rfl <;> omega
  · by_contra hk
    have hp1 : p ∣ 241920 := (dvd_pow_self p hk).trans h
    rcases s7crk_prime_dvd hp hp1 with rfl | rfl | rfl | rfl <;> omega

private theorem s7crk_card_mulAut {X : Type} [Group X] (hL : LieModel X .PSL 3 2 2) :
    Nat.card (MulAut X) ∣ 241920 := by
  have h1 : Nat.card (MulAut X) = Nat.card (Outer X) *
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ∣ 20160 := by
    rw [← CFSG.Blueprint.LieModel.card_psl_three_four hL]
    exact Subgroup.card_range_dvd _
  rw [h1]
  exact (mul_dvd_mul (CFSG.EvenSporadicStandard.HSStd.InvCent.Harada.card_outer_L34 hL) h2).trans
    (by norm_num)

private theorem s7crk_ker_card {B X : Type} [Group B] [Group X] {p m : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hB : Nat.card B = p ^ m) (hX : Nat.card X ∣ 241920) (φ : B →* X) :
    ∃ k, Nat.card φ.ker = p ^ k ∧ m ≤ k + 1 ∧ (11 ≤ p → m ≤ k) := by
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hB] at h1
  obtain ⟨j, -, hjr⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ h1)
  obtain ⟨k, -, hkr⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ h1)
  have hjX : p ^ j ∣ 241920 :=
    hjr ▸ (Subgroup.card_subgroup_dvd_card φ.range).trans hX
  have hpj := s7crk_pow_dvd hp hp5 hjX
  have hsum : k + j = m := by
    rw [hkr, hjr, ← pow_add] at h1
    exact Nat.pow_right_injective hp.two_le h1
  exact ⟨k, hkr, by omega, fun h11 => by have := hpj.2 h11; omega⟩

private theorem s7crk_centralize {G : Type} [Group G] {S : Subgroup G} (hS : Nat.card S = 7)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {b : G}
    (hb : b ∈ Subgroup.normalizer (S : Set G)) (hbp : b ^ p = 1) :
    b ∈ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : IsCyclic S := isCyclic_of_prime_card hS
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  have hcard : Nat.card (MulAut S) = 6 := by
    rw [IsCyclic.card_mulAut, hS, Nat.totient_prime (by norm_num)]
  have hp6 : ¬ p ∣ 6 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp (by norm_num; exact h : p ∣ 2 * 3) with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3; omega
  set φ := Subgroup.normalizerMonoidHom S ⟨b, hb⟩ with hφ
  have hφp : φ ^ p = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨b, hb⟩ : Subgroup.normalizer (S : Set G)) ^ p = 1 := Subtype.ext (by simpa using hbp)
    rw [this, map_one]
  have hφ1 : φ = 1 :=
    CFSG.RankThree.PartTwo.Sec5.Bender.eq_one_of_orderOf_dvd_of_pPow hp ⟨1, by simpa using hφp⟩
      (hcard ▸ orderOf_dvd_natCard φ) hp6
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 : φ ⟨s, hs⟩ = ⟨s, hs⟩ := by rw [hφ1]; rfl
  have h2 : b * s * b⁻¹ = s := congrArg Subtype.val h1
  calc s * b = (b * s * b⁻¹) * b := by rw [h2]
    _ = b * s := by group


private theorem s7crk_le_normalizer {G : Type} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : H ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h x hx k hk, fun hk => ?_⟩
  have h1 := h x⁻¹ (inv_mem hx) _ hk
  have e : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
  rwa [e] at h1

private theorem s7crk_index {G : Type} [Group G] [Finite G] {A O : Subgroup G}
    (hA7 : Nat.card A = 7) (hO : IsPGroup 2 O) (hAO : A ≤ Subgroup.normalizer (O : Set G)) :
    ∃ j, (A.subgroupOf (A ⊔ O)).index = 2 ^ j := by
  obtain ⟨n, hn⟩ := hO.exists_card_eq
  set Γ : Subgroup G := A ⊔ O with hΓ
  have hAΓ : A ≤ Γ := le_sup_left
  have hOΓ : O ≤ Γ := le_sup_right
  have h1 : Nat.card Γ = Nat.card (Γ ⧸ O.subgroupOf Γ) * Nat.card (O.subgroupOf Γ) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (Γ ⧸ O.subgroupOf Γ) ∣ 7 := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hAO
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAO
    have e := Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient A O hAO).toEquiv
    rw [← e, ← hA7]
    exact Subgroup.index_dvd_card _
  have h3 : Nat.card (O.subgroupOf Γ) = 2 ^ n := by
    rw [← hn]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOΓ).toEquiv
  have h4 : Nat.card (A.subgroupOf Γ) = 7 := by
    rw [← hA7]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΓ).toEquiv
  have h5 := Subgroup.index_mul_card (A.subgroupOf Γ)
  rw [h4, h1, h3] at h5
  have h6 : (A.subgroupOf Γ).index ∣ 2 ^ n := by
    refine Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) ?_
    calc 7 * (A.subgroupOf Γ).index = (A.subgroupOf Γ).index * 7 := mul_comm _ _
      _ = Nat.card (Γ ⧸ O.subgroupOf Γ) * 2 ^ n := h5
      _ ∣ 7 * 2 ^ n := mul_dvd_mul_right h2 _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h6
  exact ⟨j, hj⟩

open scoped Pointwise in
private theorem s7crk_fixed_sylow {Γ E : Type} [Group Γ] [Finite Γ] [Group E] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hE : IsPGroup p E) (ρ : E →* MulAut Γ)
    (hcount : ¬ p ∣ Nat.card (Sylow q Γ)) :
    ∃ Q : Sylow q Γ, ∀ e : E, ∀ γ ∈ (Q : Subgroup Γ), ρ e γ ∈ (Q : Subgroup Γ) := by
  let : MulDistribMulAction E Γ := MulDistribMulAction.compHom Γ ρ
  obtain ⟨Q, hQ⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q Γ) hcount
  refine ⟨Q, fun e γ hγ => ?_⟩
  have h : e • Q = Q := hQ e
  have h2 : e • (Q : Subgroup Γ) = (Q : Subgroup Γ) := by
    rw [← Sylow.pointwise_smul_def, h]
  rw [← h2]
  exact Subgroup.smul_mem_pointwise_smul γ e _ hγ


open scoped Pointwise in
private theorem s7crk_exists_conj {G : Type} [Group G] [Finite G] {A O B₀ : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hA7 : Nat.card A = 7) (hO : IsPGroup 2 O)
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) (hB₀ : IsPGroup p B₀)
    (hinv : ∀ b ∈ B₀, ∀ y ∈ A ⊔ O, b * y * b⁻¹ ∈ A ⊔ O) (hp2 : p ≠ 2) :
    ∃ x ∈ A ⊔ O, ∀ b ∈ B₀, ∀ s ∈ A.map (MulAut.conj x⁻¹).toMonoidHom,
      b * s * b⁻¹ ∈ A.map (MulAut.conj x⁻¹).toMonoidHom := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set Γ : Subgroup G := A ⊔ O with hΓ
  have hAΓ : A ≤ Γ := le_sup_left
  have hB₀N : B₀ ≤ Subgroup.normalizer (Γ : Set G) := s7crk_le_normalizer hinv
  let ρ : ↥B₀ →* MulAut ↥Γ := (Subgroup.normalizerMonoidHom Γ).comp (Subgroup.inclusion hB₀N)
  obtain ⟨j, hj⟩ := s7crk_index hA7 hO hAO
  have hA₀card : Nat.card (A.subgroupOf Γ) = 7 := by
    rw [← hA7]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΓ).toEquiv
  have hA₀p : IsPGroup 7 ↥(A.subgroupOf Γ) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA₀card)
  have h7 : ¬ 7 ∣ (A.subgroupOf Γ).index := by
    rw [hj]; intro h
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
    norm_num at this
  let P : Sylow 7 ↥Γ := hA₀p.toSylow h7
  have hcount : ¬ p ∣ Nat.card (Sylow 7 ↥Γ) := by
    intro h
    have h2 : p ∣ (A.subgroupOf Γ).index := h.trans (Sylow.card_dvd_index P)
    rw [hj] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  obtain ⟨Q, hQ⟩ := s7crk_fixed_sylow hB₀ ρ hcount
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Γ P Q
  have hQeq : (Q : Subgroup ↥Γ) = MulAut.conj g • (P : Subgroup ↥Γ) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  refine ⟨(g : G)⁻¹, inv_mem g.2, fun b hb s hs => ?_⟩
  rw [inv_inv] at hs ⊢
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hs
  have haP : (⟨a, hAΓ ha⟩ : ↥Γ) ∈ (P : Subgroup ↥Γ) := ha
  have hq : MulAut.conj g ⟨a, hAΓ ha⟩ ∈ (Q : Subgroup ↥Γ) := by
    rw [hQeq]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ haP
  have hq2 := hQ ⟨b, hb⟩ _ hq
  rw [hQeq, Subgroup.mem_smul_pointwise_iff_exists] at hq2
  obtain ⟨a', ha', hea⟩ := hq2
  refine Subgroup.mem_map.mpr ⟨(a' : G), ha', ?_⟩
  exact congrArg Subtype.val hea


private theorem s7crk_pCore_normalized {G : Type} [Group G] {L A : Subgroup G} (hAL : A ≤ L) :
    A ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) := by
  refine s7crk_le_normalizer (fun x hx k hk => ?_)
  obtain ⟨n, hn, rfl⟩ := hk
  exact ⟨⟨x, hAL hx⟩ * n * ⟨x, hAL hx⟩⁻¹, (CFSG.pCore_normal (p := 2)).conj_mem n hn _, rfl⟩

private theorem s7crk_trivial_bar {G : Type} [Group G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (h1 : barAction L ⟨b, hb⟩ = 1) {y : G}
    (hy : y ∈ L) : y⁻¹ * (b * y * b⁻¹) ∈ pCoreOf 2 L := by
  have h2 : barAction L ⟨b, hb⟩ (QuotientGroup.mk ⟨y, hy⟩ : Bar2 L) =
      (QuotientGroup.mk ⟨y, hy⟩ : Bar2 L) := by
    rw [h1]; rfl
  rw [barAction_mk] at h2
  exact ⟨_, QuotientGroup.eq.mp h2.symm, rfl⟩

private theorem s7crk_inv_sup {G : Type} [Group G] {L A : Subgroup G} {b : G} (hAL : A ≤ L)
    (hb : ∀ y ∈ L, y⁻¹ * (b * y * b⁻¹) ∈ pCoreOf 2 L) :
    ∀ y ∈ A ⊔ pCoreOf 2 L, b * y * b⁻¹ ∈ A ⊔ pCoreOf 2 L := by
  have hOL : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have key : A ⊔ pCoreOf 2 L ≤ (A ⊔ pCoreOf 2 L).comap (MulAut.conj b).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun o ho => ?_)
    · have h1 := hb a (hAL ha)
      have e : b * a * b⁻¹ = a * (a⁻¹ * (b * a * b⁻¹)) := by group
      show b * a * b⁻¹ ∈ A ⊔ pCoreOf 2 L
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right h1)
    · have h1 := hb o (hOL ho)
      have e : b * o * b⁻¹ = o * (o⁻¹ * (b * o * b⁻¹)) := by group
      show b * o * b⁻¹ ∈ A ⊔ pCoreOf 2 L
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ho) (Subgroup.mem_sup_right h1)
  exact fun y hy => key hy

theorem s7_conj_rank {G : Type} [Group G] [Finite G] {M L A : Subgroup G} (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) (hL : IsL3 (Bar2 L) 2) (hAL : A ≤ L)
    (hA7 : Nat.card A = 7) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ x ∈ L,
      CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer
        ((A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G)) + 1 ∧
      (11 ≤ p → CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer
        ((A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G))) := by
  have _ := hLM
  obtain ⟨B, hBM, hBe, hBcard⟩ := Nat.sSup_mem
    (CFSG.PreuniquenessRankFour.Helpers.pRank_nonempty p M)
    (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp M)
  have hBm : Nat.card B = p ^ CFSG.Open.pRank p M := hBcard
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBM.trans hML
  let θ : ↥B →* MulAut (Bar2 L) := (barAction L).comp (Subgroup.inclusion hBN)
  obtain ⟨k, hk, hmk, hmk11⟩ := s7crk_ker_card hp hp5 hBm (s7crk_card_mulAut hL) θ
  let B₀ : Subgroup G := θ.ker.map B.subtype
  have hB₀B : B₀ ≤ B := Subgroup.map_subtype_le _
  have hB₀card : Nat.card B₀ = p ^ k := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hk]
  have hB₀e : IsElemAbelian p B₀ :=
    ⟨isMulCommutative_iff.mpr fun a b => by
      have hab := isMulCommutative_iff.mp hBe.1 (Subgroup.inclusion hB₀B a)
        (Subgroup.inclusion hB₀B b)
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥B → G) hab, fun x hx => hBe.2 x (hB₀B hx)⟩
  have htriv : ∀ b ∈ B₀, ∀ y ∈ L, y⁻¹ * (b * y * b⁻¹) ∈ pCoreOf 2 L := by
    rintro _ ⟨b', hb', rfl⟩ y hy
    exact s7crk_trivial_bar (hBN b'.2) hb' hy
  have hO : IsPGroup 2 (pCoreOf 2 L) := CFSG.pCore_isPGroup.map L.subtype
  have hB₀p : IsPGroup p B₀ := fun g => ⟨1, Subtype.ext (by simpa using hB₀e.2 g.1 g.2)⟩
  obtain ⟨x, hxΓ, hxn⟩ := s7crk_exists_conj hp hA7 hO (s7crk_pCore_normalized hAL) hB₀p
    (fun b hb => s7crk_inv_sup hAL (htriv b hb)) (by omega)
  refine ⟨x, sup_le hAL (Subgroup.map_subtype_le _) hxΓ, ?_⟩
  set S : Subgroup G := A.map (MulAut.conj x⁻¹).toMonoidHom with hS
  have hScard : Nat.card S = 7 := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hA7]
  have hB₀le : B₀ ≤ M ⊓ Subgroup.centralizer (S : Set G) := fun b hb =>
    ⟨hBM (hB₀B hb), s7crk_centralize hScard hp hp5 (s7crk_le_normalizer hxn hb) (hB₀e.2 b hb)⟩
  have hkle : k ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (S : Set G)) :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp _)
      ⟨B₀, hB₀le, hB₀e, hB₀card⟩
  exact ⟨by omega, fun h11 => by have := hmk11 h11; omega⟩

private theorem s7ccf_map_eq_self {G : Type} [Group G] {K : Subgroup G} {x : G} (hx : x ∈ K) :
    K.map (MulAut.conj x⁻¹).toMonoidHom = K := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h := K.mul_mem (K.mul_mem (K.inv_mem hx) hk) hx
    simpa [MulAut.conj_apply] using h
  · intro hy
    refine ⟨x * y * x⁻¹, K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

private theorem s7ccf_map_conj_comp {G : Type} [Group G] (a b : G) (K : Subgroup G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem s7ccf_normalizer_map {G : Type} [Group G] (x : G) (H : Subgroup G) :
    (Subgroup.normalizer (H : Set G)).map (MulAut.conj x⁻¹).toMonoidHom =
      Subgroup.normalizer ((H.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq H (MulAut.conj x⁻¹)

private theorem s7ccf_loc {G : Type} [Group G] [Finite G] {M L Z : Subgroup G}
    (c : Loc876 M L Z) {x : G} (hx : x ∈ L) :
    Loc876 M L (Z.map (MulAut.conj x⁻¹).toMonoidHom) where
  maxLocal := c.maxLocal
  le := c.le
  norm := c.norm
  shape := c.shape
  hZL := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) c.hZL
    rwa [s7ccf_map_eq_self hx] at h
  hZ3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact c.hZ3
  hZN := by
    rw [← s7ccf_normalizer_map]
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) c.hZN
    rwa [s7ccf_map_eq_self (c.le hx)] at h
  sylowU := c.sylowU

private theorem s7ccf_cfg0 {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg0876 M L Z Y g) {x : G} (hx : x ∈ L) :
    Cfg0876 M L (Z.map (MulAut.conj x⁻¹).toMonoidHom) (Y.map (MulAut.conj x⁻¹).toMonoidHom)
      (x⁻¹ * g * x) where
  loc := s7ccf_loc c.loc hx
  hg := fun h => c.hg (by
    have hxM : x ∈ M := c.loc.le hx
    have h1 := M.mul_mem (M.mul_mem hxM h) (M.inv_mem hxM)
    have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
    rwa [e] at h1)
  hY := by
    rw [c.hY, s7ccf_map_conj_comp, s7ccf_map_conj_comp,
      show (x⁻¹ * g * x)⁻¹ * x⁻¹ = x⁻¹ * g⁻¹ by group]
  hYM := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) c.hYM
    rwa [s7ccf_map_eq_self (c.loc.le hx)] at h

private theorem s7ccf_cfg {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg876 M L Z Y g) {x : G} (hx : x ∈ L) :
    Cfg876 M L (Z.map (MulAut.conj x⁻¹).toMonoidHom) (Y.map (MulAut.conj x⁻¹).toMonoidHom)
      (x⁻¹ * g * x) where
  base := s7ccf_cfg0 c.base hx
  hZY := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have h := congrArg (MulAut.conj x⁻¹) (Subgroup.mem_centralizer_iff.mp (c.hZY hy) z hz)
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h

private theorem s7ccf_aconf {G : Type} [Group G] [Finite G] {L Z Y A : Subgroup G} {g : G}
    (hA : AConf876 L Z Y g A) {x : G} (hx : x ∈ L) :
    AConf876 L (Z.map (MulAut.conj x⁻¹).toMonoidHom) (Y.map (MulAut.conj x⁻¹).toMonoidHom)
      (x⁻¹ * g * x) (A.map (MulAut.conj x⁻¹).toMonoidHom) where
  le := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨hac, haL⟩ := Subgroup.mem_inf.mp (hA.le ha)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have h := congrArg (MulAut.conj x⁻¹) (Subgroup.mem_centralizer_iff.mp hac y hy)
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h
    · have h := L.mul_mem (L.mul_mem (L.inv_mem hx) haL) hx
      simpa [MulAut.conj_apply] using h
  card := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hA.card
  normZ := by
    rw [← s7ccf_normalizer_map]
    exact Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hA.normZ
  comm := by
    rw [← Subgroup.map_commutator, hA.comm]
  trivBar := by
    have h1 : L.map (MulAut.conj x).toMonoidHom = L := by
      simpa using s7ccf_map_eq_self (inv_mem hx)
    have hL : L.map (MulAut.conj (x⁻¹ * g * x)⁻¹).toMonoidHom =
        (L.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [s7ccf_map_conj_comp, show (x⁻¹ * g * x)⁻¹ = x⁻¹ * g⁻¹ * x by group,
        ← s7ccf_map_conj_comp (x⁻¹ * g⁻¹) x L, h1]
    rw [hL, ← Subgroup.map_commutator,
      CFSG.GroupTheory.pCoreOf_map_of_injective 2 _ (MulAut.conj x⁻¹).injective]
    exact Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hA.trivBar

private theorem s7ccf_norm_back {G : Type} [Group G] {M A : Subgroup G} {x : G} (hxM : x ∈ M) :
    Subgroup.normalizer ((A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ M →
      Subgroup.normalizer (A : Set G) ≤ M := by
  intro h n hn
  have h1 : x⁻¹ * n * x ∈
      Subgroup.normalizer ((A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [← s7ccf_normalizer_map]
    exact ⟨n, hn, by simp⟩
  have h2 := M.mul_mem (M.mul_mem hxM (h h1)) (M.inv_mem hxM)
  have e : x * (x⁻¹ * n * x) * x⁻¹ = n := by group
  rwa [e] at h2

theorem s7_conj_cfg {G : Type} [Group G] [Finite G] {M L Z Y A : Subgroup G} {g : G}
    (c : Cfg876 M L Z Y g) (hA : AConf876 L Z Y g A) {x : G} (hx : x ∈ L) :
    Cfg876 M L (Z.map (MulAut.conj x⁻¹).toMonoidHom) (Y.map (MulAut.conj x⁻¹).toMonoidHom)
        (x⁻¹ * g * x) ∧
      AConf876 L (Z.map (MulAut.conj x⁻¹).toMonoidHom) (Y.map (MulAut.conj x⁻¹).toMonoidHom)
        (x⁻¹ * g * x) (A.map (MulAut.conj x⁻¹).toMonoidHom) ∧
      (Subgroup.normalizer ((A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ M →
        Subgroup.normalizer (A : Set G) ≤ M) :=
  ⟨s7ccf_cfg c hx, s7ccf_aconf hA hx, s7ccf_norm_back (c.base.loc.le hx)⟩

private theorem s7_normalizer_le_normalizer_centralizer {G : Type} [Group G]
    (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      have h1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      exact (hg _).mpr (by rw [h1]; exact ha)
    have hc := hh _ ha'
    calc a * (g * h * g⁻¹) = g * ((g⁻¹ * a * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * a * g)) * g⁻¹ := by rw [hc]
      _ = g * h * g⁻¹ * a := by group
  · intro hh a ha
    have ha' : g * a * g⁻¹ ∈ A := (hg a).mp ha
    have hc := hh _ ha'
    calc a * h = g⁻¹ * ((g * a * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * a * g⁻¹)) * g := by rw [hc]
      _ = h * a := by group

private theorem s7noc_normalizer_map_subtype {G : Type} [Group G] {N : Subgroup G}
    {Q : Subgroup ↥N} {n : ↥N} (hn : n ∈ Subgroup.normalizer (Q : Set ↥N)) :
    (n : G) ∈ Subgroup.normalizer ((Q.map N.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨n * q * n⁻¹, (hn q).mp hq, rfl⟩
  · rintro ⟨q, hq, hqh⟩
    refine ⟨n⁻¹ * q * n, (hn (n⁻¹ * q * n)).mpr (by simpa [mul_assoc] using hq), ?_⟩
    have e : (n : G)⁻¹ * (q : G) * n = h := by
      rw [show (q : G) = n * h * (n : G)⁻¹ from hqh]
      group
    exact e

private theorem s7noc_frattini {G : Type} [Group G] [Finite G] {N C M : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hCN : C ≤ N) (hNC : N ≤ Subgroup.normalizer (C : Set G)) (hCM : C ≤ M)
    (hdvd : p ∣ Nat.card C)
    (hM : ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ → IsPGroup p X →
      Subgroup.normalizer (X : Set G) ≤ M) : N ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  have hC' : (C.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr hNC
  have hdvd' : p ∣ Nat.card (C.subgroupOf N) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
  obtain ⟨P⟩ : Nonempty (Sylow p ↥(C.subgroupOf N)) := inferInstance
  have hP1 := P.ne_bot_of_dvd_card hdvd'
  have hP₀C : ((P : Subgroup ↥(C.subgroupOf N)).map (C.subgroupOf N).subtype).map N.subtype ≤ C := by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp x.2
  have hP₀1 : ((P : Subgroup ↥(C.subgroupOf N)).map (C.subgroupOf N).subtype).map N.subtype ≠ ⊥ :=
    fun h => hP1 ((Subgroup.map_eq_bot_iff_of_injective _ (C.subgroupOf N).subtype_injective).mp
      ((Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h))
  have hN := hM _ (hP₀C.trans hCM) hP₀1
    ((P.isPGroup'.map (C.subgroupOf N).subtype).map N.subtype)
  intro g hg
  have hmem : (⟨g, hg⟩ : ↥N) ∈ (↑(Subgroup.normalizer
      ((P : Subgroup ↥(C.subgroupOf N)).map (C.subgroupOf N).subtype : Set ↥N) ⊔ C.subgroupOf N)
      : Set ↥N) := by
    rw [Sylow.normalizer_sup_eq_top P]
    trivial
  rw [Subgroup.mul_normal] at hmem
  obtain ⟨n, hn, c, hc, hnc⟩ := hmem
  have hg' : g = (n : G) * (c : G) := (congrArg Subtype.val hnc).symm
  rw [hg']
  exact M.mul_mem (hN (s7noc_normalizer_map_subtype hn))
    (hCM (Subgroup.mem_subgroupOf.mp hc))

theorem s7_norm_of_cent {G : Type} [Group G] [Finite G] {M A : Subgroup G} {p : ℕ}
    (hp : p.Prime)
    (hM : ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ → IsPGroup p X →
      Subgroup.normalizer (X : Set G) ≤ M)
    (hrk : 1 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)))
    (hC : Subgroup.centralizer (A : Set G) ≤ M) : Subgroup.normalizer (A : Set G) ≤ M := by
  obtain ⟨z, hz, hzp⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hp hrk
  have hdvd : p ∣ Nat.card (Subgroup.centralizer (A : Set G)) := by
    have h := orderOf_dvd_natCard (⟨z, (Subgroup.mem_inf.mp hz).2⟩ :
      ↥(Subgroup.centralizer (A : Set G)))
    rwa [← Subgroup.orderOf_coe, hzp] at h
  exact s7noc_frattini hp (Subgroup.centralizer_le_normalizer _)
    (s7_normalizer_le_normalizer_centralizer A) hC hdvd hM

open scoped commutatorElement in
private theorem s7sec_le_normalizer {G : Type} [Group G] {A X : Subgroup G}
    (htr : ⁅A, X⁆ ≤ pCoreOf 2 X) : A ≤ Subgroup.normalizer (X : Set G) := by
  have key : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X := by
    intro a ha x hx
    have h1 : ⁅a, x⁆ ∈ pCoreOf 2 X := htr (Subgroup.commutator_mem_commutator ha hx)
    have h2 : ⁅a, x⁆ ∈ X := Subgroup.map_subtype_le _ h1
    have e : a * x * a⁻¹ = ⁅a, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e]
    exact X.mul_mem h2 hx
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  have h := key a⁻¹ (inv_mem ha) _ hx
  have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
  rwa [e] at h

open scoped commutatorElement in
private theorem s7sec_cover {G : Type} [Group G] [Finite G] {X A : Subgroup G}
    (hA7 : Nat.card A = 7) (htr : ⁅A, X⁆ ≤ pCoreOf 2 X) (x : ↥X) :
    ∃ c : ↥X, x⁻¹ * c ∈ CFSG.pCore 2 ↥X ∧ (c : G) ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hAN := s7sec_le_normalizer htr
  let α : ↥A →* MulAut ↥X := (Subgroup.normalizerMonoidHom X).comp (Subgroup.inclusion hAN)
  have hA7' : IsPGroup 7 ↥A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA7)
  have hcop : ¬ 7 ∣ Nat.card (CFSG.pCore 2 ↥X) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
    norm_num at this
  have htr' : ∀ (a : ↥A) (y : ↥X), y⁻¹ * α a y ∈ CFSG.pCore 2 ↥X := by
    intro a y
    obtain ⟨n, hn, hne⟩ := htr (Subgroup.commutator_mem_commutator a.2 y.2)
    have hmem := (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem n hn y⁻¹
    rw [inv_inv] at hmem
    have e : y⁻¹ * α a y = y⁻¹ * n * y := by
      apply Subtype.ext
      have hn' : (n : G) = (a : G) * (y : G) * (a : G)⁻¹ * (y : G)⁻¹ := hne
      change (y : G)⁻¹ * ((a : G) * (y : G) * (a : G)⁻¹) = (y : G)⁻¹ * (n : G) * (y : G)
      rw [hn']
      group
    rw [e]
    exact hmem
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 7 hA7' α
    (CFSG.pCore 2 ↥X) hcop x).2 (fun a y hy => by
      have h := (CFSG.pCore 2 ↥X).mul_mem hy (htr' a y)
      simpa [mul_assoc] using h)
  refine ⟨c, hc, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h : a * (c : G) * a⁻¹ = c := congrArg Subtype.val (hfix ⟨a, ha⟩)
  calc a * (c : G) = (a * (c : G) * a⁻¹) * a := by group
    _ = c * a := by rw [h]

private theorem s7sec_simple_ker {H : Type} [Group H] {K V : Subgroup H} [K.Normal] {Q : Type}
    [Group Q] [Finite Q] (hS : IsSimpleGroup Q) (hev : 2 ∣ Nat.card Q) (hodd : Odd (Nat.card K))
    (ρ : ↥V →* Q) (hρ : Function.Surjective ρ) (v : ↥V) (hv : (v : H) ∈ K) : ρ v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : ((K.comap V.subtype).map ρ).Normal :=
    (Subgroup.Normal.comap inferInstance V.subtype).map ρ hρ
  rcases hS.eq_bot_or_eq_top_of_normal ((K.comap V.subtype).map ρ) with h | h
  · have hmem : ρ v ∈ (K.comap V.subtype).map ρ := ⟨v, hv, rfl⟩
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exfalso
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have ht' : t ∈ (K.comap V.subtype).map ρ := by rw [h]; trivial
    obtain ⟨k, hk, rfl⟩ := ht'
    have h1 : 2 ∣ orderOf k := ht ▸ orderOf_map_dvd ρ k
    have h2 : orderOf k ∣ Nat.card K := by
      have hkK : (k : H) ∈ K := hk
      have := orderOf_dvd_natCard (⟨(k : H), hkK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at this
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h1.trans h2))

private theorem s7sec_exists_surj {H : Type} [Group H] {K V : Subgroup H} [K.Normal] {Q : Type}
    [Group Q] (ρ : ↥V →* Q) (hρ : Function.Surjective ρ)
    (hk : ∀ v : ↥V, (v : H) ∈ K → ρ v = 1) :
    ∃ σ : ↥(V.map (QuotientGroup.mk' K)) →* Q, Function.Surjective σ := by
  let π := (QuotientGroup.mk' K).subgroupMap V
  have hπ := MonoidHom.subgroupMap_surjective (QuotientGroup.mk' K) V
  have hker : π.ker ≤ ρ.ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    refine hk v ((QuotientGroup.eq_one_iff _).mp ?_)
    exact congrArg Subtype.val hv
  refine ⟨(MonoidHom.liftOfSurjective π hπ) ⟨ρ, hker⟩, fun q => ?_⟩
  obtain ⟨v, rfl⟩ := hρ q
  exact ⟨π v, MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ, hker⟩ v⟩

theorem s7_section {G : Type} [Group G] [Finite G] {M L Z Y A : Subgroup G} {g : G} {p : ℕ}
    (c : Cfg876 M L Z Y g) (hA : AConf876 L Z Y g A)
    (hodd : Odd (Nat.card (CFSG.pPrimeCore p ↥(Subgroup.centralizer (A : Set G))))) :
    HasL34Section (⊤ : Subgroup (QuotK7 p (Subgroup.centralizer (A : Set G)))) := by
  set H : Subgroup G := Subgroup.centralizer (A : Set G) with hH
  set Lg : Subgroup G := L.map (MulAut.conj g⁻¹).toMonoidHom with hLg
  have hshape : IsL3 (Bar2 Lg) 2 := (r876_cfg_symm c).base.loc.shape
  have hsimp : IsSimpleGroup (Bar2 Lg) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hshape
  have hcard : Nat.card (Bar2 Lg) = 20160 := CFSG.Blueprint.LieModel.card_psl_three_four hshape
  have hKn : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal
  let V : Subgroup ↥H := (Lg ⊓ H).subgroupOf H
  let φ : ↥V →* ↥Lg :=
    { toFun := fun v => ⟨((v : ↥H) : G),
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp v.2)).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ρ : ↥V →* Bar2 Lg := (QuotientGroup.mk' (CFSG.pCore 2 ↥Lg)).comp φ
  have hρ : Function.Surjective ρ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c', hc', hcH⟩ := s7sec_cover hA.card hA.trivBar x
    exact ⟨⟨⟨c', hcH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨c'.2, hcH⟩)⟩,
      (QuotientGroup.eq.mpr hc').symm⟩
  have hk := s7sec_simple_ker (K := CFSG.pPrimeCore p ↥H) hsimp
    (by rw [hcard]; norm_num) hodd ρ hρ
  obtain ⟨σ, hσ⟩ := s7sec_exists_surj ρ hρ hk
  exact ⟨_, le_top, σ.ker, σ.normal_ker,
    CFSG.Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective σ hσ).symm
      hshape⟩

theorem s7_j4_false (hJ4 : S7J4Rank) {G : Type} [Group G] [Finite G] {H M : Subgroup G}
    (hF : genFittingFStar (QuotK7 11 H) ≤ ImageModK 11 H (Opp 11 H))
    (hE : IsSpor (LKQuot7 11 H) .J4) (hrk : 3 ≤ CFSG.Open.pRank 11 (H ⊓ M)) : False := by
  have hp : Nat.Prime 11 := by norm_num
  have : Fact (Nat.Prime 11) := ⟨hp⟩
  have h2 : CFSG.Open.pRank 11 (⊤ : Subgroup (QuotK7 11 H)) ≤ 2 :=
    hJ4 (QuotK7 11 H) (ImageModK 11 H (Opp 11 H)) hF hE
  have hK : ¬ 11 ∣ Nat.card (CFSG.pPrimeCore 11 ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp CFSG.pPrimeCore_coprime_card
  have hq : CFSG.Open.pRank 11 (⊤ : Subgroup (QuotK7 11 H)) =
      CFSG.Open.pRank 11 (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore 11 ↥H) hK
  have h3 : CFSG.Open.pRank 11 (H ⊓ M) ≤ CFSG.Open.pRank 11 H :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono 11 hp inf_le_left
  have h4 : CFSG.Open.pRank 11 H = CFSG.Open.pRank 11 (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup H
  omega

private theorem s7iop_normal {X : Type} [Group X] (p : ℕ) :
    (CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup X)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hle : (CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup X)).map
        (MulAut.conj g).toMonoidHom ≤ CFSG.RankThree.PartOne.pElementSubgroup p ⊤ := by
    unfold CFSG.RankThree.PartOne.pElementSubgroup
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, ⟨-, j, hj⟩, rfl⟩
    exact ⟨Subgroup.mem_top _, j, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hj]⟩
  exact hle ⟨x, hx, by simp [MulAut.conj_apply]⟩

private theorem s7iop_mem {X : Type} [Group X] {p : ℕ} (hp : p.Prime) {x : X}
    (hx : IsPGroup p (Subgroup.zpowers x)) :
    x ∈ CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hx ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  exact Subgroup.subset_closure ⟨Subgroup.mem_top _, k, hk⟩

theorem s7_image_opp {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    (ImageModK p H (Opp p H)).Normal ∧
      ∀ x : QuotK7 p H, IsPGroup p (Subgroup.zpowers x) → x ∈ ImageModK p H (Opp p H) := by
  rw [CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.imageModK_opp_eq_pElementSubgroup hp H]
  exact ⟨s7iop_normal p, fun x hx => s7iop_mem hp hx⟩

private theorem s7_not_solvable {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hLM : L ≤ M) (hL : IsL3 (Bar2 L) 2) : ¬ Group.IsSolvable ↥M := by
  intro hs
  have : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLM)
      (Subgroup.inclusion_injective hLM)
  have hsol : Group.IsSolvable (Bar2 L) := inferInstance
  have hsimp : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  have : IsMulCommutative (Bar2 L) := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hsol⟩⟩
  have hprime : (Nat.card (Bar2 L)).Prime := Group.is_simple_iff_prime_card.mp hsimp
  rw [CFSG.Blueprint.LieModel.card_psl_three_four hL] at hprime
  norm_num at hprime

private theorem s7_centralizer_ne_top {G : Type} [Group G] {A Z : Subgroup G} (hA : A ≠ ⊥)
    (hc : ⁅A, Z⁆ = A) : Subgroup.centralizer (A : Set G) ≠ ⊤ := by
  intro htop
  apply hA
  rw [← hc, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mpr (by rw [htop]; exact le_top)

private theorem s7_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  by_contra hlt
  interval_cases p
  · exact hp2 rfl
  · exact hp3 rfl
  · exact absurd hp (by norm_num)

theorem s7_876_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (h71 : UC22.F07.R71 D)
    (h72 : UC22.F07.R72 D) (hSimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL)
    (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    (hOut : Nat.card (Outer CFSG.Blueprint.NativeSporadic.McL) ≤ 2)
    (hMult : ∀ {Q : Type} [Group Q], Group.IsPerfect Q →
      (Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.McL) →
        Nat.card (Subgroup.center Q) ∣ 3)
    (hCent : McLThreeCentralizerOrders) (hMax : McLThreeFiveMax) (hL34 : S7ListL34)
    (hJ4 : S7J4Rank) : S7_876 D := by
  intro hSg h3 L Z Y A g c hA
  have hns : ¬ Group.IsSolvable ↥D.M := s7_not_solvable c.base.loc.le c.base.loc.shape
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have : Fact p.Prime := ⟨hp⟩
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hpσ
  have hM : ∀ X : Subgroup G, X ≤ D.M → X ≠ ⊥ → IsPGroup p X →
      Subgroup.normalizer (X : Set G) ≤ D.M :=
    fun X hXM hX1 hXp => hsp.normalizer_le hX1 hXp hXM
  have hp3 : p ≠ 3 := fun h => h3 (h ▸ hpσ)
  have hp5 : 5 ≤ p := s7_five_le hp hp2 hp3
  have hthree : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpσ
  have hAL : A ≤ L := hA.le.trans inf_le_right
  by_cases hp7 : p = 7
  · subst hp7
    have hA1 : A ≠ ⊥ := by
      intro h
      have hcard := hA.card
      rw [h, Subgroup.card_bot] at hcard
      norm_num at hcard
    exact hM A (hAL.trans c.base.loc.le) hA1
      (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA.card))
  obtain ⟨x, hxL, hr1, hr11⟩ :=
    s7_conj_rank c.base.loc.le c.base.loc.norm c.base.loc.shape hAL hA.card hp hp5
  obtain ⟨c', hA', hback⟩ := s7_conj_cfg c hA hxL
  refine hback ?_
  set A' : Subgroup G := A.map (MulAut.conj x⁻¹).toMonoidHom with hA'def
  set Z' : Subgroup G := Z.map (MulAut.conj x⁻¹).toMonoidHom with hZ'def
  set H : Subgroup G := Subgroup.centralizer (A' : Set G) with hHdef
  have hrkH : 2 ≤ CFSG.Open.pRank p (D.M ⊓ H) := by omega
  by_cases hHM : H ≤ D.M
  · exact s7_norm_of_cent hp hM (le_trans (by norm_num) hrkH) hHM
  exfalso
  have hA'1 : A' ≠ ⊥ := by
    intro h
    have hcard := hA'.card
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hHtop : H ≠ ⊤ := s7_centralizer_ne_top hA'1 hA'.comm
  have h7 : UC22.F07.Sec7Hyp D p H := ⟨hp, hp2, hsp, hHtop, hHM, by rw [inf_comm]; omega⟩
  obtain ⟨hKodd, -, -⟩ := h71 p H h7
  obtain ⟨hF, hlist⟩ := h72 p H h7
  have hodd : Odd (Nat.card (CFSG.pPrimeCore p ↥H)) := by
    have hc : Nat.card (UC22.F07.PPrimeCoreIn p H) = Nat.card (CFSG.pPrimeCore p ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rwa [← hc]
  have hsec := s7_section c' hA' hodd
  rcases hL34 (QuotK7 p H) p (ImageModK p H (Opp p H)) hp hp5 hp7 hF
      (CFSG.pPrimeCore_quotient_eq_bot hp) hlist hsec with ⟨rfl, hMcL⟩ | ⟨rfl, hJ⟩
  ·
    obtain ⟨hEn, hE5⟩ := s7_image_opp hp H
    have h3M : CFSG.Open.pRank 3 D.M ≤ 3 := by
      by_contra hlt
      exact h3 (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))
    have hZH : Z' ≤ Subgroup.normalizer (H : Set G) :=
      hA'.normZ.trans (s7_normalizer_le_normalizer_centralizer A')
    have hCZ : Subgroup.centralizer (Z' : Set G) ≤ D.M :=
      (Subgroup.centralizer_le_normalizer (Z' : Set G)).trans c'.base.loc.hZN
    exact s7_theoremM hSimp hCard hOut hMult hCent hMax D.M H Z' hM hHM
      (by rw [inf_comm]; exact hrkH) (ImageModK 5 H (Opp 5 H)) hEn hE5 hMcL h3M hodd
      c'.base.loc.hZ3 hZH hCZ
  ·
    exact s7_j4_false (M := D.M) hJ4 hF hJ (by rw [inf_comm]; exact hthree.trans (hr11 le_rfl))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
