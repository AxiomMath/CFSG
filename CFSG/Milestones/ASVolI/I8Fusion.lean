module

public import CFSG.Milestones.ASVolI.I8
public import CFSG.Holt.General.Aschbacher73
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LargeExtraspecial.S8CBFList
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Open.StatedCenterThree
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.Quasithin.Background.ASVolIRegistered
public import CFSG.LargeExtraspecial.S8CBFOut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

theorem burnsideI8h_stabilizer_eq {G : Type} [Group G] (M : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ M) = M := by
  ext g
  simp [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, QuotientGroup.eq]

theorem burnsideI8h_conjugate_eq_iff {G : Type} [Group G] (K : Subgroup G) (g : G) :
    CFSG.conjugate K g = K ↔ g ∈ Subgroup.normalizer (K : Set G) := by
  unfold CFSG.conjugate
  rw [← inv_mem_iff (x := g) (H := Subgroup.normalizer (K : Set G))]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.symm

theorem burnsideI8h_closure_eq {G : Type} [Group G] (K : Subgroup G) :
    involutionNormalClosure K =
      Subgroup.closure (CFSG.Holt.General.involutionConjugates K) := by
  unfold involutionNormalClosure
  congr 1
  ext x
  constructor
  · rintro ⟨g, i, hiK, hi2, hi1, rfl⟩
    have hx2 : (g⁻¹ * i * g) ^ 2 = 1 := by
      calc (g⁻¹ * i * g) ^ 2 = g⁻¹ * i ^ 2 * g := by simp only [pow_two]; group
        _ = 1 := by rw [hi2]; group
    have hx1 : g⁻¹ * i * g ≠ 1 := by
      intro h
      apply hi1
      have : i = g * (g⁻¹ * i * g) * g⁻¹ := by group
      rw [this, h]
      group
    refine ⟨orderOf_eq_prime hx2 hx1, g⁻¹, ?_⟩
    have h : (g⁻¹)⁻¹ * (g⁻¹ * i * g) * g⁻¹ = i := by group
    rw [h]
    exact hiK
  · rintro ⟨hx, g, hg⟩
    have hx2 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      exact absurd hx (by norm_num)
    refine ⟨g⁻¹, g⁻¹ * x * g, hg, ?_, ?_, ?_⟩
    · calc (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by simp only [pow_two]; group
        _ = 1 := by rw [hx2]; group
    · intro h
      apply hx1
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h]
      group
    · group

theorem burnsideI8h_exists_involution {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : Even (Nat.card K)) : ∃ z ∈ K, orderOf z = 2 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (even_iff_two_dvd.1 hK)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem burnsideI8h_mem_of_conj_mem {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hJ : ∀ g : G, CFSG.conjugate K g ≠ K →
      Odd (Nat.card ↥(CFSG.conjugate K g ⊓ Subgroup.normalizer (K : Set G))))
    {q g : G} (hqK : q ∈ K) (hq : orderOf q = 2)
    (hg : g⁻¹ * q * g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hgn
  have hne : CFSG.conjugate K g ≠ K := fun h => hgn ((burnsideI8h_conjugate_eq_iff K g).1 h)
  have hodd := hJ g hne
  have hy2 : orderOf (g⁻¹ * q * g) = 2 := by
    rw [← hq]
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective q
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hyJ : g⁻¹ * q * g ∈ CFSG.conjugate K g := by
    refine ⟨q, hqK, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hle : Subgroup.zpowers (g⁻¹ * q * g) ≤
      CFSG.conjugate K g ⊓ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.2 ⟨hyJ, hg⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hy2] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem burnsideI8h_stronglyEmbedded
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hKe : Even (Nat.card K)) (hKn : ¬ K.Normal)
    (hJ : ∀ g : G, CFSG.conjugate K g ≠ K →
      Odd (Nat.card ↥(CFSG.conjugate K g ⊓ Subgroup.normalizer (K : Set G)))) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (K : Set G)).subgroupOf (involutionNormalClosure K)) := by
  classical
  set M := Subgroup.normalizer (K : Set G) with hM
  obtain ⟨z, hzK, hz⟩ := burnsideI8h_exists_involution hKe
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hKn (Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 fun x _ => hcon x))
  have hfix : ∀ q ∈ K, orderOf q = 2 → ∀ ω : G ⧸ M, q • ω = ω ↔ ω = ((1 : G) : G ⧸ M) := by
    intro q hqK hq ω
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ω
    constructor
    · intro h
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h
      have hq' : orderOf q⁻¹ = 2 := by rw [orderOf_inv, hq]
      have h' : a⁻¹ * q⁻¹ * a ∈ M := by simpa [mul_assoc] using h
      have := burnsideI8h_mem_of_conj_mem hJ (K.inv_mem hqK) hq' h'
      rw [QuotientGroup.eq]
      simpa using M.inv_mem this
    · intro h
      rw [QuotientGroup.eq] at h
      have ha : a ∈ M := by simpa using M.inv_mem h
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
      have hq' : q ∈ M := Subgroup.le_normalizer hqK
      have : (q * a)⁻¹ * a = a⁻¹ * q⁻¹ * a := by group
      rw [this]
      exact M.mul_mem (M.mul_mem (M.inv_mem ha) (M.inv_mem hq')) ha
  have hgα : g • ((1 : G) : G ⧸ M) ≠ ((1 : G) : G ⧸ M) := by
    rw [MulAction.Quotient.smul_mk, Ne, QuotientGroup.eq]
    intro h
    exact hg (by simpa using M.inv_mem h)
  have h := CFSG.Holt.General.fusionStronglyEmbedded_stabilizer_subgroupOf_closure
    (Q := K) (α := ((1 : G) : G ⧸ M)) hfix
    (by rw [burnsideI8h_stabilizer_eq]) hzK hz hgα
  rw [burnsideI8h_stabilizer_eq, ← burnsideI8h_closure_eq] at h
  exact h

theorem burnsideI8h_zpowers_elemAbelian {X : Type} [Group X] {z : X} (hz2 : z ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 (Subgroup.zpowers z) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
  have hx : (x : X) ∈ Subgroup.zpowers z := x.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
  apply Subtype.ext
  show (x : X) ^ 2 = 1
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [← zpow_natCast, hz2]

theorem burnsideI8h_oddCore_eq (G : Type*) [Group G] : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]

theorem burnsideI8h_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  rw [burnsideI8h_oddCore_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

theorem burnsideI8h_rank_one {X : Type} [Group X] [Finite X]
    (hgen : Subgroup.closure {x : X | x ^ 2 = 1 ∧ x ≠ 1} = ⊤)
    (hrank : ¬ CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo X)
    {z : X} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    CFSG.pRank 2 X = 1 ∧ CFSG.oddCore X ⊔ Subgroup.zpowers z = ⊤ ∧ ¬ 4 ∣ Nat.card X := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  set O := CFSG.oddCore X with hO
  have hOodd : Odd (Nat.card O) := burnsideI8h_odd_card_oddCore X
  have hcent : ∀ t : X, t ^ 2 = 1 → t ≠ 1 → ∀ g : X, g * t * g⁻¹ * t⁻¹ ∈ O := by
    intro t ht2 ht1
    have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
    obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X t ht1 ht2' (by
      intro g hc
      by_contra hne
      refine hrank (CFSG.Timmesfeld.Bridge.twoRankAtLeastTwo_of_commute
        (a := g * t * g⁻¹) (b := t) ?_ ht2' (show Commute (g * t * g⁻¹) t from hc) ?_ ht1 hne)
      · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
          _ = 1 := by rw [ht2']; group
      · intro h
        apply ht1
        have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
        rw [this, h]
        group)
    intro g
    exact (le_sSup (show N ∈ {N : Subgroup X | N.Normal ∧ Odd (Nat.card N)} from ⟨hNn, hNodd⟩))
      (hN g)
  have hQ : ∀ w : X ⧸ O, w ∈ Subgroup.center (X ⧸ O) ∧ w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    have hx : x ∈ Subgroup.closure {x : X | x ^ 2 = 1 ∧ x ≠ 1} := by rw [hgen]; trivial
    induction hx using Subgroup.closure_induction with
    | mem t ht =>
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
        have h := hcent t ht.1 ht.2 y
        have h' : ((y * t * y⁻¹ * t⁻¹ : X) : X ⧸ O) = 1 := (QuotientGroup.eq_one_iff _).2 h
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h'
        have h'' : ((y : X ⧸ O) * (t : X ⧸ O) * (y : X ⧸ O)⁻¹) = (t : X ⧸ O) :=
          (mul_inv_eq_one.1 h')
        calc (y : X ⧸ O) * (t : X ⧸ O) = (y : X ⧸ O) * (t : X ⧸ O) * (y : X ⧸ O)⁻¹ * (y : X ⧸ O) := by
              group
          _ = (t : X ⧸ O) * (y : X ⧸ O) := by rw [h'']
      · rw [← QuotientGroup.mk_pow, ht.1]
        rfl
    | one => exact ⟨Subgroup.one_mem _, by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, ?_⟩
      rw [QuotientGroup.mk_mul]
      have hc : Commute ((a : X ⧸ O)) ((b : X ⧸ O)) := (Subgroup.mem_center_iff.1 iha.1 _).symm
      rw [hc.mul_pow, iha.2, ihb.2, one_mul]
    | inv a _ iha =>
      refine ⟨?_, ?_⟩
      · rw [QuotientGroup.mk_inv]
        exact Subgroup.inv_mem _ iha.1
      · rw [QuotientGroup.mk_inv, inv_pow, iha.2, inv_one]
  have hsq : ∀ w : X ⧸ O, w ^ 2 = 1 := fun w => (hQ w).2
  have h4 : ¬ 4 ∣ Nat.card X := by
    intro h4
    obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := 2) (by simpa using h4)
    apply hrank
    refine ⟨E, by simpa using hE, fun x => ?_⟩
    have hx2 : ((x : X) ^ 2) ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hsq _
    have hinf : E ⊓ O = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      have h1 : Nat.card ↥(E ⊓ O) ∣ Nat.card E := Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(E ⊓ O) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_right
      have hcop : Nat.Coprime (Nat.card E) (Nat.card O) := by
        rw [hE]
        exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hOodd)
      exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have : (x : X) ^ 2 ∈ E ⊓ O := ⟨E.pow_mem x.2 2, hx2⟩
    rw [hinf] at this
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  have hz_notO : z ∉ O := by
    intro hzO
    have hle : Subgroup.zpowers z ≤ O := Subgroup.zpowers_le.2 hzO
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1] at hdvd
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 hdvd)
  have hπz : ((z : X) : X ⧸ O) ≠ 1 := fun h => hz_notO ((QuotientGroup.eq_one_iff _).1 h)
  have hQcard : Nat.card (X ⧸ O) = 2 := by
    have hp : IsPGroup 2 (X ⧸ O) := fun w => ⟨1, by simpa using hsq w⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hp
    have hdvd : Nat.card (X ⧸ O) ∣ Nat.card X := Subgroup.card_quotient_dvd_card O
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      haveI : Subsingleton (X ⧸ O) := (Nat.card_eq_one_iff_unique.1 hj).1
      exact hπz (Subsingleton.elim _ _)
    have hj2 : j ≤ 1 := by
      by_contra hj2
      push Not at hj2
      exact h4 ((pow_dvd_pow 2 hj2 : 2 ^ 2 ∣ 2 ^ j).trans (hj ▸ hdvd))
    have : j = 1 := by omega
    rw [hj, this, pow_one]
  have htop : Subgroup.zpowers ((z : X) : X ⧸ O) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hQcard]
    exact orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hz2]; rfl) hπz
  have hbound : ∀ r ∈ {r : ℕ | ∃ A : Subgroup X, CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ r}, r ≤ 1 := by
    rintro r ⟨A, -, hAc⟩
    by_contra hr
    push Not at hr
    exact h4 ((pow_dvd_pow 2 hr : 2 ^ 2 ∣ 2 ^ r).trans (hAc ▸ Subgroup.card_subgroup_dvd_card A))
  refine ⟨?_, ?_, h4⟩
  · unfold CFSG.pRank
    have hmem : 1 ∈ {r : ℕ | ∃ A : Subgroup X, CFSG.IsElementaryAbelian 2 A ∧
        Nat.card A = 2 ^ r} :=
      ⟨Subgroup.zpowers z, burnsideI8h_zpowers_elemAbelian hz2, by
        rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]⟩
    exact le_antisymm (csSup_le ⟨1, hmem⟩ hbound) (le_csSup ⟨1, hbound⟩ hmem)
  · rw [eq_top_iff]
    intro x _
    have hx : ((x : X) : X ⧸ O) ∈ Subgroup.zpowers ((z : X) : X ⧸ O) := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hxO : x * (z ^ k)⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow, hk]
      simp
    have : x = (x * (z ^ k)⁻¹) * z ^ k := by group
    rw [this]
    exact Subgroup.mul_mem_sup hxO (Subgroup.zpow_mem_zpowers z k)

theorem burnsideI8h_SE_dichotomy {X : Type} [Group X] [Finite X]
    (hgen : Subgroup.closure {x : X | x ^ 2 = 1 ∧ x ≠ 1} = ⊤) {M : Subgroup X}
    (hSE : fusionStronglyEmbedded M) :
    ¬ CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo X ∨
      (CFSG.BenderSuzuki.IsSimpleBenderGroup (X ⧸ CFSG.oddCore X) ∧
        CFSG.oddCore X ≤ M ∧
        CFSG.BenderSuzuki.IsBorelSubgroup (M.map (QuotientGroup.mk' (CFSG.oddCore X)))) := by
  classical
  have hcore : CFSG.BenderSuzuki.involutionCore X = ⊤ := by
    rw [eq_top_iff, ← hgen]
    apply Subgroup.closure_mono
    intro x hx
    exact ⟨hx.2, hx.1⟩
  rcases CFSG.BenderSuzuki.theorem_SE M hSE.to_native with hlow | hB
  · left
    exact fun h => hlow (CFSG.BenderSuzuki.twoRankAtLeastTwo_involutionCore_iff.2 h)
  · right
    obtain ⟨hBender, hOle, hBorel⟩ := hB
    set K := CFSG.BenderSuzuki.involutionCore X with hK
    let e : K ≃* X := (MulEquiv.subgroupCongr hcore).trans Subgroup.topEquiv
    have hmap : (CFSG.BenderSuzuki.twoPrimeCore K).map e.toMonoidHom = CFSG.oddCore X := by
      have := CFSG.pPrimeCore_map_iso 2 e
      rw [burnsideI8h_oddCore_eq]
      exact this
    let q : (K ⧸ CFSG.BenderSuzuki.twoPrimeCore K) ≃* (X ⧸ CFSG.oddCore X) :=
      QuotientGroup.congr _ _ e hmap
    have hee : ∀ y : K, e y = (y : X) := fun y => rfl
    refine ⟨hBender.map_mulEquiv q, ?_, ?_⟩
    · intro x hx
      rw [← hmap] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := (Subgroup.mem_inf.1 (hOle ⟨y, hy, rfl⟩)).1
      simpa [hee] using this
    · have hB' := CFSG.ShultStronglyClosedTI.ProperPairModel.isBorelSubgroup_map_mulEquiv q hBorel
      have hcomp : q.toMonoidHom.comp (QuotientGroup.mk' (CFSG.BenderSuzuki.twoPrimeCore K)) =
          (QuotientGroup.mk' (CFSG.oddCore X)).comp e.toMonoidHom := by
        ext y
        rfl
      have hM : ((M ⊓ K).subgroupOf K).map e.toMonoidHom = M := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1
        · intro hx
          have hxK : x ∈ K := by rw [hcore]; trivial
          exact ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 ⟨hx, hxK⟩, rfl⟩
      have : (((M ⊓ K).subgroupOf K).map
          (QuotientGroup.mk' (CFSG.BenderSuzuki.twoPrimeCore K))).map q.toMonoidHom =
          M.map (QuotientGroup.mk' (CFSG.oddCore X)) := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hM]
      rwa [this] at hB'

theorem burnsideI8h_isBender_of_fusion {X : Type} [Group X]
    (h : fusionIsBenderGroup X) : IsBenderGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · left
    have hq4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    haveI : Finite (GaloisField 2 f) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    refine ⟨f, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, GaloisField 2 f, inferInstance,
      inferInstance, hcard, ⟨e.trans
        (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL (GaloisField 2 f) 2 2 f
          (by omega) hcard).symm⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  · right
    right
    have hcard : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) :=
      GaloisField.card 2 (2 * f) (by omega)
    haveI : Finite (GaloisField 2 (2 * f)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    have hq4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    refine ⟨f, ⟨Nat.prime_two, by omega, by norm_num, ?_⟩, GaloisField 2 (2 * f), inferInstance,
      inferInstance, by rw [hcard, ← pow_mul, mul_comm], ⟨?_⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · exact e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative (K := GaloisField 2 (2 * f))
        f hf hcard).symm
  · right
    left
    have hcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
      GaloisField.card 2 (2 * a + 1) (by omega)
    haveI : Finite (GaloisField 2 (2 * a + 1)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    refine ⟨2 * a + 1, rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
      hcard, ⟨?_⟩⟩
    exact e.trans ((MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1)))).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard)).symm

theorem burnsideI8h_eq_one_of_odd {X : Type} [Group X] {O : Subgroup X} (hO : Odd (Nat.card O))
    {x : X} (hx : x ∈ O) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h2 : orderOf x ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem burnsideI8h_central_odd_borel {X : Type} [Group X] [Finite X]
    {O : Subgroup X} [O.Normal] (hOodd : Odd (Nat.card O)) (hOc : O ≤ Subgroup.center X)
    {B V : Subgroup X} (hOB : O ≤ B) (hVB : V ≤ B) (hVn : (V.subgroupOf B).Normal)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV1 : V ≠ ⊥)
    (Q : Sylow 2 (X ⧸ O))
    (hB : B.map (QuotientGroup.mk' O) = Subgroup.normalizer ((Q : Subgroup (X ⧸ O)) : Set (X ⧸ O)))
    (hcomm : ∀ y ∈ Q, y * y = 1 → ∀ z ∈ Q, Commute y z)
    (htrans : ∀ x y : X ⧸ O, (x ∈ Q ∧ ∀ q ∈ Q, Commute q x) → x ≠ 1 →
      (y ∈ Q ∧ ∀ q ∈ Q, Commute q y) → y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer ((Q : Subgroup (X ⧸ O)) : Set (X ⧸ O)), g * x * g⁻¹ = y) :
    ∃ S : Sylow 2 X, V ≤ S ∧ B = Subgroup.normalizer ((S : Subgroup X) : Set X) ∧
      (∀ y ∈ S, y ^ 2 = 1 → y ∈ V) ∧
      (S : Subgroup X).map (QuotientGroup.mk' O) = (Q : Subgroup (X ⧸ O)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' O with hπ
  obtain ⟨S, hSQ⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective O) 2 Q
  have hSπ : (S : Subgroup X).map π = (Q : Subgroup (X ⧸ O)) := by
    rw [← hSQ, Sylow.coe_mapSurjective]
  have hE4 : ∀ x s : X, (∃ k : ℕ, x ^ 2 ^ k = 1) → s ∈ S → π x = π s → x ∈ S := by
    rintro x s ⟨k, hk⟩ hs hxs
    have hos : s⁻¹ * x ∈ O := by
      have := (QuotientGroup.eq (s := O)).1 hxs.symm
      simpa using this
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨s, hs⟩
    have hsj : s ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hcomm' : Commute s (s⁻¹ * x) := Subgroup.mem_center_iff.1 (hOc hos) s
    have hxs' : x = s * (s⁻¹ * x) := by group
    have hpow : (s⁻¹ * x) ^ 2 ^ (k + j) = 1 := by
      have h1 : x ^ 2 ^ (k + j) = 1 := by
        rw [pow_add, pow_mul, hk, one_pow]
      have h2 : s ^ 2 ^ (k + j) = 1 := by
        rw [add_comm, pow_add, pow_mul, hsj, one_pow]
      rw [hxs', hcomm'.mul_pow, h2, one_mul] at h1
      exact h1
    have := burnsideI8h_eq_one_of_odd hOodd hos hpow
    rw [hxs', this, mul_one]
    exact hs
  have hinj : ∀ y w : X, y ∈ S → w ∈ S → π y = π w → y = w := by
    intro y w hy hw hyw
    have hos : w⁻¹ * y ∈ O := by
      have := (QuotientGroup.eq (s := O)).1 hyw.symm
      simpa using this
    have hmem : w⁻¹ * y ∈ (S : Subgroup X) := (S : Subgroup X).mul_mem
      ((S : Subgroup X).inv_mem hw) hy
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨w⁻¹ * y, hmem⟩
    have hwj : (w⁻¹ * y) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have h1 := burnsideI8h_eq_one_of_odd hOodd hos hwj
    calc y = w * (w⁻¹ * y) := by group
      _ = w := by rw [h1, mul_one]
  have hmemQ : ∀ s ∈ (S : Subgroup X), π s ∈ (Q : Subgroup (X ⧸ O)) := by
    intro s hs
    rw [← hSπ]
    exact Subgroup.mem_map_of_mem _ hs
  have hSB : (S : Subgroup X) ≤ B := by
    intro s hs
    have hQN : π s ∈ B.map π := by
      rw [hB]
      exact Subgroup.le_normalizer (hmemQ s hs)
    obtain ⟨b, hb, hbs⟩ := hQN
    have hos : s⁻¹ * b ∈ O := by
      have := (QuotientGroup.eq (s := O)).1 hbs.symm
      simpa using this
    have : s = b * (s⁻¹ * b)⁻¹ := by group
    rw [this]
    exact B.mul_mem hb (B.inv_mem (hOB hos))
  have hconj : ∀ b ∈ B, ∀ h ∈ (S : Subgroup X), b * h * b⁻¹ ∈ (S : Subgroup X) := by
    intro b hb h hh
    have hbN : π b ∈ Subgroup.normalizer ((Q : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
      rw [← hB]
      exact Subgroup.mem_map_of_mem _ hb
    have hQ' : π (b * h * b⁻¹) ∈ (Q : Subgroup (X ⧸ O)) := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hbN (π h)).1 (hmemQ h hh)
    rw [← hSπ] at hQ'
    obtain ⟨s, hs, hsπ⟩ := hQ'
    refine hE4 (b * h * b⁻¹) s ?_ hs hsπ.symm
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨h, hh⟩
    refine ⟨j, ?_⟩
    have hj' : h ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    calc (b * h * b⁻¹) ^ 2 ^ j = b * h ^ 2 ^ j * b⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hj']; group
  have hBN : ∀ b ∈ B, b ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj b hb h hh, fun hh => ?_⟩
    have := hconj b⁻¹ (B.inv_mem hb) _ hh
    simpa [mul_assoc] using this
  have hNB : ∀ n ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), n ∈ B := by
    intro n hn
    have hnQ : π n ∈ Subgroup.normalizer ((Q : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [← hSπ] at hz ⊢
        obtain ⟨s, hs, rfl⟩ := hz
        exact ⟨n * s * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn s).1 hs, by simp [map_mul, map_inv]⟩
      · intro hz
        rw [← hSπ] at hz ⊢
        obtain ⟨t, ht, hzt⟩ := hz
        have hn' : n⁻¹ ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
          (Subgroup.normalizer ((S : Subgroup X) : Set X)).inv_mem hn
        refine ⟨n⁻¹ * t * n, ?_, ?_⟩
        · have h3 := (Subgroup.mem_normalizer_iff.1 hn' t).1 ht
          rw [inv_inv] at h3
          exact h3
        · have : z = (π n)⁻¹ * (π n * z * (π n)⁻¹) * π n := by group
          rw [this, ← hzt]
          simp [map_mul, map_inv]
    rw [← hB] at hnQ
    obtain ⟨b, hb, hbn⟩ := hnQ
    have hos : b⁻¹ * n ∈ O := by
      have := (QuotientGroup.eq (s := O)).1 hbn
      simpa using this
    have : n = b * (b⁻¹ * n) := by group
    rw [this]
    exact B.mul_mem hb (hOB hos)
  have hVp0 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV2 x x.2)⟩
  have hVS : V ≤ (S : Subgroup X) := by
    have hVp : IsPGroup 2 (V.subgroupOf B) :=
      hVp0.of_equiv (Subgroup.subgroupOfEquivOfLe hVB).symm
    haveI := hVn
    have hle := hVp.le_sylow_of_normal (S.subtype hSB)
    intro v hv
    have hvB : v ∈ B := hVB hv
    have := hle (Subgroup.mem_subgroupOf.2 hv : (⟨v, hvB⟩ : B) ∈ V.subgroupOf B)
    exact this
  refine ⟨S, hVS, le_antisymm (fun b hb => hBN b hb) (fun n hn => hNB n hn), ?_, hSπ⟩
  intro y hy hy2
  obtain ⟨⟨v₀, hv₀⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV1
  have hv₀1 : v₀ ≠ 1 := fun h => hne (Subtype.ext h)
  have hπy2 : π y * π y = 1 := by
    rw [← map_mul, ← pow_two, hy2, map_one]
  have hπv2 : π v₀ * π v₀ = 1 := by
    rw [← map_mul, ← pow_two, hV2 v₀ hv₀, map_one]
  by_cases hπy : π y = 1
  · have hyO : y ∈ O := (QuotientGroup.eq_one_iff y).1 hπy
    have := burnsideI8h_eq_one_of_odd hOodd hyO (k := 1) (by simpa using hy2)
    rw [this]
    exact V.one_mem
  have hπv1 : π v₀ ≠ 1 := by
    intro h
    exact hv₀1 (burnsideI8h_eq_one_of_odd hOodd ((QuotientGroup.eq_one_iff v₀).1 h) (k := 1)
      (by simpa using hV2 v₀ hv₀))
  obtain ⟨g, hg, hgx⟩ := htrans (π v₀) (π y)
    ⟨hmemQ v₀ (hVS hv₀), fun q hq => (hcomm _ (hmemQ v₀ (hVS hv₀)) hπv2 q hq).symm⟩ hπv1
    ⟨hmemQ y hy, fun q hq => (hcomm _ (hmemQ y hy) hπy2 q hq).symm⟩ hπy
  rw [← hB] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  have hw : b * v₀ * b⁻¹ ∈ V := by
    have := hVn.conj_mem (⟨v₀, hVB hv₀⟩ : B) (Subgroup.mem_subgroupOf.2 hv₀) ⟨b, hb⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hπw : π y = π (b * v₀ * b⁻¹) := by
    rw [← hgx]
    simp [map_mul, map_inv]
  have := hinj y _ hy (hVS hw) hπw
  rw [this]
  exact hw

open scoped commutatorElement in
theorem burnsideI8h_perfect_of_simple {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hnab : ∃ a b : Y, a * b ≠ b * a) : Group.IsPerfect Y := by
  refine Group.isPerfect_def.2 ?_
  rcases hs.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h1 : ⁅a, b⁆ ∈ commutator Y :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exact h

theorem burnsideI8h_center_eq {X : Type} [Group X] (hOc : CFSG.oddCore X ≤ Subgroup.center X)
    (hs : IsSimpleGroup (X ⧸ CFSG.oddCore X))
    (hnab : ∃ a b : X ⧸ CFSG.oddCore X, a * b ≠ b * a) :
    Subgroup.center X = CFSG.oddCore X := by
  refine le_antisymm (fun z hz => ?_) hOc
  rw [← QuotientGroup.eq_one_iff]
  have hzc : (z : X ⧸ CFSG.oddCore X) ∈ Subgroup.center (X ⧸ CFSG.oddCore X) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz w]
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ CFSG.oddCore X)) with h | h
  · rw [h] at hzc
    exact Subgroup.mem_bot.1 hzc
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

theorem burnsideI8h_perfect_of_central {X : Type} [Group X] [Finite X]
    (hgen : Subgroup.closure {x : X | x ^ 2 = 1 ∧ x ≠ 1} = ⊤)
    (hOc : CFSG.oddCore X ≤ Subgroup.center X)
    (hp : Group.IsPerfect (X ⧸ CFSG.oddCore X)) : Group.IsPerfect X := by
  refine Group.isPerfect_def.2 ?_
  have hO := burnsideI8h_odd_card_oddCore X
  set O := CFSG.oddCore X with hOdef
  have himage : (commutator X).map (QuotientGroup.mk' O) = ⊤ := by
    have h1 : (⊤ : Subgroup X).map (QuotientGroup.mk' O) = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective O)
    rw [commutator_def, Subgroup.map_commutator, h1, ← commutator_def]
    exact hp.commutator_eq_top
  rw [eq_top_iff, ← hgen]
  refine (Subgroup.closure_le (commutator X)).2 fun w hw => ?_
  have hmem : (w : X ⧸ O) ∈ (commutator X).map (QuotientGroup.mk' O) := by
    rw [himage]
    trivial
  obtain ⟨c, hc, hcw⟩ := hmem
  have ho : c⁻¹ * w ∈ O := (QuotientGroup.eq (s := O)).1 hcw
  have hno : (c⁻¹ * w) ^ Nat.card O = 1 := by
    have := pow_card_eq_one' (G := ↥O) (x := ⟨c⁻¹ * w, ho⟩)
    exact congrArg Subtype.val this
  have hcomm : Commute c (c⁻¹ * w) := Subgroup.mem_center_iff.1 (hOc ho) c
  have hwn : w ^ Nat.card O = c ^ Nat.card O := by
    have : w = c * (c⁻¹ * w) := by group
    calc w ^ Nat.card O = (c * (c⁻¹ * w)) ^ Nat.card O := by rw [← this]
      _ = c ^ Nat.card O * (c⁻¹ * w) ^ Nat.card O := hcomm.mul_pow _
      _ = c ^ Nat.card O := by rw [hno, mul_one]
  have hw1 : w ^ Nat.card O = w := by
    obtain ⟨k, hk⟩ := hO
    rw [hk, pow_succ, pow_mul, hw.1, one_pow, one_mul]
  rw [← hw1, hwn]
  exact (commutator X).pow_mem hc _

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem burnsideI8h_solvable_of_out {G : Type} [Group G] [Finite G] {L V : Subgroup G}
    [L.Normal] (hVL : V ≤ L)
    (hB : Group.IsSolvable ↥(Subgroup.normalizer (V : Set G) ⊓ L))
    (hOut : Group.IsSolvable (Outer ↥L)) :
    ∃ (_ : ((Subgroup.centralizer (V : Set G)).subgroupOf
        (Subgroup.normalizer (V : Set G))).Normal),
      Group.IsSolvable (↥(Subgroup.normalizer (V : Set G)) ⧸
        (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))) := by
  classical
  set N := Subgroup.normalizer (V : Set G) with hN
  set C : Subgroup ↥N := (Subgroup.centralizer (V : Set G)).subgroupOf N with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc n => ?_⟩
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hw : (n : G)⁻¹ * v * (n : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (N.inv_mem n.2) v).1 hv
      simpa using this
    obtain ⟨w, hwV, rfl⟩ : ∃ w ∈ V, v = (n : G) * w * (n : G)⁻¹ :=
      ⟨(n : G)⁻¹ * v * (n : G), hw, by group⟩
    have h1 := hc w hwV
    calc (n : G) * w * (n : G)⁻¹ * ↑(n * c * n⁻¹) =
        (n : G) * (w * (c : G)) * (n : G)⁻¹ := by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (n : G) * ((c : G) * w) * (n : G)⁻¹ := by rw [h1]
      _ = ↑(n * c * n⁻¹) * ((n : G) * w * (n : G)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  refine ⟨hCn, ?_⟩
  let ψ : ↥N →* Outer ↥L :=
    (QuotientGroup.mk' (inner ↥L)).comp ((MulAut.conjNormal : G →* MulAut ↥L).comp N.subtype)
  set B' : Subgroup ↥N := (N ⊓ L).subgroupOf N with hB'
  let u : ↥N →* ↥N ⧸ C := QuotientGroup.mk' C
  have hker : ψ.ker ≤ B' ⊔ C := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have hm' : (MulAut.conjNormal (m : G) : MulAut ↥L) ∈ inner ↥L :=
      (QuotientGroup.eq_one_iff _).1 hm
    obtain ⟨l, hl⟩ := hm'
    have hlx : ∀ x : ↥L, (l : G) * x * (l : G)⁻¹ = (m : G) * x * (m : G)⁻¹ := by
      intro x
      have := congrArg (fun a : MulAut ↥L => ((a x : ↥L) : G)) hl
      simpa [MulAut.conj_apply] using this
    have hlV : ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ ∈ V := by
      intro v hv
      rw [hlx ⟨v, hVL hv⟩]
      exact (Subgroup.mem_normalizer_iff.1 m.2 v).1 hv
    have hlN : (l : G) ∈ N := by
      have h1 : V.map (MulAut.conj (l : G)).toMonoidHom ≤ V := by
        rintro _ ⟨v, hv, rfl⟩
        simpa [MulAut.conj_apply] using hlV v hv
      have h2 : V.map (MulAut.conj (l : G)).toMonoidHom = V :=
        Subgroup.eq_of_le_of_card_ge h1
          (by rw [Subgroup.card_map_of_injective (MulAut.conj (l : G)).injective])
      exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h2
    have hcC : m * (⟨l, hlN⟩ : ↥N)⁻¹ ∈ C := by
      rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro v hv
      have hxL : (l : G)⁻¹ * v * (l : G) ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem l.2) (hVL hv)) l.2
      have h1 := hlx ⟨_, hxL⟩
      have key : (m : G) * ((l : G)⁻¹ * v * (l : G)) * (m : G)⁻¹ = v := by
        rw [← h1]
        group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc v * ((m : G) * (l : G)⁻¹) =
          ((m : G) * ((l : G)⁻¹ * v * (l : G)) * (m : G)⁻¹) * ((m : G) * (l : G)⁻¹) := by
            rw [key]
        _ = (m : G) * (l : G)⁻¹ * v := by group
    have hlB : (⟨l, hlN⟩ : ↥N) ∈ B' := Subgroup.mem_subgroupOf.2 ⟨hlN, l.2⟩
    have hmeq : m = (m * (⟨l, hlN⟩ : ↥N)⁻¹) * ⟨l, hlN⟩ := by group
    rw [hmeq]
    exact (B' ⊔ C).mul_mem (Subgroup.mem_sup_right hcC) (Subgroup.mem_sup_left hlB)
  have hCJ : C ≤ ψ.ker ⊔ C := le_sup_right
  have hG'' : Group.IsSolvable (↥N ⧸ (ψ.ker ⊔ C)) := by
    haveI : Group.IsSolvable ψ.range := inferInstance
    haveI : Group.IsSolvable (↥N ⧸ ψ.ker) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientKerEquivRange ψ).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange ψ).injective
    exact Group.isSolvable_of_surjective
      (f := QuotientGroup.map ψ.ker (ψ.ker ⊔ C) (MonoidHom.id _)
        (by simpa using (le_sup_left : ψ.ker ≤ ψ.ker ⊔ C)))
      (QuotientGroup.map_surjective_of_surjective _ _ _
        (by simpa using QuotientGroup.mk_surjective) _)
  haveI hsolvB' : Group.IsSolvable ↥B' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ L ≤ N)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ L ≤ N)).injective
  haveI := hG''
  refine Group.isSolvable_of_ker_le_range (u.comp B'.subtype)
    (QuotientGroup.map C (ψ.ker ⊔ C) (MonoidHom.id _) (by simpa using hCJ)) ?_
  rw [QuotientGroup.ker_map]
  have hCu : C.map u = ⊥ := (Subgroup.map_eq_bot_iff C).2 (le_of_eq (QuotientGroup.ker_mk' C).symm)
  have h1 : (ψ.ker ⊔ C).map u ≤ B'.map u := by
    rw [Subgroup.map_sup, hCu, sup_bot_eq]
    calc ψ.ker.map u ≤ (B' ⊔ C).map u := Subgroup.map_mono hker
      _ = B'.map u := by rw [Subgroup.map_sup, hCu, sup_bot_eq]
  rw [Subgroup.comap_id]
  intro x hx
  have := h1 hx
  rw [MonoidHom.mem_range]
  obtain ⟨b, hb, rfl⟩ := this
  exact ⟨⟨b, hb⟩, rfl⟩


theorem burnsideI8h_closure_normal {G : Type} [Group G] (K : Subgroup G) :
    (involutionNormalClosure K).Normal := by
  refine ⟨fun x hx g => ?_⟩
  unfold involutionNormalClosure at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨g', i, hiK, hi2, hi1, rfl⟩ := hy
    apply Subgroup.subset_closure
    exact ⟨g' * g⁻¹, i, hiK, hi2, hi1, by group⟩
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ iha

theorem burnsideI8h_oddCore_conj {G : Type} [Group G] {L : Subgroup G} [L.Normal] (g : G) {x : G}
    (hx : x ∈ (CFSG.oddCore ↥L).map L.subtype) :
    g * x * g⁻¹ ∈ (CFSG.oddCore ↥L).map L.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hmap : (CFSG.oddCore ↥L).map (MulAut.conjNormal g : MulAut ↥L).toMonoidHom =
      CFSG.oddCore ↥L := by
    rw [burnsideI8h_oddCore_eq]
    exact CFSG.pPrimeCore_map_iso 2 (MulAut.conjNormal g : MulAut ↥L)
  have hy' : (MulAut.conjNormal g : MulAut ↥L) y ∈ CFSG.oddCore ↥L := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hy
  exact ⟨_, hy', rfl⟩

theorem burnsideI8h_models_of_fusion {X : Type} [Group X] (h : fusionIsBenderGroup X) :
    CFSG.BenderSuzuki.IsBenderGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact .isPSL2 f hf e
  · exact .isPSU3 f hf
      (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 f).symm))
  · exact .isSuzuki a ha
      (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm))

theorem burnsideI8h_oddCore_central {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hOle : CFSG.oddCore ↥(involutionNormalClosure V) ≤
      (Subgroup.normalizer (V : Set G)).subgroupOf (involutionNormalClosure V)) :
    CFSG.oddCore ↥(involutionNormalClosure V) ≤ Subgroup.center ↥(involutionNormalClosure V) := by
  haveI : (involutionNormalClosure V).Normal := burnsideI8h_closure_normal V
  set L := involutionNormalClosure V with hL
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro x
  have hgen : Subgroup.closure (((↑) : ↥L → G) ⁻¹'
      {x | ∃ g : G, ∃ i ∈ V, i ^ 2 = 1 ∧ i ≠ 1 ∧ x = g⁻¹ * i * g}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hle : Subgroup.closure (((↑) : ↥L → G) ⁻¹'
      {x | ∃ g : G, ∃ i ∈ V, i ^ 2 = 1 ∧ i ≠ 1 ∧ x = g⁻¹ * i * g}) ≤
      Subgroup.centralizer ({o} : Set ↥L) := by
    rw [Subgroup.closure_le]
    rintro y ⟨g, i, hiV, hi2, hi1, hy⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hOo : (o : G) ∈ (CFSG.oddCore ↥L).map L.subtype := ⟨o, ho, rfl⟩
    have ho' := burnsideI8h_oddCore_conj (L := L) g hOo
    have hoN : g * (o : G) * g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      obtain ⟨o'', ho'', hoeq⟩ := ho'
      have := Subgroup.mem_subgroupOf.1 (hOle ho'')
      have h3 : (o'' : G) = g * (o : G) * g⁻¹ := hoeq
      rw [h3] at this
      exact this
    set o' := g * (o : G) * g⁻¹ with ho'def
    have hc1 : o' * i * o'⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hoN i).1 hiV
    have hc2 : o' * i * o'⁻¹ * i⁻¹ ∈ V := V.mul_mem hc1 (V.inv_mem hiV)
    have hiL : i ∈ L := Subgroup.subset_closure ⟨1, i, hiV, hi2, hi1, by simp⟩
    have hc3 : o' * i * o'⁻¹ * i⁻¹ ∈ (CFSG.oddCore ↥L).map L.subtype := by
      have h1 := burnsideI8h_oddCore_conj (L := L) i (Subgroup.inv_mem _ ho')
      have h2 := (CFSG.oddCore ↥L).map L.subtype |>.mul_mem ho' h1
      have : o' * (i * o'⁻¹ * i⁻¹) = o' * i * o'⁻¹ * i⁻¹ := by group
      rw [← this]
      simpa [mul_assoc] using h2
    have hodd : Odd (Nat.card ((CFSG.oddCore ↥L).map L.subtype)) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact burnsideI8h_odd_card_oddCore _
    have hsq : (o' * i * o'⁻¹ * i⁻¹) ^ 2 ^ 1 = 1 := by
      have hmem := hc2
      simpa using hV2 _ hmem
    have h1 := burnsideI8h_eq_one_of_odd hodd hc3 hsq
    have hcomm : o' * i = i * o' := by
      have : o' * i * o'⁻¹ * i⁻¹ = 1 := h1
      have h2 := mul_inv_eq_one.1 this
      calc o' * i = (o' * i * o'⁻¹) * o' := by group
        _ = i * o' := by rw [h2]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (y : G) = g⁻¹ * i * g from hy]
    calc (g⁻¹ * i * g) * (o : G) = g⁻¹ * (i * (g * (o : G) * g⁻¹)) * g := by group
      _ = g⁻¹ * (o' * i) * g := by rw [← hcomm]
      _ = (o : G) * (g⁻¹ * i * g) := by rw [ho'def]; group
  have hx : x ∈ Subgroup.centralizer ({o} : Set ↥L) := hle (hgen ▸ Subgroup.mem_top x)
  exact Subgroup.mem_centralizer_singleton_iff.1 hx

theorem burnsideI8h_mem_normalizer_map_subtype {G : Type} [Group G] {L : Subgroup G}
    (S : Subgroup ↥L) (l : ↥L) :
    (l : G) ∈ Subgroup.normalizer ((S.map L.subtype : Subgroup G) : Set G) ↔
      l ∈ Subgroup.normalizer (S : Set ↥L) := by
  have hmem : ∀ h : ↥L, (h : G) ∈ S.map L.subtype ↔ h ∈ S := fun h =>
    Subgroup.mem_map_iff_mem L.subtype_injective
  constructor
  · intro hl
    rw [Subgroup.mem_normalizer_iff] at hl ⊢
    intro h
    rw [← hmem, ← hmem (l * h * l⁻¹)]
    simpa using hl (h : G)
  · intro hl
    rw [Subgroup.mem_normalizer_iff] at hl ⊢
    intro h
    constructor
    · rintro ⟨h₀, hh₀, rfl⟩
      exact ⟨l * h₀ * l⁻¹, (hl h₀).1 hh₀, by simp⟩
    · intro hh
      obtain ⟨t, ht, hteq⟩ := hh
      have hhL : h ∈ L := by
        have : h = (l : G)⁻¹ * (t : G) * (l : G) := by
          have h1 : (t : G) = (l : G) * h * (l : G)⁻¹ := hteq
          rw [h1]
          group
        rw [this]
        exact L.mul_mem (L.mul_mem (L.inv_mem l.2) t.2) l.2
      refine ⟨⟨h, hhL⟩, ?_, rfl⟩
      have h2 : l * ⟨h, hhL⟩ * l⁻¹ = t := by
        apply Subtype.ext
        have h1 : (t : G) = (l : G) * h * (l : G)⁻¹ := hteq
        simp [h1]
      exact (hl ⟨h, hhL⟩).2 (h2 ▸ ht)

theorem burnsideI8h_le_closure {G : Type} [Group G] {V : Subgroup G} (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    V ≤ involutionNormalClosure V := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨1, v, hv, hV2 v hv, hv1, by simp⟩

theorem burnsideI8h_exists_conj_mem_sylow {X : Type} [Group X] [Finite X] (S₀ : Sylow 2 X) {x : X}
    (hx : x ^ 2 = 1) : ∃ l : X, l⁻¹ * x * l ∈ S₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    show (g : X) ^ 2 ^ 1 = 1
    rw [← hj, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hx]
  obtain ⟨S', hS'⟩ := hp.exists_le_sylow
  obtain ⟨l, rfl⟩ := MulAction.exists_smul_eq X S₀ S'
  have hxS : x ∈ ((l • S₀ : Sylow 2 X) : Subgroup X) := hS' (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  refine ⟨l, ?_⟩
  have h3 : (MulAut.conj l)⁻¹ • x ∈ (S₀ : Subgroup X) := hxS
  have h4 : (MulAut.conj l)⁻¹ • x = l⁻¹ * x * l := by simp [MulAut.conj_inv_apply]
  rw [h4] at h3
  exact h3

theorem burnsideI8h_sylow_data
    {G : Type} [Group G] [Finite G]
    {V : Subgroup G} (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV1 : V ≠ ⊥)
    (hBender : CFSG.BenderSuzuki.IsSimpleBenderGroup
      (↥(involutionNormalClosure V) ⧸ CFSG.oddCore ↥(involutionNormalClosure V)))
    (hOle : CFSG.oddCore ↥(involutionNormalClosure V) ≤
      (Subgroup.normalizer (V : Set G)).subgroupOf (involutionNormalClosure V))
    (hBorel : CFSG.BenderSuzuki.IsBorelSubgroup
      (((Subgroup.normalizer (V : Set G)).subgroupOf (involutionNormalClosure V)).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(involutionNormalClosure V))))) :
    ∃ S : Subgroup G, IsSylowTwoIn S (involutionNormalClosure V) ∧ V ≤ S ∧
      (∀ y ∈ S, y ^ 2 = 1 → y ∈ V) ∧
      involutionNormalClosure V ⊓ Subgroup.normalizer (S : Set G) =
        Subgroup.normalizer (V : Set G) ⊓ involutionNormalClosure V ∧
      (∀ x ∈ involutionNormalClosure V, x ^ 2 = 1 →
        ∃ l ∈ involutionNormalClosure V, l⁻¹ * x * l ∈ S) ∧
      ∃ Q : Sylow 2 (↥(involutionNormalClosure V) ⧸ CFSG.oddCore ↥(involutionNormalClosure V)),
        Nat.card V = Nat.card ↥(Subgroup.center (Q : Subgroup
          (↥(involutionNormalClosure V) ⧸ CFSG.oddCore ↥(involutionNormalClosure V)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := involutionNormalClosure V with hL
  set N := Subgroup.normalizer (V : Set G) with hN
  have hVL : V ≤ L := burnsideI8h_le_closure hV2
  have hVN : V ≤ N := Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := hBorel.2
  have hK := burnsideI8h_models_of_fusion
    (CFSG.Open.fusionIsBenderGroup_of_isSimpleBenderGroup hBender)
  have hOc := burnsideI8h_oddCore_central hV2 hOle
  have hVn : ((V.subgroupOf L).subgroupOf (N.subgroupOf L)).Normal := by
    refine ⟨fun x hx b => ?_⟩
    have hbN : ((b : ↥L) : G) ∈ N := b.2
    have hxV : (((x : ↥(N.subgroupOf L)) : ↥L) : G) ∈ V := hx
    show (((b * x * b⁻¹ : ↥(N.subgroupOf L)) : ↥L) : G) ∈ V
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 hbN _).1 hxV
  have hV1' : V.subgroupOf L ≠ ⊥ := by
    obtain ⟨⟨v, hv⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV1
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨⟨v, hVL hv⟩, hv⟩, fun h => hne (Subtype.ext
      (congrArg (fun z : ↥(V.subgroupOf L) => ((z : ↥L) : G)) h))⟩
  obtain ⟨S₀, hVS₀, hBS₀, hΩ, hS₀π⟩ := burnsideI8h_central_odd_borel (X := ↥L)
    (O := CFSG.oddCore ↥L) (burnsideI8h_odd_card_oddCore _) hOc (B := N.subgroupOf L)
    (V := V.subgroupOf L) hOle (fun x hx => hVN hx) hVn
    (fun v hv => Subtype.ext (hV2 _ hv)) hV1' Q hQ
    (fun y hy hy2 z hz =>
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hy hy2 z hz)
    (fun x y hx hx1 hy hy1 =>
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_normalizer_conj hK Q hx hx1 hy hy1)
  refine ⟨(S₀ : Subgroup ↥L).map L.subtype, ⟨Subgroup.map_subtype_le _, S₀.isPGroup'.map _, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hsub : ((S₀ : Subgroup ↥L).map L.subtype).subgroupOf L = (S₀ : Subgroup ↥L) :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [hsub]
    exact S₀.not_dvd_index
  · intro v hv
    exact ⟨⟨v, hVL hv⟩, hVS₀ hv, rfl⟩
  · rintro y ⟨y₀, hy₀, rfl⟩ hy2
    exact hΩ y₀ hy₀ (Subtype.ext hy2)
  · ext x
    constructor
    · rintro ⟨hxL, hxN⟩
      refine ⟨?_, hxL⟩
      have h1 := (burnsideI8h_mem_normalizer_map_subtype (S₀ : Subgroup ↥L) ⟨x, hxL⟩).1 hxN
      rw [← hBS₀] at h1
      exact h1
    · rintro ⟨hxN, hxL⟩
      refine ⟨hxL, ?_⟩
      have h1 : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer ((S₀ : Subgroup ↥L) : Set ↥L) := by
        rw [← hBS₀]
        exact hxN
      exact (burnsideI8h_mem_normalizer_map_subtype (S₀ : Subgroup ↥L) ⟨x, hxL⟩).2 h1
  · intro x hxL hx2
    obtain ⟨l, hl⟩ := burnsideI8h_exists_conj_mem_sylow S₀ (x := (⟨x, hxL⟩ : ↥L))
      (Subtype.ext hx2)
    exact ⟨l, l.2, ⟨l⁻¹ * ⟨x, hxL⟩ * l, hl, rfl⟩⟩
  · refine ⟨Q, ?_⟩
    set π := QuotientGroup.mk' (CFSG.oddCore ↥L) with hπ
    have hOodd : Odd (Nat.card (CFSG.oddCore ↥L)) := burnsideI8h_odd_card_oddCore _
    have hQmem : ∀ (v : G) (hv : v ∈ V),
        π ⟨v, hVL hv⟩ ∈ (Q : Subgroup (↥L ⧸ CFSG.oddCore ↥L)) := by
      intro v hv
      rw [← hS₀π]
      exact Subgroup.mem_map_of_mem _ (hVS₀ (show (⟨v, hVL hv⟩ : ↥L) ∈ V.subgroupOf L from hv))
    have hsqπ : ∀ (v : G) (hv : v ∈ V), π ⟨v, hVL hv⟩ * π ⟨v, hVL hv⟩ = 1 := by
      intro v hv
      rw [← map_mul]
      have : (⟨v, hVL hv⟩ : ↥L) * ⟨v, hVL hv⟩ = 1 := Subtype.ext (by
        simpa [pow_two] using hV2 v hv)
      rw [this, map_one]
    have hcen : ∀ v : ↥V, (⟨π ⟨v, hVL v.2⟩, hQmem v.1 v.2⟩ :
        ↥(Q : Subgroup (↥L ⧸ CFSG.oddCore ↥L))) ∈
        Subgroup.center ↥(Q : Subgroup (↥L ⧸ CFSG.oddCore ↥L)) := by
      intro v
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q
        (hQmem v.1 v.2) (hsqπ v.1 v.2) g.1 g.2).symm.eq
    let f : ↥V → ↥(Subgroup.center ↥(Q : Subgroup (↥L ⧸ CFSG.oddCore ↥L))) :=
      fun v => ⟨_, hcen v⟩
    have hinj : Function.Injective f := by
      intro v₁ v₂ h12
      have h1 : π ⟨v₁, hVL v₁.2⟩ = π ⟨v₂, hVL v₂.2⟩ := congrArg (fun z => (z.1).1) h12
      have hmem : (⟨v₁, hVL v₁.2⟩ : ↥L)⁻¹ * ⟨v₂, hVL v₂.2⟩ ∈ CFSG.oddCore ↥L :=
        (QuotientGroup.eq (s := CFSG.oddCore ↥L)).1 h1
      have hsq : ((⟨v₁, hVL v₁.2⟩ : ↥L)⁻¹ * ⟨v₂, hVL v₂.2⟩) ^ 2 ^ 1 = 1 := by
        apply Subtype.ext
        have : (v₁ : G)⁻¹ * v₂ ∈ V := V.mul_mem (V.inv_mem v₁.2) v₂.2
        simpa using hV2 _ this
      have := burnsideI8h_eq_one_of_odd hOodd hmem hsq
      apply Subtype.ext
      have h2 := congrArg Subtype.val this
      simpa [inv_mul_eq_one, eq_comm] using h2
    have hsurj : Function.Surjective f := by
      rintro ⟨⟨z₀, hz₀Q⟩, hzc⟩
      have hz₀S : z₀ ∈ (S₀ : Subgroup ↥L).map π := by
        rw [hS₀π]
        exact hz₀Q
      obtain ⟨s, hs, hsz⟩ := hz₀S
      have hcz : ∀ y ∈ (Q : Subgroup (↥L ⧸ CFSG.oddCore ↥L)), Commute z₀ y := by
        intro y hy
        have := Subgroup.mem_center_iff.1 hzc ⟨y, hy⟩
        exact (congrArg Subtype.val this).symm
      have hz2 : z₀ * z₀ = 1 :=
        CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hK Q hz₀Q hcz
      have hs2O : s ^ 2 ∈ CFSG.oddCore ↥L := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        have hsz' : (s : ↥L ⧸ CFSG.oddCore ↥L) = z₀ := hsz
        rw [QuotientGroup.mk_pow, hsz', pow_two]
        exact hz2
      obtain ⟨j, hj⟩ := S₀.isPGroup' ⟨s, hs⟩
      have hsj : s ^ 2 ^ j = 1 := by
        have := congrArg Subtype.val hj
        simpa using this
      have hs2 : s ^ 2 = 1 := by
        refine burnsideI8h_eq_one_of_odd hOodd hs2O (k := j) ?_
        rw [← pow_mul, mul_comm, pow_mul, hsj, one_pow]
      have hsV : s ∈ V.subgroupOf L := hΩ s hs hs2
      refine ⟨⟨(s : G), hsV⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hsz
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem burnsideI8h_gen {G : Type} [Group G] (K : Subgroup G) :
    Subgroup.closure {x : ↥(involutionNormalClosure K) | x ^ 2 = 1 ∧ x ≠ 1} = ⊤ := by
  have h0 : Subgroup.closure (((↑) : ↥(involutionNormalClosure K) → G) ⁻¹'
      {x | ∃ g : G, ∃ i ∈ K, i ^ 2 = 1 ∧ i ≠ 1 ∧ x = g⁻¹ * i * g}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← h0]
  apply Subgroup.closure_mono
  rintro x ⟨g, i, hiK, hi2, hi1, hx⟩
  have hx2 : (x : G) ^ 2 = 1 := by
    rw [hx]
    calc (g⁻¹ * i * g) ^ 2 = g⁻¹ * i ^ 2 * g := by simp only [pow_two]; group
      _ = 1 := by rw [hi2]; group
  have hx1 : (x : G) ≠ 1 := by
    rw [hx]
    intro h
    apply hi1
    have : i = g * (g⁻¹ * i * g) * g⁻¹ := by group
    rw [this, h]
    group
  exact ⟨Subtype.ext hx2, fun h => hx1 (congrArg Subtype.val h)⟩

theorem burnsideI8h_conjClosure_eq {G : Type} [Group G] {V : Subgroup G}
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) : conjClosure V ⊤ = involutionNormalClosure V := by
  apply le_antisymm
  · refine iSup₂_le fun y _ => ?_
    rintro _ ⟨v, hv, rfl⟩
    by_cases hv1 : v = 1
    · rw [hv1, map_one]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨y, v, hv, hV2 v hv, hv1, by simp [MulAut.conj_apply]⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨g, i, hiV, -, -, rfl⟩
    refine (le_iSup₂ (f := fun y (_ : y ∈ (⊤ : Subgroup G)) => CFSG.conjugate V y) g
      (Subgroup.mem_top g)) ?_
    exact ⟨i, hiV, by simp [MulAut.conj_apply]⟩

open CFSG.Assembly.LowTwoRank CFSG.Blueprint in
theorem burnsideI8h_outer_solvable_of_bender
    {Y : Type} [Group Y] (h : IsBenderGroup Y) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) := by
  rcases h with ⟨n, hn⟩ | ⟨f, hf⟩ | ⟨n, hn⟩
  · exact CFSG.LargeExtraspecial.S8.outer_solvable_of_lieModel_of_not_ree
      (t := .PSL) (by simp [reeTitsTags]) (Or.inl ⟨by decide, hn⟩)
  · exact CFSG.LargeExtraspecial.S8.outer_solvable_of_lieModel_of_not_ree
      (t := .twistedB2) (by simp [reeTitsTags]) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hf⟩)))
  · exact CFSG.LargeExtraspecial.S8.outer_solvable_of_lieModel_of_not_ree
      (t := .PSU) (by simp [reeTitsTags]) (Or.inl ⟨by decide, hn⟩)

theorem burnsideI8h_solvable_normalizer {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hOle : CFSG.oddCore ↥(involutionNormalClosure V) ≤
      (Subgroup.normalizer (V : Set G)).subgroupOf (involutionNormalClosure V))
    (hBorel : CFSG.BenderSuzuki.IsBorelSubgroup
      (((Subgroup.normalizer (V : Set G)).subgroupOf (involutionNormalClosure V)).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(involutionNormalClosure V))))) :
    Group.IsSolvable ↥(Subgroup.normalizer (V : Set G) ⊓ involutionNormalClosure V) := by
  set L := involutionNormalClosure V with hL
  set N := Subgroup.normalizer (V : Set G) with hN
  set B' : Subgroup ↥L := N.subgroupOf L with hB'
  set O := CFSG.oddCore ↥L with hO
  haveI : Group.IsSolvable ↥O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (burnsideI8h_odd_card_oddCore _)
  haveI : Group.IsSolvable ↥(B'.map (QuotientGroup.mk' O)) := hBorel.1
  let g : ↥B' →* ↥(B'.map (QuotientGroup.mk' O)) :=
    MonoidHom.codRestrict ((QuotientGroup.mk' O).comp B'.subtype) (B'.map (QuotientGroup.mk' O))
      (fun b => Subgroup.mem_map.2 ⟨b, b.2, rfl⟩)
  have hB'solv : Group.IsSolvable ↥B' := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hOle) g ?_
    intro b hb
    have hb1 : (QuotientGroup.mk' O) (b : ↥L) = 1 := by
      have := congrArg Subtype.val ((MonoidHom.mem_ker).1 hb)
      simpa [g] using this
    have hbO : (b : ↥L) ∈ O := (QuotientGroup.eq_one_iff _).1 hb1
    exact ⟨⟨b, hbO⟩, rfl⟩
  have heq : (N ⊓ L).subgroupOf L = N.subgroupOf L := Subgroup.inf_subgroupOf_right N L
  let e : ↥B' ≃* ↥(N ⊓ L) :=
    (MulEquiv.subgroupCongr heq.symm).trans (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ L ≤ L))
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem burnsideI8h_eq_one_or_eq {G : Type} [Group G] {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    {w : G} (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have ho : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

@[expose] def burnsideI8h_Concl1 {G : Type} [Group G] (V L : Subgroup G) : Prop :=
  Nat.card ↥V = 2 ∧ L = (CFSG.oddCore ↥L).map L.subtype ⊔ V

@[expose] def burnsideI8h_Concl2 {G : Type} [Group G] (M V L : Subgroup G) : Prop :=
  CFSG.IsQuasisimple ↥L ∧ IsBenderGroup (↥L ⧸ Subgroup.center ↥L) ∧
    (∃ TL : Subgroup G, IsSylowTwoIn TL L ∧ V = omegaOne TL) ∧
    M ⊓ L = L ⊓ Subgroup.normalizer (V : Set G) ∧
    ∃ S : Subgroup G, IsSylowTwoIn S L ∧ M ⊓ L = L ⊓ Subgroup.normalizer (S : Set G)

theorem burnsideI8h_Concl_congr {G : Type} [Group G] {M V L₁ L₂ : Subgroup G} (h : L₁ = L₂) :
    (burnsideI8h_Concl1 V L₂ ∨ burnsideI8h_Concl2 M V L₂) →
      (burnsideI8h_Concl1 V L₁ ∨ burnsideI8h_Concl2 M V L₁) := by
  subst h
  exact id

theorem burnsideI8h_card_ker_dvd {K X : Type} [Group K] [Finite K] [Group X] [Finite X]
    [Group.IsPerfect K] [Group.IsPerfect X] (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) {m : ℕ}
    (hm : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) = m) :
    Nat.card π.ker ∣ m := by
  obtain ⟨-, h, -, -, -, hmap, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier π hπ hker
  rw [← hmap, ← hm]
  exact Subgroup.card_map_dvd _ h

theorem burnsideI8h_stated_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y t n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X t n p f := by
  unfold CFSG.Assembly.LowTwoRank.StatedClassicalModel at h ⊢
  obtain ⟨hadm, h⟩ := h
  refine ⟨hadm, ?_⟩
  cases t <;> first
    | exact (False.elim h)
    | (obtain ⟨K, hK1, hK2, hK3, ⟨e'⟩⟩ := h
       exact ⟨K, hK1, hK2, hK3, ⟨e.trans e'⟩⟩)
    | (obtain ⟨K, hK1, hK2, hK3, b, c, hbc, ⟨e'⟩⟩ := h
       exact ⟨K, hK1, hK2, hK3, b, c, hbc, ⟨e.trans e'⟩⟩)

theorem burnsideI8h_suzuki_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel Y p f) : CFSG.Blueprint.SuzukiModel X p f := by
  obtain ⟨hp, a, ha, K, hK1, hK2, hf, hK, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, hK1, hK2, hf, hK, ⟨e.trans e'⟩⟩

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier in
theorem burnsideI8h_card_hopf
    {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨e⟩ := CFSG.Open.ASVolIRegistered.griess h
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  have hm : ∀ a : ℕ, Nat.card (Multiplicative (ZMod a)) = a := fun a => by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod a) ≃ ZMod a)]
    exact Nat.card_zmod a
  simp only [hm]

theorem burnsideI8h_hopf_bijective {S E : Type} [Group S] [Finite S] [Group.IsPerfect S]
    [Group E] [Finite E] [Group.IsPerfect E] (q : E →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E)
    (hcard : Nat.card q.ker = Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S)) :
    ∃ h : CFSG.RankThree.PerfectCover.HopfCover S →* E, Function.Bijective h := by
  haveI := CFSG.RankThree.PerfectCover.finite_hopfMultiplier (inferInstance : Group.IsPerfect S)
  obtain ⟨-, h, hcomp, -, hsurj, hmap, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier q hq hker
  refine ⟨h, ?_, hsurj⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxM : x ∈ CFSG.RankThree.PerfectCover.hopfMultiplier S := by
    change CFSG.RankThree.PerfectCover.hopfCoverMap S x = 1
    rw [← hcomp, MonoidHom.comp_apply, (MonoidHom.mem_ker.1 hx), map_one]
  let g : ↥(CFSG.RankThree.PerfectCover.hopfMultiplier S) →* ↥q.ker :=
    MonoidHom.codRestrict (h.comp (CFSG.RankThree.PerfectCover.hopfMultiplier S).subtype) q.ker
      (fun m => by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ m.2)
  have hgs : Function.Surjective g := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨m, hm, hmc⟩ := hc
    exact ⟨⟨m, hm⟩, Subtype.ext hmc⟩
  have hgb := hgs.bijective_of_nat_card_le (by rw [hcard])
  have : g ⟨x, hxM⟩ = 1 := Subtype.ext (MonoidHom.mem_ker.1 hx)
  have h1 : (⟨x, hxM⟩ : ↥(CFSG.RankThree.PerfectCover.hopfMultiplier S)) = 1 :=
    hgb.1 (this.trans (map_one g).symm)
  have := congrArg Subtype.val h1
  simpa using this

open CFSG.Assembly.LowTwoRank in
theorem burnsideI8h_su3_cover {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hOc : CFSG.oddCore X ≤ Subgroup.center X) {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2)
    (e : X ⧸ CFSG.oddCore X ≃* StatedProj (StatedSU 3 (2 ^ m) K))
    (h3 : 3 ∣ 2 ^ m + 1) (hcardO : Nat.card (CFSG.oddCore X) = 3)
    (hhopf : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (X ⧸ CFSG.oddCore X)) = 3) :
    Nonempty (X ≃* ↥(StatedSU 3 (2 ^ m) K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore X with hO
  haveI : Group.IsPerfect (X ⧸ O) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
  have hπ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  have hker : (QuotientGroup.mk' O).ker ≤ Subgroup.center X := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  obtain ⟨hX, hXb⟩ := burnsideI8h_hopf_bijective (QuotientGroup.mk' O) hπ hker
    (by rw [QuotientGroup.ker_mk', hcardO, hhopf])
  set SU := StatedSU 3 (2 ^ m) K with hSU
  set Sc : Subgroup ↥SU := (StatedScalars (Fin 3) K).subgroupOf SU with hSc
  let p' : ↥SU →* X ⧸ O := e.symm.toMonoidHom.comp (QuotientGroup.mk' Sc)
  have hp's : Function.Surjective p' := e.symm.surjective.comp (QuotientGroup.mk'_surjective Sc)
  have hp'k : ∀ x : ↥SU, x ∈ p'.ker ↔ x ∈ Sc := by
    intro x
    rw [MonoidHom.mem_ker]
    show e.symm (QuotientGroup.mk' Sc x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hp'c : p'.ker ≤ Subgroup.center ↥SU := by
    intro x hx
    have hx' : x ∈ Sc := (hp'k x).1 hx
    obtain ⟨c, hc⟩ : (x : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hx'
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : GL (Fin 3) K) * (x : GL (Fin 3) K) = (x : GL (Fin 3) K) * (g : GL (Fin 3) K)
    rw [← hc]
    exact (Matrix.GeneralLinearGroup.scalar_commute c (g : GL (Fin 3) K)).symm
  have hq : (3, 2 ^ m) ≠ (3, 2) := by
    intro he
    have h2 : 2 ^ m = 2 ^ 1 := by simpa using he
    have := Nat.pow_right_injective le_rfl h2
    omega
  haveI : Group.IsPerfect ↥SU :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := m) hK le_rfl hq
  have hdvd := burnsideI8h_card_ker_dvd p' hp's hp'c hhopf
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK, CFSG.Open.StatedCenterThree.sq_sub_one_eq (Nat.one_le_two_pow)]
    exact Dvd.dvd.mul_left h3 _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3K
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hmem := CFSG.Open.StatedCenterThree.scalar_mem (K := K) (q := 2 ^ m)
    (by positivity) h3 hζ3
  have hscal : (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) ζ, hmem⟩ : ↥SU) ∈ p'.ker := by
    rw [hp'k]
    exact ⟨ζ, rfl⟩
  have hscal1 : (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) ζ, hmem⟩ : ↥SU) ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : ↥SU => (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)) h
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    have hζ' : ζ = 1 := h1
    rw [hζ', orderOf_one] at hζ
    omega
  have hker3 : Nat.card p'.ker = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hbot : p'.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      rw [hbot, Subgroup.mem_bot] at hscal
      exact hscal1 hscal
    · exact h1
  obtain ⟨hS, hSb⟩ := burnsideI8h_hopf_bijective p' hp's hp'c (by rw [hker3, hhopf])
  exact ⟨(MulEquiv.ofBijective hX hXb).symm.trans (MulEquiv.ofBijective hS hSb)⟩

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier in
theorem burnsideI8h_lift_models
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hOc : CFSG.oddCore X ≤ Subgroup.center X) {m : ℕ} (hm : 2 ≤ m)
    (hmod : StatedClassicalModel (X ⧸ CFSG.oddCore X) .PSL 2 2 m ∨
      SuzukiModel (X ⧸ CFSG.oddCore X) 2 m ∨
      StatedClassicalModel (X ⧸ CFSG.oddCore X) .PSU 3 2 m) :
    StatedClassicalModel X .PSL 2 2 m ∨ SuzukiModel X 2 m ∨ StatedClassicalModel X .PSU 3 2 m ∨
      IsSU3Group (2 ^ m) X := by
  classical
  set O := CFSG.oddCore X with hO
  have hOodd : Odd (Nat.card O) := burnsideI8h_odd_card_oddCore X
  haveI : Group.IsPerfect (X ⧸ O) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
  have hπ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  have hker : (QuotientGroup.mk' O).ker ≤ Subgroup.center X := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  have hdvd : ∀ {d : ℕ}, Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (X ⧸ O)) = d →
      Nat.card O ∣ d := by
    intro d hd
    have := burnsideI8h_card_ker_dvd (QuotientGroup.mk' O) hπ hker hd
    rwa [QuotientGroup.ker_mk'] at this
  have hiso : Nat.card O = 1 → Nonempty (X ≃* X ⧸ O) := by
    intro h1
    have hO1 : O = ⊥ := Subgroup.eq_bot_of_card_eq O h1
    exact ⟨(QuotientGroup.quotientBot (G := X)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO1.symm)⟩
  have hone : ∀ d : ℕ, Nat.card O ∣ d → d ∣ 4 → Nat.card O = 1 := by
    intro d h1 h2
    have h3 : Nat.card O ∣ 4 := h1.trans h2
    have h4 : Nat.card O ≤ 4 := Nat.le_of_dvd (by norm_num) h3
    have h5 : 0 < Nat.card O := Nat.card_pos
    obtain ⟨k, hk⟩ := hOodd
    interval_cases hc : Nat.card O <;> first | rfl | omega | (exfalso; revert h3; decide)
  rcases hmod with hP | hS | hU
  ·
    have hLie : LieModel (X ⧸ O) .PSL 2 2 m := Or.inl ⟨by decide, hP⟩
    have hc := hdvd (burnsideI8h_card_hopf hLie)
    have hg : genericOrders .PSL 2 2 m = (1, 1) := by
      have h1 : Odd (2 ^ m - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
        (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
      show (Nat.gcd 2 (2 ^ m - 1), 1) = (1, 1)
      rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 h1)]
    have hO1 : Nat.card O = 1 := by
      refine hone _ hc ?_
      rw [hg]
      by_cases hm2 : m = 2
      · subst hm2
        have e : exceptionalOrders .PSL 2 2 2 = (2, 1) := rfl
        rw [e]
        decide
      · have e : exceptionalOrders .PSL 2 2 m = (1, 1) := by
          unfold exceptionalOrders
          split <;> first | rfl | omega | (simp_all)
        rw [e]
        decide
    obtain ⟨e⟩ := hiso hO1
    exact Or.inl (burnsideI8h_stated_congr e hP)
  ·
    have hLie : LieModel (X ⧸ O) .twistedB2 0 2 m := Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hS⟩))
    have hc := hdvd (burnsideI8h_card_hopf hLie)
    have hg : genericOrders .twistedB2 0 2 m = (1, 1) := rfl
    have hO1 : Nat.card O = 1 := by
      refine hone _ hc ?_
      rw [hg]
      by_cases hm3 : m = 3
      · subst hm3
        have e : exceptionalOrders .twistedB2 0 2 3 = (2, 2) := rfl
        rw [e]
        decide
      · have e : exceptionalOrders .twistedB2 0 2 m = (1, 1) := by
          unfold exceptionalOrders
          split <;> first | rfl | omega | (simp_all)
        rw [e]
        decide
    obtain ⟨e⟩ := hiso hO1
    exact Or.inr (Or.inl (burnsideI8h_suzuki_congr e hS))
  ·
    have hLie : LieModel (X ⧸ O) .PSU 3 2 m := Or.inl ⟨by decide, hU⟩
    have hhopf := burnsideI8h_card_hopf hLie
    have hg : genericOrders .PSU 3 2 m = (Nat.gcd 3 (2 ^ m + 1), 1) := rfl
    have he : exceptionalOrders .PSU 3 2 m = (1, 1) := by
      unfold exceptionalOrders
      split <;> first | rfl | omega | (simp_all)
    rw [hg, he] at hhopf
    simp only [mul_one, one_mul] at hhopf
    have hOd : Nat.card O ∣ Nat.gcd 3 (2 ^ m + 1) := hdvd hhopf
    have hO3 : Nat.card O ∣ 3 := hOd.trans (Nat.gcd_dvd_left _ _)
    rcases (Nat.dvd_prime Nat.prime_three).1 hO3 with h1 | h3
    · obtain ⟨e⟩ := hiso h1
      exact Or.inr (Or.inr (Or.inl (burnsideI8h_stated_congr e hU)))
    · have h3d : 3 ∣ 2 ^ m + 1 := (Nat.dvd_gcd_iff.1 (h3 ▸ hOd)).2
      have hgcd : Nat.gcd 3 (2 ^ m + 1) = 3 := Nat.gcd_eq_left h3d
      rw [hgcd] at hhopf
      obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
      obtain ⟨e'⟩ := burnsideI8h_su3_cover hperf hOc hm hK e h3d h3 hhopf
      exact Or.inr (Or.inr (Or.inr ⟨K, hKf, hKfin, hK, ⟨e'⟩⟩))

open scoped MatrixGroups in
theorem burnsideI8h_stated_psl {Y : Type} [Group Y] {f : ℕ} (hf : 2 ≤ f)
    (e : Y ≃* PSL(2, GaloisField 2 f)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 2 f := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : Finite (GaloisField 2 f) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, GaloisField 2 f, inferInstance,
    inferInstance, hcard, ⟨e.trans
      (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL (GaloisField 2 f) 2 2 f
        (by omega) hcard).symm⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

theorem burnsideI8h_stated_psu {Y : Type} [Group Y] {f : ℕ} (hf : 2 ≤ f)
    (e : Y ≃* PSU3 2 f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSU 3 2 f := by
  have hcard : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) :=
    GaloisField.card 2 (2 * f) (by omega)
  haveI : Finite (GaloisField 2 (2 * f)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨⟨Nat.prime_two, by omega, by norm_num, ?_⟩, GaloisField 2 (2 * f), inferInstance,
    inferInstance, by rw [hcard, ← pow_mul, mul_comm], ⟨?_⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · exact e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative (K := GaloisField 2 (2 * f))
      f hf hcard).symm

theorem burnsideI8h_stated_sz {Y : Type} [Group Y] {a : ℕ} (ha : 1 ≤ a) (e : Y ≃* Sz a) :
    CFSG.Blueprint.SuzukiModel Y 2 (2 * a + 1) := by
  have hcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  haveI : Finite (GaloisField 2 (2 * a + 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl, hcard, ⟨?_⟩⟩
  exact e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1)))).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard)).symm

open scoped MatrixGroups in
theorem burnsideI8h_bender_param {Y : Type} [Group Y] [Finite Y] (h : fusionIsBenderGroup Y) :
    ∃ m k : ℕ, 2 ≤ m ∧ fusionBenderBorel Y (2 ^ m) k ∧
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 2 m ∨
        CFSG.Blueprint.SuzukiModel Y 2 m ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSU 3 2 m) := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · refine ⟨f, 1, hf, ?_, Or.inl (burnsideI8h_stated_psl hf e)⟩
    have : Finite (PSL(2, GaloisField 2 f)) := Finite.of_equiv Y e.toEquiv
    exact (bender_psl2_borel_full f hf).map_mulEquiv e.symm
  · exact ⟨f, 3, hf, CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e,
      Or.inr (Or.inr (burnsideI8h_stated_psu hf e))⟩
  · exact ⟨2 * a + 1, 2, by omega,
      CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_sz ha e,
      Or.inr (Or.inl (burnsideI8h_stated_sz ha e))⟩

theorem burnsideI8h_pRank_eq {G : Type} [Group G] {V : Subgroup G}
    (hVe : IsElemAbelian 2 V) {m : ℕ} (hcard : Nat.card V = 2 ^ m) : CFSG.pRank 2 ↥V = m := by
  have hc : ∀ a b : ↥V, a * b = b * a := fun a b => hVe.1.is_comm.comm a b
  have hA : CFSG.IsElementaryAbelian 2 (⊤ : Subgroup ↥V) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a.1 b.1)⟩⟩, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using hVe.2 (a : ↥V).1 (a : ↥V).2
  have hbound : ∀ r ∈ {r : ℕ | ∃ A : Subgroup ↥V, CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ r}, r ≤ m := by
    rintro r ⟨A, -, hAc⟩
    have h1 : 2 ^ r ∣ 2 ^ m := hAc ▸ hcard ▸ Subgroup.card_subgroup_dvd_card A
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have hmem : m ∈ {r : ℕ | ∃ A : Subgroup ↥V, CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ r} := ⟨⊤, hA, by rw [Subgroup.card_top, hcard]⟩
  unfold CFSG.pRank
  exact le_antisymm (csSup_le ⟨m, hmem⟩ hbound) (le_csSup ⟨m, hbound⟩ hmem)

theorem burnsideI8h_ne_bot_of_pRank {G : Type} [Group G] {V : Subgroup G}
    (h : 0 < CFSG.pRank 2 ↥V) : V ≠ ⊥ := by
  rintro rfl
  unfold CFSG.pRank at h
  have hbound : (0 : ℕ) ∈ upperBounds {r : ℕ | ∃ A : Subgroup ↥(⊥ : Subgroup G),
      CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
    rintro r ⟨A, -, hA⟩
    have h1 : Nat.card A ∣ Nat.card ↥(⊥ : Subgroup G) := Subgroup.card_subgroup_dvd_card A
    rw [Subgroup.card_bot] at h1
    have h2 : Nat.card A = 1 := Nat.dvd_one.1 h1
    rw [h2] at hA
    exact (Nat.pow_eq_one.1 hA.symm).resolve_left (by norm_num) |>.le
  exact absurd (csSup_le' hbound) (not_le.2 h)

theorem burnsideI8h_exists_sylow_of_top {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowTwoIn T ⊤) : ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  exact ⟨hT.2.1.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

section


theorem as_I_8_2 : I_8_2 := by
  intro G _ _ K hK hKn hJ
  have hSE := burnsideI8h_stronglyEmbedded hK.1 hKn hJ
  obtain ⟨z, hzK, hz⟩ := burnsideI8h_exists_involution hK.1
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzL : z ∈ involutionNormalClosure K :=
    Subgroup.subset_closure ⟨1, z, hzK, hz2, hz1, by simp⟩
  have hgen : Subgroup.closure {x : ↥(involutionNormalClosure K) | x ^ 2 = 1 ∧ x ≠ 1} = ⊤ := by
    have h0 : Subgroup.closure (((↑) : ↥(involutionNormalClosure K) → G) ⁻¹'
        {x | ∃ g : G, ∃ i ∈ K, i ^ 2 = 1 ∧ i ≠ 1 ∧ x = g⁻¹ * i * g}) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [eq_top_iff, ← h0]
    apply Subgroup.closure_mono
    rintro x ⟨g, i, hiK, hi2, hi1, hx⟩
    have hx2 : (x : G) ^ 2 = 1 := by
      rw [hx]
      calc (g⁻¹ * i * g) ^ 2 = g⁻¹ * i ^ 2 * g := by simp only [pow_two]; group
        _ = 1 := by rw [hi2]; group
    have hx1 : (x : G) ≠ 1 := by
      rw [hx]
      intro h
      apply hi1
      have : i = g * (g⁻¹ * i * g) * g⁻¹ := by group
      rw [this, h]
      group
    exact ⟨Subtype.ext hx2, fun h => hx1 (congrArg Subtype.val h)⟩
  rcases burnsideI8h_SE_dichotomy hgen hSE with hrank | ⟨hBender, hOle, hBorel⟩
  · left
    have hz2' : (⟨z, hzL⟩ : ↥(involutionNormalClosure K)) ^ 2 = 1 := Subtype.ext hz2
    have hz1' : (⟨z, hzL⟩ : ↥(involutionNormalClosure K)) ≠ 1 :=
      fun h => hz1 (congrArg Subtype.val h)
    obtain ⟨hr, hO, -⟩ := burnsideI8h_rank_one hgen hrank hz2' hz1'
    refine ⟨hr, z, hzK, hz2, hz1, ?_⟩
    have := congrArg (Subgroup.map (involutionNormalClosure K).subtype) hO
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top,
      Subgroup.range_subtype] at this
    exact this.symm
  · right
    refine ⟨burnsideI8h_isBender_of_fusion
      (CFSG.Open.fusionIsBenderGroup_of_isSimpleBenderGroup hBender), ?_, hBorel.2⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.mem_subgroupOf.1 (hOle hy)

end

section


theorem as_I_8_5 : I_8_5 := by
  intro G _ _ M V hM hV hVM hVn hVe hstar
  classical
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := hVe.2
  obtain ⟨v₀, hv₀V, hv₀1⟩ : ∃ v ∈ V, v ≠ 1 := by
    obtain ⟨⟨v, hv⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV
    exact ⟨v, hv, fun h => hne (Subtype.ext h)⟩
  have hv₀2 : v₀ ^ 2 = 1 := hV2 v₀ hv₀V
  have hKP : ∀ v ∈ V, v ≠ 1 → ∀ g : G, g⁻¹ * v * g ∈ M → g ∈ M := by
    intro v hv hv1 g hg
    obtain ⟨x, -, huniq⟩ := hstar v hv hv1
    have hg' : v • ((g : G) : G ⧸ M) = ((g : G) : G ⧸ M) := by
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
      have : (v * g)⁻¹ * g = (g⁻¹ * v * g)⁻¹ := by group
      rw [this]
      exact M.inv_mem hg
    have h1 : ((g : G) : G ⧸ M) = x := huniq _ hg'
    have hg'' : v • (((1 : G)) : G ⧸ M) = (((1 : G)) : G ⧸ M) := by
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
      simpa using M.inv_mem (hVM hv)
    have h2 : ((1 : G) : G ⧸ M) = x := huniq _ hg''
    have h3 := h1.trans h2.symm
    rw [QuotientGroup.eq] at h3
    simpa using M.inv_mem h3
  have hMN : M ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVn.1).1 hVn.2
  have hNM : Subgroup.normalizer (V : Set G) = M := by
    refine le_antisymm (fun g hg => ?_) hMN
    have : g⁻¹ * v₀ * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (V : Set G)).inv_mem hg) v₀).1 hv₀V
      simpa using this
    exact hKP v₀ hv₀V hv₀1 g (hVM this)
  subst hNM
  have hVeven : Even (Nat.card V) := by
    have hord : orderOf (⟨v₀, hv₀V⟩ : V) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hv₀2)) (fun h => hv₀1 (congrArg Subtype.val h))
    have : 2 ∣ Nat.card V := hord ▸ orderOf_dvd_natCard _
    exact even_iff_two_dvd.2 this
  have hJ0 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → ∀ x ∈ CFSG.conjugate V g,
      x ∈ Subgroup.normalizer (V : Set G) → x = 1 := by
    intro g hg x hx hxN
    obtain ⟨w, hw, rfl⟩ := hx
    by_contra hne
    have hw1 : w ≠ 1 := fun h => hne (by simp [h])
    exact hg (hKP w hw hw1 g (by simpa [MulAut.conj_apply] using hxN))
  have hnn : ¬ V.Normal := fun h => hM (Subgroup.normalizer_eq_top_iff.2 h)
  have hJ : ∀ g : G, CFSG.conjugate V g ≠ V →
      Odd (Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.normalizer (V : Set G))) := by
    intro g hg
    have hgN : g ∉ Subgroup.normalizer (V : Set G) :=
      fun h => hg ((burnsideI8h_conjugate_eq_iff V g).2 h)
    have : CFSG.conjugate V g ⊓ Subgroup.normalizer (V : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hJ0 g hgN x hx.1 hx.2)
    rw [this, Subgroup.card_bot]
    exact odd_one
  have hSE := burnsideI8h_stronglyEmbedded hVeven hnn hJ
  have hgen := burnsideI8h_gen V
  have hconj := burnsideI8h_conjClosure_eq hV2
  haveI hLn : (involutionNormalClosure V).Normal := burnsideI8h_closure_normal V
  have hVL : V ≤ involutionNormalClosure V := burnsideI8h_le_closure hV2
  rcases burnsideI8h_SE_dichotomy hgen hSE with hrank | ⟨hBender, hOle, hBorel⟩
  ·
    have hz2' : (⟨v₀, hVL hv₀V⟩ : ↥(involutionNormalClosure V)) ^ 2 = 1 := Subtype.ext hv₀2
    have hz1' : (⟨v₀, hVL hv₀V⟩ : ↥(involutionNormalClosure V)) ≠ 1 :=
      fun h => hv₀1 (congrArg Subtype.val h)
    obtain ⟨-, hO, h4⟩ := burnsideI8h_rank_one hgen hrank hz2' hz1'
    have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV2 x x.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hVp
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hV (Subgroup.eq_bot_of_card_eq V hk)
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have h42 : 4 ∣ Nat.card V := by
        rw [hk]
        exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
      exact h4 (h42.trans (Subgroup.card_dvd_of_le hVL))
    have hVcard : Nat.card V = 2 := by
      have : k = 1 := by omega
      rw [hk, this, pow_one]
    have hzV : Subgroup.zpowers v₀ = V :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hv₀V)
        (by rw [Nat.card_zpowers, orderOf_eq_prime hv₀2 hv₀1, hVcard])
    have hcentral : ∀ n ∈ Subgroup.normalizer (V : Set G), Commute v₀ n := by
      intro n hn
      have hw : n * v₀ * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hn v₀).1 hv₀V
      have hw2 : (n * v₀ * n⁻¹) ^ 2 = 1 := by
        calc (n * v₀ * n⁻¹) ^ 2 = n * v₀ ^ 2 * n⁻¹ := by simp only [pow_two]; group
          _ = 1 := by rw [hv₀2]; group
      have hw1 : n * v₀ * n⁻¹ ≠ 1 := by
        intro h
        apply hv₀1
        have : v₀ = n⁻¹ * (n * v₀ * n⁻¹) * n := by group
        rw [this, h]
        group
      rcases burnsideI8h_eq_one_or_eq hv₀2 hv₀1 (hzV ▸ hw) with h | h
      · exact absurd h hw1
      · have : n * v₀ = v₀ * n := by
          calc n * v₀ = n * v₀ * n⁻¹ * n := by group
            _ = v₀ * n := by rw [h]
        exact this.symm
    have hCtop : (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) =
        ⊤ := by
      rw [eq_top_iff]
      intro n _
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hzV ▸ hv)
      exact (hcentral n n.2).zpow_left j
    refine ⟨burnsideI8h_Concl_congr hconj (Or.inl ⟨hVcard, ?_⟩), ?_⟩
    · have := congrArg (Subgroup.map (involutionNormalClosure V).subtype) hO
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top,
        Subgroup.range_subtype] at this
      have h5 : Subgroup.zpowers ((involutionNormalClosure V).subtype
          ⟨v₀, hVL hv₀V⟩) = V := hzV
      rw [h5] at this
      exact this.symm
    · have hCn : ((Subgroup.centralizer (V : Set G)).subgroupOf
          (Subgroup.normalizer (V : Set G))).Normal := by
        rw [hCtop]
        exact Subgroup.normal_top
      refine ⟨hCn, ?_⟩
      haveI : Subsingleton (↥(Subgroup.normalizer (V : Set G)) ⧸
          (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [QuotientGroup.eq, hCtop]
        exact Subgroup.mem_top _
      infer_instance
  ·
    have hsimp : IsSimpleGroup (↥(involutionNormalClosure V) ⧸
        CFSG.oddCore ↥(involutionNormalClosure V)) := hBender.isSimple
    have hnab : ∃ a b : ↥(involutionNormalClosure V) ⧸ CFSG.oddCore ↥(involutionNormalClosure V),
        a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact CFSG.BenderSuzuki.IsSimpleBenderGroup.not_commutative hBender hcon
    have hOc := burnsideI8h_oddCore_central hV2 hOle
    have hZ := burnsideI8h_center_eq hOc hsimp hnab
    have hperf : Group.IsPerfect ↥(involutionNormalClosure V) :=
      burnsideI8h_perfect_of_central hgen hOc (burnsideI8h_perfect_of_simple hsimp hnab)
    let e : ↥(involutionNormalClosure V) ⧸ Subgroup.center ↥(involutionNormalClosure V) ≃*
        ↥(involutionNormalClosure V) ⧸ CFSG.oddCore ↥(involutionNormalClosure V) :=
      QuotientGroup.quotientMulEquivOfEq hZ
    have hBenderStated : IsBenderGroup (↥(involutionNormalClosure V) ⧸
        Subgroup.center ↥(involutionNormalClosure V)) :=
      burnsideI8h_isBender_of_fusion
        (CFSG.Open.fusionIsBenderGroup_of_isSimpleBenderGroup (hBender.map_mulEquiv e.symm))
    obtain ⟨S, hS, hVS, hΩ, hN, -, -⟩ := burnsideI8h_sylow_data hV2 hV hBender hOle hBorel
    have hqs : CFSG.IsQuasisimple ↥(involutionNormalClosure V) := by
      refine ⟨hperf, e.isSimpleGroup_congr.mpr hsimp, ?_⟩
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    have hΩeq : V = omegaOne S := by
      unfold omegaOne
      have : {x | x ∈ S ∧ x ^ 2 = 1} = (V : Set G) := by
        ext x
        constructor
        · rintro ⟨hxS, hx2⟩
          exact hΩ x hxS hx2
        · intro hx
          exact ⟨hVS hx, hV2 x hx⟩
      rw [this, Subgroup.closure_eq]
    refine ⟨burnsideI8h_Concl_congr hconj
      (Or.inr ⟨hqs, hBenderStated, ⟨S, hS, hΩeq⟩, inf_comm _ _, ⟨S, hS, hN.symm⟩⟩), ?_⟩
    have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ↥(involutionNormalClosure V)) := by
      haveI : Group.IsPerfect ↥(involutionNormalClosure V) := hperf
      haveI := burnsideI8h_outer_solvable_of_bender hBenderStated
      exact Group.isSolvable_of_isSolvable_injective
        (f := CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom
          ↥(involutionNormalClosure V))
        (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective _)
    exact burnsideI8h_solvable_of_out hVL (burnsideI8h_solvable_normalizer hOle hBorel) hOut

end

section


theorem as_I_8_3 : I_8_3 := by
  intro G _ _ T hT V hVe hTI hsc hpR hnn
  classical
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := hVe.2
  have hV : V ≠ ⊥ := burnsideI8h_ne_bot_of_pRank hpR
  obtain ⟨v₀, hv₀V, hv₀1⟩ : ∃ v ∈ V, v ≠ 1 := by
    obtain ⟨⟨v, hv⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV
    exact ⟨v, hv, fun h => hne (Subtype.ext h)⟩
  have hv₀2 : v₀ ^ 2 = 1 := hV2 v₀ hv₀V
  obtain ⟨S₀, hS₀⟩ := burnsideI8h_exists_sylow_of_top hT
  have hVeven : Even (Nat.card V) := by
    have hord : orderOf (⟨v₀, hv₀V⟩ : V) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hv₀2)) (fun h => hv₀1 (congrArg Subtype.val h))
    have : 2 ∣ Nat.card V := hord ▸ orderOf_dvd_natCard _
    exact even_iff_two_dvd.2 this
  have hsc' : ∀ a ∈ V, ∀ g : G, g⁻¹ * a * g ∈ T → g⁻¹ * a * g ∈ V := hsc.2
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV2 x x.2)⟩
  have hJ0 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → ∀ x ∈ CFSG.conjugate V g,
      x ∈ Subgroup.normalizer (V : Set G) → x = 1 := by
    intro g hg x hx hxN
    by_contra hx1
    obtain ⟨w, hw, hwx⟩ := hx
    have hxeq : x = g⁻¹ * w * g := by
      rw [← hwx]
      simp [MulAut.conj_apply]
    have hx2 : x ^ 2 = 1 := by
      rw [hxeq]
      calc (g⁻¹ * w * g) ^ 2 = g⁻¹ * w ^ 2 * g := by simp only [pow_two]; group
        _ = 1 := by rw [hV2 w hw]; group
    have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
      intro y
      refine ⟨1, ?_⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 y.2
      apply Subtype.ext
      show (y : G) ^ 2 ^ 1 = 1
      rw [← hj, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hx2]
    have hP : IsPGroup 2 (V ⊔ Subgroup.zpowers x : Subgroup G) :=
      hVp.to_sup_of_normal_left' hxp (Subgroup.zpowers_le.2 hxN)
    obtain ⟨S', hS'⟩ := hP.exists_le_sylow
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G S₀ S'
    have hconjT : ∀ y ∈ V ⊔ Subgroup.zpowers x, h⁻¹ * y * h ∈ T := by
      intro y hy
      have h1 := hS' hy
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
      have h3 : (MulAut.conj h)⁻¹ • y ∈ (S₀ : Subgroup G) := h1
      have h4 : (MulAut.conj h)⁻¹ • y = h⁻¹ * y * h := by simp [MulAut.conj_inv_apply]
      rw [h4, hS₀] at h3
      exact h3
    have hhV : ∀ a ∈ V, h⁻¹ * a * h ∈ V := fun a ha =>
      hsc' a ha h (hconjT a (Subgroup.mem_sup_left ha))
    have hhN : h ∈ Subgroup.normalizer (V : Set G) := by
      have h1 : V.map (MulAut.conj h⁻¹).toMonoidHom ≤ V := by
        rintro _ ⟨a, ha, rfl⟩
        simpa [MulAut.conj_apply] using hhV a ha
      have h2 : V.map (MulAut.conj h⁻¹).toMonoidHom = V :=
        Subgroup.eq_of_le_of_card_ge h1
          (by rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective])
      have h3 := Subgroup.mem_normalizer_iff_map_conj_eq.2 h2
      simpa using (Subgroup.normalizer (V : Set G)).inv_mem h3
    have hxT : (g * h)⁻¹ * w * (g * h) ∈ T := by
      have h1 := hconjT x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
      rw [hxeq] at h1
      have : (g * h)⁻¹ * w * (g * h) = h⁻¹ * (g⁻¹ * w * g) * h := by group
      rw [this]
      exact h1
    have hxV' : h⁻¹ * x * h ∈ V := by
      have h1 := hsc' w hw (g * h) hxT
      have : h⁻¹ * x * h = (g * h)⁻¹ * w * (g * h) := by rw [hxeq]; group
      rw [this]
      exact h1
    have hxV : x ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.1 hhN (h⁻¹ * x * h)).1 hxV'
      have : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rw [this] at h1
      exact h1
    have hmem : x ∈ V ⊓ CFSG.conjugate V g := ⟨hxV, ⟨w, hw, hwx⟩⟩
    rw [hTI g hg] at hmem
    exact hx1 (Subgroup.mem_bot.1 hmem)
  have hJ : ∀ g : G, CFSG.conjugate V g ≠ V →
      Odd (Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.normalizer (V : Set G))) := by
    intro g hg
    have hgN : g ∉ Subgroup.normalizer (V : Set G) :=
      fun h => hg ((burnsideI8h_conjugate_eq_iff V g).2 h)
    have : CFSG.conjugate V g ⊓ Subgroup.normalizer (V : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hJ0 g hgN x hx.1 hx.2)
    rw [this, Subgroup.card_bot]
    exact odd_one
  have hSE := burnsideI8h_stronglyEmbedded hVeven hnn hJ
  have hgen := burnsideI8h_gen V
  have hconj := burnsideI8h_conjClosure_eq hV2
  haveI hLn : (involutionNormalClosure V).Normal := burnsideI8h_closure_normal V
  have hVL : V ≤ involutionNormalClosure V := burnsideI8h_le_closure hV2
  rw [hconj]
  rcases burnsideI8h_SE_dichotomy hgen hSE with hrank | ⟨hBender, hOle, hBorel⟩
  ·
    left
    have hz2' : (⟨v₀, hVL hv₀V⟩ : ↥(involutionNormalClosure V)) ^ 2 = 1 := Subtype.ext hv₀2
    have hz1' : (⟨v₀, hVL hv₀V⟩ : ↥(involutionNormalClosure V)) ≠ 1 :=
      fun h => hv₀1 (congrArg Subtype.val h)
    obtain ⟨-, hO, h4⟩ := burnsideI8h_rank_one hgen hrank hz2' hz1'
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hVp
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hV (Subgroup.eq_bot_of_card_eq V hk)
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have h42 : 4 ∣ Nat.card V := by
        rw [hk]
        exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
      exact h4 (h42.trans (Subgroup.card_dvd_of_le hVL))
    have hVcard : Nat.card V = 2 := by
      have : k = 1 := by omega
      rw [hk, this, pow_one]
    have hzV : Subgroup.zpowers v₀ = V :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hv₀V)
        (by rw [Nat.card_zpowers, orderOf_eq_prime hv₀2 hv₀1, hVcard])
    refine ⟨burnsideI8h_pRank_eq hVe (m := 1) (by rw [hVcard, pow_one]), ?_⟩
    have := congrArg (Subgroup.map (involutionNormalClosure V).subtype) hO
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top,
      Subgroup.range_subtype] at this
    have h5 : Subgroup.zpowers ((involutionNormalClosure V).subtype
        ⟨v₀, hVL hv₀V⟩) = V := hzV
    rw [h5] at this
    exact this.symm
  ·
    right
    have hsimp : IsSimpleGroup (↥(involutionNormalClosure V) ⧸
        CFSG.oddCore ↥(involutionNormalClosure V)) := hBender.isSimple
    have hnab : ∃ a b : ↥(involutionNormalClosure V) ⧸ CFSG.oddCore ↥(involutionNormalClosure V),
        a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact CFSG.BenderSuzuki.IsSimpleBenderGroup.not_commutative hBender hcon
    have hOc := burnsideI8h_oddCore_central hV2 hOle
    have hZ := burnsideI8h_center_eq hOc hsimp hnab
    have hperf : Group.IsPerfect ↥(involutionNormalClosure V) :=
      burnsideI8h_perfect_of_central hgen hOc (burnsideI8h_perfect_of_simple hsimp hnab)
    let e : ↥(involutionNormalClosure V) ⧸ Subgroup.center ↥(involutionNormalClosure V) ≃*
        ↥(involutionNormalClosure V) ⧸ CFSG.oddCore ↥(involutionNormalClosure V) :=
      QuotientGroup.quotientMulEquivOfEq hZ
    have hqs : CFSG.IsQuasisimple ↥(involutionNormalClosure V) := by
      refine ⟨hperf, e.isSimpleGroup_congr.mpr hsimp, ?_⟩
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    obtain ⟨m, k, hm2, hB, hmod⟩ :=
      burnsideI8h_bender_param (CFSG.Open.fusionIsBenderGroup_of_isSimpleBenderGroup hBender)
    obtain ⟨S, hS, hVS, hΩ, hN, hconjS, Q, hcardQ⟩ :=
      burnsideI8h_sylow_data hV2 hV hBender hOle hBorel
    have hcardV : Nat.card V = 2 ^ m := hcardQ.trans (hB Q).2.2.2.1
    have hpRm : CFSG.pRank 2 ↥V = m := burnsideI8h_pRank_eq hVe hcardV
    rw [hpRm]
    refine ⟨by omega, hqs, burnsideI8h_lift_models hperf hOc hm2 hmod, ?_⟩
    apply le_antisymm
    · intro v hv
      exact Subgroup.subset_closure ⟨⟨hsc.1 hv, hVL hv⟩, hV2 v hv⟩
    · refine (Subgroup.closure_le V).2 ?_
      rintro x ⟨⟨hxT, hxL⟩, hx2⟩
      obtain ⟨l, hlL, hlx⟩ := hconjS x hxL hx2
      have hy2 : (l⁻¹ * x * l) ^ 2 = 1 := by
        calc (l⁻¹ * x * l) ^ 2 = l⁻¹ * x ^ 2 * l := by simp only [pow_two]; group
          _ = 1 := by rw [hx2]; group
      have hy : l⁻¹ * x * l ∈ V := hΩ _ hlx hy2
      have hxT' : (l⁻¹)⁻¹ * (l⁻¹ * x * l) * l⁻¹ ∈ T := by
        have : (l⁻¹)⁻¹ * (l⁻¹ * x * l) * l⁻¹ = x := by group
        rw [this]
        exact hxT
      have h1 := hsc' _ hy l⁻¹ hxT'
      have : (l⁻¹)⁻¹ * (l⁻¹ * x * l) * l⁻¹ = x := by group
      rw [this] at h1
      exact h1

end

end CFSG.ASVolI
