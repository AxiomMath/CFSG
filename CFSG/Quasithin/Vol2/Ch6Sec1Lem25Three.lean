module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Lie
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Rank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

theorem zpowers_eq_of_mem_ch625 {Q : Type} [Group Q] [Finite Q] {r : ℕ} (hr : r.Prime)
    {v x : Q} (hv : orderOf v = r) (hx : x ∈ Subgroup.zpowers v) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Subgroup.zpowers v := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers v := Subgroup.zpowers_le.mpr hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hpow : (v ^ i) ^ r = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hv, pow_orderOf_eq_one,
      one_zpow]
  have hord : orderOf (v ^ i) = r := by
    rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hv])

theorem card_sup_zpowers_ch625 {Q : Type} [Group Q] [Finite Q] {r : ℕ} {X : Subgroup Q} {c : Q}
    (hc : orderOf c = r) (hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (X : Set Q))
    (hXC : X ⊓ Subgroup.zpowers c = ⊥) :
    Nat.card ↥(X ⊔ Subgroup.zpowers c) = Nat.card X * r := by
  set C := Subgroup.zpowers c with hC
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hcN
  have h2 : X.relIndex C = Nat.card C := by
    rw [← Subgroup.inf_relIndex_right, hXC, Subgroup.relIndex_bot_left]
  have h3 := Subgroup.relIndex_mul_card X (C ⊔ X)
  rw [inf_eq_left.mpr le_sup_right, h1, h2, Nat.card_zpowers, hc] at h3
  rw [sup_comm, ← h3]
  ring

theorem zpowers_commute_ch625 {Q : Type} [Group Q] {u v : Q} (h : u * v = v * u) :
    ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow h i j).eq

theorem elemAbelian_card_three_ch625 {Q : Type} [Group Q] [Finite Q] {r : ℕ} (hr : r.Prime)
    {a b c : Q} (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (har : a ^ r = 1) (hbr : b ^ r = 1) (hcr : c ^ r = 1) (ha : a ≠ 1)
    (hb : b ∉ Subgroup.zpowers a) (hc : c ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    IsElemAbelian r (Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c) = r ^ 3 := by
  have : Fact r.Prime := ⟨hr⟩
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hc1 : c ≠ 1 := fun h => hc (h ▸ Subgroup.one_mem _)
  have hao := orderOf_eq_prime har ha
  have hbo := orderOf_eq_prime hbr hb1
  have hco := orderOf_eq_prime hcr hc1
  set A := Subgroup.zpowers a with hA
  set B := Subgroup.zpowers b with hB
  set C := Subgroup.zpowers c with hC
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := zpowers_commute_ch625 rfl
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := zpowers_commute_ch625 rfl
  have hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := zpowers_commute_ch625 rfl
  have hAB := zpowers_commute_ch625 hab
  have hAC := zpowers_commute_ch625 hac
  have hBC := zpowers_commute_ch625 hbc
  have hABc := isMulCommutative_sup_of_commute_ch625 hAc hBc hAB
  have hABC : ∀ x ∈ A ⊔ B, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    have hle : A ⊔ B ≤ Subgroup.centralizer ({y} : Set Q) := sup_le
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAC u hu y hy))
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hBC u hu y hy))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hFc := isMulCommutative_sup_of_commute_ch625 hABc hCc hABC
  have hAB1 : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    apply hb
    have h1 : Subgroup.zpowers x = Subgroup.zpowers b := zpowers_eq_of_mem_ch625 hr hbo hxB hx1
    have h2 : b ∈ Subgroup.zpowers x := h1 ▸ Subgroup.mem_zpowers b
    exact Subgroup.zpowers_le.mpr hxA h2
  have hBN : B ≤ Subgroup.normalizer (A : Set Q) := fun y hy =>
    mem_normalizer_of_forall_conj_mem_of_le fun x hx => by
      rw [← hAB x hx y hy]
      simpa using hx
  have hcardAB : Nat.card ↥(A ⊔ B) = r ^ 2 := by
    rw [card_sup_zpowers_ch625 hbo hBN hAB1, Nat.card_zpowers, hao]
    ring
  have hABC1 : (A ⊔ B) ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxAB, hxC⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    apply hc
    have hcx : c ∈ Subgroup.zpowers x := by
      rw [zpowers_eq_of_mem_ch625 hr hco hxC hx1]
      exact Subgroup.mem_zpowers c
    exact Subgroup.zpowers_le.mpr hxAB hcx
  have hCN : C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup Q) : Set Q) := fun y hy =>
    mem_normalizer_of_forall_conj_mem_of_le fun x hx => by
      rw [← hABC x hx y hy]
      simpa using hx
  have hcard : Nat.card ↥(A ⊔ B ⊔ C) = r ^ 3 := by
    rw [card_sup_zpowers_ch625 hco hCN hABC1, hcardAB]
    ring
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (hFc x x.2 y y.2)⟩⟩, ?_⟩, hcard⟩
  have hsub : A ⊔ B ⊔ C ≤
      { carrier := {z | z ∈ A ⊔ B ⊔ C ∧ z ^ r = 1}
        mul_mem' := fun {x y} hx hy => ⟨(A ⊔ B ⊔ C).mul_mem hx.1 hy.1, by
          rw [(Commute.mul_pow (hFc x hx.1 y hy.1) r), hx.2, hy.2, one_mul]⟩
        one_mem' := ⟨(A ⊔ B ⊔ C).one_mem, one_pow r⟩
        inv_mem' := fun {x} hx => ⟨(A ⊔ B ⊔ C).inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ } := by
    have hpow : ∀ u : Q, u ^ r = 1 → ∀ z ∈ Subgroup.zpowers u, z ^ r = 1 := by
      intro u hu z hz
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
    refine sup_le (sup_le (fun z hz => ⟨?_, hpow a har z hz⟩) fun z hz => ⟨?_, hpow b hbr z hz⟩)
      fun z hz => ⟨Subgroup.mem_sup_right hz, hpow c hcr z hz⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hz)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hz)
  intro z hz
  exact (hsub hz).2

theorem piK_eq_one_iff_ch625 {G : Type} [Group G] {K : Subgroup G}
    (hZ : Subgroup.center (KQ K) = ⊥) (k : ↥K) : piK K k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [pCoreOf_two_eq_map_ch625]
  constructor
  · intro h
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k : KQ K) ∈ Subgroup.center (KQ K) :=
      (QuotientGroup.eq_one_iff _).mp h
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨k, h1, rfl⟩
  · rintro ⟨k', hk', hkk⟩
    have : k' = k := Subtype.ext hkk
    subst this
    show (QuotientGroup.mk' (Subgroup.center (KQ K)))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k') = 1
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) k' = 1 from
      (QuotientGroup.eq_one_iff k').mpr hk', map_one]

theorem mem_pCoreOf_of_comm_ch625 {G : Type} [Group G] {K : Subgroup G}
    (hZ : Subgroup.center (KQ K) = ⊥) {k : G} (hk : k ∈ K)
    (hc : ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) : k ∈ pCoreOf 2 K := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hcen : π ⟨k, hk⟩ ∈ Subgroup.center (KQ K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
    have h1 : π (⟨k, hk⟩ * k' * (⟨k, hk⟩ : ↥K)⁻¹ * k'⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have h2 := hc k' k'.2
      rw [pCoreOf_two_eq_map_ch625] at h2
      obtain ⟨w, hw, hwe⟩ := h2
      have : w = ⟨k, hk⟩ * k' * (⟨k, hk⟩ : ↥K)⁻¹ * k'⁻¹ := Subtype.ext hwe
      rw [← this]
      exact hw
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc QuotientGroup.mk' (CFSG.pCore 2 ↥K) k' * π ⟨k, hk⟩ =
        (π ⟨k, hk⟩ * π k' * (π ⟨k, hk⟩)⁻¹ * (π k')⁻¹)⁻¹ * (π ⟨k, hk⟩ * π k') := by
          rw [hπ]; group
      _ = π ⟨k, hk⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥K) k' := by
          rw [h1, inv_one, one_mul]
  rw [hZ, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  rw [pCoreOf_two_eq_map_ch625]
  exact ⟨_, hcen, rfl⟩

theorem comm_mem_of_phiK_eq_conj_ch625 {G : Type} [Group G] {K : Subgroup G}
    (hZ : Subgroup.center (KQ K) = ⊥) {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (y : ↥K)
    (hxy : phiK K ⟨x, hxN⟩ = MulAut.conj (piK K y)) :
    x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 K := by
  have h1 : piK K (K.normalizerMonoidHom ⟨x, hxN⟩ y) = piK K y := by
    rw [← phiK_piK, hxy, MulAut.conj_apply, mul_inv_cancel_right]
  have h2 : piK K (K.normalizerMonoidHom ⟨x, hxN⟩ y * y⁻¹) = 1 := by
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  have h3 := (piK_eq_one_iff_ch625 hZ _).mp h2
  simpa [normalizerMonoidHom_coe, mul_assoc] using h3

variable {G : Type} [Group G] [Finite G]

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

theorem false_of_three {W N : Subgroup G}
    (hWH : W ≤ Subgroup.normalizer (ch6ZS T L V : Set G)) (hNW : N ≤ W)
    (hWN : W ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {a b c : G} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W)
    (hab : a * b * a⁻¹ * b⁻¹ ∈ N) (hac : a * c * a⁻¹ * c⁻¹ ∈ N) (hbc : b * c * b⁻¹ * c⁻¹ ∈ N)
    (har : a ^ r ∈ N) (hbr : b ^ r ∈ N) (hcr : c ^ r ∈ N) {P₁ P₂ : Subgroup G} (hNP : N ≤ P₁)
    (haP : a ∈ P₁) (hP : P₁ ≤ P₂) (hbP : b ∈ P₂) (ha1 : a ∉ N) (hb1 : b ∉ P₁) (hc1 : c ∉ P₂) :
    False := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup ↥W := N.subgroupOf W with hN'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).mpr hWN
  set μ : ↥W →* ↥W ⧸ N' := QuotientGroup.mk' N' with hμ
  have hμ1 : ∀ w : ↥W, μ w = 1 ↔ (w : G) ∈ N := fun w => by
    rw [hμ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
  set a' : ↥W := ⟨a, ha⟩
  set b' : ↥W := ⟨b, hb⟩
  set c' : ↥W := ⟨c, hc⟩
  have hcomm : ∀ u v : ↥W, (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ ∈ N → μ u * μ v = μ v * μ u := by
    intro u v huv
    have h1 : μ (u * v * u⁻¹ * v⁻¹) = 1 := (hμ1 _).mpr huv
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc μ u * μ v = (μ u * μ v * (μ u)⁻¹ * (μ v)⁻¹) * (μ v * μ u) := by group
      _ = μ v * μ u := by rw [h1, one_mul]
  have hpow : ∀ u : ↥W, (u : G) ^ r ∈ N → μ u ^ r = 1 := fun u hu => by
    rw [← map_pow]
    exact (hμ1 _).mpr (by simpa using hu)
  have himg : ∀ (P : Subgroup G), N ≤ P → ∀ w : ↥W, μ w ∈ (P.subgroupOf W).map μ →
      (w : G) ∈ P := by
    intro P hNP w hw
    obtain ⟨v, hv, hvw⟩ := hw
    have h1 : μ (v⁻¹ * w) = 1 := by rw [map_mul, map_inv, hvw, inv_mul_cancel]
    have h2 := hNP ((hμ1 _).mp h1)
    have e : (w : G) = v * ((v⁻¹ * w : ↥W) : G) := by simp
    rw [e]
    exact P.mul_mem (Subgroup.mem_subgroupOf.mp hv) h2
  have hb' : μ b' ∉ Subgroup.zpowers (μ a') := by
    intro hmem
    apply hb1
    refine himg P₁ hNP b' ?_
    have hle : Subgroup.zpowers (μ a') ≤ (P₁.subgroupOf W).map μ :=
      Subgroup.zpowers_le.mpr ⟨a', Subgroup.mem_subgroupOf.mpr haP, rfl⟩
    exact hle hmem
  have hc' : μ c' ∉ Subgroup.zpowers (μ a') ⊔ Subgroup.zpowers (μ b') := by
    intro hmem
    apply hc1
    refine himg P₂ (hNP.trans hP) c' ?_
    have hle : Subgroup.zpowers (μ a') ⊔ Subgroup.zpowers (μ b') ≤ (P₂.subgroupOf W).map μ :=
      sup_le (Subgroup.zpowers_le.mpr ⟨a', Subgroup.mem_subgroupOf.mpr (hP haP), rfl⟩)
        (Subgroup.zpowers_le.mpr ⟨b', Subgroup.mem_subgroupOf.mpr hbP, rfl⟩)
    exact hle hmem
  have ha' : μ a' ≠ 1 := fun h => ha1 ((hμ1 a').mp h)
  obtain ⟨hFel, hFcard⟩ := elemAbelian_card_three_ch625 hr (hcomm a' b' hab) (hcomm a' c' hac)
    (hcomm b' c' hbc) (hpow a' har) (hpow b' hbr) (hpow c' hcr) ha' hb' hc'
  have h3 : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup (↥W ⧸ N')) :=
    le_pRank_of_isElemAbelian_ch625 hr.one_lt le_top hFel hFcard
  have hNr : ¬ r ∣ Nat.card N' := by
    have hN2' : IsPGroup 2 N' := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNW).symm
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hN2'
    rw [hm]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  have h4 := K1.pRank_top_quotient_le W N' hr hNr
  have h5 : CFSG.Open.pRank r W ≤
      CFSG.Open.pRank r (Subgroup.normalizer (ch6ZS T L V : Set G)) :=
    CFSG.SectionRank.pRank_mono hr.one_lt hWH
  have h6 : CFSG.Open.pRank r (Subgroup.normalizer (ch6ZS T L V : Set G)) ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot d.hyp.qtke d.hyp.pCoreOf_H_ne_bot hr hr2
  omega

theorem exists_inner_elt (hZ : Subgroup.center (KQ K) = ⊥) {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) {r : ℕ} (hxr : x ^ r = 1)
    (hx1 : phiK K ⟨x, hxN⟩ ≠ 1) (hinn : phiK K ⟨x, hxN⟩ ∈ innAut (KBar K)) :
    ∃ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K ∧ y ^ r ∈ pCoreOf 2 K ∧ y ∉ pCoreOf 2 K := by
  obtain ⟨yb, hyb⟩ := hinn
  obtain ⟨y₁, rfl⟩ := piK_surjective K yb
  refine ⟨y₁, y₁.2, comm_mem_of_phiK_eq_conj_ch625 hZ hxN y₁ hyb.symm, ?_, ?_⟩
  · have h1 : MulAut.conj ((piK K y₁) ^ r) = 1 := by
      rw [map_pow, hyb, ← map_pow]
      have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ r = 1 :=
        Subtype.ext (by simp [hxr])
      rw [e, map_one]
    have h2 := mem_center_of_conj_eq_one h1
    rw [d.center_KBar, Subgroup.mem_bot, ← map_pow] at h2
    have h3 := (piK_eq_one_iff_ch625 hZ _).mp h2
    simpa using h3
  · intro hy
    apply hx1
    rw [← hyb, (piK_eq_one_iff_ch625 hZ y₁).mpr hy, map_one]

include hI in
theorem false_of_two_inner {K₀ : Subgroup G} (d₀ : Dat625 T M L V n l DL K₀) (hne : K₀ ≠ K)
    {x : G} (hx : x ∈ DL) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hxr : orderOf x = r)
    (hinn : phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K))
    (hinn₀ : phiK K₀ ⟨x, d₀.DL_le_NK hI hx⟩ ∈ innAut (KBar K₀))
    (hZ : Subgroup.center (KQ K) = ⊥) (hZ₀ : Subgroup.center (KQ K₀) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := d.hyp.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat d.hyp.nonabelian d.hyp.qtke).1
  set I := Subgroup.centralizer (ch6ZS T L V : Set G) with hIdef
  set Hn := Subgroup.normalizer (ch6ZS T L V : Set G) with hHn
  have hxr' : x ^ r = 1 := by rw [← hxr, pow_orderOf_eq_one]
  have hxN := d.DL_le_NK hI hx
  have hxN₀ := d₀.DL_le_NK hI hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxr
    exact hr.one_lt.ne hxr
  obtain ⟨y, hyK, hxy, hyr, hyO⟩ := d.exists_inner_elt hZ hxN hxr'
    (fun h => hx1 (d.eq_one_of_phi_DL hI hx h)) hinn
  obtain ⟨y₀, hy₀K, hxy₀, hy₀r, hy₀O⟩ := d₀.exists_inner_elt hZ₀ hxN₀ hxr'
    (fun h => hx1 (d₀.eq_one_of_phi_DL hI hx h)) hinn₀
  have hOI : pCoreOf 2 I ≠ ⊥ := d.pCoreOf_I_ne_bot
  have hKK₀ := (Vol2Native.lemma_1_2_1_two hLoc hI.h37 hOI d.comp d₀.comp hne.symm).1
  have hK₀N : K₀ ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_cComp_ch625 d.comp d₀.comp
  have hKN₀ : K ≤ Subgroup.normalizer (K₀ : Set G) :=
    le_normalizer_of_mem_cComp_ch625 d₀.comp d.comp
  have hcK : ∀ k₀ ∈ K₀, ∀ k ∈ K, k₀ * k * k₀⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro k₀ hk₀ k hk
    have h1 : ⁅k, k₀⁆ ∈ ⁅K, K₀⁆ := Subgroup.commutator_mem_commutator hk hk₀
    have e : k₀ * k * k₀⁻¹ * k⁻¹ = ⁅k, k₀⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ (hKK₀ h1).1
  have hcK₀ : ∀ k ∈ K, ∀ k₀ ∈ K₀, k * k₀ * k⁻¹ * k₀⁻¹ ∈ pCoreOf 2 K₀ := by
    intro k hk k₀ hk₀
    have h1 : ⁅k, k₀⁆ ∈ ⁅K, K₀⁆ := Subgroup.commutator_mem_commutator hk hk₀
    rw [← commutatorElement_def]
    exact (hKK₀ h1).2
  set W := Hn ⊓ Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (K₀ : Set G) with hW
  set N := pCoreOf 2 K ⊔ pCoreOf 2 K₀ with hN
  have hOK := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hOK₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hKW : K ≤ W := le_inf (le_inf d.K_le_H Subgroup.le_normalizer) hKN₀
  have hK₀W : K₀ ≤ W := le_inf (le_inf d₀.K_le_H hK₀N) Subgroup.le_normalizer
  have hxW : x ∈ W := ⟨⟨d.hyp.DL_le_normalizer_ZS d.hall hx, hxN⟩, hxN₀⟩
  have hNW : N ≤ W := sup_le (hOK.trans hKW) (hOK₀.trans hK₀W)
  have hWO : W ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    inf_le_left.trans (inf_le_right.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hWO₀ : W ≤ Subgroup.normalizer (pCoreOf 2 K₀ : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀)
  have hWN : W ≤ Subgroup.normalizer (N : Set G) := fun w hw =>
    mem_normalizer_sup_ch6 (hWO hw) (hWO₀ hw)
  have hN2 : IsPGroup 2 N :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_sup_of_normal_left'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀) (hOK₀.trans (hK₀W.trans hWO))
  have hab : y * y₀ * y⁻¹ * y₀⁻¹ ∈ N := Subgroup.mem_sup_right (hcK₀ y hyK y₀ hy₀K)
  have hac : y * x * y⁻¹ * x⁻¹ ∈ N := by
    have e : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_sup_left (Subgroup.inv_mem _ hxy)
  have hbc : y₀ * x * y₀⁻¹ * x⁻¹ ∈ N := by
    have e : y₀ * x * y₀⁻¹ * x⁻¹ = (x * y₀ * x⁻¹ * y₀⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_sup_right (Subgroup.inv_mem _ hxy₀)
  have hOKN₀ : pCoreOf 2 K ≤ Subgroup.normalizer (K₀ : Set G) := hOK.trans hKN₀
  have hy₀N : y₀ ∉ N := by
    intro hy
    have hON : pCoreOf 2 K₀ ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      hOK₀.trans (hK₀W.trans hWO)
    obtain ⟨o, ho, o₀, ho₀, he⟩ := exists_mul_of_mem_sup_ch625 hON hy
    have hoK₀ : o ∈ K₀ := by
      have h1 : o = y₀ * o₀⁻¹ := by rw [he]; group
      rw [h1]
      exact K₀.mul_mem hy₀K (K₀.inv_mem (hOK₀ ho₀))
    have hoO : o ∈ pCoreOf 2 K₀ := by
      have hle : K₀ ⊓ pCoreOf 2 K ≤ pCoreOf 2 K₀ :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
          (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
            ⟨Subgroup.le_normalizer hk, hK₀W.trans hWO hk⟩)
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_right)
      exact hle ⟨hoK₀, ho⟩
    exact hy₀O (he ▸ (pCoreOf 2 K₀).mul_mem hoO ho₀)
  have hyP : y ∉ pCoreOf 2 K ⊔ K₀ := by
    intro hy
    obtain ⟨o, ho, k₀, hk₀, he⟩ := exists_mul_of_mem_sup_ch625
      (hK₀N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hy
    have hk₀K : k₀ ∈ K := by
      have h1 : k₀ = o⁻¹ * y := by rw [he]; group
      rw [h1]
      exact K.mul_mem (K.inv_mem (hOK ho)) hyK
    have hk₀O := mem_pCoreOf_of_comm_ch625 hZ hk₀K fun k' hk' => hcK k₀ hk₀ k' hk'
    exact hyO (he ▸ (pCoreOf 2 K).mul_mem ho hk₀O)
  have hxP : x ∉ K ⊔ K₀ := by
    intro hxKK
    have hxI : x ∈ DL ⊓ I := ⟨hx, sup_le d.K_le_I d₀.K_le_I hxKK⟩
    rw [d.hyp.DL_inf_I d.hall, Subgroup.mem_bot] at hxI
    exact hx1 hxI
  exact d.false_of_three (inf_le_left.trans inf_le_left) hNW hWN hN2 hr hr2 (hK₀W hy₀K) (hKW hyK)
    hxW (by
      have e : y₀ * y * y₀⁻¹ * y⁻¹ = (y * y₀ * y⁻¹ * y₀⁻¹)⁻¹ := by group
      rw [e]; exact N.inv_mem hab) hbc hac (Subgroup.mem_sup_right hy₀r) (Subgroup.mem_sup_left hyr)
    (by rw [hxr']; exact N.one_mem) (sup_le_sup_left hOK₀ _) (Subgroup.mem_sup_right hy₀K)
    (sup_le_sup_right hOK _) (Subgroup.mem_sup_left hyK) hy₀N hyP hxP

end Dat625

end CFSG.Quasithin.H13
