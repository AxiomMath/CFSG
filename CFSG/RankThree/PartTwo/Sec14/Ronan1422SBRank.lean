module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SRankTwo
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_13
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open scoped commutatorElement
open CFSG.OrderReductions.FrattiniAutomorphisms

theorem eq_one_of_pow_three_mem_rGroup {G : Type*} [Group G] {r : ℕ} [Fact r.Prime]
    (hr5 : 5 ≤ r) (K : Subgroup G) (hK : IsPGroup r K) {x : G} (hxK : x ∈ K)
    (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hK ⟨x, hxK⟩
  have hn' : x ^ r ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : Nat.Coprime 3 (r ^ n) :=
    Nat.Coprime.pow_right n
      ((Nat.coprime_primes Nat.prime_three (Fact.out : r.Prime)).mpr (by omega))
  have hg := pow_gcd_eq_one.mpr ⟨hx3, hn'⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
  exact hg

theorem card_mul_le_of_lt_pGroup {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (hG : IsPGroup r G) {K L : Subgroup G} (hKL : K < L) :
    r * Nat.card K ≤ Nat.card L := by
  have hLp : IsPGroup r L := hG.to_subgroup L
  have hne : K.subgroupOf L ≠ ⊤ := fun htop =>
    (ne_of_lt hKL) (le_antisymm hKL.le (Subgroup.subgroupOf_eq_top.mp htop))
  obtain ⟨n, hn⟩ := hLp.index (K.subgroupOf L)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.index_eq_one.mp (by rw [hn, pow_zero]))
  have hdvd : r ∣ (K.subgroupOf L).index := by
    rw [hn]
    exact dvd_pow_self r hn0
  have hpos : 0 < (K.subgroupOf L).index := by
    rw [hn]
    exact pow_pos (Fact.out : r.Prime).pos n
  have hle : r ≤ (K.subgroupOf L).index := Nat.le_of_dvd hpos hdvd
  have hKc : Nat.card (K.subgroupOf L) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL.le).toEquiv
  have hm := Subgroup.card_mul_index (K.subgroupOf L)
  rw [hKc] at hm
  calc r * Nat.card K ≤ (K.subgroupOf L).index * Nat.card K := Nat.mul_le_mul_right _ hle
    _ = Nat.card L := by rw [mul_comm]; exact hm

theorem isMulCommutative_closure_of_comm {G : Type*} [Group G] (T : Set G)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    ∀ a ∈ Subgroup.closure T, ∀ b ∈ Subgroup.closure T, a * b = b * a := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer T := by
    refine (Subgroup.closure_le _).mpr fun t ht => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    exact hT s hs t ht
  have h2 : T ⊆ ((Subgroup.centralizer ((Subgroup.closure T : Subgroup G) : Set G) :
      Subgroup G) : Set G) := by
    intro t ht
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    exact (Subgroup.mem_centralizer_iff.mp (h1 hs) t ht).symm
  have h3 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure T) :=
    (Subgroup.closure_le _).mpr h2
  intro a ha b hb
  exact Subgroup.mem_centralizer_iff.mp (h3 hb) a ha

theorem pow_eq_one_of_mem_closure_of_comm {G : Type*} [Group G] {r : ℕ} {T : Set G}
    (hcl : ∀ a ∈ Subgroup.closure T, ∀ b ∈ Subgroup.closure T, a * b = b * a)
    (hT : ∀ t ∈ T, t ^ r = 1) {a : G} (ha : a ∈ Subgroup.closure T) : a ^ r = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hT x hx
  | one => exact one_pow r
  | mul x y hx hy hxr hyr =>
    have hc : Commute x y := hcl x hx y hy
    rw [hc.mul_pow, hxr, hyr, one_mul]
  | inv x hx hxr => rw [inv_pow, hxr, inv_one]

theorem card_le_cube_of_class_two {Q : Type} [Group Q] [Finite Q] {r : ℕ} [Fact r.Prime]
    (hr5 : 5 ≤ r) (hQ : IsPGroup r Q) (H : Subgroup Q)
    (hexp : ∀ h ∈ H, h ^ r = 1)
    (hcls : ∀ h ∈ H, ∀ g : Q, ⁅h, g⁆ ∈ CFSG.centerIn H)
    (hrank : ∀ A : Subgroup Q, A ≤ H → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ r = 1) → Nat.card A ≤ r ^ 2)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) :
    Nat.card H ≤ r ^ 3 := by
  have hZH : ∀ z ∈ CFSG.centerIn H, z ∈ H := fun z hz => (Subgroup.mem_inf.mp hz).1
  have hZc : ∀ z ∈ CFSG.centerIn H, ∀ g ∈ H, g * z = z * g := fun z hz g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 g hg
  have hZcomm : ∀ a ∈ CFSG.centerIn H, ∀ b ∈ CFSG.centerIn H, a * b = b * a :=
    fun a ha b hb => (hZc a ha b (hZH b hb)).symm
  obtain ⟨x, hxH, hxZ⟩ : ∃ x ∈ H, x ∉ CFSG.centerIn H := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab (hZcomm a (hcon a ha) b (hcon b hb))
  have hx1 : x ≠ 1 := fun h => hxZ (by rw [h]; exact Subgroup.one_mem _)
  have hHp : IsPGroup r H := hQ.to_subgroup H
  obtain ⟨z0, hz0Z, hz01⟩ : ∃ z ∈ CFSG.centerIn H, z ≠ 1 := by
    haveI : Nontrivial H := ⟨⟨x, hxH⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩
    haveI : Nontrivial (Subgroup.center H) := IsPGroup.center_nontrivial hHp
    obtain ⟨g, hg⟩ := exists_ne (1 : Subgroup.center H)
    exact ⟨((g : H) : Q),
      Subgroup.mem_inf.mpr ⟨(g : H).2, Subgroup.mem_centralizer_iff.mpr fun k hk =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp g.2 ⟨k, hk⟩)⟩,
      fun h => hg (Subtype.ext (Subtype.ext h))⟩
  have hZbot : (⊥ : Subgroup Q) < CFSG.centerIn H := by
    refine lt_of_le_of_ne bot_le fun h => hz01 ?_
    have hz : z0 ∈ (⊥ : Subgroup Q) := by rw [h]; exact hz0Z
    simpa using hz
  have hZr : r ≤ Nat.card (CFSG.centerIn H) := by
    have h1 := card_mul_le_of_lt_pGroup hQ hZbot
    rw [Subgroup.card_bot, mul_one] at h1
    exact h1
  have hT1comm : ∀ a ∈ (CFSG.centerIn H : Set Q) ∪ {x},
      ∀ b ∈ (CFSG.centerIn H : Set Q) ∪ {x}, a * b = b * a := by
    intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hZcomm a ha b hb
    · rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact (hZc a ha x hxH).symm
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hZc b hb x hxH
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  have hT1H : ∀ t ∈ (CFSG.centerIn H : Set Q) ∪ {x}, t ∈ H := by
    intro t ht
    rcases ht with ht | ht
    · exact hZH t ht
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hxH
  have hT1e : ∀ t ∈ (CFSG.centerIn H : Set Q) ∪ {x}, t ^ r = 1 :=
    fun t ht => hexp t (hT1H t ht)
  have hA1comm := isMulCommutative_closure_of_comm _ hT1comm
  have hA1card : Nat.card (Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x})) ≤ r ^ 2 :=
    hrank _ ((Subgroup.closure_le _).mpr hT1H) hA1comm
      (fun a ha => pow_eq_one_of_mem_closure_of_comm hA1comm hT1e ha)
  have hZA1 : CFSG.centerIn H ≤ Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x}) :=
    fun z hz => Subgroup.subset_closure (Or.inl hz)
  have hxA1 : x ∈ Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x}) :=
    Subgroup.subset_closure (Or.inr (Set.mem_singleton x))
  have hZlt : CFSG.centerIn H < Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x}) :=
    lt_of_le_of_ne hZA1 fun h => hxZ (by rw [h]; exact hxA1)
  have hA1ge := card_mul_le_of_lt_pGroup hQ hZlt
  have hZle : Nat.card (CFSG.centerIn H) ≤ r := by
    have h1 : r * Nat.card (CFSG.centerIn H) ≤ r * r := by
      rw [← sq]
      exact hA1ge.trans hA1card
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hA1sq : r * r ≤ Nat.card (Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x})) :=
    (Nat.mul_le_mul_left r hZr).trans hA1ge
  have hcomm_y : ∀ y ∈ H, y * x = x * y →
      y ∈ Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x}) := by
    intro y hyH hyx
    by_contra hyA
    have hcomm_T1 : ∀ a ∈ (CFSG.centerIn H : Set Q) ∪ {x}, a * y = y * a := by
      intro a ha
      rcases ha with ha | ha
      · exact (hZc a ha y hyH).symm
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact hyx.symm
    have hT2comm : ∀ a ∈ (CFSG.centerIn H : Set Q) ∪ {x} ∪ {y},
        ∀ b ∈ (CFSG.centerIn H : Set Q) ∪ {x} ∪ {y}, a * b = b * a := by
      intro a ha b hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hT1comm a ha b hb
      · rw [Set.mem_singleton_iff] at hb
        rw [hb]
        exact hcomm_T1 a ha
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact (hcomm_T1 b hb).symm
      · rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb]
    have hT2H : ∀ t ∈ (CFSG.centerIn H : Set Q) ∪ {x} ∪ {y}, t ∈ H := by
      intro t ht
      rcases ht with ht | ht
      · exact hT1H t ht
      · rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact hyH
    have hT2e : ∀ t ∈ (CFSG.centerIn H : Set Q) ∪ {x} ∪ {y}, t ^ r = 1 :=
      fun t ht => hexp t (hT2H t ht)
    have hA2comm := isMulCommutative_closure_of_comm _ hT2comm
    have hA2card :
        Nat.card (Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x} ∪ {y})) ≤ r ^ 2 :=
      hrank _ ((Subgroup.closure_le _).mpr hT2H) hA2comm
        (fun a ha => pow_eq_one_of_mem_closure_of_comm hA2comm hT2e ha)
    have hA12 : Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x}) <
        Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x} ∪ {y}) := by
      refine lt_of_le_of_ne (Subgroup.closure_mono fun t ht => Or.inl ht) fun h => hyA ?_
      rw [h]
      exact Subgroup.subset_closure (Or.inr (Set.mem_singleton y))
    have hr12 := card_mul_le_of_lt_pGroup hQ hA12
    have hbad : r * (r * r) ≤ r ^ 2 :=
      (Nat.mul_le_mul_left r hA1sq).trans (hr12.trans hA2card)
    nlinarith
  have hid : ∀ a b : Q, ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
    intro a b
    simp only [commutatorElement_def, mul_inv_rev]
    group
  let f : H →* Q := MonoidHom.mk' (fun k : H => ⁅(k : Q), x⁆) (by
    intro a b
    show ⁅(a : Q) * (b : Q), x⁆ = ⁅(a : Q), x⁆ * ⁅(b : Q), x⁆
    rw [hid]
    have hac : (a : Q) * ⁅(b : Q), x⁆ = ⁅(b : Q), x⁆ * (a : Q) :=
      hZc _ (hcls (b : Q) b.2 x) a a.2
    rw [hac, mul_inv_cancel_right]
    exact hZcomm _ (hcls (b : Q) b.2 x) _ (hcls (a : Q) a.2 x))
  have hfZ : f.range ≤ CFSG.centerIn H := by
    rintro _ ⟨k, rfl⟩
    exact hcls (k : Q) k.2 x
  have hmemA1 : ∀ k : f.ker,
      ((k : H) : Q) ∈ Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x}) := by
    intro k
    have hk1 : ⁅((k : H) : Q), x⁆ = 1 := MonoidHom.mem_ker.mp k.2
    exact hcomm_y _ (k : H).2 (commutatorElement_eq_one_iff_mul_comm.mp hk1)
  have hker : Nat.card f.ker ≤ Nat.card (Subgroup.closure ((CFSG.centerIn H : Set Q) ∪ {x})) :=
    Nat.card_le_card_of_injective (fun k => ⟨((k : H) : Q), hmemA1 k⟩) (by
      intro k1 k2 hk
      have h1 := congrArg Subtype.val hk
      exact Subtype.ext (Subtype.ext h1))
  have hindex : Nat.card f.ker * Nat.card f.range = Nat.card H := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  have hrange : Nat.card f.range ≤ Nat.card (CFSG.centerIn H) := Subgroup.card_le_of_le hfZ
  calc Nat.card H = Nat.card f.ker * Nat.card f.range := hindex.symm
    _ ≤ r ^ 2 * r := Nat.mul_le_mul (hker.trans hA1card) (hrange.trans hZle)
    _ = r ^ 3 := by ring

theorem card_frattini_quotient_le_sq {Q : Type} [Group Q] [Finite Q] {r : ℕ} [Fact r.Prime]
    (hr5 : 5 ≤ r) (hQ : IsPGroup r Q) (H : Subgroup Q)
    (hexp : ∀ h ∈ H, h ^ r = 1)
    (hcls : ∀ h ∈ H, ∀ g : Q, ⁅h, g⁆ ∈ CFSG.centerIn H)
    (hrank : ∀ A : Subgroup Q, A ≤ H → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ r = 1) → Nat.card A ≤ r ^ 2) :
    Nat.card (↥H ⧸ frattini ↥H) ≤ r ^ 2 := by
  have hHp : IsPGroup r H := hQ.to_subgroup H
  haveI : Fact (IsPGroup r H) := ⟨hHp⟩
  have hr0 : 0 < r := by omega
  by_cases hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  · have hH2 : Nat.card H ≤ r ^ 2 := hrank H le_rfl hcomm hexp
    have hm := Subgroup.card_mul_index (frattini ↥H)
    have hdvd : Nat.card (↥H ⧸ frattini ↥H) ∣ Nat.card H := Dvd.intro_left _ hm
    exact (Nat.le_of_dvd (Nat.card_pos (α := ↥H)) hdvd).trans hH2
  · push Not at hcomm
    have hcard3 : Nat.card H ≤ r ^ 3 :=
      card_le_cube_of_class_two hr5 hQ H hexp hcls hrank hcomm
    have hΦ : frattini ↥H ≠ ⊥ := by
      intro hbot
      have hel : IsElementaryAbelian r ↥H :=
        (CFSG.frattini_eq_bot_iff_isElementaryAbelian).mp hbot
      obtain ⟨a, ha, b, hb, hab⟩ := hcomm
      exact hab (congrArg Subtype.val
        (isMulCommutative_iff.mp hel.toIsMulCommutative ⟨a, ha⟩ ⟨b, hb⟩))
    have hlt : (⊥ : Subgroup ↥H) < frattini ↥H := bot_lt_iff_ne_bot.mpr hΦ
    have hr_le := card_mul_le_of_lt_pGroup hHp hlt
    rw [Subgroup.card_bot, mul_one] at hr_le
    have hm := Subgroup.card_mul_index (frattini ↥H)
    have hVr : Nat.card (↥H ⧸ frattini ↥H) * r ≤ r ^ 2 * r := by
      calc Nat.card (↥H ⧸ frattini ↥H) * r
          ≤ Nat.card (↥H ⧸ frattini ↥H) * Nat.card (frattini ↥H) :=
            Nat.mul_le_mul_left _ hr_le
        _ = Nat.card ↥H := by rw [mul_comm]; exact hm
        _ ≤ r ^ 3 := hcard3
        _ = r ^ 2 * r := by ring
    exact Nat.le_of_mul_le_mul_right hVr hr0

theorem false_of_E9_of_commGroup {V : Type} [Group V] [Finite V] [IsMulCommutative V] {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hexp : ∀ v : V, v ^ r = 1) (hcard : Nat.card V ≤ r ^ 2)
    (E : Subgroup (MulAut V)) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9)
    (h : MulAut V) (hinv : ∀ e ∈ E, h * e * h⁻¹ = e⁻¹) : False := by
  letI : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := isMulCommutative_iff.mp inferInstance }
  have hV : ∃ v : V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    haveI : Subsingleton V := ⟨fun a b => by rw [hcon a, hcon b]⟩
    haveI : Subsingleton (MulAut V) := ⟨fun a b => MulEquiv.ext fun v => Subsingleton.elim _ _⟩
    have h1 : Nat.card E ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  obtain ⟨g, hgE, hg1, v, hv1, hgv⟩ :=
    exists_fixed_of_elemAbelian_nine hr (by omega) hexp hV E hEc hE3 hE9
  exact false_of_inverted_of_fixed hr hr5 hexp hcard g h (hE3 g hgE) hg1 ⟨v, hv1, hgv⟩
    (hinv g hgE)

theorem false_of_inverted_E9_of_rank_two {Q : Type} [Group Q] [Finite Q] {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hQ : IsPGroup r Q)
    (hrank : ∀ E : Subgroup Q, CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2)
    (E : Subgroup (MulAut Q)) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9)
    (h : MulAut Q) (hinv : ∀ e ∈ E, h * e * h⁻¹ = e⁻¹) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (IsPGroup r Q) := ⟨hQ⟩
  have hQnt : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI : Subsingleton (MulAut Q) := ⟨fun a b => MulEquiv.ext fun v => Subsingleton.elim _ _⟩
    have h1 : Nat.card E ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  obtain ⟨H, hHchar, hHcls, -, hHexp, hHfix⟩ :=
    CFSG.theorem_1_13 (G := Q) (p := r) (by omega)
  haveI : H.Characteristic := hHchar
  have hHp : IsPGroup r H := hQ.to_subgroup H
  have hexpH : ∀ k ∈ H, k ^ r = 1 := by
    intro k hk
    have h1 := Monoid.pow_exponent_eq_one (⟨k, hk⟩ : H)
    rw [hHexp] at h1
    simpa using congrArg Subtype.val h1
  have hcls : ∀ k ∈ H, ∀ g : Q, ⁅k, g⁆ ∈ CFSG.centerIn H := fun k hk g =>
    hHcls (Subgroup.commutator_mem_commutator hk (Subgroup.mem_top g))
  have hrankH : ∀ A : Subgroup Q, A ≤ H → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ r = 1) → Nat.card A ≤ r ^ 2 := by
    intro A _ hcomm hA
    apply hrank A
    show IsMulCommutative A ∧ ∀ x ∈ A, x ^ r = 1
    exact ⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext (hcomm a a.2 b b.2)), hA⟩
  obtain ⟨-, hVcomm, hVexp, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hHp
  haveI : IsMulCommutative (↥H ⧸ frattini ↥H) := hVcomm
  have hVcard : Nat.card (↥H ⧸ frattini ↥H) ≤ r ^ 2 :=
    card_frattini_quotient_le_sq hr5 hQ H hexpH hcls hrankH
  have hkerφ : IsPGroup r (quotientAutomorphism (frattini ↥H)).ker :=
    frattini_automorphism_kernel_isPGroup r hHp
  let ρ : MulAut Q →* MulAut H := MulAut.characteristic H
  let φ : MulAut H →* MulAut (↥H ⧸ frattini ↥H) := quotientAutomorphism (frattini ↥H)
  let ψ : E →* MulAut (↥H ⧸ frattini ↥H) := (φ.comp ρ).comp E.subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one ψ]
    rintro ⟨e, heE⟩ hψe
    have hρker : ρ e ∈ φ.ker := MonoidHom.mem_ker.mpr hψe
    have hρ3 : (ρ e) ^ 3 = 1 := by rw [← map_pow, hE3 e heE, map_one]
    have hρe1 : ρ e = 1 := eq_one_of_pow_three_mem_rGroup hr5 _ hkerφ hρker hρ3
    have hefix : e ∈ fixingSubgroup (M := MulAut Q) (α := Q) (H : Set Q) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have hy' := congrArg (fun σ : MulAut H => ((σ ⟨y, hy⟩ : H) : Q)) hρe1
      exact hy'
    have he1 : e = 1 := eq_one_of_pow_three_mem_rGroup hr5 _ hHfix hefix (hE3 e heE)
    exact Subtype.ext he1
  have hψcard : Nat.card ψ.range = 9 := by
    rw [← hE9]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hψcomm : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc _ a.2 _ b.2)
  have hψexp : ∀ a ∈ ψ.range, a ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext (hE3 a a.2)
    rw [← map_pow, ha3, map_one]
  have hψinv : ∀ a ∈ ψ.range, φ (ρ h) * a * (φ (ρ h))⁻¹ = a⁻¹ := by
    rintro _ ⟨a, rfl⟩
    have key : φ (ρ (h * (a : MulAut Q) * h⁻¹)) =
        φ (ρ h) * φ (ρ (a : MulAut Q)) * (φ (ρ h))⁻¹ := by
      simp only [map_mul, map_inv]
    rw [hinv a a.2] at key
    simp only [map_inv] at key
    exact key.symm
  exact false_of_E9_of_commGroup hr hr5 hVexp hVcard ψ.range hψcomm hψexp hψcard (φ (ρ h))
    hψinv

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
