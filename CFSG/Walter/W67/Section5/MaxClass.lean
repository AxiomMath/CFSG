module

public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped commutatorElement

namespace MaxClass

variable {P : Type*} [Group P]

theorem commutator_mem_center {g x : P}
    (h : (g : P ⧸ Subgroup.center P) * (x : P ⧸ Subgroup.center P) =
      (x : P ⧸ Subgroup.center P) * (g : P ⧸ Subgroup.center P)) :
    g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center P := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have e : g * x * g⁻¹ * x⁻¹ = ((g * x) * ((g * x)⁻¹ * (x * g)) * (g * x)⁻¹)⁻¹ := by group
  rw [e]
  exact (Subgroup.center P).inv_mem (Subgroup.Normal.conj_mem inferInstance _ h _)

@[expose] def commHom (x : P) (D : Subgroup P)
    (hD : ∀ g ∈ D, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center P) : D →* Subgroup.center P where
  toFun g := ⟨g * x * (g : P)⁻¹ * x⁻¹, hD g g.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    have hb := Subgroup.mem_center_iff.mp (hD b b.2)
    change (a : P) * b * x * ((a : P) * b)⁻¹ * x⁻¹ =
      ((a : P) * x * (a : P)⁻¹ * x⁻¹) * ((b : P) * x * (b : P)⁻¹ * x⁻¹)
    calc (a : P) * b * x * ((a : P) * b)⁻¹ * x⁻¹
        = ((a : P) * ((b : P) * x * (b : P)⁻¹ * x⁻¹)) * (x * (a : P)⁻¹ * x⁻¹) := by group
      _ = (((b : P) * x * (b : P)⁻¹ * x⁻¹) * a) * (x * (a : P)⁻¹ * x⁻¹) := by rw [hb a]
      _ = ((b : P) * x * (b : P)⁻¹ * x⁻¹) * ((a : P) * x * (a : P)⁻¹ * x⁻¹) := by group
      _ = ((a : P) * x * (a : P)⁻¹ * x⁻¹) * ((b : P) * x * (b : P)⁻¹ * x⁻¹) := (hb _).symm

theorem card_le_of_commutator_mem_center [Finite P] (x : P) (D : Subgroup P)
    (hD : ∀ g ∈ D, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center P) :
    Nat.card D ≤ Nat.card (Subgroup.centralizer ({x} : Set P)) * Nat.card (Subgroup.center P) := by
  have h1 := Subgroup.card_ker_mul_card_range (commHom x D hD)
  have hker : Nat.card (commHom x D hD).ker ≤ Nat.card (Subgroup.centralizer ({x} : Set P)) := by
    refine Nat.card_le_card_of_injective (fun g => ⟨((g : D) : P), ?_⟩) ?_
    · have hg := g.2
      rw [MonoidHom.mem_ker] at hg
      have hg' : ((g : D) : P) * x * ((g : D) : P)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : ((g : D) : P) * x = x * ((g : D) : P) := by
        calc ((g : D) : P) * x = (((g : D) : P) * x * ((g : D) : P)⁻¹ * x⁻¹) * (x * (g : D)) := by
              group
          _ = x * ((g : D) : P) := by rw [hg', one_mul]
      exact this
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
  rw [← h1]
  exact Nat.mul_le_mul hker (Subgroup.card_le_card_group _)

theorem card_comap_mk [Finite P] (H : Subgroup (P ⧸ Subgroup.center P)) :
    Nat.card (H.comap (QuotientGroup.mk' (Subgroup.center P))) =
      Nat.card H * Nat.card (Subgroup.center P) := by
  have hsurj := QuotientGroup.mk'_surjective (Subgroup.center P)
  have hidx := Subgroup.index_comap_of_surjective H hsurj
  have h1 := (H.comap (QuotientGroup.mk' (Subgroup.center P))).card_mul_index
  have h2 := H.card_mul_index
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
  rw [hidx] at h1
  have hpos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h3, ← h2]
  ring

end MaxClass

theorem isMaximalClass_of_card_centralizer :
    ∀ {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P], IsPGroup p P → ∀ (x : P),
      orderOf x = p → Nat.card (Subgroup.centralizer ({x} : Set P)) = p ^ 2 → IsMaximalClass p P := by
  intro p hp P _ _ hP x hx hc
  suffices H : ∀ n, ∀ (P : Type) [Group P] [Finite P], Nat.card P = n → IsPGroup p P →
      ∀ x : P, orderOf x = p → Nat.card (Subgroup.centralizer ({x} : Set P)) = p ^ 2 →
      IsMaximalClass p P from H _ P rfl hP x hx hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ hn hP x hx hc
  have hp1 := hp.out.one_lt
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hCdvd : p ^ 2 ∣ p ^ m := by
    rw [← hc, ← hm]
    exact Subgroup.card_subgroup_dvd_card _
  have h2m : 2 ≤ m := (Nat.pow_dvd_pow_iff_le_right hp1).mp hCdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  rcases h2m.eq_or_lt with h2 | h3
  ·
    refine ⟨2, le_rfl, by rw [hm, ← h2], ?_⟩
    rw [Nat.sub_self, Subgroup.lowerCentralSeries_zero]
    intro htop
    apply hx1
    have : x ∈ (⊤ : Subgroup P) := Subgroup.mem_top x
    rw [htop, Subgroup.mem_bot] at this
    exact this
  set Z := Subgroup.center P with hZdef
  have hxZ : x ∉ Z := by
    intro hxZ
    have htop : Subgroup.centralizer ({x} : Set P) = ⊤ := by
      ext g
      simp only [Subgroup.mem_top, iff_true, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hxZ g)
    rw [htop, Subgroup.card_top, hm] at hc
    have := Nat.pow_right_injective hp.out.two_le hc
    omega
  have hZC : Z ≤ Subgroup.centralizer ({x} : Set P) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hz x).symm
  have hZcard : Nat.card Z = p := by
    have hdvd : Nat.card Z ∣ p ^ 2 := by
      rw [← hc]
      exact Subgroup.card_dvd_of_le hZC
    obtain ⟨j, hj, hZj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have : Nontrivial P := by
      rw [← Finite.one_lt_card_iff_nontrivial, hm]
      exact Nat.one_lt_pow (by omega) hp1
    have hZnt : Nontrivial Z := hP.center_nontrivial
    have hZ1 : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    have hZne : Z ≠ Subgroup.centralizer ({x} : Set P) := by
      intro he
      apply hxZ
      rw [he, Subgroup.mem_centralizer_singleton_iff]
    have hjlt : j < 2 := by
      rcases hj.eq_or_lt with hj2 | hj2
      · exfalso
        apply hZne
        apply Subgroup.eq_of_le_of_card_ge hZC
        rw [hc, hZj, hj2]
      · exact hj2
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [hZj, pow_zero] at hZ1
      exact lt_irrefl _ hZ1
    rw [hZj]
    have : j = 1 := by omega
    rw [this, pow_one]
  set Q := P ⧸ Z
  have hQcard : Nat.card Q * p = p ^ m := by
    calc Nat.card Q * p = Nat.card Q * Nat.card Z := by rw [hZcard]
      _ = Nat.card P := (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
      _ = p ^ m := hm
  have hQcard' : Nat.card Q = p ^ (m - 1) := by
    have : p ^ m = p ^ (m - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [this] at hQcard
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos hQcard
  have hQ : IsPGroup p Q := hP.to_quotient Z
  set xbar : Q := (x : Q)
  have hxbar1 : xbar ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hxZ
  have hxbar : orderOf xbar = p := by
    apply orderOf_eq_prime _ hxbar1
    rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
  set CQ := Subgroup.centralizer ({xbar} : Set Q)
  set D := CQ.comap (QuotientGroup.mk' Z)
  have hD : ∀ g ∈ D, g * x * g⁻¹ * x⁻¹ ∈ Z := by
    intro g hg
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [show xbar = (x : Q) from rfl, QuotientGroup.mk'_apply] at hg
    have hg' : (g : Q) * (x : Q) = (x : Q) * (g : Q) := hg
    exact MaxClass.commutator_mem_center hg'
  have hDle := MaxClass.card_le_of_commutator_mem_center x D hD
  rw [hc, hZcard, ← pow_succ] at hDle
  have hDcard := MaxClass.card_comap_mk CQ
  rw [hZcard] at hDcard
  have hCQle : Nat.card CQ ≤ p ^ 2 := by
    have : Nat.card CQ * p ≤ p ^ 2 * p := by
      rw [← hDcard, ← pow_succ]
      exact hDle
    exact Nat.le_of_mul_le_mul_right this hp.out.pos
  by_cases hxbarZ : xbar ∈ Subgroup.center Q
  ·
    have htop : CQ = ⊤ := by
      ext g
      simp only [CQ, Subgroup.mem_top, iff_true, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hxbarZ g)
    rw [htop, Subgroup.card_top, hQcard'] at hCQle
    have hm3 : m = 3 := by
      have := (Nat.pow_le_pow_iff_right hp1).mp hCQle
      omega
    refine ⟨3, by norm_num, by rw [hm, hm3], ?_⟩
    rw [show 3 - 2 = 1 by norm_num, Subgroup.top_lowerCentralSeries_one]
    intro hab
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    have hcomm : ⁅g, x⁆ ∈ commutator P := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top g) (Subgroup.mem_top x)
    rw [hab, Subgroup.mem_bot, commutatorElement_def] at hcomm
    calc g * x = (g * x * g⁻¹ * x⁻¹) * (x * g) := by group
      _ = x * g := by rw [hcomm, one_mul]
  ·
    have hCQ : Nat.card CQ = p ^ 2 := by
      have hCQp : IsPGroup p CQ := hQ.to_subgroup CQ
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hCQp
      have hjle : j ≤ 2 := by
        rw [hj] at hCQle
        exact (Nat.pow_le_pow_iff_right hp1).mp hCQle
      have hxCQ : xbar ∈ CQ := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have hj2 : j = 2 := by
        by_contra hne
        have hj01 : j ≤ 1 := by omega
        have hzp : Subgroup.zpowers xbar = CQ := by
          apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxCQ)
          rw [Nat.card_zpowers, hxbar, hj]
          calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hj01
            _ = p := pow_one p
        have hZQle : Subgroup.center Q ≤ Subgroup.zpowers xbar := by
          rw [hzp]
          intro z hz
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_center_iff.mp hz xbar).symm
        have : Nontrivial Q := by
          rw [← Finite.one_lt_card_iff_nontrivial, hQcard']
          exact Nat.one_lt_pow (by omega) hp1
        have hZQnt : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
        have hprime : Nat.card (Subgroup.zpowers xbar) = p := by rw [Nat.card_zpowers, hxbar]
        have : Fact (Nat.card (Subgroup.zpowers xbar)).Prime := ⟨by rw [hprime]; exact hp.out⟩
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card
          ((Subgroup.center Q).subgroupOf (Subgroup.zpowers xbar)) with hb | ht
        · apply (Subgroup.nontrivial_iff_ne_bot _).mp hZQnt
          rw [Subgroup.subgroupOf_eq_bot] at hb
          exact hb.eq_bot_of_le hZQle
        · apply hxbarZ
          rw [Subgroup.subgroupOf_eq_top] at ht
          exact ht (Subgroup.mem_zpowers xbar)
      rw [hj, hj2]
    have hlt : Nat.card Q < n := by
      rw [← hn, hm, hQcard']
      exact Nat.pow_lt_pow_right hp1 (by omega)
    obtain ⟨m', hm'2, hm', hγ⟩ := ih _ hlt Q rfl hQ xbar hxbar hCQ
    have hm'eq : m' = m - 1 := by
      rw [hQcard'] at hm'
      exact (Nat.pow_right_injective hp.out.two_le hm').symm
    refine ⟨m, h2m, hm, fun hbot => hγ ?_⟩
    have hcen : (⊤ : Subgroup P).lowerCentralSeries (m - 3) ≤ Z := by
      intro g hg
      rw [Subgroup.mem_center_iff]
      intro y
      have hmem : ⁅g, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (m - 3 + 1) := by
        rw [Subgroup.lowerCentralSeries_succ]
        exact Subgroup.commutator_mem_commutator hg (Subgroup.mem_top y)
      rw [show m - 3 + 1 = m - 2 by omega, hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
      calc y * g = (g * y * g⁻¹ * y⁻¹)⁻¹ * (g * y) := by group
        _ = g * y := by rw [hmem, inv_one, one_mul]
    have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup P) (QuotientGroup.mk' Z) (m - 3)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)] at hmap
    rw [hm'eq, show m - 1 - 2 = m - 3 by omega, ← hmap, eq_bot_iff]
    intro q hq
    obtain ⟨g, hg, rfl⟩ := hq
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcen hg

end CFSG.Walter.W67
