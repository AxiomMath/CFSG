module

public import CFSG.Walter.ReeOrder.JT.Section4A
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_abelian_le_of_isSolvable {Y : Subgroup X} (hY : Group.IsSolvable Y)
    (hY1 : Y ≠ ⊥) :
    ∃ M : Subgroup X, M ≤ Y ∧ M ≠ ⊥ ∧ M ≤ Subgroup.centralizer (M : Set X) ∧
      Subgroup.normalizer (Y : Set X) ≤ Subgroup.normalizer (M : Set X) := by
  classical
  have hex : ∃ n, derivedSeries Y n = ⊥ := (Group.isSolvable_def Y).mp hY
  set n := Nat.find hex with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hn, h0, derivedSeries_zero] at this
    apply hY1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : Y) ∈ (⊤ : Subgroup Y) := Subgroup.mem_top _
    rw [‹(⊤ : Subgroup Y) = ⊥›, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  set M₀ := derivedSeries Y (n - 1)
  have hM₀ : M₀ ≠ ⊥ := Nat.find_min hex (by omega)
  have hM₀ab : ⁅M₀, M₀⁆ = ⊥ := by
    rw [← derivedSeries_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
    exact Nat.find_spec hex
  refine ⟨M₀.map Y.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h0
    apply hM₀
    rw [eq_bot_iff]
    intro x hx
    have : (x : X) ∈ M₀.map Y.subtype := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hM₀ab ha
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp this) b hb)
  · intro g hg
    refine mem_normalizer_of_conj_mem ?_
    rintro _ ⟨a, ha, rfl⟩
    let φ : Y ≃* Y :=
      { toFun := fun y => ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
        invFun := fun y => ⟨g⁻¹ * y * g, by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp y.2
          simpa using this⟩
        left_inv := fun y => Subtype.ext (by simp [mul_assoc])
        right_inv := fun y => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    have hmap := map_derivedSeries_eq (f := φ.toMonoidHom) φ.surjective (n - 1)
    have : φ a ∈ M₀ := by
      change φ a ∈ derivedSeries Y (n - 1)
      rw [← hmap]
      exact ⟨a, ha, rfl⟩
    exact ⟨φ a, this, rfl⟩

end General

namespace PSL2Facts

variable {G : Type*} [Group G] [Finite G] {F : Subgroup G} {p f : ℕ}

omit [Finite G] in
theorem inf_normalizer_eq (hF : PSL2Facts F p f) {a : G} (haF : a ∈ F) (ha : orderOf a = 2)
    {A : Subgroup G} (hAF : A ≤ F) (hAa : A ≤ Subgroup.centralizer ({a} : Set G)) (hA : A ≠ ⊥)
    (hodd : Odd (Nat.card A)) :
    F ⊓ Subgroup.normalizer (A : Set G) = F ⊓ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨U, w, hU, haU, -⟩ := hF.even_torus a haF ha
  have hAU : A ≤ U := by
    intro x hx
    have hx' : x ∈ F ⊓ Subgroup.centralizer ({a} : Set G) := ⟨hAF hx, hAa hx⟩
    rw [hU.centralizer_eq haU ha, hU.mem_sup_iff] at hx'
    rcases hx' with hxU | hxU
    · exact hxU
    · have hx2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        rw [pow_two]; exact hU.mul_self_of_mul_mem hxU)
      have hxo : Odd (orderOf x) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hx)
      have : orderOf x = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hx2 with h1 | h1
        · exact h1
        · rw [h1] at hxo
          exact absurd hxo (by decide)
      rw [orderOf_eq_one_iff.mp this]
      exact U.one_mem
  rw [hU.normalizer A hAU hA, hU.centralizer_eq haU ha]

theorem exists_centralizing_involution (hF : PSL2Facts F p f) {V : Subgroup G} (hVF : V ≤ F)
    (hV : IsKleinFour V) {X : Subgroup G} (hXF : X ≤ F) (hodd : Odd (Nat.card X))
    (hVX : V ≤ Subgroup.normalizer (X : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ X ≤ Subgroup.centralizer ({v} : Set G) := by
  classical
  have : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hV.card_four]
    norm_num
  by_cases hX : X = ⊥
  · obtain ⟨⟨v, hv⟩, hv1⟩ := exists_ne (1 : V)
    exact ⟨v, hv, fun h0 => hv1 (Subtype.ext h0), by rw [hX]; exact bot_le⟩
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨M, hMX, hM1, hMab, hMN⟩ := exists_abelian_le_of_isSolvable hsolv hX
  have hMF : M ≤ F := hMX.trans hXF
  have hModd : Odd (Nat.card M) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hMX)
  have hVM : V ≤ Subgroup.normalizer (M : Set G) := hVX.trans hMN
  have hXM : X ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer.trans hMN
  obtain ⟨⟨a, haV⟩, ha1⟩ := exists_ne (1 : V)
  have ha1' : a ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
  obtain ⟨b, hbV, hb1, hab⟩ : ∃ b ∈ V, b ≠ 1 ∧ a ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set G) ⊆ {1, a} := fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1).symm
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm ha1'), ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      hV.card_four] at this
    omega
  have hcab : Commute a b := by
    have := hV.isMulCommutative.is_comm.comm ⟨a, haV⟩ ⟨b, hbV⟩
    exact congrArg Subtype.val this
  have haa : a * a = 1 := mul_self_of_isKleinFour' hV haV
  have hbb : b * b = 1 := mul_self_of_isKleinFour' hV hbV
  have hab1 : a * b ≠ 1 := by
    intro h1
    apply hab
    rw [← mul_one a, ← h1, ← mul_assoc, haa, one_mul]
  have hCcd : ∀ c ∈ V, ∀ d ∈ V, c ≠ 1 → d ≠ 1 → c ≠ d → ∀ y ∈ M, y * c = c * y →
      y * d = d * y → y = 1 := by
    intro c hcV d hdV hc1 hd1 hcd y hy hyc hyd
    have hyC : y ∈ F ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨hMF hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      by_cases hx1 : x = 1
      · rw [hx1]; simp
      by_cases hxc : x = c
      · rw [hxc]; exact hyc.symm
      by_cases hxd : x = d
      · rw [hxd]; exact hyd.symm
      have := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨c, hcV⟩) (y := ⟨d, hdV⟩)
        (z := ⟨x, hx⟩) (fun h0 => hc1 (congrArg Subtype.val h0))
        (fun h0 => hd1 (congrArg Subtype.val h0)) (fun h0 => hcd (congrArg Subtype.val h0))
        (fun h0 => hx1 (congrArg Subtype.val h0)) (fun h0 => hxc (congrArg Subtype.val h0))
        (fun h0 => hxd (congrArg Subtype.val h0))
      rw [show x = c * d from congrArg Subtype.val this]
      rw [mul_assoc, ← hyd, ← mul_assoc, ← hyc, mul_assoc]
    rw [hF.kleinFour V hVF hV] at hyC
    have h4 : orderOf y ∣ 4 := hV.card_four ▸ Subgroup.orderOf_dvd_natCard V hyC
    have ho : Odd (orderOf y) := Odd.of_dvd_nat hModd (Subgroup.orderOf_dvd_natCard M hy)
    have : orderOf y = 1 := by
      have h4' : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4'] at h4
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
      interval_cases k
      · simpa using hk'
      · rw [hk'] at ho; exact absurd ho (by decide)
      · rw [hk'] at ho; exact absurd ho (by decide)
    exact orderOf_eq_one_iff.mp this
  have hc2 : ∀ c ∈ V, c ≠ 1 → orderOf c = 2 := fun c hc hc1 =>
    orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_isKleinFour' hV hc) hc1
  have hpair : ∀ c ∈ V, ∀ d ∈ V, c ≠ 1 → d ≠ 1 → c ≠ d →
      M ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ ∨
        M ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
    intro c hcV d hdV hc1 hd1 hcd
    by_contra hcon
    push Not at hcon
    obtain ⟨hAc, hAd⟩ := hcon
    have hN := hF.inf_normalizer_eq (hVF hcV) (hc2 c hcV hc1)
      (A := M ⊓ Subgroup.centralizer ({c} : Set G)) (inf_le_left.trans hMF) inf_le_right hAc
      (Odd.of_dvd_nat hModd (Subgroup.card_dvd_of_le inf_le_left))
    apply hAd
    rw [eq_bot_iff]
    intro y hy
    have hyN : y ∈ F ⊓ Subgroup.normalizer
        ((M ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
      refine ⟨hMF hy.1, mem_normalizer_of_conj_mem fun x hx => ?_⟩
      have hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp (hMab hy.1)) x hx.1
      rw [show y * x * y⁻¹ = x by rw [← hxy, mul_inv_cancel_right]]
      exact hx
    rw [hN] at hyN
    exact Subgroup.mem_bot.mpr (hCcd c hcV d hdV hc1 hd1 hcd y hy.1
      (Subgroup.mem_centralizer_singleton_iff.mp hyN.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2))
  have hBW := card_mul_card_sq_eq_mul haa hbb ha1' hb1 hab hcab M (hVM haV) (hVM hbV) hModd
  have hC0 : M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) = ⊥ :=
    eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (hCcd a haV b hbV ha1' hb1 hab y hy.1.1
      (Subgroup.mem_centralizer_singleton_iff.mp hy.1.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2))
  rw [hC0, Subgroup.card_bot, one_pow, mul_one] at hBW
  have habV : a * b ∈ V := V.mul_mem haV hbV
  have hane : a ≠ a * b := by
    intro h0
    apply hb1
    have := congrArg (a⁻¹ * ·) h0
    simpa using this.symm
  have hbne : b ≠ a * b := by
    intro h0
    apply ha1'
    have := congrArg (· * b⁻¹) h0
    simpa using this.symm
  have hfinish : ∀ c ∈ V, c ≠ 1 → Nat.card M = Nat.card
      (M ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) →
      ∃ v ∈ V, v ≠ 1 ∧ X ≤ Subgroup.centralizer ({v} : Set G) := by
    intro c hcV hc1 hcard
    have hMc : M ≤ Subgroup.centralizer ({c} : Set G) := by
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : M ⊓ Subgroup.centralizer
        ({c} : Set G) ≤ M) (le_of_eq hcard)
      rw [← this]
      exact inf_le_right
    have hN := hF.inf_normalizer_eq (hVF hcV) (hc2 c hcV hc1) hMF hMc hM1 hModd
    refine ⟨c, hcV, hc1, fun x hx => ?_⟩
    have : x ∈ F ⊓ Subgroup.normalizer (M : Set G) := ⟨hXF hx, hXM hx⟩
    rw [hN] at this
    exact this.2
  by_cases hA : M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥
  · by_cases hB : M ⊓ Subgroup.centralizer ({b} : Set G) = ⊥
    · by_cases hAB : M ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥
      · exfalso
        rw [hA, hB, hAB, Subgroup.card_bot] at hBW
        exact hM1 ((Subgroup.card_eq_one).mp (by simpa using hBW))
      · refine hfinish (a * b) habV hab1 ?_
        rw [hBW, hA, hB, Subgroup.card_bot]
        ring
    · have hAB := (hpair b hbV (a * b) habV hb1 hab1 hbne).resolve_left hB
      refine hfinish b hbV hb1 ?_
      rw [hBW, hA, hAB, Subgroup.card_bot]
      ring
  · have hB := (hpair a haV b hbV ha1' hb1 hab).resolve_left hA
    have hAB := (hpair a haV (a * b) habV ha1' hab1 hane).resolve_left hA
    refine hfinish a haV ha1' ?_
    rw [hBW, hB, hAB, Subgroup.card_bot]
    ring

end PSL2Facts

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2)
include hp

theorem exists_conj_le_Q_of_le_normalizer
    {K : Subgroup G} (hodd : Odd (Nat.card K))
    (hSK : (s.S : Subgroup G) ≤ Subgroup.normalizer (K : Set G)) :
    ∃ g : G, K.map (MulAut.conj g).toMonoidHom ≤ s.Q := by
  classical
  by_cases hK : K = ⊥
  · exact ⟨1, by rw [hK, Subgroup.map_bot]; exact bot_le⟩
  let : Fintype G := Fintype.ofFinite G
  have hab := h.abelian_sylow s.S
  have hcommS : ∀ x ∈ s.S, ∀ y ∈ s.S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set I := Finset.univ.filter (fun x : G => x ∈ (s.S : Subgroup G) ∧ x ≠ 1)
  set φ : G → ℕ := fun x => Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)
  have htI : h.t ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.t_mem_S, h.t_ne_one⟩
  obtain ⟨t', ht'I, hmax⟩ := Finset.exists_max_image I φ ⟨h.t, htI⟩
  simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at ht'I hmax
  obtain ⟨ht'S, ht'1⟩ := ht'I
  set d := s.data hp
  have hvS : d.v ∈ s.S := s.le_S d.v_mem_T
  have hX1 : K ⊓ Subgroup.centralizer ({t'} : Set G) ≠ ⊥ := by
    intro hX
    have hall : ∀ x ∈ s.S, x ≠ 1 → K ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
      intro x hxS hx1
      have := hmax x ⟨hxS, hx1⟩
      simp only [φ, hX, Subgroup.card_bot] at this
      exact Subgroup.card_eq_one.mp (le_antisymm this Nat.card_pos)
    have htv1 : h.t * d.v ≠ 1 := fun h0 => d.t_ne_v (by
      rw [← mul_one h.t, ← h0, ← mul_assoc, h.t_mul_t, one_mul])
    have hBW := card_mul_card_sq_eq_mul h.t_mul_t d.v_mul_v h.t_ne_one d.v_ne_one d.t_ne_v
      (hcommS _ s.t_mem_S _ hvS) K (hSK s.t_mem_S) (hSK hvS) hodd
    rw [hall _ s.t_mem_S h.t_ne_one, hall _ hvS d.v_ne_one,
      hall _ ((s.S : Subgroup G).mul_mem s.t_mem_S hvS) htv1, bot_inf_eq, Subgroup.card_bot]
      at hBW
    exact hK (Subgroup.card_eq_one.mp (by simpa using hBW))
  have ht'2 : orderOf t' = 2 := orderOf_eq_prime
    (by rw [pow_two]; exact h.mul_self_of_mem_sylow hp s.S s.t_mem_S ht'S) ht'1
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp ht'2
  set h' := h.conj g⁻¹
  have hh't : h'.t = t' := by
    rw [JTHyp.conj_t, ← hg, inv_inv]
    group
  have hh'p : h'.p ≠ 2 := hp
  set X := K ⊓ Subgroup.centralizer ({t'} : Set G)
  have hXodd : Odd (Nat.card X) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  have hXF : X ≤ h'.F := h'.le_F_of_odd (hh't ▸ inf_le_right) hXodd
  have ht'S' : h'.t ∈ s.S := hh't ▸ ht'S
  have hV' := h'.isKleinFour_inf_F hh'p s.S ht'S'
  have hV'X : (s.S : Subgroup G) ⊓ h'.F ≤ Subgroup.normalizer (X : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_mem fun y hy => ⟨(Subgroup.mem_normalizer_iff.mp
      (hSK hx.1) y).mp hy.1, ?_⟩
    have hxt : x * t' = t' * x := hcommS _ hx.1 _ ht'S
    have hyt : y * t' = t' * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    show x * y * x⁻¹ ∈ Subgroup.centralizer ({t'} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * y * x⁻¹ * t' = x * y * (x⁻¹ * t') := by group
      _ = x * y * (t' * x⁻¹) := by
        rw [show x⁻¹ * t' = t' * x⁻¹ by
          calc x⁻¹ * t' = x⁻¹ * (t' * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * t') * x⁻¹ := by rw [hxt]
            _ = t' * x⁻¹ := by group]
      _ = x * (y * t') * x⁻¹ := by group
      _ = x * (t' * y) * x⁻¹ := by rw [hyt]
      _ = t' * (x * y * x⁻¹) := by
        rw [show x * (t' * y) * x⁻¹ = (x * t') * y * x⁻¹ by group, hxt]
        group
  obtain ⟨τ, hτV, hτ1, hXτ⟩ := (h'.facts hh'p).exists_centralizing_involution inf_le_right hV'
    hXF hXodd hV'X
  have hτS : τ ∈ s.S := hτV.1
  have hτt : t' ≠ τ := fun h0 => h'.t_not_mem (hh't ▸ h0 ▸ hτV.2)
  have hτ2 : τ * τ = 1 := h.mul_self_of_mem_sylow hp s.S s.t_mem_S hτS
  have ht't : t' * t' = 1 := h.mul_self_of_mem_sylow hp s.S s.t_mem_S ht'S
  have hcτ : Commute t' τ := hcommS _ ht'S _ hτS
  have ht'τ1 : t' * τ ≠ 1 := fun h0 => hτt (by
    rw [← mul_one t', ← h0, ← mul_assoc, ht't, one_mul])
  have hXτ' : X ≤ K ⊓ Subgroup.centralizer ({τ} : Set G) := le_inf inf_le_left hXτ
  have hτeq : K ⊓ Subgroup.centralizer ({τ} : Set G) = X :=
    (Subgroup.eq_of_le_of_card_ge hXτ' (hmax τ ⟨hτS, hτ1⟩)).symm
  have hXt'τ : X ≤ K ⊓ Subgroup.centralizer ({t' * τ} : Set G) := by
    refine le_inf inf_le_left fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hXτ hx)
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  have ht'τeq : K ⊓ Subgroup.centralizer ({t' * τ} : Set G) = X :=
    (Subgroup.eq_of_le_of_card_ge hXt'τ (hmax (t' * τ)
      ⟨(s.S : Subgroup G).mul_mem ht'S hτS, ht'τ1⟩)).symm
  have hX3 : K ⊓ Subgroup.centralizer ({t'} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) =
      X := inf_eq_left.mpr hXτ
  have hBW := card_mul_card_sq_eq_mul ht't hτ2 ht'1 hτ1 hτt hcτ K (hSK ht'S) (hSK hτS) hodd
  rw [hX3, hτeq, ht'τeq] at hBW
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hKX : Nat.card K = Nat.card X := by
    have : Nat.card K * Nat.card X ^ 2 = Nat.card X * Nat.card X ^ 2 := by rw [hBW]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hXpos 2) this
  have hKeq : X = K := Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hKX)
  set T' := GorensteinWalter.kleinFourOfCommutingInvolutions t' τ ht't hτ2 hcτ
  have hT' : IsKleinFour T' :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ _ _ ht'1 hτ1 hτt _
  have hKT' : K ≤ Subgroup.centralizer (T' : Set G) := by
    intro x hx
    rw [← hKeq] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hXτ hx)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ ({t' * τ, t', τ, 1} : Set G) at hy
    rcases hy with rfl | rfl | rfl | rfl
    · rw [mul_assoc, ← h2, ← mul_assoc, ← h1, mul_assoc]
    · exact h1.symm
    · exact h2.symm
    · simp
  obtain ⟨g₂, hg₂⟩ := (lemma_2_1 h hp).2.2.2.2.2 T' s.T hT' s.four
  refine ⟨g₂, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine (s.mem_Q_iff hp).mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hg₂] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    have := (Subgroup.mem_centralizer_iff.mp (hKT' hx)) y' hy'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g₂ * y' * g₂⁻¹ * (g₂ * x * g₂⁻¹) = g₂ * (y' * x) * g₂⁻¹ by group, this]
    group
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K hx)

theorem lemma_4_2_b
    {K : Subgroup G} (hK : IsTwoSignalizer K) :
    ∃ g : G, K.map (MulAut.conj g).toMonoidHom ≤ s.Q := by
  obtain ⟨hodd, S', hS'⟩ := hK
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G S' s.S
  set K₀ := K.map (MulAut.conj g₀).toMonoidHom
  have hK₀odd : Odd (Nat.card K₀) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
    exact hodd
  have hSK₀ : (s.S : Subgroup G) ≤ Subgroup.normalizer (K₀ : Set G) := by
    rw [← hg₀]
    change MulAut.conj g₀ • (S' : Subgroup G) ≤ _
    rintro _ ⟨y, hy, rfl⟩
    refine mem_normalizer_of_conj_mem ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp (hS' hy) x).mp hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulDistribMulAction.toMonoidEnd_apply,
      MulDistribMulAction.toMonoidHom_apply, MulAut.smul_def]
    group
  obtain ⟨g, hg⟩ := s.exists_conj_le_Q_of_le_normalizer hp hK₀odd hSK₀
  refine ⟨g * g₀, ?_⟩
  rw [map_conj_mul]
  exact hg

end Setup

end CFSG.Walter.JT
