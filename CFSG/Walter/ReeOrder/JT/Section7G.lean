module

public import CFSG.Walter.ReeOrder.JT.Section7F
public import CFSG.Walter.ReeOrder.JT.AuxGroup
public import CFSG.Walter.ReeOrder.JT.Section7B

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

theorem isKleinFour_of_card_four {X : Type*} [Group X] [Finite X] (h4 : Nat.card X = 4)
    (hsq : ∀ x : X, x * x = 1) : IsKleinFour X := by
  refine ⟨h4, ?_⟩
  have hdvd : Monoid.exponent X ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by rw [pow_two]; exact hsq x
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have : ∀ x : X, x = 1 := fun x => by
      have := Monoid.pow_exponent_eq_one x
      rwa [h1, pow_one] at this
    have hsub : Subsingleton X := ⟨fun a b => by rw [this a, this b]⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  · exact h1

@[expose] def omegaZ {X : Type*} [Group X] (H : Subgroup X) (r : ℕ) : Subgroup X where
  carrier := {x | x ∈ H ∧ (∀ y ∈ H, x * y = y * x) ∧ x ^ r = 1}
  mul_mem' := by
    rintro a b ⟨haH, hac, har⟩ ⟨hbH, hbc, hbr⟩
    refine ⟨H.mul_mem haH hbH, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · rw [(Commute.mul_pow (hac b hbH) r), har, hbr, one_mul]
  one_mem' := ⟨H.one_mem, fun y _ => by simp, one_pow r⟩
  inv_mem' := by
    rintro a ⟨haH, hac, har⟩
    refine ⟨H.inv_mem haH, fun y hy => ?_, by rw [inv_pow, har, inv_one]⟩
    have := hac y hy
    calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * y) * a⁻¹ := by rw [this]
      _ = y * a⁻¹ := by group

section OmegaZ

variable {X : Type*} [Group X] {H : Subgroup X} {r : ℕ}

theorem omegaZ_le : omegaZ H r ≤ H := fun _ hx => hx.1

theorem mul_comm_of_mem_omegaZ {a b : X} (ha : a ∈ omegaZ H r) (hb : b ∈ omegaZ H r) :
    a * b = b * a :=
  ha.2.1 b hb.1

theorem pow_eq_one_of_mem_omegaZ {a : X} (ha : a ∈ omegaZ H r) : a ^ r = 1 := ha.2.2

theorem normalizer_le_normalizer_omegaZ [Finite X] :
    Subgroup.normalizer (H : Set X) ≤ Subgroup.normalizer ((omegaZ H r : Subgroup X) : Set X) := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxH, hxc, hxr⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxH, fun y hy => ?_, ?_⟩
  · have hy' : g⁻¹ * y * g ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
      simpa using this
    have := hxc _ hy'
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [this]
      _ = y * (g * x * g⁻¹) := by group
  · rw [conj_pow, hxr, mul_one, mul_inv_cancel]

theorem omegaZ_ne_bot [Finite X] [hr : Fact r.Prime] (hH : IsPGroup r H) (hH1 : H ≠ ⊥) :
    omegaZ H r ≠ ⊥ := by
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH1
  have hZ := hH.center_nontrivial
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center H) r (by
    obtain ⟨n, hn⟩ := (hH.to_subgroup (Subgroup.center H)).exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hn
    rw [hn]
    exact dvd_pow_self r hn0)
  intro hbot
  have hmem : ((z : H) : X) ∈ omegaZ H r := by
    refine ⟨(z : H).2, fun y hy => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    · have : (z : Subgroup.center H) ^ r = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have := congrArg (fun w : Subgroup.center H => ((w : H) : X)) this
      simpa using this
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact hr.out.one_lt.ne hz

theorem isElementaryAbelian_omegaZ : IsElementaryAbelian r (omegaZ H r) where
  is_comm := ⟨fun a b => Subtype.ext (mul_comm_of_mem_omegaZ a.2 b.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
    Subtype.ext (by simpa using pow_eq_one_of_mem_omegaZ a.2)

end OmegaZ

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem coprime_card_Q
    (s : Setup h) : Nat.Coprime ((h.q - 1) / 2) (Nat.card s.Q) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have h4 := s.four_mul_card_Q hp
  rw [h.eps_eq_one_of_eq_three hp3] at h4
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have hQ : h.q + 1 = 4 * Nat.card s.Q := by exact_mod_cast h4.symm
  have h1 : h.q - 1 = 2 * ((h.q - 1) / 2) := by omega
  rw [Nat.coprime_iff_gcd_eq_one]
  set d := Nat.gcd ((h.q - 1) / 2) (Nat.card s.Q)
  have hd1 : d ∣ (h.q - 1) / 2 := Nat.gcd_dvd_left _ _
  have hd2 : d ∣ Nat.card s.Q := Nat.gcd_dvd_right _ _
  have hd3 : d ∣ 4 * Nat.card s.Q - 2 * ((h.q - 1) / 2) :=
    Nat.dvd_sub (dvd_mul_of_dvd_right hd2 4) (dvd_mul_of_dvd_right hd1 2)
  have he : 4 * Nat.card s.Q - 2 * ((h.q - 1) / 2) = 2 := by omega
  rw [he] at hd3
  have hodd : Odd d := (s.odd_card_Q hp).of_dvd_nat hd2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd3 with h' | h'
  · exact h'
  · rw [h'] at hodd
    exact absurd hodd (by decide)

theorem not_dvd_card_Q_of_pi
    (s : Setup h) {r : ℕ} (hr : r.Prime) (hrq : r ∣ (h.q - 1) / 2) :
    ¬ r ∣ Nat.card s.Q := fun hrQ =>
  hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (h.coprime_card_Q hp3 s) hrq hrQ)

theorem seven_le_of_pi
    {r : ℕ} [Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2) : 7 ≤ r :=
  (h.prime_mod_twelve hp3 hrq).1

theorem not_eight_dvd_card_normalizer_of_pi
    {r : ℕ} [hr : Fact r.Prime]
    (hrq : r ∣ (h.q - 1) / 2) {W : Subgroup G} (hW : IsPGroup r W) (hW1 : W ≠ ⊥) :
    ¬ 8 ∣ Nat.card (Subgroup.normalizer (W : Set G)) := by
  intro h8
  have hp := h.p_ne_two_of_eq_three hp3
  have hr7 := h.seven_le_of_pi hp3 hrq
  obtain ⟨s⟩ : Nonempty (Setup h) := by
    have hT := h.isKleinFour_inf_F hp
    obtain ⟨S, htS⟩ : ∃ S : Sylow 2 G, h.t ∈ S := by
      have h2 : IsPGroup 2 (Subgroup.zpowers h.t) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_t, pow_one])
      obtain ⟨S, hS⟩ := h2.exists_le_sylow
      exact ⟨S, hS (Subgroup.mem_zpowers _)⟩
    obtain ⟨s, -⟩ := h.exists_setup_card_normalizer hp (hT S htS)
    exact ⟨s⟩
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hW1 hn
  have hWodd : Odd (Nat.card W) := by
    rw [hn]
    exact (hr.out.odd_of_ne_two (by omega)).pow
  obtain ⟨g, hg⟩ := s.exists_conj_le_Q_of_eight_dvd hp hWodd h8
  have hdvd : Nat.card W ∣ Nat.card s.Q := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    exact Subgroup.card_dvd_of_le hg
  rw [hn] at hdvd
  exact h.not_dvd_card_Q_of_pi hp3 s hr.out hrq ((dvd_pow_self r hn0).trans hdvd)

theorem not_dvd_card_centralizer_of_isKleinFour
    {r : ℕ} [hr : Fact r.Prime]
    (hrq : r ∣ (h.q - 1) / 2) {V : Subgroup G} (hV : IsKleinFour V) :
    ¬ r ∣ Nat.card (Subgroup.centralizer (V : Set G)) := by
  intro hrC
  have hp := h.p_ne_two_of_eq_three hp3
  have hr7 := h.seven_le_of_pi hp3 hrq
  obtain ⟨s, hs⟩ := h.exists_setup_card_normalizer hp hV
  have hCN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have h1 : r ∣ 24 * Nat.card s.Q := hs ▸ hrC.trans (Subgroup.card_dvd_of_le hCN)
  rcases (Nat.Prime.dvd_mul hr.out).mp h1 with h2 | h2
  · rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num] at h2
    rcases (Nat.Prime.dvd_mul hr.out).mp h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) (hr.out.dvd_of_dvd_pow h3)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  · exact h.not_dvd_card_Q_of_pi hp3 s hr.out hrq h2

theorem card_le_of_le_centralizer
    {r : ℕ} [hr : Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2)
    {B : Subgroup G} (hBr : IsPGroup r B) (hBexp : ∀ x ∈ B, x ^ r = 1) {u : G}
    (hu : orderOf u = 2) (hBu : B ≤ Subgroup.centralizer ({u} : Set G)) :
    Nat.card B ≤ r := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hr7 := h.seven_le_of_pi hp3 hrq
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
  set B' := B.map (MulAut.conj g).toMonoidHom
  have hB'card : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hB't : B' ≤ Subgroup.centralizer ({h.t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxu := Subgroup.mem_centralizer_singleton_iff.mp (hBu hx)
    rw [← hg]
    change g * x * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  have hB'r : IsPGroup r B' := hBr.map _
  have hB'odd : Odd (Nat.card B') := by
    obtain ⟨n, hn⟩ := hB'r.exists_card_eq
    rw [hn]
    exact (hr.out.odd_of_ne_two (by omega)).pow
  have hB'F := h.le_F_of_odd hB't hB'odd
  have hB'c : IsCyclic B' :=
    (h.facts hp).cyclic r hr.out (by omega) (by rw [hp3]; omega) B' hB'F hB'r
  have hexp : Monoid.exponent B' ∣ r := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := x
    apply Subtype.ext
    simp only [Subgroup.coe_one]
    change (MulAut.conj g y) ^ r = 1
    rw [← map_pow, hBexp y hy, map_one]
  rw [← hB'card, ← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hr.out.pos hexp

theorem card_le_cube
    {r : ℕ} [hr : Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2) {A : Subgroup G}
    (hAr : IsPGroup r A) (hAexp : ∀ x ∈ A, x ^ r = 1) {V : Subgroup G} (hV : IsKleinFour V)
    (hVA : V ≤ Subgroup.normalizer (A : Set G)) : Nat.card A ≤ r ^ 3 := by
  classical
  have hr7 := h.seven_le_of_pi hp3 hrq
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV.card_four]; norm_num)
  obtain ⟨a, ha1⟩ := exists_ne (1 : V)
  obtain ⟨b, hb⟩ : ∃ b : V, b ≠ 1 ∧ b ≠ a := by
    by_contra! hcon
    have hsub : (Set.univ : Set V) ⊆ {1, a} := fun x _ => by
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr (hcon x hx)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, Set.ncard_pair (Ne.symm ha1), hV.card_four] at this
    omega
  have hsq : ∀ x : V, (x : G) * x = 1 := fun x => mul_self_of_isKleinFour' hV x.2
  have hcomm : Commute (a : G) b := congrArg Subtype.val ((hV.isMulCommutative).is_comm.comm a b)
  have ha1' : (a : G) ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
  have hb1' : (b : G) ≠ 1 := fun h0 => hb.1 (Subtype.ext h0)
  have hab' : (a : G) ≠ b := fun h0 => hb.2 (Subtype.ext h0).symm
  have hAodd : Odd (Nat.card A) := by
    obtain ⟨n, hn⟩ := hAr.exists_card_eq
    rw [hn]
    exact (hr.out.odd_of_ne_two (by omega)).pow
  have hBW := card_mul_card_sq_eq_mul (hsq a) (hsq b) ha1' hb1' hab' hcomm A (hVA a.2) (hVA b.2)
    hAodd
  have hCV : A ⊓ Subgroup.centralizer ({(a : G)} : Set G) ⊓
      Subgroup.centralizer ({(b : G)} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxa := Subgroup.mem_centralizer_singleton_iff.mp hx.1.2
    have hxb := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxV : x ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvV : (⟨v, hv⟩ : V) = 1 ∨ (⟨v, hv⟩ : V) = a ∨ (⟨v, hv⟩ : V) = b ∨
          (⟨v, hv⟩ : V) = a * b := by
        by_contra! hne
        exact hne.2.2.2 (IsKleinFour.eq_mul_of_ne_all (G := V) ha1 hb.1 (Ne.symm hb.2) hne.1
          hne.2.1 hne.2.2.1)
      rcases hvV with h1 | h1 | h1 | h1
      · have h1' : v = 1 := congrArg Subtype.val h1
        rw [h1', one_mul, mul_one]
      · have h1' : v = a := congrArg Subtype.val h1
        rw [h1']
        exact hxa.symm
      · have h1' : v = b := congrArg Subtype.val h1
        rw [h1']
        exact hxb.symm
      · have h1' : v = a * b := congrArg Subtype.val h1
        rw [h1', mul_assoc, ← hxb, ← mul_assoc, ← hxa, mul_assoc]
    have h1 : orderOf x ∣ Nat.card (Subgroup.centralizer (V : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hxV
    obtain ⟨n, hn⟩ := hAr.exists_card_eq
    have h2 : orderOf x ∣ r ^ n := hn ▸ Subgroup.orderOf_dvd_natCard A hx.1.1
    have hcop : Nat.Coprime (r ^ n) (Nat.card (Subgroup.centralizer (V : Set G))) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr.out).mpr
        (h.not_dvd_card_centralizer_of_isKleinFour hp3 hrq hV))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  rw [hCV, Subgroup.card_bot, one_pow, mul_one] at hBW
  have hinv : ∀ x : G, x * x = 1 → x ≠ 1 → Nat.card (A ⊓ Subgroup.centralizer ({x} : Set G) :
      Subgroup G) ≤ r := by
    intro x hxx hx1
    refine h.card_le_of_le_centralizer hp3 hrq (hAr.to_le inf_le_left)
      (fun y hy => hAexp y hy.1) (orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1)
      inf_le_right
  have hab1 : (a : G) * b ≠ 1 := by
    intro h0
    apply hab'
    rw [← mul_one (a : G), ← h0, ← mul_assoc, hsq a, one_mul]
  have habsq : (a : G) * b * ((a : G) * b) = 1 := by
    rw [show (a : G) * b * ((a : G) * b) = ((a : G) * a) * (b * b) by
      rw [mul_assoc, ← mul_assoc (b : G), ← hcomm.eq, mul_assoc, mul_assoc], hsq a, hsq b,
      one_mul]
  have h1 := hinv a (hsq a) ha1'
  have h2 := hinv b (hsq b) hb1'
  have h3 := hinv _ habsq hab1
  rw [hBW]
  calc _ ≤ r * r * r := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    _ = r ^ 3 := by ring

theorem isSolvable_normalizer_of_isPGroup_three
    {H : Subgroup G} (hH : IsPGroup 3 H)
    (hH1 : H ≠ ⊥) : Group.IsSolvable (Subgroup.normalizer (H : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSolvable_of_not_four_dvd fun h4 => hH1 ?_
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := Subgroup.normalizer (H : Set G)) 2
    (n := 2) (by norm_num; exact h4)
  refine h.eq_bot_of_isPGroup_three_of_le_normalizer hp3 hH
    (W := W.map (Subgroup.normalizer (H : Set G)).subtype)
    (IsPGroup.map (IsPGroup.of_card hW) _) ?_ (Subgroup.map_subtype_le _)
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hW]
  norm_num

end JTHyp

end CFSG.Walter.JT
