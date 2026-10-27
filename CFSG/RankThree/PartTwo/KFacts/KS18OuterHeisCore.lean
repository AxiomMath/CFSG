module

public import CFSG.RankThree.PartTwo.KFacts.KS18OuterInner

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS18

open scoped commutatorElement

theorem commute_of_heis {G : Type*} [Group G] {U W : Subgroup G} {w r : G} {m : ℕ}
    (hWU : W ≤ U) (hw : w ∈ W)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ W ∧ ∀ c ∈ U, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hCw : ∀ x ∈ U, x * w = w * x → x ∈ W) (hW : ∀ x ∈ W, x ^ 2 ^ m = 1 → x = 1)
    (hrU : ∀ u ∈ U, r * u * r⁻¹ ∈ U) (hrW : ∀ x ∈ W, r * x = x * r) (hr : r ^ 2 ^ m = 1)
    {u : G} (hu : u ∈ U) : r * u = u * r := by
  have hwU := hWU hw
  have hrw : r * w * r⁻¹ = w := by rw [hrW w hw, mul_inv_cancel_right]
  have h1 : ⁅w, r * u * r⁻¹⁆ = ⁅w, u⁆ := by
    have hc := (hcomm w hwU u hu).1
    calc ⁅w, r * u * r⁻¹⁆ = ⁅r * w * r⁻¹, r * u * r⁻¹⁆ := by rw [hrw]
      _ = r * ⁅w, u⁆ * r⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅w, u⁆ := by rw [hrW _ hc, mul_inv_cancel_right]
  have hdU : r * u * r⁻¹ * u⁻¹ ∈ U := U.mul_mem (hrU u hu) (U.inv_mem hu)
  have ha := (hcomm w hwU u hu).2 _ hdU
  have hdw : r * u * r⁻¹ * u⁻¹ * w = w * (r * u * r⁻¹ * u⁻¹) := by
    calc r * u * r⁻¹ * u⁻¹ * w = r * u * r⁻¹ * u⁻¹ * (⁅w, u⁆ * u * w * u⁻¹) := by
          rw [commutatorElement_def]; group
      _ = ⁅w, u⁆ * (r * u * r⁻¹ * u⁻¹) * u * w * u⁻¹ := by
          rw [ha]; simp only [mul_assoc]
      _ = ⁅w, r * u * r⁻¹⁆ * (r * u * r⁻¹) * w * u⁻¹ := by rw [h1]; group
      _ = w * (r * u * r⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
  have hdW : r * u * r⁻¹ * u⁻¹ ∈ W := hCw _ hdU hdw
  have hpow : ∀ n : ℕ, r ^ n * u * (r ^ n)⁻¹ = (r * u * r⁻¹ * u⁻¹) ^ n * u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hrd : r * (r * u * r⁻¹ * u⁻¹) ^ n * r⁻¹ = (r * u * r⁻¹ * u⁻¹) ^ n := by
        rw [((Commute.pow_right (hrW _ hdW) n)).eq, mul_inv_cancel_right]
      calc r ^ (n + 1) * u * (r ^ (n + 1))⁻¹ = r * (r ^ n * u * (r ^ n)⁻¹) * r⁻¹ := by
            rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = r * (r * u * r⁻¹ * u⁻¹) ^ n * r⁻¹ * (r * u * r⁻¹) := by
            rw [ih]; simp only [mul_assoc, inv_mul_cancel_left]
        _ = (r * u * r⁻¹ * u⁻¹) ^ n * (r * u * r⁻¹) := by rw [hrd]
        _ = (r * u * r⁻¹ * u⁻¹) ^ (n + 1) * u := by
            rw [pow_succ]; simp only [mul_assoc, inv_mul_cancel, mul_one]
  have h2 : (r * u * r⁻¹ * u⁻¹) ^ 2 ^ m = 1 := by
    have := hpow (2 ^ m)
    rw [hr, one_mul, inv_one, mul_one] at this
    exact mul_eq_right.mp this.symm
  have h3 := hW _ hdW h2
  calc r * u = r * u * r⁻¹ * u⁻¹ * (u * r) := by group
    _ = u * r := by rw [h3, one_mul]

theorem mem_of_commute_of_card {G : Type*} [Group G] [Finite G] {U W : Subgroup G} {w : G}
    (hU27 : Nat.card U = 27) (hW9 : Nat.card W = 9) (hWU : W ≤ U) (hw : w ∈ W)
    (hwZ : ∃ x ∈ U, x * w ≠ w * x) {x : G} (hx : x ∈ U) (hxw : x * w = w * x) : x ∈ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsMulCommutative W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hW9]; norm_num)
  have hWC : W ≤ U ⊓ Subgroup.centralizer ({w} : Set G) := fun y hy =>
    ⟨hWU hy, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : W) ⟨w, hw⟩))⟩
  have hCU : U ⊓ Subgroup.centralizer ({w} : Set G) ≤ U := inf_le_left
  have hdvd : Nat.card ↥(U ⊓ Subgroup.centralizer ({w} : Set G)) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hU27]
    exact Subgroup.card_dvd_of_le hCU
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hne : U ⊓ Subgroup.centralizer ({w} : Set G) ≠ U := by
    intro h
    obtain ⟨y, hy, hyw⟩ := hwZ
    have : y ∈ U ⊓ Subgroup.centralizer ({w} : Set G) := by rw [h]; exact hy
    exact hyw (Subgroup.mem_centralizer_singleton_iff.mp this.2)
  have hle9 : Nat.card ↥(U ⊓ Subgroup.centralizer ({w} : Set G)) ≤ 9 := by
    interval_cases i
    · rw [hci]; norm_num
    · rw [hci]; norm_num
    · rw [hci]; norm_num
    · exact absurd (Subgroup.eq_of_le_of_card_ge hCU (by rw [hci, hU27]; norm_num)) hne
  have hWeq : W = U ⊓ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hWC (by rw [hW9]; exact hle9)
  rw [hWeq]
  exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxw⟩

theorem eq_one_of_pow_two_of_pow_three {G : Type*} [Group G] {x : G} {m n : ℕ}
    (h2 : x ^ 2 ^ m = 1) (h3 : x ^ 3 ^ n = 1) : x = 1 := by
  have hd : orderOf x ∣ Nat.gcd (2 ^ m) (3 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow m n (by norm_num))] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem card_le_nine_of_pRank {H : Type*} [Group H] [Finite H] (h : CFSG.pRank 3 H = 2)
    (A : Subgroup H) [CFSG.IsElementaryAbelian 3 A] : Nat.card A ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr⟩ := (CFSG.IsElementaryAbelian.isPGroup 3 A).exists_card_eq
  have hmem : r ∈ {r : ℕ | ∃ A : Subgroup H, CFSG.IsElementaryAbelian 3 A ∧ Nat.card A = 3 ^ r} :=
    ⟨A, inferInstance, hr⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup H, CFSG.IsElementaryAbelian 3 A ∧ Nat.card A = 3 ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro s ⟨B, -, hB⟩
    have h1 := Subgroup.card_le_card_group B
    rw [hB] at h1
    exact (Nat.lt_pow_self (by norm_num)).le.trans h1
  have hle : r ≤ 2 := by
    have := le_csSup hbdd hmem
    rwa [show sSup {r : ℕ | ∃ A : Subgroup H, CFSG.IsElementaryAbelian 3 A ∧
      Nat.card A = 3 ^ r} = CFSG.pRank 3 H from rfl, h] at this
  rw [hr]
  calc 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 9 := by norm_num

variable {Y : Type} [Group Y]

theorem card_inf_le_nine [Finite Y] {E L : Subgroup Y} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hL : CFSG.pRank 3 L = 2) : Nat.card ↥(E ⊓ L) ≤ 9 := by
  have := hE.1
  have : CFSG.IsElementaryAbelian 3 (E.subgroupOf L) :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        apply Subtype.ext; apply Subtype.ext
        change ((a : L) : Y) * ((b : L) : Y) = ((b : L) : Y) * ((a : L) : Y)
        exact congrArg Subtype.val (mul_comm' (⟨_, a.2⟩ : E) ⟨_, b.2⟩)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (Subtype.ext (hE.2 _ a.2)) }
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L.subtype_injective]
  exact card_le_nine_of_pRank hL _

theorem nine_le_card_inf_sup [Finite Y] {L U E : Subgroup Y} [L.Normal]
    (hEL : Nat.card ↥(E ⊓ L) ≤ 9) (hE27 : Nat.card E = 27) (hUL : Nat.card ↥(U ⊓ L) = 3)
    (hdec : ∀ e ∈ E, ∃ l ∈ L, ∃ u ∈ U, e = l * u) : 9 ≤ Nat.card ↥(U ⊓ (E ⊔ L)) := by
  have hker : (QuotientGroup.mk' L).ker = L := QuotientGroup.ker_mk' L
  have h1 := card_eq_card_map_mul_card_inf_ker (QuotientGroup.mk' L) E
  rw [hker, hE27] at h1
  have hE3 : 3 ≤ Nat.card (E.map (QuotientGroup.mk' L)) := by nlinarith
  have hmap : E.map (QuotientGroup.mk' L) ≤ (U ⊓ (E ⊔ L)).map (QuotientGroup.mk' L) := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨l, hl, u, hu, rfl⟩ := hdec e he
    refine ⟨u, ⟨hu, ?_⟩, ?_⟩
    · have : u = l⁻¹ * (l * u) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (L.inv_mem hl)) (Subgroup.mem_sup_left he)
    · have hl1 : QuotientGroup.mk' L l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
      rw [map_mul, hl1, one_mul]
  have h2 := card_eq_card_map_mul_card_inf_ker (QuotientGroup.mk' L) (U ⊓ (E ⊔ L))
  rw [hker, inf_assoc, inf_eq_right.mpr (le_sup_right : L ≤ E ⊔ L), hUL] at h2
  have h3 := Subgroup.card_le_of_le hmap
  rw [h2]
  omega

end CFSG.RankThree.PartTwo.KFacts.KS18
