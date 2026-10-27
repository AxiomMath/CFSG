module

public import CFSG.RankThree.PartTwo.Sec11.Item1121ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121ProofQuot
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.Sec11.Item1123Proof
import CFSG.RankThree.PartTwo.Sec11.Item1125Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1121Proof

section Group

variable {G : Type*} [Group G]

theorem centralizer_eq_of_zpowers_eq {y z : G} (h : Subgroup.zpowers y = Subgroup.zpowers z) :
    Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
    GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, h]

theorem conj_inv_pow (h c : G) (n : ℕ) : (h⁻¹ * c * h) ^ n = h⁻¹ * c ^ n * h := by
  have e := conj_pow (a := h⁻¹) (b := c) (i := n)
  rw [inv_inv] at e
  exact e

theorem conj_mem_zpowers_conj {c y : G} (hc : c ∈ Subgroup.zpowers y) (h : G) :
    h⁻¹ * c * h ∈ Subgroup.zpowers (h⁻¹ * y * h) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  have e := conj_zpow (a := h⁻¹) (b := y) (i := m)
  rw [inv_inv] at e
  exact e

theorem conj_pow_mul_pow {t u a y z : G} (hty : t * y = y * t) (htz : t * z = z * t)
    (huz : u * z = z * u) (hta : t * a * t⁻¹ = y * a) (hua : u * a * u⁻¹ = z * a) (m n : ℤ) :
    (t ^ m * u ^ n) * a * (t ^ m * u ^ n)⁻¹ = z ^ n * (y ^ m * a) := by
  have h1 := Item1119Proof.zpow_conj_eq_zpow_mul huz hua n
  have h2 := Item1119Proof.zpow_conj_eq_zpow_mul hty hta m
  have h3 : t ^ m * z ^ n * (t ^ m)⁻¹ = z ^ n := by
    rw [← conj_zpow, (Commute.zpow_left (htz : Commute t z) m).eq, mul_inv_cancel_right]
  calc (t ^ m * u ^ n) * a * (t ^ m * u ^ n)⁻¹ = t ^ m * (u ^ n * a * (u ^ n)⁻¹) * (t ^ m)⁻¹ := by
        group
    _ = (t ^ m * z ^ n * (t ^ m)⁻¹) * (t ^ m * a * (t ^ m)⁻¹) := by rw [h1]; group
    _ = z ^ n * (y ^ m * a) := by rw [h3, h2]

end Group

theorem orderOf_eq_three_of_mem {G : Type*} [Group G] {y z : G} (hz : orderOf z = 3)
    (hyz : y ∈ Subgroup.zpowers z) (hy1 : y ≠ 1) : orderOf y = 3 := by
  have h := orderOf_dvd_of_mem_zpowers hyz
  rw [hz] at h
  rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hy1
  · exact h3

section Finite

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_of_mem_of_orderOf {y z : G} (hyz : y ∈ Subgroup.zpowers z)
    (hy : orderOf y = 3) (hz : orderOf z = 3) : Subgroup.zpowers y = Subgroup.zpowers z :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyz)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hy, hz])

theorem mem_zpowers_of_mem_of_ne_one {y z : G} (hz : orderOf z = 3)
    (hyz : y ∈ Subgroup.zpowers z) (hy1 : y ≠ 1) : z ∈ Subgroup.zpowers y := by
  rw [zpowers_eq_of_mem_of_orderOf hyz (orderOf_eq_three_of_mem hz hyz hy1) hz]
  exact Subgroup.mem_zpowers z

theorem nine_dvd_orderOf_of_not_mem {r u w : G} (hr : ∃ k : ℕ, r ^ 3 ^ k = 1)
    (hu : u ∈ Subgroup.zpowers r) (hw : w ∈ Subgroup.zpowers r) (hu3 : orderOf u = 3)
    (hwu : w ∉ Subgroup.zpowers u) : 9 ∣ orderOf w := by
  obtain ⟨j, hj⟩ := Item1115Proof.exists_orderOf_eq_three_pow
    (Item1115Proof.exists_pow_three_pow_of_mem_zpowers hr hw)
  have hj2 : 2 ≤ j := by
    by_contra hj2
    apply hwu
    refine Item1115Proof.mem_zpowers_of_orderOf_dvd hw hu ?_
    rw [hj, hu3]
    interval_cases j <;> norm_num
  rw [hj, show (9 : ℕ) = 3 ^ 2 by norm_num]
  exact pow_dvd_pow 3 hj2

end Finite

theorem isList1118_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : (∃ q : TauCeti.PrimePower, Sec4.IsoGTwo X' q) ∨ (∃ n : ℕ, Sec8.IsoTrialityD4 X' n) ∨
      Sec13.IsLThreePi X') :
    (∃ q : TauCeti.PrimePower, Sec4.IsoGTwo X q) ∨ (∃ n : ℕ, Sec8.IsoTrialityD4 X n) ∨
      Sec13.IsLThreePi X := by
  rcases h with ⟨q, hq, ⟨f⟩⟩ | ⟨n, q, hq, hp, he, ⟨f⟩⟩ | ⟨p, k, hp, hk, hL⟩
  · exact Or.inl ⟨q, hq, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, q, hq, hp, he, ⟨e.trans f⟩⟩)
  · refine Or.inr (Or.inr ⟨p, k, hp, hk, ?_⟩)
    rcases hL with ⟨h1, ⟨f⟩⟩ | ⟨h1, ⟨f⟩⟩
    · exact Or.inl ⟨h1, ⟨e.trans f⟩⟩
    · exact Or.inr ⟨h1, ⟨e.trans f⟩⟩

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem commutator_r_a_mem (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : Sec11Data G A c L a R Y d x s r g) : r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := by
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hrR := (Item1116Proof.mem_R h).1
  have hrN : r ∈ Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G) :=
    h.closure_rs_le_normalizer h45 h113 (Subgroup.subset_closure (by simp))
  have hca : c * a = a * c :=
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  have hra : r * a * r⁻¹ ∈ Subgroup.closure ({c, a} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hrN a).mp (Subgroup.subset_closure (by simp))
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hca hra
  have hrc : r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le hrR
  have haNc : a ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [← hca, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  refine Item1123Proof.conj_mul_inv_mem_of_pow_three_mem hrc haNc
    (by rw [hexp a h.a_mem]; exact Subgroup.one_mem _)
    (Item1116Proof.exists_pow_eq_one_of_mem h hrR) (k := j) ?_
  have hcom : Commute (c ^ i) (a ^ j) := (Commute.zpow_zpow hca i j)
  rw [hij, hcom.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  exact Subgroup.zpow_mem_zpowers c i

theorem exists_conj_eq_mul (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a ≠ a * r) {w : G}
    (hw : w ∈ Subgroup.closure ({c, d} : Set G)) : ∃ p ∈ R, p * a * p⁻¹ = a * w := by
  obtain ⟨hrR, hxR, -⟩ := Item1116Proof.mem_R h
  have hRP := Item1119Proof.R_le_P R g
  obtain ⟨hcd, -, -⟩ := Item1119Proof.c_d_facts h
  obtain ⟨hc3', hd3'⟩ := Item1115Proof.orderOf_c_d h
  have hdA := (Item1115Proof.d_mem h).1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr h.mem_A
  have hdA' : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  set y₀ := r * a * r⁻¹ * a⁻¹ with hy₀
  set z₀ := x * a * x⁻¹ * a⁻¹ with hz₀
  have hy₀c : y₀ ∈ Subgroup.zpowers c := commutator_r_a_mem h45 h113 h
  obtain ⟨hz₀d, hz₀1⟩ := Item1119Proof.commutator_x_a_facts h45 h
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    apply hra
    calc r * a = y₀ * (a * r) := by rw [hy₀]; group
      _ = a * r := by rw [h1, one_mul]
  have hcy : c ∈ Subgroup.zpowers y₀ := mem_zpowers_of_mem_of_ne_one hc3' hy₀c hy₀1
  have hdz : d ∈ Subgroup.zpowers z₀ := mem_zpowers_of_mem_of_ne_one hd3' hz₀d hz₀1
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hw
  obtain ⟨α, hα⟩ := Subgroup.mem_zpowers_iff.mp hcy
  obtain ⟨β, hβ⟩ := Subgroup.mem_zpowers_iff.mp hdz
  have hrc : r * c = c * r :=
    Subgroup.mem_centralizer_singleton_iff.mp (Item1119Proof.R_le_centralizer_c h hrR)
  have hry : r * y₀ = y₀ * r := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy₀c
    rw [← hm]
    exact (Commute.zpow_right (hrc : Commute r c) m).eq
  have hcomm_d : ∀ q ∈ sec11P R g, q * z₀ = z₀ * q := fun q hq =>
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hz₀d hq
  have hrz := hcomm_d r (hRP hrR)
  have hxz := hcomm_d x (hRP hxR)
  have hra' : r * a * r⁻¹ = y₀ * a := by rw [hy₀]; group
  have hxa : x * a * x⁻¹ = z₀ * a := by rw [hz₀]; group
  refine ⟨r ^ (α * i) * x ^ (β * j), R.mul_mem (R.zpow_mem hrR _) (R.zpow_mem hxR _), ?_⟩
  rw [conj_pow_mul_pow hry hrz hxz hra' hxa]
  have hyA : y₀ ∈ A := hcA hy₀c
  have hzA : z₀ ∈ A := hdA' hz₀d
  have e1 : y₀ ^ (α * i) = c ^ i := by rw [zpow_mul, hα]
  have e2 : z₀ ^ (β * j) = d ^ j := by rw [zpow_mul, hβ]
  rw [e1, e2]
  have h1 := hcomm _ (A.zpow_mem h.mem_A i) _ h.a_mem
  have h2 := hcomm _ (A.zpow_mem hdA j) _ h.a_mem
  have h3 := hcomm _ (A.zpow_mem hdA j) _ (A.zpow_mem h.mem_A i)
  calc d ^ j * (c ^ i * a) = d ^ j * (a * c ^ i) := by rw [h1]
    _ = (d ^ j * a) * c ^ i := by group
    _ = (a * d ^ j) * c ^ i := by rw [h2]
    _ = a * (d ^ j * c ^ i) := by group
    _ = a * (c ^ i * d ^ j) := by rw [h3]

theorem c_mem_zpowers_r (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a ≠ a * r) :
    c ∈ Subgroup.zpowers r := by
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hRP := Item1119Proof.R_le_P R g
  have hr3 := Item1116Proof.exists_pow_eq_one_of_mem h hrR
  obtain ⟨hcd, hc3, -⟩ := Item1119Proof.c_d_facts h
  obtain ⟨hc3', -⟩ := Item1115Proof.orderOf_c_d h
  have hdA := (Item1115Proof.d_mem h).1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hr1 : r ≠ 1 := fun h1 => h.r_not_mem_V (h1 ▸ Subgroup.one_mem _)
  obtain ⟨m, hm⟩ := Item1119Proof.exists_orderOf_eq_three_pow' hr3
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m'
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hm, pow_zero])) hr1
    · exact ⟨m', rfl⟩
  set u := r ^ 3 ^ m' with hu
  have hu3 : orderOf u = 3 := by
    rw [hu, orderOf_pow_of_dvd (by positivity) (by rw [hm]; exact pow_dvd_pow 3 (by omega)), hm,
      pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have hur : u ∈ Subgroup.zpowers r := Subgroup.pow_mem _ (Subgroup.mem_zpowers r) _
  have hu1 : u ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hu3; norm_num at hu3
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have huA : u ∈ A := Item1119Proof.mem_A_of_mem_R h113 h (R.pow_mem hrR _) hu3'
  set y₀ := r * a * r⁻¹ * a⁻¹ with hy₀
  have hy₀c : y₀ ∈ Subgroup.zpowers c := commutator_r_a_mem h45 h113 h
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    apply hra
    calc r * a = y₀ * (a * r) := by rw [hy₀]; group
      _ = a * r := by rw [h1, one_mul]
  have hy₀3 : orderOf y₀ = 3 := orderOf_eq_three_of_mem hc3' hy₀c hy₀1
  have hrc : r * c = c * r :=
    Subgroup.mem_centralizer_singleton_iff.mp (Item1119Proof.R_le_centralizer_c h hrR)
  have hrd : r * d = d * r := Item1119Proof.commute_d h113 h117 h (hRP hrR)
  have hcdC : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer {r} := by
    rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hrc.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hrd.symm
  have hucd : u ∈ Subgroup.closure ({c, d} : Set G) := by
    obtain ⟨k, w, hw, hkw⟩ := Item1119Proof.exists_zpow_mul_of_mem_A h huA
    have hrw : r * w * r⁻¹ = w := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hcdC hw), mul_inv_cancel_right]
    have hra' : r * a * r⁻¹ = y₀ * a := by rw [hy₀]; group
    have hy₀a : Commute y₀ a := hcomm _ (Subgroup.zpowers_le.mpr h.mem_A hy₀c) _ h.a_mem
    have hru : r * u * r⁻¹ = u := by
      rw [hu, ← pow_succ', pow_succ, mul_inv_cancel_right]
    have h1 : r * u * r⁻¹ = y₀ ^ k * u := by
      rw [hkw]
      calc r * (a ^ k * w) * r⁻¹ = (r * a * r⁻¹) ^ k * (r * w * r⁻¹) := by
            rw [conj_zpow]; group
        _ = y₀ ^ k * (a ^ k * w) := by rw [hra', hrw, hy₀a.mul_zpow]; group
    rw [hru] at h1
    have hk : y₀ ^ k = 1 := by
      calc y₀ ^ k = y₀ ^ k * u * u⁻¹ := by group
        _ = 1 := by rw [← h1, mul_inv_cancel]
    have h3k : ((3 : ℕ) : ℤ) ∣ k := by
      rw [← hy₀3]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hk
    obtain ⟨t, rfl⟩ := h3k
    rw [hkw, zpow_mul, zpow_natCast, h.mem_partTwoF.1.2 a h.a_mem, one_zpow, one_mul]
    exact hw
  have hrs : r ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
    Item1115Proof.mem_normalizer_zpowers_s h45 h hrR
  obtain ⟨i, j, hij⟩ := Item1116Proof.exists_zpow_mul_zpow_of_mem_closure hrs h.a_mem_closure
  have hsI : s ∈ innerPreimage L := by
    have := (h.inf_innerPreimage_eq).ge (Subgroup.subset_closure (by simp) : s ∈ _)
    exact this.2
  have hxI : x ∈ innerPreimage L := by
    have := (h.inf_innerPreimage_eq).ge (Subgroup.subset_closure (by simp) : x ∈ _)
    exact this.2
  have hri : r ^ i ∉ innerPreimage L := by
    intro hri
    apply h.toSec11Std.a_not_mem_innerPreimage
    rw [hij]
    exact Subgroup.mul_mem _ hri (Subgroup.zpow_mem _ hsI j)
  have hr3i : (r ^ i) ^ 3 ∈ Subgroup.zpowers s := by
    have h1 := Item1115Proof.inv_pow_mul_pow_mem (Subgroup.zpow_mem _ hrs i)
      (Subgroup.zpow_mem_zpowers s j) 3
    rw [← hij, h.mem_partTwoF.1.2 a h.a_mem, mul_one] at h1
    simpa using Subgroup.inv_mem _ h1
  have hcI : c ∈ innerPreimage L :=
    Subgroup.zpowers_le.mpr hsI h.c_mem_zpowers_s
  have hdI : d ∈ innerPreimage L :=
    Subgroup.zpowers_le.mpr hxI (Item1115Proof.d_mem_zpowers_x h)
  have hcdI : Subgroup.closure ({c, d} : Set G) ≤ innerPreimage L := by
    rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    exacts [hcI, hdI]
  have hris : r ^ i ∈ Subgroup.zpowers r := Subgroup.zpow_mem_zpowers r i
  have hus : u ∈ Subgroup.zpowers s := by
    rcases Item1115Proof.mem_zpowers_or_mem_zpowers hr3 hur hris with h1 | h1
    · have h9 : 9 ∣ orderOf (r ^ i) := by
        refine nine_dvd_orderOf_of_not_mem hr3 hur hris hu3 ?_
        exact fun h2 => hri (Subgroup.zpowers_le.mpr (hcdI hucd) h2)
      exact Subgroup.zpowers_le.mpr hr3i (Item1125Proof.mem_zpowers_pow_three hu3' h1 h9)
    · exfalso
      exact hri (Subgroup.zpowers_le.mpr (hcdI hucd) h1)
  obtain ⟨α, β, hαβ⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hucd
  have hdβ : d ^ β = 1 := by
    have h1 : d ^ β ∈ Subgroup.zpowers s := by
      have e : d ^ β = (c ^ α)⁻¹ * u := by rw [hαβ]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ h.c_mem_zpowers_s α)) hus
    have h2 : d ^ β ∈ Subgroup.zpowers x :=
      Subgroup.zpow_mem _ (Item1115Proof.d_mem_zpowers_x h) β
    have h3 : d ^ β ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers x := ⟨h1, h2⟩
    rw [Item1115Proof.inf_zpowers_eq_bot h, Subgroup.mem_bot] at h3
    exact h3
  have huc : u ∈ Subgroup.zpowers c := by
    rw [hαβ, hdβ, mul_one]
    exact Subgroup.zpow_mem_zpowers c α
  exact Subgroup.zpowers_le.mpr hur (mem_zpowers_of_mem_of_ne_one hc3' huc hu1)

theorem conj_c_not_mem_zpowers_a (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hK : KFact1121Lists) (hbig : Sec11Big G A c L a R Y d x s r g) (g₀ : G) :
    g₀ * c * g₀⁻¹ ∉ Subgroup.zpowers a := by
  intro hmem
  have h := hbig.toSec11Data
  set x₀ := g₀ * c * g₀⁻¹ with hx₀
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    apply h.ne_one
    calc c = g₀⁻¹ * x₀ * g₀ := by rw [hx₀]; group
      _ = 1 := by rw [h1]; group
  have ha3 : orderOf a = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 a h.a_mem) h.a_ne_one
  have hza : Subgroup.zpowers x₀ = Subgroup.zpowers a :=
    zpowers_eq_of_mem_of_orderOf hmem (orderOf_eq_three_of_mem ha3 hmem hx₀1) ha3
  have hC := centralizer_eq_of_zpowers_eq hza
  have hxA : x₀ ∈ A := Subgroup.zpowers_le.mpr h.a_mem hmem
  have hxcd : x₀ ∉ Subgroup.closure ({c, d} : Set G) := by
    intro hx
    have haz : a ∈ Subgroup.zpowers x₀ := hza ▸ Subgroup.mem_zpowers a
    exact (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).2.1 (Subgroup.zpowers_le.mpr hx haz)
  have hYx : Y ∈ thetaComponentsAt 3 x₀ := by
    have hY := h.mem_thetaComponentsAt_Y
    unfold thetaComponentsAt at hY ⊢
    rw [hC]
    exact hY
  have hKY : sec11K L x₀ ≤ Y := by
    have hK' := h.sec11K_le
    unfold sec11K at hK' ⊢
    rw [hC]
    exact hK'
  have hYL := eq_map_conj_of_sec11K_le h45 h48 h.toSec11Std h.inf_eq h.closure_eq hxA hxcd hYx hKY
  have hlist := hbig.isList
  have hl1016 := h.isList1016
  clear hYx hKY
  subst hYL
  set e₁ : L ≃* L.map (MulAut.conj g₀).toMonoidHom :=
    L.equivMapOfInjective _ (MulAut.conj g₀).injective
  have e₂ : L ⧸ aschbacherSolvableCore 3 L ≃* (L.map (MulAut.conj g₀).toMonoidHom) ⧸
      aschbacherSolvableCore 3 (L.map (MulAut.conj g₀).toMonoidHom) :=
    QuotientGroup.congr _ _ e₁ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₁)
  exact hK _ hl1016 (isList1118_of_mulEquiv e₂ hlist)

theorem conj_c_facts (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113) (h117 : Item117)
    (hK : KFact1121Lists) (hbig : Sec11Big G A c L a R Y d x s r g) (hra : r * a ≠ a * r)
    {h₁ : G} (hA' : h₁ * c * h₁⁻¹ ∈ A) :
    h₁ * c * h₁⁻¹ ∈ Subgroup.closure ({c, d} : Set G) ∧
      (Subgroup.zpowers c).map (MulAut.conj h₁).toMonoidHom ≠ Subgroup.zpowers d := by
  have h := hbig.toSec11Data
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  constructor
  · by_contra hcd
    obtain ⟨k, w, hw, hkw⟩ := Item1119Proof.exists_zpow_mul_of_mem_A h hA'
    have h3k : ¬ (3 : ℤ) ∣ k := by
      rintro ⟨t, rfl⟩
      apply hcd
      rw [hkw, zpow_mul]
      norm_cast
      rw [ha3, one_zpow, one_mul]
      exact hw
    obtain ⟨p, -, hp⟩ := exists_conj_eq_mul h45 h113 h117 h hra (Subgroup.zpow_mem _ hw k)
    have hw3 : w ^ 3 = 1 := h.mem_partTwoF.1.2 w (Item1119Proof.closure_cd_le_A h hw)
    have hkk : w ^ (k * k) = w := by
      have hw3' : w ^ (3 : ℤ) = 1 := by exact_mod_cast hw3
      have hmod : (k * k) % 3 = 1 := by
        have : k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases this with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
      rw [zpow_eq_zpow_emod _ hw3', hmod, zpow_one]
    have haw : Commute a (w ^ k) := by
      have := congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨a, h.a_mem⟩
        ⟨w ^ k, A.zpow_mem (Item1119Proof.closure_cd_le_A h hw) k⟩)
      exact this
    have hpak : p * a ^ k * p⁻¹ = a ^ k * w := by
      rw [← conj_zpow, hp, haw.mul_zpow, ← zpow_mul, hkk]
    apply conj_c_not_mem_zpowers_a h45 h48 hK hbig (p⁻¹ * h₁)
    have e : p⁻¹ * h₁ * c * (p⁻¹ * h₁)⁻¹ = a ^ k := by
      calc p⁻¹ * h₁ * c * (p⁻¹ * h₁)⁻¹ = p⁻¹ * (h₁ * c * h₁⁻¹) * p := by group
        _ = p⁻¹ * (a ^ k * w) * p := by rw [hkw]
        _ = p⁻¹ * (p * a ^ k * p⁻¹) * p := by rw [hpak]
        _ = a ^ k := by group
    rw [e]
    exact Subgroup.zpow_mem_zpowers a k
  · intro heq
    have hle : (Subgroup.zpowers c).map (MulAut.conj h₁).toMonoidHom ≤ A := by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hA'
    obtain ⟨w, hwW, hw⟩ := item114_of h113 G A c L a R Y h.toSec11Std h₁ hle
    rw [hw] at heq
    have hwd := Item1115Proof.W_le_normalizer_d h117 h (Subgroup.inv_mem _ hwW)
    apply h.zpowers_ne
    have h1 : (Subgroup.zpowers d).map (MulAut.conj w⁻¹).toMonoidHom = Subgroup.zpowers d :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hwd
    calc Subgroup.zpowers c = ((Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom).map
          (MulAut.conj w⁻¹).toMonoidHom := by
          rw [map_conj_map_conj, inv_mul_cancel, map_one]
          ext z
          simp
      _ = (Subgroup.zpowers d).map (MulAut.conj w⁻¹).toMonoidHom := by rw [heq]
      _ = Subgroup.zpowers d := h1

theorem fusion_mem_preU (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h1115 : Item1115) (h1120 : Item1120) (hK : KFact1121Lists)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (π : sec11P R g →* W33) (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) (hra : r * a ≠ a * r)
    (k : ℕ) (h₀ : G) (hz : h₀⁻¹ * r ^ k * h₀ ∈ sec11P R g) :
    (r ^ k)⁻¹ * (h₀⁻¹ * r ^ k * h₀) ∈
      preU π (mapP π (Subgroup.closure {s, x, a}) ⊔ Subgroup.zpowers (piG π g)) := by
  have h := hbig.toSec11Data
  obtain ⟨-, habel, -, hsxU, hU3⟩ := preU_facts h45 h1115 h1120 hbig π hπ hrs
  set U := preU π (mapP π (Subgroup.closure ({s, x, a} : Set G)) ⊔
    Subgroup.zpowers (piG π g)) with hU
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  have hRL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2
  have hr3 := Item1116Proof.exists_pow_eq_one_of_mem h hrR
  obtain ⟨-, hc3, -⟩ := Item1119Proof.c_d_facts h
  obtain ⟨hc3', -⟩ := Item1115Proof.orderOf_c_d h
  have hcr := c_mem_zpowers_r h45 h113 h117 h hra
  set r₀ := r ^ k with hr₀
  set z := h₀⁻¹ * r₀ * h₀ with hzdef
  have hr₀R : r₀ ∈ R := R.pow_mem hrR k
  have hr₀r : r₀ ∈ Subgroup.zpowers r := Subgroup.pow_mem _ (Subgroup.mem_zpowers r) k
  have key : h₀⁻¹ * c * h₀ ∈ A → r₀⁻¹ * z ∈ U := by
    intro hcA
    have hcA' : h₀⁻¹ * c * h₀⁻¹⁻¹ ∈ A := by rwa [inv_inv]
    obtain ⟨hcd, hne⟩ := conj_c_facts h45 h48 h113 h117 hK hbig hra hcA'
    set F := (Subgroup.zpowers c).map (MulAut.conj h₀⁻¹).toMonoidHom with hF
    have hFcd : F ≤ Subgroup.closure ({c, d} : Set G) := by
      rw [hF, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hcd
    have hFc : Nat.card F = Nat.card (Subgroup.zpowers c) :=
      Subgroup.card_map_of_injective (MulAut.conj h₀⁻¹).injective
    obtain ⟨p, hpP, hpF⟩ := h.htrans hcdN hNd F hFcd hFc hne
    set n := p⁻¹ * h₀⁻¹ with hn
    have hnc : (Subgroup.zpowers c).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers c := by
      rw [hn, ← map_conj_map_conj, ← hF, hpF, map_conj_map_conj, inv_mul_cancel, map_one]
      ext y
      simp
    have hnH : n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hnc
    have hnL := h.toSec11Std.normalizer_le_normalizer_L h45 hnH
    have hz' : n * r₀ * n⁻¹ = p⁻¹ * z * p := by rw [hn, hzdef]; group
    have hz'P : n * r₀ * n⁻¹ ∈ sec11P R g := by
      rw [hz']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hpP) hz) hpP
    have hz'L : n * r₀ * n⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hnL (hRL hr₀R)) (Subgroup.inv_mem _ hnL)
    have hz'R : n * r₀ * n⁻¹ ∈ R := by
      rw [← h.inf_normalizer_L h45 h113]
      exact ⟨hz'P, hz'L⟩
    have hI : r₀⁻¹ * (n * r₀ * n⁻¹) ∈ innerPreimage L := by
      have h1 := commutator_mem_innerPreimage outAbelian1016 h.isList1016 hnL (hRL hr₀R)
      have h2 := normalizer_le_normalizer_innerPreimage L (Subgroup.inv_mem _ (hRL hr₀R))
      have h3 := (Subgroup.mem_normalizer_iff.mp h2 _).mp h1
      have e : r₀⁻¹ * (n * r₀ * n⁻¹ * r₀⁻¹) * r₀⁻¹⁻¹ = r₀⁻¹ * (n * r₀ * n⁻¹) := by group
      rwa [e] at h3
    have hmem : r₀⁻¹ * (n * r₀ * n⁻¹) ∈ U := by
      refine hsxU ?_
      rw [← h.inf_innerPreimage_eq]
      exact ⟨R.mul_mem (R.inv_mem hr₀R) hz'R, hI⟩
    set z' := n * r₀ * n⁻¹ with hz'def
    have hzz : z = p * z' * p⁻¹ := by rw [hz']; group
    have hcomm := habel z'⁻¹ (Subgroup.inv_mem _ hz'P) p hpP
    have e : r₀⁻¹ * z = (r₀⁻¹ * z') * (z'⁻¹ * p * z'⁻¹⁻¹ * p⁻¹) := by rw [hzz]; group
    rw [e]
    exact U.mul_mem hmem hcomm
  have hconjA : ∀ y : G, y ∈ R → y ^ 3 = 1 → y ∈ A := fun y hy hy3 =>
    Item1119Proof.mem_A_of_mem_R h113 h hy hy3
  have hcc3 : (h₀⁻¹ * c * h₀) ^ 3 = 1 := by
    rw [conj_inv_pow, hc3]
    group
  by_cases hr0c : r₀ ∈ Subgroup.zpowers c
  · have hr0U : r₀ ∈ U := hsxU (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      (Subgroup.zpowers_le.mpr h.c_mem_zpowers_s hr0c))
    by_cases hr01 : r₀ = 1
    · have e : r₀⁻¹ * z = 1 := by rw [hzdef, hr01]; group
      rw [e]
      exact U.one_mem
    have hcr0 : c ∈ Subgroup.zpowers r₀ := mem_zpowers_of_mem_of_ne_one hc3' hr0c hr01
    have hr03 : r₀ ^ 3 = 1 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hr0c
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
    have hz3 : z ^ 3 = 1 := by
      rw [hzdef, conj_inv_pow, hr03]
      group
    by_cases hzR : z ∈ R
    · exact key (hconjA _ (Subgroup.zpowers_le.mpr hzR (conj_mem_zpowers_conj hcr0 h₀)) hcc3)
    · exact U.mul_mem (U.inv_mem hr0U) (hU3 z hz hz3 hzR)
  · have hcr0 : c ∈ Subgroup.zpowers r₀ :=
      (Item1115Proof.mem_zpowers_or_mem_zpowers hr3 hr₀r hcr).resolve_left hr0c
    have h9 : 9 ∣ orderOf r₀ := nine_dvd_orderOf_of_not_mem hr3 hcr hr₀r hc3' hr0c
    have hc3r : c ∈ Subgroup.zpowers (r₀ ^ 3) := Item1125Proof.mem_zpowers_pow_three hc3 hcr0 h9
    have h1 := conj_mem_zpowers_conj hc3r h₀
    have hz3R : z ^ 3 ∈ R := pow_three_mem_R h45 h1115 h1120 hbig π hπ hz
    have e : h₀⁻¹ * r₀ ^ 3 * h₀ = z ^ 3 := by rw [hzdef, conj_inv_pow]
    rw [e] at h1
    exact key (hconjA _ (Subgroup.zpowers_le.mpr hz3R h1) hcc3)

end Data

end Item1121Proof

end CFSG.RankThree.PartTwo.Sec11
