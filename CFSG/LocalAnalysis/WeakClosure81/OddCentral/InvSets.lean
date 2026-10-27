module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.InvertsMinimal
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup CFSG.LocalAnalysis.WeakClosure81.OddCentral

section
variable {Y : Type*} [Group Y] [Finite Y]

@[expose] def InvSet (P : Subgroup Y) (d : Fin 3 → Y) (i : Fin 3) : Set Y :=
  {x | x ∈ P ∧ d i * x * (d i)⁻¹ = x⁻¹ ∧ ∀ j, j ≠ i → d j * x = x * d j}

theorem commute_of_mul_inv_mem {Z₀ : Subgroup Y} (hZc : Z₀ ≤ center Y) {a b : Y}
    (h : a⁻¹ * b ∈ Z₀) : a * b = b * a := by
  have hz : a * (a⁻¹ * b) = (a⁻¹ * b) * a := mem_center_iff.mp (hZc h) a
  calc a * b = a * (a * (a⁻¹ * b)) := by group
    _ = a * ((a⁻¹ * b) * a) := by rw [hz]
    _ = b * a := by group

theorem avg_step {Z₀ : Subgroup Y} (hZc : Z₀ ≤ center Y) {e u q : Y} (he : e * e = 1)
    (hcong : q⁻¹ * (e * q * e⁻¹) ∈ Z₀) (hue : u * e = e * u) (huq : u * q * u⁻¹ = q⁻¹) :
    e * (q * (e * q * e⁻¹)) = (q * (e * q * e⁻¹)) * e ∧
      u * (q * (e * q * e⁻¹)) * u⁻¹ = (q * (e * q * e⁻¹))⁻¹ := by
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hcomm := commute_of_mul_inv_mem hZc hcong
  constructor
  · calc e * (q * (e * q * e⁻¹)) = (e * q * e⁻¹) * (e * (e * q * e⁻¹) * e⁻¹) * e := by group
      _ = (e * q * e⁻¹) * q * e := by
          rw [show e * (e * q * e⁻¹) * e⁻¹ = (e * e) * q * (e * e)⁻¹ by group, he]; group
      _ = (q * (e * q * e⁻¹)) * e := by rw [← hcomm]
  · have hueq : u * (e * q * e⁻¹) * u⁻¹ = (e * q * e⁻¹)⁻¹ := by
      have hue' : u * e⁻¹ = e⁻¹ * u := by
        rw [heinv]; exact hue
      calc u * (e * q * e⁻¹) * u⁻¹ = e * (u * q * u⁻¹) * e⁻¹ := by
            rw [show u * (e * q * e⁻¹) * u⁻¹ = (u * e) * q * (e⁻¹ * u⁻¹) by group, hue,
              show e⁻¹ * u⁻¹ = (u * e)⁻¹ by group, hue]; group
        _ = (e * q * e⁻¹)⁻¹ := by rw [huq]; group
    calc u * (q * (e * q * e⁻¹)) * u⁻¹ = (u * q * u⁻¹) * (u * (e * q * e⁻¹) * u⁻¹) := by group
      _ = q⁻¹ * (e * q * e⁻¹)⁻¹ := by rw [huq, hueq]
      _ = (q * (e * q * e⁻¹))⁻¹ := by rw [← mul_inv_rev, ← hcomm]

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup CFSG.LocalAnalysis.WeakClosure81.OddCentral

section
variable {G : Type*} [Group G] [Finite G]

theorem pm_fix {W : Subgroup G} {n : ℕ} {u e w : G} (heu : e * u = u * e)
    (hew : e * w * e⁻¹ = w) :
    e * (w * (u * w * u⁻¹)) ^ (n + 1) * e⁻¹ = (w * (u * w * u⁻¹)) ^ (n + 1) ∧
      e * (w * (u * w * u⁻¹)⁻¹) ^ (n + 1) * e⁻¹ = (w * (u * w * u⁻¹)⁻¹) ^ (n + 1) := by
  have heuw : e * (u * w * u⁻¹) * e⁻¹ = u * w * u⁻¹ := by
    calc e * (u * w * u⁻¹) * e⁻¹ = (e * u) * w * (e * u)⁻¹ := by group
      _ = (u * e) * w * (u * e)⁻¹ := by rw [heu]
      _ = u * (e * w * e⁻¹) * u⁻¹ := by group
      _ = u * w * u⁻¹ := by rw [hew]
  constructor
  · rw [← conj_pow, show e * (w * (u * w * u⁻¹)) * e⁻¹ = (e * w * e⁻¹) * (e * (u * w * u⁻¹) * e⁻¹)
      by group, hew, heuw]
  · rw [← conj_pow, show e * (w * (u * w * u⁻¹)⁻¹) * e⁻¹ =
      (e * w * e⁻¹) * (e * (u * w * u⁻¹) * e⁻¹)⁻¹ by group, hew, heuw]

theorem pm_decomp2 {W : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hWodd : Odd (Nat.card W)) {u v : G} (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (huW : ∀ w ∈ W, u * w * u⁻¹ ∈ W) (hvW : ∀ w ∈ W, v * w * v⁻¹ ∈ W) {w : G} (hw : w ∈ W) :
    ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, ∃ e ∈ W, w = a * b * c * e ∧
      u * a * u⁻¹ = a ∧ v * a * v⁻¹ = a ∧
      u * b * u⁻¹ = b ∧ v * b * v⁻¹ = b⁻¹ ∧
      u * c * u⁻¹ = c⁻¹ ∧ v * c * v⁻¹ = c ∧
      u * e * u⁻¹ = e⁻¹ ∧ v * e * v⁻¹ = e⁻¹ := by
  obtain ⟨n, hn⟩ := hWodd
  obtain ⟨hp, hm, hpm, hup, hum⟩ := pm_decomp hWab hn hu huW hw
  set wp := (w * (u * w * u⁻¹)) ^ (n + 1)
  set wm := (w * (u * w * u⁻¹)⁻¹) ^ (n + 1)
  obtain ⟨hpp, hpq, hpd, hvpp, hvpq⟩ := pm_decomp hWab hn hv hvW hp
  obtain ⟨hmp, hmq, hmd, hvmp, hvmq⟩ := pm_decomp hWab hn hv hvW hm
  obtain ⟨hupp, hupq⟩ := pm_fix (W := W) (n := n) huv hup
  obtain ⟨humm, humq⟩ := pm_inv (n := n) hWab hvW huv hm hum
  refine ⟨_, hpp, _, hpq, _, hmp, _, hmq, ?_, hupp, hvpp, hupq, hvpq, humm, hvmp, humq, hvmq⟩
  rw [hpm]
  conv_lhs => rw [hpd, hmd]
  group

end
end CFSG.LocalAnalysis.WeakClosure81.OddCentral

namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup CFSG.LocalAnalysis.WeakClosure81.OddCentral

section
variable {Y : Type*} [Group Y] [Finite Y]

theorem pow_cube_succ_eq {G : Type*} [Group G] {g : G} {N : ℕ} (hN : g ^ N = 1) :
    g ^ ((N + 1) ^ 3) = g := by
  rw [show (N + 1) ^ 3 = N * (N ^ 2 + 3 * N + 3) + 1 by ring, pow_succ, pow_mul, hN, one_pow,
    one_mul]

theorem fin3_other (i j : Fin 3) (hji : j ≠ i) : j = i + 1 ∨ j = i + 2 := by
  revert i j; decide

theorem fin3_add1_ne (i : Fin 3) : i + 1 ≠ i := by revert i; decide

theorem fin3_add2_ne (i : Fin 3) : i + 2 ≠ i := by revert i; decide

theorem exists_inv_lift {P Z₀ : Subgroup Y} [hZn : Z₀.Normal] (hZc : Z₀ ≤ center Y)
    {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (hdP : ∀ i, ∀ x ∈ P, d i * x * (d i)⁻¹ ∈ P) (hPodd : Odd (Nat.card P)) {i : Fin 3} {x : Y}
    (hx : x ∈ P) (hxi : (d i * x * (d i)⁻¹) * x ∈ Z₀) (hxj : ∀ j, j ≠ i → (d j * x * (d j)⁻¹) * x⁻¹ ∈ Z₀) :
    ∃ a ∈ InvSet P d i, x⁻¹ * a ∈ Z₀ := by
  let π : Y →* Y ⧸ Z₀ := QuotientGroup.mk' Z₀
  have hπ1 : ∀ y, π y = 1 ↔ y ∈ Z₀ := fun y => QuotientGroup.eq_one_iff y
  have hπeq : ∀ a b, π a = π b → a⁻¹ * b ∈ Z₀ := fun a b h => QuotientGroup.eq.mp h
  have hπc : ∀ e y, e * y * e⁻¹ * y⁻¹ ∈ Z₀ → π e * π y = π y * π e := by
    intro e y h
    have := (hπ1 _).mpr h
    simp only [map_mul, map_inv] at this
    calc π e * π y = (π e * π y * (π e)⁻¹ * (π y)⁻¹) * π y * π e := by group
      _ = π y * π e := by rw [this, one_mul]
  set j := i + 1 with hj
  set k := i + 2 with hk
  have hji : j ≠ i := fin3_add1_ne i
  have hki : k ≠ i := fin3_add2_ne i
  have hdi : (d i)⁻¹ = d i := inv_eq_of_mul_eq_one_right (hd i)
  set q₀ := x * (d i * x * (d i)⁻¹)⁻¹ with hq₀
  have hq₀P : q₀ ∈ P := P.mul_mem hx (P.inv_mem (hdP i x hx))
  have hdd : ∀ y, d i * (d i * y * (d i)⁻¹) * (d i)⁻¹ = y := fun y => by
    rw [show d i * (d i * y * (d i)⁻¹) * (d i)⁻¹ = (d i * d i) * y * (d i * d i)⁻¹ by group, hd i]
    group
  have hq₀i : d i * q₀ * (d i)⁻¹ = q₀⁻¹ := by
    calc d i * q₀ * (d i)⁻¹
        = (d i * x * (d i)⁻¹) * (d i * (d i * x * (d i)⁻¹) * (d i)⁻¹)⁻¹ := by rw [hq₀]; group
      _ = (d i * x * (d i)⁻¹) * x⁻¹ := by rw [hdd]
      _ = q₀⁻¹ := by rw [hq₀]; group
  have hπxi : π (d i) * π x * (π (d i))⁻¹ = (π x)⁻¹ := by
    have := (hπ1 _).mpr hxi
    simp only [map_mul, map_inv] at this
    exact eq_inv_of_mul_eq_one_left this
  have hπq₀ : π q₀ = π x * π x := by
    rw [hq₀, map_mul, map_inv, map_mul, map_mul, map_inv, hπxi, inv_inv]
  have hcomm_l : ∀ l, l ≠ i → Commute (π (d l)) (π x) := fun l hl => hπc _ _ (hxj l hl)
  have hcong : ∀ l, l ≠ i → ∀ q, π q = π x ^ (2 ^ 3) ∨ π q = π x * π x ∨
      π q = (π x * π x) * (π x * π x) → q⁻¹ * (d l * q * (d l)⁻¹) ∈ Z₀ := by
    intro l hl q hq
    apply hπeq
    have hc : π (d l) * π q = π q * π (d l) := by
      rcases hq with h | h | h <;> rw [h]
      · exact ((Commute.pow_right (hcomm_l l hl) _)).eq
      · exact ((hcomm_l l hl).mul_right (hcomm_l l hl)).eq
      · exact (((hcomm_l l hl).mul_right (hcomm_l l hl)).mul_right
          ((hcomm_l l hl).mul_right (hcomm_l l hl))).eq
    simp only [map_mul, map_inv]
    rw [hc]; group
  obtain ⟨hq₁j, hq₁i⟩ := avg_step hZc (hd j) (hcong j hji q₀ (Or.inr (Or.inl hπq₀)))
    (hdc i j) hq₀i
  set q₁ := q₀ * (d j * q₀ * (d j)⁻¹) with hq₁
  have hq₁P : q₁ ∈ P := P.mul_mem hq₀P (hdP j _ hq₀P)
  have hπq₁ : π q₁ = (π x * π x) * (π x * π x) := by
    have e1 : π (d j * q₀ * (d j)⁻¹) = π q₀ := by
      rw [map_mul, map_mul, map_inv, hπq₀, ((hcomm_l j hji).mul_right (hcomm_l j hji)).eq]; group
    rw [hq₁, map_mul π q₀ (d j * q₀ * (d j)⁻¹), e1, hπq₀]
  obtain ⟨hq₂k, hq₂i⟩ := avg_step hZc (hd k) (hcong k hki q₁ (Or.inr (Or.inr hπq₁)))
    (hdc i k) hq₁i
  set q₂ := q₁ * (d k * q₁ * (d k)⁻¹) with hq₂
  have hq₂P : q₂ ∈ P := P.mul_mem hq₁P (hdP k _ hq₁P)
  have hπq₂ : π q₂ = π x ^ (2 ^ 3) := by
    have e1 : π (d k * q₁ * (d k)⁻¹) = π q₁ := by
      rw [map_mul, map_mul, map_inv, hπq₁, (((hcomm_l k hki).mul_right (hcomm_l k hki)).mul_right
        ((hcomm_l k hki).mul_right (hcomm_l k hki))).eq]; group
    rw [hq₂, map_mul π q₁ (d k * q₁ * (d k)⁻¹), e1, hπq₁]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    norm_num [pow_succ, mul_assoc]
  have hq₂j : d j * q₂ = q₂ * d j := by
    have hjk' : Commute (d j) (d k) := hdc j k
    have h1 : Commute (d j) q₁ := hq₁j
    have h2 : Commute (d j) (d k * q₁ * (d k)⁻¹) :=
      (hjk'.mul_right h1).mul_right hjk'.inv_right
    exact (h1.mul_right h2).eq
  obtain ⟨n, hn⟩ := hPodd
  set h := n + 1
  have hxN : x ^ Nat.card P = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hx)
  refine ⟨q₂ ^ (h ^ 3), ⟨pow_mem hq₂P _, ?_, ?_⟩, ?_⟩
  · rw [← conj_pow, hq₂i, inv_pow]
  · intro l hl
    rcases fin3_other i l hl with rfl | rfl
    · exact (Commute.pow_right (show Commute (d (i + 1)) q₂ from hq₂j) _).eq
    · exact (Commute.pow_right (show Commute (d (i + 2)) q₂ from hq₂k) _).eq
  · apply hπeq
    rw [map_pow, hπq₂, ← pow_mul, show 2 ^ 3 * h ^ 3 = (Nat.card P + 1) ^ 3 by rw [hn]; ring,
      ← map_pow, pow_cube_succ_eq hxN]

theorem eq_one_of_sq_of_odd {G : Type*} [Group G] {W : Subgroup G} (hW : Odd (Nat.card W))
    {e : G} (he : e ∈ W) (hee : e * e = 1) : e = 1 := by
  have h1 : orderOf e ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [sq, hee])
  have h2 : Odd (orderOf e) := Odd.of_dvd_nat hW (Subgroup.orderOf_dvd_natCard W he)
  have h3 : orderOf e = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2; exact absurd h2 (by decide)
  exact orderOf_eq_one_iff.mp h3

theorem exists_inv_decomp {P Z₀ : Subgroup Y} [hPn : P.Normal] [hZn : Z₀.Normal]
    (hZc : Z₀ ≤ center Y) (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀)
    (hPodd : Odd (Nat.card P)) {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1)
    (hdc : ∀ i j, d i * d j = d j * d i)
    (hc : ∀ x ∈ P, (d 0 * d 1 * d 2) * x * (d 0 * d 1 * d 2)⁻¹ * x ∈ Z₀)
    (hLA : ∀ i j, i ≠ j → ∀ x ∈ P, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Z₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Z₀) {x : Y} (hx : x ∈ P) :
    ∃ a : Fin 3 → Y, (∀ l, a l ∈ InvSet P d l) ∧ x⁻¹ * (a 0 * a 1 * a 2) ∈ Z₀ := by
  let π : Y →* Y ⧸ Z₀ := QuotientGroup.mk' Z₀
  have hπ1 : ∀ y, π y = 1 ↔ y ∈ Z₀ := fun y => QuotientGroup.eq_one_iff y
  have hdP : ∀ i, ∀ y ∈ P, d i * y * (d i)⁻¹ ∈ P := fun i y hy => hPn.conj_mem y hy (d i)
  set W : Subgroup (Y ⧸ Z₀) := P.map π
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have := (hπ1 _).mpr (hP' y hy z hz)
    simp only [map_mul, map_inv] at this
    calc π y * π z = (π y * π z * (π y)⁻¹ * (π z)⁻¹) * π z * π y := by group
      _ = π z * π y := by rw [this, one_mul]
  have hWodd : Odd (Nat.card W) := Odd.of_dvd_nat hPodd (Subgroup.card_map_dvd P π)
  have hπd : ∀ i, π (d i) * π (d i) = 1 := fun i => by rw [← map_mul, hd i, map_one]
  have hWd : ∀ i, ∀ w ∈ W, π (d i) * w * (π (d i))⁻¹ ∈ W := by
    rintro i _ ⟨y, hy, rfl⟩
    exact ⟨_, hdP i y hy, by simp only [π, map_mul, map_inv]⟩
  have hcW : ∀ w ∈ W, π (d 0 * d 1 * d 2) * w * (π (d 0 * d 1 * d 2))⁻¹ = w⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    have := (hπ1 _).mpr (hc y hy)
    simp only [map_mul, map_inv] at this ⊢
    exact eq_inv_of_mul_eq_one_left this
  have hLAW : ∀ i j, i ≠ j → ∀ w ∈ W, π (d i * d j) * w * (π (d i * d j))⁻¹ = w →
      π (d i) * w * (π (d i))⁻¹ = w := by
    rintro i j hij _ ⟨y, hy, rfl⟩ h
    have h' : (d i * d j) * y * (d i * d j)⁻¹ * y⁻¹ ∈ Z₀ := by
      rw [← hπ1]; simp only [map_mul, map_inv] at h ⊢; rw [h, mul_inv_cancel]
    have := (hπ1 _).mpr (hLA i j hij y hy h')
    simp only [map_mul, map_inv] at this ⊢
    exact mul_inv_eq_one.mp this
  obtain ⟨a, haW, b, hbW, c, hcW', e, heW, hdec, hua, hva, hub, hvb, huc, hvc, hue, hve⟩ :=
    pm_decomp2 hWab hWodd (hπd 0) (hπd 1) (by rw [← map_mul, hdc 0 1, map_mul]) (hWd 0) (hWd 1)
      (show π x ∈ W from ⟨x, hx, rfl⟩)
  have he1 : e = 1 := by
    have h01 : π (d 0 * d 1) * e * (π (d 0 * d 1))⁻¹ = e := by
      rw [map_mul, show π (d 0) * π (d 1) * e * (π (d 0) * π (d 1))⁻¹ =
        π (d 0) * (π (d 1) * e * (π (d 1))⁻¹) * (π (d 0))⁻¹ by group, hve,
        show π (d 0) * e⁻¹ * (π (d 0))⁻¹ = (π (d 0) * e * (π (d 0))⁻¹)⁻¹ by group, hue, inv_inv]
    have := hLAW 0 1 (by decide) e heW h01
    rw [hue] at this
    exact eq_one_of_sq_of_odd hWodd heW (by
      calc e * e = e * e⁻¹ := by rw [this]
        _ = 1 := mul_inv_cancel e)
  have hd2 : π (d 2) = π (d 0) * π (d 1) * π (d 0 * d 1 * d 2) := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [show d 0 * d 1 * (d 0 * d 1 * d 2) = d 0 * (d 1 * d 0) * d 1 * d 2 by group, ← hdc 0 1,
      show d 0 * (d 0 * d 1) * d 1 * d 2 = (d 0 * d 0) * (d 1 * d 1) * d 2 by group, hd 0, hd 1]
    group
  have hd2act : ∀ w ∈ W, π (d 2) * w * (π (d 2))⁻¹ =
      (π (d 0) * (π (d 1) * w * (π (d 1))⁻¹) * (π (d 0))⁻¹)⁻¹ := by
    intro w hw
    rw [hd2, show π (d 0) * π (d 1) * π (d 0 * d 1 * d 2) * w *
      (π (d 0) * π (d 1) * π (d 0 * d 1 * d 2))⁻¹ = π (d 0) * (π (d 1) *
        (π (d 0 * d 1 * d 2) * w * (π (d 0 * d 1 * d 2))⁻¹) * (π (d 1))⁻¹) * (π (d 0))⁻¹ by group,
      hcW w hw]
    group
  have hlift : ∀ i, ∀ w ∈ W, π (d i) * w * (π (d i))⁻¹ = w⁻¹ →
      (∀ j, j ≠ i → π (d j) * w * (π (d j))⁻¹ = w) → ∃ a' ∈ InvSet P d i, π a' = w := by
    rintro i _ ⟨y, hy, rfl⟩ hi hj
    obtain ⟨a', ha', hya'⟩ := exists_inv_lift hZc hd hdc hdP hPodd hy
      (by rw [← hπ1]; simp only [map_mul, map_inv]; rw [hi, inv_mul_cancel])
      (fun j hji => by rw [← hπ1]; simp only [map_mul, map_inv]; rw [hj j hji, mul_inv_cancel])
    exact ⟨a', ha', (QuotientGroup.eq.mpr hya').symm⟩
  obtain ⟨a₂, ha₂, hπa₂⟩ := hlift 2 a haW (by rw [hd2act a haW, hva, hua]) (by
    intro j hj; fin_cases j
    · exact hua
    · exact hva
    · exact absurd rfl hj)
  obtain ⟨a₁, ha₁, hπa₁⟩ := hlift 1 b hbW hvb (by
    intro j hj; fin_cases j
    · exact hub
    · exact absurd rfl hj
    · show π (d 2) * b * (π (d 2))⁻¹ = b
      rw [hd2act b hbW, hvb, show π (d 0) * b⁻¹ * (π (d 0))⁻¹ = (π (d 0) * b * (π (d 0))⁻¹)⁻¹
        by group, hub, inv_inv])
  obtain ⟨a₀, ha₀, hπa₀⟩ := hlift 0 c hcW' huc (by
    intro j hj; fin_cases j
    · exact absurd rfl hj
    · exact hvc
    · show π (d 2) * c * (π (d 2))⁻¹ = c
      rw [hd2act c hcW', hvc, huc, inv_inv])
  refine ⟨![a₀, a₁, a₂], fun l => by fin_cases l <;> assumption, ?_⟩
  apply QuotientGroup.eq.mp
  show π x = π (a₀ * a₁ * a₂)
  rw [map_mul, map_mul, hπa₀, hπa₁, hπa₂, hdec, he1, mul_one, hWab a haW b hbW,
    mul_assoc, hWab a haW c hcW', ← mul_assoc, hWab b hbW c hcW']

theorem conj_eq_of_comm {a b : Y} (h : a * b = b * a) : a * b * a⁻¹ = b := by
  rw [h]; group

theorem c_inv_of_mem_invSet {P : Subgroup Y} {d : Fin 3 → Y} {l : Fin 3} {a : Y}
    (ha : a ∈ InvSet P d l) : (d 0 * d 1 * d 2) * a * (d 0 * d 1 * d 2)⁻¹ = a⁻¹ := by
  obtain ⟨-, hl, hj⟩ := ha
  have hconj : ∀ j, j ≠ l → d j * a * (d j)⁻¹ = a := fun j hj' => conj_eq_of_comm (hj j hj')
  have e : (d 0 * d 1 * d 2) * a * (d 0 * d 1 * d 2)⁻¹ =
      d 0 * (d 1 * (d 2 * a * (d 2)⁻¹) * (d 1)⁻¹) * (d 0)⁻¹ := by group
  rw [e]
  fin_cases l
  · rw [hconj 2 (by decide), hconj 1 (by decide)]; exact hl
  · change d 1 * a * (d 1)⁻¹ = a⁻¹ at hl
    rw [hconj 2 (by decide), hl, show d 0 * a⁻¹ * (d 0)⁻¹ = (d 0 * a * (d 0)⁻¹)⁻¹ by group,
      hconj 0 (by decide)]
  · change d 2 * a * (d 2)⁻¹ = a⁻¹ at hl
    rw [hl, show d 1 * a⁻¹ * (d 1)⁻¹ = (d 1 * a * (d 1)⁻¹)⁻¹ by group, hconj 1 (by decide),
      show d 0 * a⁻¹ * (d 0)⁻¹ = (d 0 * a * (d 0)⁻¹)⁻¹ by group, hconj 0 (by decide)]

theorem commute_of_invSet {P Z₀ : Subgroup Y} (hZc : Z₀ ≤ center Y) (hZP : Z₀ ≤ P)
    (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀) (hPodd : Odd (Nat.card P))
    {d : Fin 3 → Y} {i j : Fin 3} (hij : i ≠ j) {a b : Y} (ha : a ∈ InvSet P d i)
    (hb : b ∈ InvSet P d j) : a * b = b * a := by
  obtain ⟨haP, hai, -⟩ := ha
  obtain ⟨hbP, -, hbj⟩ := hb
  set ζ := a * b * a⁻¹ * b⁻¹ with hζ
  have hζZ : ζ ∈ Z₀ := hP' a haP b hbP
  have hζc := mem_center_iff.mp (hZc hζZ)
  have hbi : d i * b * (d i)⁻¹ = b := conj_eq_of_comm (hbj i hij)
  have h1 : d i * ζ * (d i)⁻¹ = ζ := by rw [hζc (d i)]; group
  have h2 : d i * ζ * (d i)⁻¹ = ζ⁻¹ := by
    rw [hζ, show d i * (a * b * a⁻¹ * b⁻¹) * (d i)⁻¹ = (d i * a * (d i)⁻¹) * (d i * b * (d i)⁻¹) *
      (d i * a * (d i)⁻¹)⁻¹ * (d i * b * (d i)⁻¹)⁻¹ by group, hai, hbi, inv_inv]
    calc a⁻¹ * b * a * b⁻¹ = a⁻¹ * (b * a * b⁻¹ * a⁻¹) * a := by group
      _ = a⁻¹ * ζ⁻¹ * a := by rw [hζ]; group
      _ = ζ⁻¹ := by rw [show a⁻¹ * ζ⁻¹ = ζ⁻¹ * a⁻¹ from
          (mem_center_iff.mp (hZc (Z₀.inv_mem hζZ)) a⁻¹)]; group
  have hζ1 : ζ = 1 := eq_one_of_sq_of_odd hPodd (hZP hζZ) (by
    calc ζ * ζ = ζ * ζ⁻¹ := by rw [← h2, h1]
      _ = 1 := mul_inv_cancel ζ)
  calc a * b = ζ * b * a := by rw [hζ]; group
    _ = b * a := by rw [hζ1, one_mul]

theorem abelian_of_invSet_comm {P Z₀ : Subgroup Y} [hPn : P.Normal] [hZn : Z₀.Normal]
    (hZc : Z₀ ≤ center Y) (hZP : Z₀ ≤ P) (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀)
    (hPodd : Odd (Nat.card P)) {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1)
    (hdc : ∀ i j, d i * d j = d j * d i)
    (hc : ∀ x ∈ P, (d 0 * d 1 * d 2) * x * (d 0 * d 1 * d 2)⁻¹ * x ∈ Z₀)
    (hLA : ∀ i j, i ≠ j → ∀ x ∈ P, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Z₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Z₀)
    (hsame : ∀ i, ∀ a ∈ InvSet P d i, ∀ b ∈ InvSet P d i, a * b = b * a) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have hcomm : ∀ i j, ∀ a ∈ InvSet P d i, ∀ b ∈ InvSet P d j, Commute a b := by
    intro i j a ha b hb
    by_cases hij : i = j
    · subst hij; exact hsame i a ha b hb
    · exact commute_of_invSet hZc hZP hP' hPodd hij ha hb
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := exists_inv_decomp hZc hP' hPodd hd hdc hc hLA hx
  obtain ⟨b, hb, hyb⟩ := exists_inv_decomp hZc hP' hPodd hd hdc hc hLA hy
  have hAB : Commute (a 0 * a 1 * a 2) (b 0 * b 1 * b 2) := by
    have h : ∀ i, Commute (a i) (b 0 * b 1 * b 2) := fun i =>
      ((hcomm i 0 _ (ha i) _ (hb 0)).mul_right (hcomm i 1 _ (ha i) _ (hb 1))).mul_right
        (hcomm i 2 _ (ha i) _ (hb 2))
    exact ((h 0).mul_left (h 1)).mul_left (h 2)
  set A := a 0 * a 1 * a 2
  set B := b 0 * b 1 * b 2
  have hzx : A⁻¹ * x ∈ Z₀ := by
    have := Z₀.inv_mem hxa; rwa [mul_inv_rev, inv_inv] at this
  have hzy : B⁻¹ * y ∈ Z₀ := by
    have := Z₀.inv_mem hyb; rwa [mul_inv_rev, inv_inv] at this
  have czx : ∀ g : Y, Commute (A⁻¹ * x) g := fun g =>
    (mem_center_iff.mp (hZc hzx) g).symm
  have czy : ∀ g : Y, Commute (B⁻¹ * y) g := fun g =>
    (mem_center_iff.mp (hZc hzy) g).symm
  have hx' : x = A * (A⁻¹ * x) := by group
  have hy' : y = B * (B⁻¹ * y) := by group
  have hAy : Commute A y := by
    rw [hy']; exact hAB.mul_right (czy A).symm
  have hxy : Commute x y := by
    rw [hx']; exact hAy.mul_left (czx y)
  exact hxy.eq

theorem conj_mem_invSet_succ {P : Subgroup Y} [hPn : P.Normal] {d : Fin 3 → Y} {t : Y}
    (ht : ∀ i, t * d i * t⁻¹ = d (i + 1)) {i : Fin 3} {x : Y} (hx : x ∈ InvSet P d i) :
    t * x * t⁻¹ ∈ InvSet P d (i + 1) := by
  obtain ⟨hxP, hxi, hxj⟩ := hx
  refine ⟨hPn.conj_mem x hxP t, ?_, fun j hj => ?_⟩
  · rw [← ht i, show t * d i * t⁻¹ * (t * x * t⁻¹) * (t * d i * t⁻¹)⁻¹ =
      t * (d i * x * (d i)⁻¹) * t⁻¹ by group, hxi]
    group
  · have hj' : j - 1 ≠ i := fun h => hj (by rw [← h, sub_add_cancel])
    rw [show j = (j - 1) + 1 by rw [sub_add_cancel], ← ht (j - 1)]
    calc t * d (j - 1) * t⁻¹ * (t * x * t⁻¹) = t * (d (j - 1) * x) * t⁻¹ := by group
      _ = t * (x * d (j - 1)) * t⁻¹ := by rw [hxj (j - 1) hj']
      _ = t * x * t⁻¹ * (t * d (j - 1) * t⁻¹) := by group

theorem exists_all_but_one {S : Fin 3 → Prop} (h : ∀ i j, i ≠ j → S i ∨ S j) :
    ∃ k, ∀ l, l ≠ k → S l := by
  by_cases h0 : S 0
  · by_cases h1 : S 1
    · refine ⟨2, fun l hl => ?_⟩
      fin_cases l
      · exact h0
      · exact h1
      · exact absurd rfl hl
    · have h2 : S 2 := (h 1 2 (by decide)).resolve_left h1
      refine ⟨1, fun l hl => ?_⟩
      fin_cases l
      · exact h0
      · exact absurd rfl hl
      · exact h2
  · have h1 : S 1 := (h 0 1 (by decide)).resolve_left h0
    have h2 : S 2 := (h 0 2 (by decide)).resolve_left h0
    refine ⟨0, fun l hl => ?_⟩
    fin_cases l
    · exact absurd rfl hl
    · exact h1
    · exact h2

@[expose] def supCentral (L Z₀ : Subgroup Y) (hZc : Z₀ ≤ center Y) : Subgroup Y where
  carrier := {x | ∃ l ∈ L, ∃ z ∈ Z₀, x = l * z}
  one_mem' := ⟨1, L.one_mem, 1, Z₀.one_mem, by rw [one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨l, hl, z, hz, rfl⟩ ⟨l', hl', z', hz', rfl⟩
    refine ⟨l * l', L.mul_mem hl hl', z * z', Z₀.mul_mem hz hz', ?_⟩
    have := mem_center_iff.mp (hZc hz) l'
    calc l * z * (l' * z') = l * (z * l') * z' := by group
      _ = l * (l' * z) * z' := by rw [this]
      _ = l * l' * (z * z') := by group
  inv_mem' := by
    rintro _ ⟨l, hl, z, hz, rfl⟩
    refine ⟨l⁻¹, L.inv_mem hl, z⁻¹, Z₀.inv_mem hz, ?_⟩
    have := mem_center_iff.mp (hZc (Z₀.inv_mem hz)) l⁻¹
    rw [mul_inv_rev]; exact this.symm

theorem le_or_sup_eq_of_frames {P Z₀ R : Subgroup Y} [hPn : P.Normal] [hZn : Z₀.Normal]
    [hRn : R.Normal] (hZc : Z₀ ≤ center Y) (hZP : Z₀ ≤ P)
    (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀) (hPodd : Odd (Nat.card P))
    {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (hc : ∀ x ∈ P, (d 0 * d 1 * d 2) * x * (d 0 * d 1 * d 2)⁻¹ * x ∈ Z₀)
    (hLA : ∀ i j, i ≠ j → ∀ x ∈ P, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Z₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Z₀)
    (hRS : ∀ r ∈ R, ∀ x ∈ P, (d 0 * r * (d 0)⁻¹ * r⁻¹) * x * (d 0 * r * (d 0)⁻¹ * r⁻¹)⁻¹ *
      x⁻¹ ∈ Z₀)
    (hYR : ∀ y : Y, ∃ r ∈ R, ∃ g : Y, g * (d 0 * d 1 * d 2) * g⁻¹ = d 0 * d 1 * d 2 ∧ y = r * g)
    (hgen : normalClosure ({d 0} : Set Y) = ⊤)
    (hmax : ∀ N : Subgroup Y, N.Normal → Z₀ ≤ N → N ≤ P → N = Z₀ ∨ N = P)
    (L : Subgroup Y) (hLP : L ≤ P)
    (hfr : ∀ g : Y, g * (d 0 * d 1 * d 2) * g⁻¹ = d 0 * d 1 * d 2 → ∀ i j, i ≠ j →
      InvSet P (fun l => g * d l * g⁻¹) i ⊆ L ∨ InvSet P (fun l => g * d l * g⁻¹) j ⊆ L) :
    L ≤ Z₀ ∨ ∀ x ∈ P, ∃ l ∈ L, x⁻¹ * l ∈ Z₀ := by
  set N := supCentral L Z₀ hZc with hNdef
  have hZN : Z₀ ≤ N := fun z hz => ⟨1, L.one_mem, z, hz, by rw [one_mul]⟩
  have hLN : L ≤ N := fun l hl => ⟨l, hl, 1, Z₀.one_mem, by rw [mul_one]⟩
  have hNP : N ≤ P := by
    rintro _ ⟨l, hl, z, hz, rfl⟩; exact P.mul_mem (hLP hl) (hZP hz)
  have hfN : ∀ g : Y, g * (d 0 * d 1 * d 2) * g⁻¹ = d 0 * d 1 * d 2 → ∀ n ∈ N,
      (g * d 0 * g⁻¹) * n * (g * d 0 * g⁻¹)⁻¹ ∈ N := by
    intro g hg n hn
    set e : Fin 3 → Y := fun l => g * d l * g⁻¹ with he
    have hed : ∀ i, e i * e i = 1 := fun i => by
      show g * d i * g⁻¹ * (g * d i * g⁻¹) = 1
      rw [show g * d i * g⁻¹ * (g * d i * g⁻¹) = g * (d i * d i) * g⁻¹ by group, hd i]; group
    have hedc : ∀ i j, e i * e j = e j * e i := fun i j => by
      show g * d i * g⁻¹ * (g * d j * g⁻¹) = g * d j * g⁻¹ * (g * d i * g⁻¹)
      rw [show g * d i * g⁻¹ * (g * d j * g⁻¹) = g * (d i * d j) * g⁻¹ by group, hdc i j]; group
    have hce : e 0 * e 1 * e 2 = d 0 * d 1 * d 2 := by
      show g * d 0 * g⁻¹ * (g * d 1 * g⁻¹) * (g * d 2 * g⁻¹) = _
      rw [← hg]; group
    have hec : ∀ x ∈ P, (e 0 * e 1 * e 2) * x * (e 0 * e 1 * e 2)⁻¹ * x ∈ Z₀ := by
      rw [hce]; exact hc
    have heLA : ∀ i j, i ≠ j → ∀ x ∈ P, (e i * e j) * x * (e i * e j)⁻¹ * x⁻¹ ∈ Z₀ →
        e i * x * (e i)⁻¹ * x⁻¹ ∈ Z₀ := by
      intro i j hij x hx hx'
      have hx'' : (d i * d j) * (g⁻¹ * x * g) * (d i * d j)⁻¹ * (g⁻¹ * x * g)⁻¹ ∈ Z₀ := by
        have := hZn.conj_mem _ hx' g⁻¹
        convert this using 1
        simp only [he]; group
      have := hZn.conj_mem _ (hLA i j hij _ (by simpa using hPn.conj_mem x hx g⁻¹) hx'') g
      convert this using 1
      simp only [he]; group
    obtain ⟨k, hk⟩ := exists_all_but_one (hfr g hg)
    obtain ⟨a, ha, hm⟩ := exists_inv_decomp hZc hP' hPodd hed hedc hec heLA (hNP hn)
    set m := n⁻¹ * (a 0 * a 1 * a 2) with hmdef
    have hn' : n = a 0 * a 1 * a 2 * m⁻¹ := by rw [hmdef]; group
    have hmc := mem_center_iff.mp (hZc (Z₀.inv_mem hm)) (e 0)
    have h0 : e 0 * a 0 * (e 0)⁻¹ = (a 0)⁻¹ := (ha 0).2.1
    have h1 : e 0 * a 1 * (e 0)⁻¹ = a 1 := conj_eq_of_comm ((ha 1).2.2 0 (by decide))
    have h2 : e 0 * a 2 * (e 0)⁻¹ = a 2 := conj_eq_of_comm ((ha 2).2.2 0 (by decide))
    have hm' : e 0 * m⁻¹ * (e 0)⁻¹ = m⁻¹ := by rw [hmc]; group
    have hfn : (g * d 0 * g⁻¹) * n * (g * d 0 * g⁻¹)⁻¹ = (a 0)⁻¹ * (a 1 * a 2 * m⁻¹) := by
      show e 0 * n * (e 0)⁻¹ = _
      rw [hn', show e 0 * (a 0 * a 1 * a 2 * m⁻¹) * (e 0)⁻¹ = (e 0 * a 0 * (e 0)⁻¹) *
        (e 0 * a 1 * (e 0)⁻¹) * (e 0 * a 2 * (e 0)⁻¹) * (e 0 * m⁻¹ * (e 0)⁻¹) by group,
        h0, h1, h2, hm']
      group
    rw [hfn]
    have hmN : m⁻¹ ∈ N := hZN (Z₀.inv_mem hm)
    by_cases hk0 : k = 0
    · subst hk0
      have ha1 : a 1 ∈ N := hLN (hk 1 (by decide) (ha 1))
      have ha2 : a 2 ∈ N := hLN (hk 2 (by decide) (ha 2))
      have hrest : a 1 * a 2 * m⁻¹ ∈ N := N.mul_mem (N.mul_mem ha1 ha2) hmN
      have ha0 : a 0 = n * (a 1 * a 2 * m⁻¹)⁻¹ := by rw [hn']; group
      have ha0N : a 0 ∈ N := by rw [ha0]; exact N.mul_mem hn (N.inv_mem hrest)
      exact N.mul_mem (N.inv_mem ha0N) hrest
    · have ha0N : a 0 ∈ N := hLN (hk 0 (Ne.symm hk0) (ha 0))
      have hrest : a 1 * a 2 * m⁻¹ = (a 0)⁻¹ * n := by rw [hn']; group
      rw [hrest]
      exact N.mul_mem (N.inv_mem ha0N) (N.mul_mem (N.inv_mem ha0N) hn)
  have hkey : ∀ y : Y, ∀ n ∈ N, (y * d 0 * y⁻¹) * n * (y * d 0 * y⁻¹)⁻¹ ∈ N := by
    intro y n hn
    obtain ⟨r, hr, g, hg, rfl⟩ := hYR y
    set f := g * d 0 * g⁻¹ with hf
    have hS : ∀ x ∈ P, (f * (r * f * r⁻¹)⁻¹) * x * (f * (r * f * r⁻¹)⁻¹)⁻¹ * x⁻¹ ∈ Z₀ := by
      intro x hx
      have hr' : g⁻¹ * r * g ∈ R := by simpa using hRn.conj_mem r hr g⁻¹
      have hx' : g⁻¹ * x * g ∈ P := by simpa using hPn.conj_mem x hx g⁻¹
      have := hZn.conj_mem _ (hRS _ hr' _ hx') g
      convert this using 1
      rw [hf]; group
    set x := (r * f * r⁻¹) * n * (r * f * r⁻¹)⁻¹ with hx
    have hxP : x ∈ P := hPn.conj_mem n (hNP hn) _
    have hz := hS x hxP
    have hzN : (f * (r * f * r⁻¹)⁻¹) * x * (f * (r * f * r⁻¹)⁻¹)⁻¹ * x⁻¹ ∈ N := hZN hz
    have hfn := hfN g hg n hn
    have hxe : x = ((f * (r * f * r⁻¹)⁻¹) * x * (f * (r * f * r⁻¹)⁻¹)⁻¹ * x⁻¹)⁻¹ *
        (f * n * f⁻¹) := by rw [hx]; group
    have : (r * g) * d 0 * (r * g)⁻¹ = r * f * r⁻¹ := by rw [hf]; group
    rw [this, ← hx, hxe]
    exact N.mul_mem (N.inv_mem hzN) hfn
  have hNn : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.normalClosure,
      Subgroup.closure_le]
    intro e he
    obtain ⟨b, hb, hbe⟩ := (Group.mem_conjugatesOfSet_iff).mp he
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨y, rfl⟩ := isConj_iff.mp hbe
    have hee : (y * d 0 * y⁻¹) * (y * d 0 * y⁻¹) = 1 := by
      rw [show y * d 0 * y⁻¹ * (y * d 0 * y⁻¹) = y * (d 0 * d 0) * y⁻¹ by group, hd 0]; group
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hkey y n, fun h => ?_⟩
    have := hkey y _ h
    rwa [show (y * d 0 * y⁻¹) * ((y * d 0 * y⁻¹) * n * (y * d 0 * y⁻¹)⁻¹) *
      (y * d 0 * y⁻¹)⁻¹ = ((y * d 0 * y⁻¹) * (y * d 0 * y⁻¹)) * n *
      ((y * d 0 * y⁻¹) * (y * d 0 * y⁻¹))⁻¹ by group, hee, one_mul, inv_one, mul_one] at this
  rcases hmax N hNn hZN hNP with h | h
  · left; rw [← h]; exact hLN
  · right
    intro x hx
    rw [← h] at hx
    obtain ⟨l, hl, z, hz, rfl⟩ := hx
    exact ⟨l, hl, by rw [show (l * z)⁻¹ * l = z⁻¹ by group]; exact Z₀.inv_mem hz⟩
end
end CFSG.LocalAnalysis.WeakClosure81.OddCentral
