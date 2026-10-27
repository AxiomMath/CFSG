module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KN1
public import CFSG.RankThree.PartTwo.Sec12.Hering129KN2

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129KN3

theorem conj_zpow_eq {Q : Type*} [Group Q] {a z w : Q} (haz : a * z = z * a)
    (hwa : w * a * w⁻¹ = z * a) (j : ℤ) : w * a ^ j * w⁻¹ = z ^ j * a ^ j := by
  rw [← conj_zpow, hwa, (show Commute z a from haz.symm).mul_zpow]

theorem inv_conj_zpow_eq {Q : Type*} [Group Q] {a z w : Q} (haz : a * z = z * a)
    (hwa : w * a * w⁻¹ = z * a) (hwz : w * z = z * w) (j : ℤ) :
    w⁻¹ * a ^ j * w = z ^ (-j) * a ^ j := by
  have h := conj_zpow_eq haz hwa j
  have hzw : w⁻¹ * z ^ j = z ^ j * w⁻¹ :=
    ((show Commute w z from hwz).inv_left.zpow_right j).eq
  have h2 : z ^ j * (w⁻¹ * a ^ j * w) = a ^ j := by
    calc z ^ j * (w⁻¹ * a ^ j * w) = (z ^ j * w⁻¹) * a ^ j * w := by group
      _ = w⁻¹ * (z ^ j * a ^ j) * w := by rw [← hzw]; group
      _ = w⁻¹ * (w * a ^ j * w⁻¹) * w := by rw [h]
      _ = a ^ j := by group
  calc w⁻¹ * a ^ j * w = z ^ (-j) * (z ^ j * (w⁻¹ * a ^ j * w)) := by group
    _ = z ^ (-j) * a ^ j := by rw [h2]

end Hering129KN3

open Hering129KN3

theorem exists_inverted_w {Q : Type} [Group Q] (τ : Q ≃* Q) (m : ℕ)
    (hτ : (τ ^ (2 ^ m) : Q ≃* Q) = 1) {a z w : Q} (haz : a * z = z * a) (ha3 : a ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hwa : w * a * w⁻¹ = z * a) (hwz : w * z = z * w)
    (hw3 : w ^ 3 = 1) (hτa : τ a = a) (hτz : τ z = z⁻¹) {i k : ℤ}
    (hτw : τ w = a ^ i * z ^ k * w⁻¹) :
    ∃ i' k' : ℤ, τ (a ^ i' * z ^ k' * w) = (a ^ i' * z ^ k' * w)⁻¹ := by
  have hza : Commute z a := (show Commute a z from haz).symm
  have hzw : Commute z w := (show Commute w z from hwz).symm
  have hττw : τ (τ w) = z ^ (-2 * k - i) * w := by
    have e1 : w * a ^ (-i) = z ^ (-i) * a ^ (-i) * w := by
      rw [← conj_zpow_eq haz hwa (-i)]; group
    have e2 : w * z ^ (-k) = z ^ (-k) * w := ((hzw.zpow_left (-k)).eq).symm
    have e3 : a ^ i * z ^ (-2 * k - i) = z ^ (-2 * k - i) * a ^ i :=
      ((hza.zpow_zpow (-2 * k - i) i).eq).symm
    calc τ (τ w) = a ^ i * z ^ (-k) * (w * z ^ (-k)) * a ^ (-i) := by
          rw [hτw]; simp only [map_mul, map_zpow, map_inv, hτa, hτz, hτw]; group
      _ = a ^ i * z ^ (-k) * z ^ (-k) * (w * a ^ (-i)) := by rw [e2]; group
      _ = a ^ i * z ^ (-k) * z ^ (-k) * (z ^ (-i) * a ^ (-i) * w) := by rw [e1]
      _ = a ^ i * z ^ (-2 * k - i) * a ^ (-i) * w := by group
      _ = z ^ (-2 * k - i) * a ^ i * a ^ (-i) * w := by rw [e3]
      _ = z ^ (-2 * k - i) * w := by group
  have hφz : (τ ^ 2) z = z := by
    rw [pow_two, MulAut.mul_apply, hτz, map_inv, hτz, inv_inv]
  have hφw : (τ ^ 2) w = z ^ (-2 * k - i) * w := by
    rw [pow_two, MulAut.mul_apply, hττw]
  have hφn : ∀ n : ℕ, ((τ ^ 2) ^ n) w = z ^ ((n : ℤ) * (-2 * k - i)) * w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_zpow, hφz, hφw, ← mul_assoc,
        ← zpow_add]
      congr 2
      push_cast
      ring
  have hki : z ^ (k - i) = 1 := by
    rcases m with _ | m
    · exfalso
      have h1 : τ z = z := by
        rw [show τ = 1 by simpa using hτ]
        rfl
      rw [hτz] at h1
      apply hz1
      have h2 : z * z = 1 := by
        nth_rewrite 1 [← h1]
        exact inv_mul_cancel z
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [hz3, h2]; group
    · have h2 : ((τ ^ 2) ^ (2 ^ m)) w = w := by
        rw [← pow_mul, ← pow_succ', hτ]
        rfl
      rw [hφn, mul_eq_right] at h2
      have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
      rw [← orderOf_dvd_iff_zpow_eq_one, hord] at h2
      have h4 : (3 : ℤ) ∣ (-2 * k - i) := by
        rcases Int.prime_three.dvd_or_dvd h2 with h | h
        · exfalso
          have h' : (3 : ℤ) ∣ (2 : ℤ) ^ m := by exact_mod_cast h
          have := Int.prime_three.dvd_of_dvd_pow h'
          norm_num at this
        · exact h
      rw [← orderOf_dvd_iff_zpow_eq_one, hord]
      push_cast
      omega
  refine ⟨i, 0, ?_⟩
  have e4 : w⁻¹ * a ^ (-i) = z ^ i * a ^ (-i) * w⁻¹ := by
    have h := inv_conj_zpow_eq haz hwa hwz (-i)
    rw [neg_neg] at h
    rw [← h]
    group
  have e5 : a ^ i * z ^ k = z ^ k * a ^ i := ((hza.zpow_zpow k i).eq).symm
  have hzk : z ^ k = z ^ i := by
    calc z ^ k = z ^ (k - i) * z ^ i := by group
      _ = z ^ i := by rw [hki, one_mul]
  have ha3i : a ^ (3 * i) = 1 := by rw [zpow_mul, zpow_ofNat, ha3, one_zpow]
  calc τ (a ^ i * z ^ (0 : ℤ) * w) = a ^ i * (a ^ i * z ^ k) * w⁻¹ := by
        simp only [map_mul, map_zpow, hτa, hτw, zpow_zero, mul_one, one_mul]; group
    _ = a ^ i * (z ^ i * a ^ i) * w⁻¹ := by rw [e5, hzk]
    _ = z ^ i * a ^ (3 * i) * a ^ (-i) * w⁻¹ := by
        have : a ^ i * z ^ i = z ^ i * a ^ i := ((hza.zpow_zpow i i).eq).symm
        calc a ^ i * (z ^ i * a ^ i) * w⁻¹ = (a ^ i * z ^ i) * a ^ i * w⁻¹ := by group
          _ = z ^ i * a ^ i * a ^ i * w⁻¹ := by rw [this]
          _ = z ^ i * a ^ (3 * i) * a ^ (-i) * w⁻¹ := by group
    _ = z ^ i * a ^ (-i) * w⁻¹ := by rw [ha3i, mul_one]
    _ = w⁻¹ * a ^ (-i) := e4.symm
    _ = (a ^ i * z ^ (0 : ℤ) * w)⁻¹ := by group

namespace Hering129KN3

theorem mem_sup_comm {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hle : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hc h hh n hn, mul_inv_cancel_right]
      exact hn
    · intro hn
      have h1 := hc h hh _ hn
      have h2 : h * n * h⁻¹ = n := by
        calc h * n * h⁻¹ = h⁻¹ * (h * (h * n * h⁻¹)) := by group
          _ = h⁻¹ * (h * n * h⁻¹ * h) := by rw [h1]
          _ = n := by group
      rw [← h2]
      exact hn
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H K hle] at hx
  obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.1 hx
  exact ⟨h, hh, k, hk, rfl⟩

theorem zpow_pow_three {G : Type*} [Group G] {a : G} (ha3 : a ^ 3 = 1) (n : ℤ) :
    (a ^ n) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]

theorem exists_zpow_of_mem_sup {G : Type*} [Group G] {a z : G} (haz : a * z = z * a) {v : G}
    (hv : v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z) : ∃ α γ : ℤ, v = a ^ α * z ^ γ := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_comm (fun p hp q hq => by
    obtain ⟨α, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    obtain ⟨γ, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    exact ((show Commute a z from haz).zpow_zpow α γ).eq) hv
  obtain ⟨α, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  obtain ⟨γ, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
  exact ⟨α, γ, rfl⟩

theorem card_sup_zpowers_eq_nine {G : Type*} [Group G] [Finite G] {Z V : G}
    (hZV : Z * V = V * Z) (hZ3 : Z ^ 3 = 1) (hZ1 : Z ≠ 1) (hV3 : V ^ 3 = 1)
    (hVZ : V ∉ Subgroup.zpowers Z) :
    Nat.card (Subgroup.zpowers Z ⊔ Subgroup.zpowers V : Subgroup G) = 9 := by
  have hV1 : V ≠ 1 := fun h => hVZ (h ▸ Subgroup.one_mem _)
  have hZo : orderOf Z = 3 := orderOf_eq_prime hZ3 hZ1
  have hVo : orderOf V = 3 := orderOf_eq_prime hV3 hV1
  have hinf : Subgroup.zpowers Z ⊓ Subgroup.zpowers V = ⊥ := by
    have hd : Nat.card (Subgroup.zpowers Z ⊓ Subgroup.zpowers V : Subgroup G) ∣ 3 := by
      rw [← hVo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      have heq : Subgroup.zpowers Z ⊓ Subgroup.zpowers V = Subgroup.zpowers V :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hVo])
      apply hVZ
      have hV : V ∈ Subgroup.zpowers Z ⊓ Subgroup.zpowers V := by
        rw [heq]
        exact Subgroup.mem_zpowers V
      exact hV.1
  have hc : ∀ (x : Subgroup.zpowers Z) (y : Subgroup.zpowers V),
      Commute ((Subgroup.zpowers Z).subtype x) ((Subgroup.zpowers V).subtype y) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨α, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨β, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (show Commute Z V from hZV).zpow_zpow α β
  let μ := MonoidHom.noncommCoprod (Subgroup.zpowers Z).subtype (Subgroup.zpowers V).subtype hc
  have hμ : ∀ x, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = Subgroup.zpowers Z ⊔ Subgroup.zpowers V := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun g hg => ⟨(⟨g, hg⟩, 1), by rw [hμ]; simp⟩)
        (fun g hg => ⟨(1, ⟨g, hg⟩), by rw [hμ]; simp⟩)
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ hxy
    have hxy0 : x * y = 1 := hxy
    have hxy' : x = y⁻¹ := eq_inv_of_mul_eq_one_left hxy0
    have hx1 : x = 1 := by
      have hxV : x ∈ Subgroup.zpowers V := hxy' ▸ inv_mem hy
      have hxinf : x ∈ Subgroup.zpowers Z ⊓ Subgroup.zpowers V := ⟨hx, hxV⟩
      rw [hinf] at hxinf
      exact (Subgroup.mem_bot.1 hxinf)
    have hy1 : y = 1 := by
      rw [hx1, one_mul] at hxy0
      exact hxy0
    subst hx1 hy1
    rfl
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
    Nat.card_zpowers, Nat.card_zpowers, hZo, hVo]

theorem quot_core {Q : Type} [Group Q] [Finite Q] (τ : Q ≃* Q) {A B Z V : Q}
    (hAZ : A * Z = Z * A) (hBZ : B * Z = Z * B) (hZ3 : Z ^ 3 = 1) (hZ1 : Z ≠ 1)
    (hV3 : V ^ 3 = 1) (hVA : V * A * V⁻¹ = Z * A) (hVB : V * B * V⁻¹ = Z⁻¹ * B)
    (hVZ : V * Z = Z * V) (hτA : τ A = A) (hτB : τ B = B) (hτZ : τ Z = Z⁻¹)
    (hτV : τ V = V⁻¹) (hgen : Subgroup.closure ({A, B, Z, V} : Set Q) = ⊤) :
    Nat.card (commSubgroup τ) = 9 ∧
    (∀ v ∈ commSubgroup τ, ∀ w ∈ commSubgroup τ, v * w = w * v) ∧
    (∀ v ∈ commSubgroup τ, v ^ 3 = 1) ∧ (∀ v ∈ commSubgroup τ, τ v = v⁻¹) ∧
    Z ∈ commSubgroup τ := by
  have cAZ : Commute A Z := hAZ
  have cBZ : Commute B Z := hBZ
  have cZV : Commute Z V := (show Commute V Z from hVZ).symm
  let E : Subgroup Q := Subgroup.zpowers Z ⊔ Subgroup.zpowers V
  have hZE : Z ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers Z)
  have hVE : V ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers V)
  have hEdec : ∀ e ∈ E, ∃ α β : ℤ, e = Z ^ α * V ^ β := fun e he =>
    exists_zpow_of_mem_sup cZV he
  have hVnZ : V ∉ Subgroup.zpowers Z := by
    intro hV
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hV
    apply hZ1
    have h1 : V * A * V⁻¹ = A := by
      rw [← hn]
      exact (cAZ.symm.zpow_left n).mul_inv_cancel
    rw [hVA] at h1
    exact mul_eq_right.1 h1
  have hZo : orderOf Z = 3 := orderOf_eq_prime hZ3 hZ1
  have hconjE : ∀ g ∈ ({A, B, Z, V} : Set Q), ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg
    have key : g * Z * g⁻¹ ∈ E ∧ g * V * g⁻¹ ∈ E := by
      rcases hg with rfl | rfl | rfl | rfl
      · refine ⟨by rw [cAZ.mul_inv_cancel]; exact hZE, ?_⟩
        have : g * V * g⁻¹ = Z⁻¹ * V := by
          calc g * V * g⁻¹ = g * (V * g * V⁻¹)⁻¹ * V := by group
            _ = g * (Z * g)⁻¹ * V := by rw [hVA]
            _ = Z⁻¹ * V := by group
        rw [this]
        exact mul_mem (inv_mem hZE) hVE
      · refine ⟨by rw [cBZ.mul_inv_cancel]; exact hZE, ?_⟩
        have : g * V * g⁻¹ = Z * V := by
          calc g * V * g⁻¹ = g * (V * g * V⁻¹)⁻¹ * V := by group
            _ = g * (Z⁻¹ * g)⁻¹ * V := by rw [hVB]
            _ = Z * V := by group
        rw [this]
        exact mul_mem hZE hVE
      · exact ⟨by rw [mul_inv_cancel_right]; exact hZE,
          by rw [cZV.mul_inv_cancel]; exact hVE⟩
      · exact ⟨by rw [cZV.symm.mul_inv_cancel]; exact hZE,
          by rw [mul_inv_cancel_right]; exact hVE⟩
    have hle : E ≤ E.comap (MulAut.conj g).toMonoidHom := by
      apply sup_le
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        exact key.1
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        exact key.2
    intro e he
    exact hle he
  have hEn : E.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_normalizer_fintype (fun n hn => hconjE g hg n hn)
  have hδ : ∀ q : Q, q * (τ q)⁻¹ ∈ E := by
    let K : Subgroup Q :=
      { carrier := {q | q * (τ q)⁻¹ ∈ E}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq, map_mul, mul_inv_rev] at hx hy ⊢
          have := mul_mem (hEn.conj_mem _ hy x) hx
          convert this using 1
          group
        one_mem' := by simp
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq, map_inv, inv_inv] at hx ⊢
          have := hEn.conj_mem _ (inv_mem hx) x⁻¹
          convert this using 1
          group }
    have hK : K = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      rintro g (rfl | rfl | rfl | rfl)
      · show g * (τ g)⁻¹ ∈ E
        rw [hτA, mul_inv_cancel]
        exact one_mem E
      · show g * (τ g)⁻¹ ∈ E
        rw [hτB, mul_inv_cancel]
        exact one_mem E
      · show g * (τ g)⁻¹ ∈ E
        rw [hτZ, inv_inv]
        exact mul_mem hZE hZE
      · show g * (τ g)⁻¹ ∈ E
        rw [hτV, inv_inv]
        exact mul_mem hVE hVE
    intro q
    have hq : q ∈ K := hK ▸ Subgroup.mem_top q
    exact hq
  have hcs : commSubgroup τ = E := by
    apply le_antisymm
    · show Subgroup.closure {q | ∃ y : Q, q = y * (τ y)⁻¹} ≤ E
      rw [Subgroup.closure_le]
      rintro q ⟨y, rfl⟩
      exact hδ y
    · apply sup_le
      · rw [Subgroup.zpowers_le]
        have hg : Z * (τ Z)⁻¹ ∈ commSubgroup τ := Subgroup.subset_closure ⟨Z, rfl⟩
        have h1 : Z = (Z * (τ Z)⁻¹) * (Z * (τ Z)⁻¹) := by
          rw [hτZ, inv_inv]
          calc Z = Z ^ 3 * Z := by rw [hZ3, one_mul]
            _ = Z * Z * (Z * Z) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [h1]
        exact mul_mem hg hg
      · rw [Subgroup.zpowers_le]
        have hg : V * (τ V)⁻¹ ∈ commSubgroup τ := Subgroup.subset_closure ⟨V, rfl⟩
        have h1 : V = (V * (τ V)⁻¹) * (V * (τ V)⁻¹) := by
          rw [hτV, inv_inv]
          calc V = V ^ 3 * V := by rw [hV3, one_mul]
            _ = V * V * (V * V) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [h1]
        exact mul_mem hg hg
  rw [hcs]
  refine ⟨card_sup_zpowers_eq_nine cZV.eq hZ3 hZ1 hV3 hVnZ, ?_, ?_, ?_, hZE⟩
  · intro v hv w hw
    obtain ⟨α, β, rfl⟩ := hEdec v hv
    obtain ⟨γ, δ, rfl⟩ := hEdec w hw
    exact (((Commute.zpow_zpow_self Z α γ).mul_right (cZV.zpow_zpow α δ)).mul_left
      ((cZV.symm.zpow_zpow β γ).mul_right (Commute.zpow_zpow_self V β δ))).eq
  · intro v hv
    obtain ⟨α, β, rfl⟩ := hEdec v hv
    rw [(cZV.zpow_zpow α β).mul_pow, zpow_pow_three hZ3, zpow_pow_three hV3, one_mul]
  · intro v hv
    obtain ⟨α, β, rfl⟩ := hEdec v hv
    rw [map_mul, map_zpow, map_zpow, hτZ, hτV, inv_zpow, inv_zpow, mul_inv_rev]
    exact ((cZV.zpow_zpow α β).inv_inv).eq

theorem cube_eq_one {G : Type*} [Group G] {f w c : G} (hwf : w * f * w⁻¹ = c * f)
    (hcf : c * f = f * c) (hcw : c * w = w * c) (hc3 : c ^ 3 = 1) (hf3 : f ^ 3 = 1)
    (hw3 : w ^ 3 = 1) : (f * w) ^ 3 = 1 := by
  have cfc : Commute f c := (show Commute c f from hcf).symm
  have hc3' : c * (c * c) = 1 := by rw [← pow_three]; exact hc3
  have hf3' : f * (f * f) = 1 := by rw [← pow_three]; exact hf3
  have hw3' : w * (w * w) = 1 := by rw [← pow_three]; exact hw3
  have hwf' : w * f = c * f * w := by rw [← hwf]; group
  rw [pow_three]
  calc f * w * (f * w * (f * w)) = f * (w * f) * (w * f) * w := by group
    _ = f * (c * f * w) * (c * f * w) * w := by rw [hwf']
    _ = f * c * f * (w * c) * f * w * w := by group
    _ = f * c * f * (c * w) * f * w * w := by rw [hcw]
    _ = f * c * f * c * (w * f) * w * w := by group
    _ = f * c * f * c * (c * f * w) * w * w := by rw [hwf']
    _ = (f * c * f * c * c * f) * (w * (w * w)) := by group
    _ = (c * (c * c)) * (f * (f * f)) * (w * (w * w)) := by
        congr 1
        simp only [mul_assoc, cfc.left_comm, cfc.eq]
    _ = 1 := by rw [hc3', hf3', hw3', one_mul, one_mul]

theorem quot_algebra {Q : Type} [Group Q] [Finite Q] (τ : Q ≃* Q) (m : ℕ)
    (hτ : (τ ^ (2 ^ m) : Q ≃* Q) = 1) {A B Z W : Q}
    (hAB : A * B = B * A) (hAZ : A * Z = Z * A) (hBZ : B * Z = Z * B)
    (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1) (hZ3 : Z ^ 3 = 1) (hZ1 : Z ≠ 1) (hW3 : W ^ 3 = 1)
    (hWA : W * A * W⁻¹ = Z * A) (hWB : W * B * W⁻¹ = Z⁻¹ * B) (hWZ : W * Z = Z * W)
    (hτA : τ A = A) (hτB : τ B = B) (hτZ : τ Z = Z⁻¹) {i j k l : ℤ}
    (hτW : τ W = A ^ i * Z ^ k * (B ^ j * Z⁻¹ ^ l) * W⁻¹)
    (hgen : Subgroup.closure ({A, B, Z, W} : Set Q) = ⊤) :
    Nat.card (commSubgroup τ) = 9 ∧
    (∀ v ∈ commSubgroup τ, ∀ w ∈ commSubgroup τ, v * w = w * v) ∧
    (∀ v ∈ commSubgroup τ, v ^ 3 = 1) ∧ (∀ v ∈ commSubgroup τ, τ v = v⁻¹) ∧
    Z ∈ commSubgroup τ := by
  have cAB : Commute A B := hAB
  have cAZ : Commute A Z := hAZ
  have cBZ : Commute B Z := hBZ
  have hWC : W * (A * B) * W⁻¹ = A * B := by
    calc W * (A * B) * W⁻¹ = (W * A * W⁻¹) * (W * B * W⁻¹) := by group
      _ = Z * A * (Z⁻¹ * B) := by rw [hWA, hWB]
      _ = A * B := by rw [← hAZ]; group
  have cCW : Commute (A * B) W := by
    have h : W * (A * B) = A * B * W := by
      calc W * (A * B) = W * (A * B) * W⁻¹ * W := by group
        _ = A * B * W := by rw [hWC]
    exact h.symm
  have cCA : Commute (A * B) A := (Commute.refl A).mul_left cAB.symm
  have cCB : Commute (A * B) B := cAB.mul_left (Commute.refl B)
  have cCZ : Commute (A * B) Z := cAZ.mul_left cBZ
  have hτC : τ (A * B) = A * B := by rw [map_mul, hτA, hτB]
  have hC3 : (A * B) ^ 3 = 1 := by rw [cAB.mul_pow, hA3, hB3, one_mul]
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Q, W₀ = (A * B) ^ j * W := ⟨_, rfl⟩
  have hW₀A : W₀ * A * W₀⁻¹ = Z * A := by
    calc W₀ * A * W₀⁻¹ = (A * B) ^ j * (W * A * W⁻¹) * ((A * B) ^ j)⁻¹ := by
          rw [hW₀]; group
      _ = Z * A := by rw [hWA]; exact ((cCZ.mul_right cCA).zpow_left j).mul_inv_cancel
  have hW₀B : W₀ * B * W₀⁻¹ = Z⁻¹ * B := by
    calc W₀ * B * W₀⁻¹ = (A * B) ^ j * (W * B * W⁻¹) * ((A * B) ^ j)⁻¹ := by
          rw [hW₀]; group
      _ = Z⁻¹ * B := by
          rw [hWB]; exact ((cCZ.inv_right.mul_right cCB).zpow_left j).mul_inv_cancel
  have hW₀Z : W₀ * Z = Z * W₀ := by
    rw [hW₀]
    calc (A * B) ^ j * W * Z = (A * B) ^ j * (W * Z) := by rw [mul_assoc]
      _ = (A * B) ^ j * (Z * W) := by rw [hWZ]
      _ = ((A * B) ^ j * Z) * W := by rw [mul_assoc]
      _ = (Z * (A * B) ^ j) * W := by rw [(cCZ.zpow_left j).eq]
      _ = Z * ((A * B) ^ j * W) := by rw [mul_assoc]
  have hW₀3 : W₀ ^ 3 = 1 := by
    rw [hW₀, (cCW.zpow_left j).mul_pow, zpow_pow_three hC3, hW3, one_mul]
  have hτW₀ : τ W₀ = A ^ (i - j) * Z ^ (k - l) * W₀⁻¹ := by
    have r1 : ∀ α β : ℤ, B ^ β * A ^ α = A ^ α * B ^ β := fun α β =>
      (cAB.zpow_zpow α β).eq.symm
    have r2 : ∀ α γ : ℤ, Z ^ γ * A ^ α = A ^ α * Z ^ γ := fun α γ =>
      (cAZ.zpow_zpow α γ).eq.symm
    have r3 : ∀ β γ : ℤ, Z ^ γ * B ^ β = B ^ β * Z ^ γ := fun β γ =>
      (cBZ.zpow_zpow β γ).eq.symm
    have hCW' : ((A * B) ^ j * W)⁻¹ = ((A * B) ^ j)⁻¹ * W⁻¹ := by
      rw [mul_inv_rev, ((cCW.zpow_left j).inv_inv).eq]
    have hA3j : A ^ (3 * j) = 1 := by rw [zpow_mul, zpow_ofNat, hA3, one_zpow]
    have hB3j : B ^ (3 * j) = 1 := by rw [zpow_mul, zpow_ofNat, hB3, one_zpow]
    have lhs : (A * B) ^ j * (A ^ i * Z ^ k * (B ^ j * Z⁻¹ ^ l)) =
        A ^ (i + j) * B ^ (2 * j) * Z ^ (k - l) := by
      calc (A * B) ^ j * (A ^ i * Z ^ k * (B ^ j * Z⁻¹ ^ l))
          = A ^ j * (B ^ j * A ^ i) * (Z ^ k * B ^ j) * Z ^ (-l) := by
            rw [cAB.mul_zpow, inv_zpow']; group
        _ = A ^ j * (A ^ i * B ^ j) * (B ^ j * Z ^ k) * Z ^ (-l) := by rw [r1, r3]
        _ = A ^ (i + j) * B ^ (2 * j) * Z ^ (k - l) := by group
    have rhs : A ^ (i - j) * Z ^ (k - l) * ((A * B) ^ j)⁻¹ =
        A ^ (i - 2 * j) * B ^ (-j) * Z ^ (k - l) := by
      calc A ^ (i - j) * Z ^ (k - l) * ((A * B) ^ j)⁻¹
          = A ^ (i - j) * (Z ^ (k - l) * B ^ (-j)) * A ^ (-j) := by
            rw [cAB.mul_zpow, mul_inv_rev]; group
        _ = A ^ (i - j) * (B ^ (-j) * Z ^ (k - l)) * A ^ (-j) := by rw [r3]
        _ = A ^ (i - j) * B ^ (-j) * (Z ^ (k - l) * A ^ (-j)) := by group
        _ = A ^ (i - j) * B ^ (-j) * (A ^ (-j) * Z ^ (k - l)) := by rw [r2]
        _ = A ^ (i - j) * (B ^ (-j) * A ^ (-j)) * Z ^ (k - l) := by group
        _ = A ^ (i - j) * (A ^ (-j) * B ^ (-j)) * Z ^ (k - l) := by rw [r1]
        _ = A ^ (i - 2 * j) * B ^ (-j) * Z ^ (k - l) := by group
    have mid : A ^ (i + j) * B ^ (2 * j) = A ^ (i - 2 * j) * B ^ (-j) := by
      calc A ^ (i + j) * B ^ (2 * j) = A ^ (i - 2 * j) * A ^ (3 * j) * B ^ (-j) * B ^ (3 * j) := by
            group
        _ = A ^ (i - 2 * j) * B ^ (-j) := by rw [hA3j, hB3j, mul_one, mul_one]
    rw [hW₀, map_mul, map_zpow, hτC, hτW, hCW']
    calc (A * B) ^ j * (A ^ i * Z ^ k * (B ^ j * Z⁻¹ ^ l) * W⁻¹)
        = ((A * B) ^ j * (A ^ i * Z ^ k * (B ^ j * Z⁻¹ ^ l))) * W⁻¹ := by group
      _ = (A ^ (i - j) * Z ^ (k - l) * ((A * B) ^ j)⁻¹) * W⁻¹ := by rw [lhs, rhs, mid]
      _ = A ^ (i - j) * Z ^ (k - l) * (((A * B) ^ j)⁻¹ * W⁻¹) := by group
  obtain ⟨i', k', hV⟩ :=
    exists_inverted_w τ m hτ hAZ hA3 hZ3 hZ1 hW₀A hW₀Z hW₀3 hτA hτZ hτW₀
  have cFZ : Commute (A ^ i' * Z ^ k') Z :=
    (cAZ.zpow_left i').mul_left ((Commute.refl Z).zpow_left k')
  have cFA : Commute (A ^ i' * Z ^ k') A :=
    ((Commute.refl A).zpow_left i').mul_left (cAZ.symm.zpow_left k')
  have cFB : Commute (A ^ i' * Z ^ k') B :=
    (cAB.zpow_left i').mul_left (cBZ.symm.zpow_left k')
  have hVA : A ^ i' * Z ^ k' * W₀ * A * (A ^ i' * Z ^ k' * W₀)⁻¹ = Z * A := by
    calc A ^ i' * Z ^ k' * W₀ * A * (A ^ i' * Z ^ k' * W₀)⁻¹
        = (A ^ i' * Z ^ k') * (W₀ * A * W₀⁻¹) * (A ^ i' * Z ^ k')⁻¹ := by group
      _ = Z * A := by rw [hW₀A]; exact (cFZ.mul_right cFA).mul_inv_cancel
  have hVB : A ^ i' * Z ^ k' * W₀ * B * (A ^ i' * Z ^ k' * W₀)⁻¹ = Z⁻¹ * B := by
    calc A ^ i' * Z ^ k' * W₀ * B * (A ^ i' * Z ^ k' * W₀)⁻¹
        = (A ^ i' * Z ^ k') * (W₀ * B * W₀⁻¹) * (A ^ i' * Z ^ k')⁻¹ := by group
      _ = Z⁻¹ * B := by rw [hW₀B]; exact (cFZ.inv_right.mul_right cFB).mul_inv_cancel
  have hVZ : A ^ i' * Z ^ k' * W₀ * Z = Z * (A ^ i' * Z ^ k' * W₀) := by
    rw [mul_assoc, hW₀Z, ← mul_assoc, cFZ.eq, mul_assoc]
  have hV3 : (A ^ i' * Z ^ k' * W₀) ^ 3 = 1 := by
    have hconj : W₀ * (A ^ i' * Z ^ k') * W₀⁻¹ = Z ^ i' * (A ^ i' * Z ^ k') := by
      have h1 := conj_zpow_eq hAZ hW₀A i'
      have h2 : W₀ * Z ^ k' * W₀⁻¹ = Z ^ k' :=
        ((show Commute W₀ Z from hW₀Z).zpow_right k').mul_inv_cancel
      calc W₀ * (A ^ i' * Z ^ k') * W₀⁻¹
          = (W₀ * A ^ i' * W₀⁻¹) * (W₀ * Z ^ k' * W₀⁻¹) := by group
        _ = Z ^ i' * (A ^ i' * Z ^ k') := by rw [h1, h2]; group
    have cZiF : Commute (Z ^ i') (A ^ i' * Z ^ k') := (cFZ.zpow_right i').symm
    have cZiW : Commute (Z ^ i') W₀ := ((show Commute W₀ Z from hW₀Z).zpow_right i').symm
    exact cube_eq_one hconj cZiF.eq cZiW.eq (zpow_pow_three hZ3 i')
      (by rw [(cAZ.zpow_zpow i' k').mul_pow, zpow_pow_three hA3, zpow_pow_three hZ3, one_mul])
      hW₀3
  have hgen' : Subgroup.closure ({A, B, Z, A ^ i' * Z ^ k' * W₀} : Set Q) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    have hA : A ∈ Subgroup.closure ({A, B, Z, A ^ i' * Z ^ k' * W₀} : Set Q) :=
      Subgroup.subset_closure (by simp)
    have hB : B ∈ Subgroup.closure ({A, B, Z, A ^ i' * Z ^ k' * W₀} : Set Q) :=
      Subgroup.subset_closure (by simp)
    have hZ : Z ∈ Subgroup.closure ({A, B, Z, A ^ i' * Z ^ k' * W₀} : Set Q) :=
      Subgroup.subset_closure (by simp)
    have hV : A ^ i' * Z ^ k' * W₀ ∈
        Subgroup.closure ({A, B, Z, A ^ i' * Z ^ k' * W₀} : Set Q) :=
      Subgroup.subset_closure (by simp)
    rintro g (rfl | rfl | rfl | rfl)
    · exact hA
    · exact hB
    · exact hZ
    · have hW : g = ((A * B) ^ j)⁻¹ * (A ^ i' * Z ^ k')⁻¹ * (A ^ i' * Z ^ k' * W₀) := by
        rw [hW₀]; group
      rw [hW]
      exact mul_mem (mul_mem (inv_mem (zpow_mem (mul_mem hA hB) j))
        (inv_mem (mul_mem (zpow_mem hA i') (zpow_mem hZ k')))) hV
  exact quot_core τ hAZ hBZ hZ3 hZ1 hV3 hVA hVB hVZ hτA hτB hτZ hV hgen'

theorem conj_mem_sup {G : Type*} [Group G] {H K L : Subgroup G} {g : G}
    (hH : ∀ u ∈ H, g * u * g⁻¹ ∈ L) (hK : ∀ u ∈ K, g * u * g⁻¹ ∈ L) :
    ∀ x ∈ H ⊔ K, g * x * g⁻¹ ∈ L := by
  have hle : H ⊔ K ≤ L.comap (MulAut.conj g).toMonoidHom := by
    apply sup_le
    · intro u hu
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using hH u hu
    · intro u hu
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using hK u hu
  intro x hx
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using hle hx

theorem conj_pow_mem {G : Type*} [Group G] {H : Subgroup G} {t : G}
    (ht : ∀ s ∈ H, t * s * t⁻¹ ∈ H) (n : ℕ) : ∀ s ∈ H, t ^ n * s * (t ^ n)⁻¹ ∈ H := by
  induction n with
  | zero => intro s hs; simpa using hs
  | succ n ih =>
    intro s hs
    have h := ht _ (ih s hs)
    rw [pow_succ']
    convert h using 1
    group

theorem conj_inv_mem {G : Type*} [Group G] {H : Subgroup G} {t : G} {m : ℕ}
    (hm : t ^ (2 ^ m) = 1) (ht : ∀ s ∈ H, t * s * t⁻¹ ∈ H) : ∀ s ∈ H, t⁻¹ * s * t ∈ H := by
  intro s hs
  have h := conj_pow_mem ht (2 ^ m - 1) s hs
  have ht' : t ^ (2 ^ m - 1) = t⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hm]
  rw [ht', inv_inv] at h
  exact h

theorem conj_wpow {G : Type*} [Group G] {a z w : G} (haz : a * z = z * a)
    (hwa : w * a * w⁻¹ = z * a) (hwz : w * z = z * w) (n : ℤ) :
    w ^ n * a * (w ^ n)⁻¹ = z ^ n * a := by
  have cwz : Commute w z := hwz
  have hinv : w⁻¹ * a * w = z⁻¹ * a := by
    have h := inv_conj_zpow_eq haz hwa hwz 1
    simpa using h
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    calc w ^ ((n : ℤ) + 1) * a * (w ^ ((n : ℤ) + 1))⁻¹
        = w * (w ^ (n : ℤ) * a * (w ^ (n : ℤ))⁻¹) * w⁻¹ := by group
      _ = w * z ^ (n : ℤ) * a * w⁻¹ := by rw [ih]; group
      _ = z ^ (n : ℤ) * (w * a * w⁻¹) := by rw [(cwz.zpow_right (n : ℤ)).eq]; group
      _ = z ^ ((n : ℤ) + 1) * a := by rw [hwa]; group
  | pred n ih =>
    calc w ^ (-(n : ℤ) - 1) * a * (w ^ (-(n : ℤ) - 1))⁻¹
        = w⁻¹ * (w ^ (-(n : ℤ)) * a * (w ^ (-(n : ℤ)))⁻¹) * w := by group
      _ = w⁻¹ * z ^ (-(n : ℤ)) * a * w := by rw [ih]; group
      _ = z ^ (-(n : ℤ)) * (w⁻¹ * a * w) := by
          rw [(cwz.inv_left.zpow_right (-(n : ℤ))).eq]; group
      _ = z ^ (-(n : ℤ) - 1) * a := by rw [hinv]; group

theorem pow_card_eq_one_of_mem {G : Type*} [Group G] {R : Subgroup G} {r : G} (hr : r ∈ R) :
    r ^ Nat.card R = 1 := by
  have h1 := pow_card_eq_one' (G := R) (x := ⟨r, hr⟩)
  exact congrArg Subtype.val h1

section Factor

variable {X : Type} [Group X] [Finite X] {U R : Subgroup X} {a z : X}

theorem mem_R_of_pow (h : SLFactor U a z) (hRU : R ≤ U) (hRa : ∀ r ∈ R, r * a = a * r)
    (hR3 : ¬ 3 ∣ Nat.card R)
    (hdec : ∀ u ∈ U, u * a = a * u →
      ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, u = v * r)
    {g : X} (hg : g ∈ U) (hga : g * a = a * g) {n : ℕ} (hn : g ^ n = 1) (h3 : ¬ 3 ∣ n) :
    g ∈ R := by
  obtain ⟨v, hv, r, hr, rfl⟩ := hdec g hg hga
  have haz : a * z = z * a := h.hzc a h.ha
  have hvU : v ∈ U := (sup_le (Subgroup.zpowers_le.2 h.ha) (Subgroup.zpowers_le.2 h.hz)) hv
  obtain ⟨α, γ, hvαγ⟩ := exists_zpow_of_mem_sup haz hv
  have hva : v * a = a * v := by
    rw [hvαγ]
    exact (((Commute.refl a).zpow_left α).mul_left
      ((show Commute z a from haz.symm).zpow_left γ)).eq
  have hvr : Commute v r := h.hcomm v hvU hva r (hRU hr) (hRa r hr)
  have hv3 : v ^ 3 = 1 := by
    rw [hvαγ, ((show Commute a z from haz).zpow_zpow α γ).mul_pow, zpow_pow_three h.ha3,
      zpow_pow_three h.hz3, one_mul]
  have hrN : r ^ Nat.card R = 1 := pow_card_eq_one_of_mem hr
  have hvN : v ^ (n * Nat.card R) = 1 := by
    have h1 : (v * r) ^ (n * Nat.card R) = 1 := by rw [pow_mul, hn, one_pow]
    have h2 : r ^ (n * Nat.card R) = 1 := by rw [mul_comm, pow_mul, hrN, one_pow]
    rwa [hvr.mul_pow, h2, mul_one] at h1
  have hcop : Nat.Coprime (n * Nat.card R) 3 :=
    Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hR3).symm
  have hv1 : v = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hvN, hv3⟩
  rw [hv1, one_mul]
  exact hr

theorem conj_mem_R (h : SLFactor U a z) (hRU : R ≤ U) (hRa : ∀ r ∈ R, r * a = a * r)
    (hR3 : ¬ 3 ∣ Nat.card R)
    (hdec : ∀ u ∈ U, u * a = a * u →
      ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, u = v * r)
    {u : X} (hu : u ∈ U) {e : ℤ} (hue : u * a * u⁻¹ = z ^ e * a) {r : X} (hr : r ∈ R) :
    u * r * u⁻¹ ∈ R := by
  have hgU : u * r * u⁻¹ ∈ U := mul_mem (mul_mem hu (hRU hr)) (inv_mem hu)
  have hgy : Commute (u * r * u⁻¹) (u * a * u⁻¹) := by
    show u * r * u⁻¹ * (u * a * u⁻¹) = u * a * u⁻¹ * (u * r * u⁻¹)
    calc u * r * u⁻¹ * (u * a * u⁻¹) = u * (r * a) * u⁻¹ := by group
      _ = u * (a * r) * u⁻¹ := by rw [hRa r hr]
      _ = u * a * u⁻¹ * (u * r * u⁻¹) := by group
  rw [hue] at hgy
  have hgz : Commute (u * r * u⁻¹) (z ^ e) :=
    (show Commute (u * r * u⁻¹) z from h.hzc _ hgU).zpow_right e
  have hga := hgz.inv_right.mul_right hgy
  rw [inv_mul_cancel_left] at hga
  have hrN : r ^ Nat.card R = 1 := pow_card_eq_one_of_mem hr
  refine mem_R_of_pow h hRU hRa hR3 hdec hgU hga.eq (n := Nat.card R) ?_ hR3
  rw [conj_pow, hrN, mul_one, mul_inv_cancel]

theorem t_conj_R (h : SLFactor U a z) (hRU : R ≤ U) (hRa : ∀ r ∈ R, r * a = a * r)
    (hR3 : ¬ 3 ∣ Nat.card R)
    (hdec : ∀ u ∈ U, u * a = a * u →
      ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, u = v * r)
    {t : X} (htU : ∀ u ∈ U, t * u * t⁻¹ ∈ U) (hta : t * a * t⁻¹ = a) {r : X} (hr : r ∈ R) :
    t * r * t⁻¹ ∈ R := by
  have hga : t * r * t⁻¹ * a = a * (t * r * t⁻¹) := by
    calc t * r * t⁻¹ * a = t * r * t⁻¹ * (t * a * t⁻¹) := by rw [hta]
      _ = t * (r * a) * t⁻¹ := by group
      _ = t * (a * r) * t⁻¹ := by rw [hRa r hr]
      _ = (t * a * t⁻¹) * (t * r * t⁻¹) := by group
      _ = a * (t * r * t⁻¹) := by rw [hta]
  have hrN : r ^ Nat.card R = 1 := pow_card_eq_one_of_mem hr
  refine mem_R_of_pow h hRU hRa hR3 hdec (htU r (hRU hr)) hga (n := Nat.card R) ?_ hR3
  rw [conj_pow, hrN, mul_one, mul_inv_cancel]

theorem decomp_factor (h : SLFactor U a z)
    (hdec : ∀ u ∈ U, u * a = a * u →
      ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, u = v * r)
    {w : X} (hwU : w ∈ U) (hwa : w * a * w⁻¹ = z * a) {u : X} (hu : u ∈ U) {e : ℤ}
    (hue : u * a * u⁻¹ = z ^ e * a) :
    ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, u = v * r * w ^ e := by
  have h1 : w ^ (-e) * a * (w ^ (-e))⁻¹ = z ^ (-e) * a :=
    conj_wpow (h.hzc a h.ha) hwa (h.hzc w hwU) (-e)
  have h2 : u * z ^ (-e) = z ^ (-e) * u :=
    ((show Commute u z from h.hzc u hu).zpow_right (-e)).eq
  have hga : u * w ^ (-e) * a * (u * w ^ (-e))⁻¹ = a := by
    calc u * w ^ (-e) * a * (u * w ^ (-e))⁻¹ = u * (w ^ (-e) * a * (w ^ (-e))⁻¹) * u⁻¹ := by
          group
      _ = u * z ^ (-e) * a * u⁻¹ := by rw [h1]; group
      _ = z ^ (-e) * (u * a * u⁻¹) := by rw [h2]; group
      _ = a := by rw [hue]; group
  have hga' : u * w ^ (-e) * a = a * (u * w ^ (-e)) := by
    calc u * w ^ (-e) * a = (u * w ^ (-e) * a * (u * w ^ (-e))⁻¹) * (u * w ^ (-e)) := by group
      _ = a * (u * w ^ (-e)) := by rw [hga]
  obtain ⟨v, hv, r, hr, hvr⟩ := hdec _ (mul_mem hu (zpow_mem hwU _)) hga'
  refine ⟨v, hv, r, hr, ?_⟩
  calc u = u * w ^ (-e) * w ^ e := by group
    _ = v * r * w ^ e := by rw [hvr]

theorem t_conj_w (h : SLFactor U a z)
    (hdec : ∀ u ∈ U, u * a = a * u →
      ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, u = v * r)
    {t : X} (htU : ∀ u ∈ U, t * u * t⁻¹ ∈ U) (hta : t * a * t⁻¹ = a)
    (htz : t * z * t⁻¹ = z⁻¹) {w : X} (hwU : w ∈ U) (hwa : w * a * w⁻¹ = z * a) :
    ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, t * w * t⁻¹ = v * r * w⁻¹ := by
  have hyU : t * w * t⁻¹ ∈ U := htU w hwU
  have hta' : t⁻¹ * a * t = a := by
    calc t⁻¹ * a * t = t⁻¹ * (t * a * t⁻¹) * t := by rw [hta]
      _ = a := by group
  have hya : t * w * t⁻¹ * a * (t * w * t⁻¹)⁻¹ = z⁻¹ * a := by
    calc t * w * t⁻¹ * a * (t * w * t⁻¹)⁻¹ = t * w * (t⁻¹ * a * t) * w⁻¹ * t⁻¹ := by group
      _ = t * (w * a * w⁻¹) * t⁻¹ := by rw [hta']; group
      _ = t * (z * a) * t⁻¹ := by rw [hwa]
      _ = (t * z * t⁻¹) * (t * a * t⁻¹) := by group
      _ = z⁻¹ * a := by rw [htz, hta]
  have hyz : t * w * t⁻¹ * z * (t * w * t⁻¹)⁻¹ = z :=
    (show Commute (t * w * t⁻¹) z from h.hzc _ hyU).mul_inv_cancel
  have hga : t * w * t⁻¹ * w * a * (t * w * t⁻¹ * w)⁻¹ = a := by
    calc t * w * t⁻¹ * w * a * (t * w * t⁻¹ * w)⁻¹
        = (t * w * t⁻¹) * (w * a * w⁻¹) * (t * w * t⁻¹)⁻¹ := by group
      _ = (t * w * t⁻¹) * (z * a) * (t * w * t⁻¹)⁻¹ := by rw [hwa]
      _ = (t * w * t⁻¹ * z * (t * w * t⁻¹)⁻¹) * (t * w * t⁻¹ * a * (t * w * t⁻¹)⁻¹) := by
          group
      _ = a := by rw [hyz, hya]; group
  have hga' : t * w * t⁻¹ * w * a = a * (t * w * t⁻¹ * w) := by
    calc t * w * t⁻¹ * w * a
        = (t * w * t⁻¹ * w * a * (t * w * t⁻¹ * w)⁻¹) * (t * w * t⁻¹ * w) := by group
      _ = a * (t * w * t⁻¹ * w) := by rw [hga]
  obtain ⟨v, hv, r, hr, hvr⟩ := hdec _ (mul_mem hyU hwU) hga'
  refine ⟨v, hv, r, hr, ?_⟩
  calc t * w * t⁻¹ = t * w * t⁻¹ * w * w⁻¹ := by group
    _ = v * r * w⁻¹ := by rw [hvr]

end Factor

theorem S_decomp {X : Type} [Group X] {U₁ U₂ : Subgroup X} {a b z : X}
    (hcomm : ∀ u ∈ U₁, ∀ v ∈ U₂, u * v = v * u)
    (hU : ∀ u, u ∈ U₁ → u ∈ U₂ → u ∈ Subgroup.zpowers z)
    (ha : a ∈ U₁) (hb : b ∈ U₂) {s : X} (hs : s ∈ U₁ ⊔ U₂)
    (hsx : s * (a * b) = a * b * s) :
    ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂, ∃ e : ℤ, s = u₁ * u₂ ∧ u₁ * a * u₁⁻¹ = z ^ e * a ∧
      u₂ * b * u₂⁻¹ = z⁻¹ ^ e * b := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_sup_comm hcomm hs
  have hp₂U : u₂ * b * u₂⁻¹ ∈ U₂ := mul_mem (mul_mem hu₂ hb) (inv_mem hu₂)
  have key : u₁ * a * u₁⁻¹ * (u₂ * b * u₂⁻¹) = a * b := by
    have e1 : u₂ * a = a * u₂ := (hcomm a ha u₂ hu₂).symm
    have e2 : u₂ * b * u₂⁻¹ * u₁⁻¹ = u₁⁻¹ * (u₂ * b * u₂⁻¹) :=
      (hcomm u₁⁻¹ (inv_mem hu₁) _ hp₂U).symm
    calc u₁ * a * u₁⁻¹ * (u₂ * b * u₂⁻¹) = u₁ * a * (u₁⁻¹ * (u₂ * b * u₂⁻¹)) := by group
      _ = u₁ * a * (u₂ * b * u₂⁻¹ * u₁⁻¹) := by rw [e2]
      _ = u₁ * (a * u₂) * b * u₂⁻¹ * u₁⁻¹ := by group
      _ = u₁ * (u₂ * a) * b * u₂⁻¹ * u₁⁻¹ := by rw [← e1]
      _ = u₁ * u₂ * (a * b) * (u₁ * u₂)⁻¹ := by group
      _ = a * b := by rw [hsx]; group
  have hc₁ : u₁ * a * u₁⁻¹ * a⁻¹ ∈ U₁ :=
    mul_mem (mul_mem (mul_mem hu₁ ha) (inv_mem hu₁)) (inv_mem ha)
  have hc₂ : u₁ * a * u₁⁻¹ * a⁻¹ = b * (u₂ * b * u₂⁻¹)⁻¹ := by
    have hp₁ : u₁ * a * u₁⁻¹ = a * b * (u₂ * b * u₂⁻¹)⁻¹ := by
      rw [← key]; group
    have e3 : a * (b * (u₂ * b * u₂⁻¹)⁻¹) = b * (u₂ * b * u₂⁻¹)⁻¹ * a :=
      hcomm a ha _ (mul_mem hb (inv_mem hp₂U))
    calc u₁ * a * u₁⁻¹ * a⁻¹ = a * (b * (u₂ * b * u₂⁻¹)⁻¹) * a⁻¹ := by rw [hp₁]; group
      _ = b * (u₂ * b * u₂⁻¹)⁻¹ := by rw [e3]; group
  have hcU₂ : u₁ * a * u₁⁻¹ * a⁻¹ ∈ U₂ := by
    rw [hc₂]
    exact mul_mem hb (inv_mem hp₂U)
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 (hU _ hc₁ hcU₂)
  refine ⟨u₁, hu₁, u₂, hu₂, e, rfl, ?_, ?_⟩
  · calc u₁ * a * u₁⁻¹ = (u₁ * a * u₁⁻¹ * a⁻¹) * a := by group
      _ = z ^ e * a := by rw [he]
  · calc u₂ * b * u₂⁻¹ = (b * (u₂ * b * u₂⁻¹)⁻¹)⁻¹ * b := by group
      _ = z⁻¹ ^ e * b := by rw [← hc₂, ← he, inv_zpow]

end Hering129KN3

theorem endLocalX_of_factors {X : Type} [Group X] [Finite X] {U₁ U₂ : Subgroup X} {a b z t : X}
    (hcomm : ∀ u ∈ U₁, ∀ v ∈ U₂, u * v = v * u)
    (hU : ∀ u, u ∈ U₁ → u ∈ U₂ → u ∈ Subgroup.zpowers z)
    (h1 : SLFactor U₁ a z) (h2 : SLFactor U₂ b z⁻¹)
    (htU₁ : ∀ u ∈ U₁, t * u * t⁻¹ ∈ U₁) (htU₂ : ∀ u ∈ U₂, t * u * t⁻¹ ∈ U₂)
    (hta : t * a * t⁻¹ = a) (htb : t * b * t⁻¹ = b) (htz : t * z * t⁻¹ = z⁻¹)
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) :
    EndLocalX (U₁ ⊔ U₂) (a * b) t z := by
  classical
  obtain ⟨w₁, hw₁U, hw₁3, hw₁a⟩ := h1.hw
  obtain ⟨w₂, hw₂U, hw₂3, hw₂b⟩ := h2.hw
  obtain ⟨R₁, hR₁U, hR₁a, hR₁3, hR₁dec⟩ := h1.hR
  obtain ⟨R₂, hR₂U, hR₂b, hR₂3, hR₂dec⟩ := h2.hR
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := ht2 ⟨t, Subgroup.mem_zpowers t⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  have ha : a ∈ U₁ := h1.ha
  have hz : z ∈ U₁ := h1.hz
  have hb : b ∈ U₂ := h2.ha
  have hzi₂ : z⁻¹ ∈ U₂ := h2.hz
  have hzc₁ : ∀ u ∈ U₁, u * z = z * u := h1.hzc
  have hzc₂ : ∀ u ∈ U₂, u * z = z * u := fun u hu => by
    have h := h2.hzc u hu
    calc u * z = z * (z⁻¹ * u) * z := by group
      _ = z * (u * z⁻¹) * z := by rw [h]
      _ = z * u := by group
  have haz : a * z = z * a := hzc₁ a ha
  have hbzi : b * z⁻¹ = z⁻¹ * b := h2.hzc b hb
  have hw₁₂ : w₁ * w₂ = w₂ * w₁ := hcomm w₁ hw₁U w₂ hw₂U
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup X, S = (U₁ ⊔ U₂) ⊓ Subgroup.centralizer {a * b} :=
    ⟨_, rfl⟩
  have hmemS : ∀ s : X, s ∈ S ↔ s ∈ U₁ ⊔ U₂ ∧ s * (a * b) = a * b * s := fun s => by
    rw [hSdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hU₁S : ∀ u ∈ U₁, u * a = a * u → u ∈ S := fun u hu hua => by
    rw [hmemS]
    refine ⟨Subgroup.mem_sup_left hu, ?_⟩
    calc u * (a * b) = (u * a) * b := by group
      _ = a * (u * b) := by rw [hua]; group
      _ = a * (b * u) := by rw [hcomm u hu b hb]
      _ = a * b * u := by group
  have hU₂S : ∀ u ∈ U₂, u * b = b * u → u ∈ S := fun u hu hub => by
    rw [hmemS]
    refine ⟨Subgroup.mem_sup_right hu, ?_⟩
    calc u * (a * b) = (u * a) * b := by group
      _ = (a * u) * b := by rw [hcomm a ha u hu]
      _ = a * (u * b) := by group
      _ = a * b * u := by rw [hub]; group
  have haS : a ∈ S := hU₁S a ha rfl
  have hbS : b ∈ S := hU₂S b hb rfl
  have hzS : z ∈ S := hU₁S z hz haz.symm
  have hwS : w₁ * w₂ ∈ S := by
    rw [hmemS]
    refine ⟨mul_mem (Subgroup.mem_sup_left hw₁U) (Subgroup.mem_sup_right hw₂U), ?_⟩
    have e1 : w₁ * a = z * a * w₁ := by rw [← hw₁a]; group
    have e2 : w₂ * b = z⁻¹ * b * w₂ := by rw [← hw₂b]; group
    have e3 : w₂ * a = a * w₂ := (hcomm a ha w₂ hw₂U).symm
    have e4 : w₁ * z⁻¹ = z⁻¹ * w₁ := hcomm w₁ hw₁U z⁻¹ hzi₂
    have e5 : w₁ * b = b * w₁ := hcomm w₁ hw₁U b hb
    calc w₁ * w₂ * (a * b) = w₁ * (w₂ * a) * b := by group
      _ = (w₁ * a) * (w₂ * b) := by rw [e3]; group
      _ = z * a * (w₁ * z⁻¹) * b * w₂ := by rw [e1, e2]; group
      _ = z * a * z⁻¹ * (w₁ * b) * w₂ := by rw [e4]; group
      _ = (z * a * z⁻¹) * b * w₁ * w₂ := by rw [e5]; group
      _ = a * b * (w₁ * w₂) := by rw [← haz]; group
  have hzU : ∀ s ∈ U₁ ⊔ U₂, s * z = z * s := by
    have hle : U₁ ⊔ U₂ ≤ Subgroup.centralizer {z} :=
      sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 (hzc₁ u hu))
        (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 (hzc₂ u hu))
    exact fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (hle hs)
  have hR₁S : R₁ ≤ S := fun r hr => hU₁S r (hR₁U hr) (hR₁a r hr)
  have hR₂S : R₂ ≤ S := fun r hr => hU₂S r (hR₂U hr) (hR₂b r hr)
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup X, R = R₁ ⊔ R₂ := ⟨_, rfl⟩
  have hR₁R : R₁ ≤ R := hRdef ▸ le_sup_left
  have hR₂R : R₂ ≤ R := hRdef ▸ le_sup_right
  have hRS : R ≤ S := hRdef ▸ sup_le hR₁S hR₂S
  have hR3 : ¬ 3 ∣ Nat.card R := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hgR : (g : X) ∈ R₁ ⊔ R₂ := hRdef ▸ g.2
    obtain ⟨r₁, hr₁, r₂, hr₂, hg'⟩ :=
      mem_sup_comm (fun x hx y hy => hcomm x (hR₁U hx) y (hR₂U hy)) hgR
    have e1 : r₁ ^ (Nat.card R₁ * Nat.card R₂) = 1 := by
      rw [pow_mul, pow_card_eq_one_of_mem hr₁, one_pow]
    have e2 : r₂ ^ (Nat.card R₁ * Nat.card R₂) = 1 := by
      rw [mul_comm, pow_mul, pow_card_eq_one_of_mem hr₂, one_pow]
    have hgN : (g : X) ^ (Nat.card R₁ * Nat.card R₂) = 1 := by
      rw [hg', (show Commute r₁ r₂ from hcomm r₁ (hR₁U hr₁) r₂ (hR₂U hr₂)).mul_pow, e1, e2,
        one_mul]
    have h' : 3 ∣ Nat.card R₁ * Nat.card R₂ := by
      rw [← hg, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hgN
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h' with h | h
    exacts [hR₁3 h, hR₂3 h]
  have htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := by
    rw [hRdef]
    exact conj_mem_sup
      (fun u hu => Subgroup.mem_sup_left (t_conj_R h1 hR₁U hR₁a hR₁3 hR₁dec htU₁ hta hu))
      (fun u hu => Subgroup.mem_sup_right (t_conj_R h2 hR₂U hR₂b hR₂3 hR₂dec htU₂ htb hu))
  have htR' : ∀ r ∈ R, t⁻¹ * r * t ∈ R := conj_inv_mem hm htR
  have htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S := by
    intro s hs
    rw [hmemS] at hs ⊢
    obtain ⟨hsU, hsx⟩ := hs
    refine ⟨conj_mem_sup (fun u hu => Subgroup.mem_sup_left (htU₁ u hu))
      (fun u hu => Subgroup.mem_sup_right (htU₂ u hu)) s hsU, ?_⟩
    have htx : t * (a * b) * t⁻¹ = a * b := by
      calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
        _ = a * b := by rw [hta, htb]
    calc t * s * t⁻¹ * (a * b) = t * s * t⁻¹ * (t * (a * b) * t⁻¹) := by rw [htx]
      _ = t * (s * (a * b)) * t⁻¹ := by group
      _ = t * (a * b * s) * t⁻¹ := by rw [hsx]
      _ = (t * (a * b) * t⁻¹) * (t * s * t⁻¹) := by group
      _ = a * b * (t * s * t⁻¹) := by rw [htx]
  have htS' : ∀ s ∈ S, t⁻¹ * s * t ∈ S := conj_inv_mem hm htS
  have hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs
    rw [hmemS] at hs
    obtain ⟨u₁, hu₁, u₂, hu₂, e, rfl, hu₁a, hu₂b⟩ := S_decomp hcomm hU ha hb hs.1 hs.2
    rw [hRdef]
    apply conj_mem_sup
    · intro r hr
      have h' : u₁ * u₂ * r * (u₁ * u₂)⁻¹ = u₁ * r * u₁⁻¹ := by
        have e' : u₂ * r = r * u₂ := (hcomm r (hR₁U hr) u₂ hu₂).symm
        calc u₁ * u₂ * r * (u₁ * u₂)⁻¹ = u₁ * (u₂ * r) * u₂⁻¹ * u₁⁻¹ := by group
          _ = u₁ * r * u₁⁻¹ := by rw [e']; group
      rw [h']
      exact Subgroup.mem_sup_left (conj_mem_R h1 hR₁U hR₁a hR₁3 hR₁dec hu₁ hu₁a hr)
    · intro r hr
      have h' : u₁ * u₂ * r * (u₁ * u₂)⁻¹ = u₂ * r * u₂⁻¹ := by
        have hy : u₂ * r * u₂⁻¹ ∈ U₂ := mul_mem (mul_mem hu₂ (hR₂U hr)) (inv_mem hu₂)
        have e' : u₁ * (u₂ * r * u₂⁻¹) = (u₂ * r * u₂⁻¹) * u₁ := hcomm u₁ hu₁ _ hy
        calc u₁ * u₂ * r * (u₁ * u₂)⁻¹ = (u₁ * (u₂ * r * u₂⁻¹)) * u₁⁻¹ := by group
          _ = u₂ * r * u₂⁻¹ := by rw [e']; group
      rw [h']
      exact Subgroup.mem_sup_right (conj_mem_R h2 hR₂U hR₂b hR₂3 hR₂dec hu₂ hu₂b hr)
  have hRSn : (R.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hRn g g.2 n hn⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : S →* S ⧸ R.subgroupOf S, ρ = QuotientGroup.mk' (R.subgroupOf S) :=
    ⟨_, rfl⟩
  have hρsurj : Function.Surjective ρ := hρ ▸ QuotientGroup.mk'_surjective _
  have hρone : ∀ s : S, ρ s = 1 ↔ (s : X) ∈ R := fun s => by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  obtain ⟨σ, hσ, hσ'⟩ : ∃ σ : S ≃* S, (∀ s : S, (σ s : X) = t * s * t⁻¹) ∧
      (∀ s : S, (σ.symm s : X) = t⁻¹ * s * t) :=
    ⟨{ toFun := fun s => ⟨t * s * t⁻¹, htS s s.2⟩
       invFun := fun s => ⟨t⁻¹ * s * t, htS' s s.2⟩
       left_inv := fun s => Subtype.ext (by
         show t⁻¹ * (t * (s : X) * t⁻¹) * t = s
         group)
       right_inv := fun s => Subtype.ext (by
         show t * (t⁻¹ * (s : X) * t) * t⁻¹ = s
         group)
       map_mul' := fun s s' => Subtype.ext (by
         show t * ((s : X) * s') * t⁻¹ = t * s * t⁻¹ * (t * s' * t⁻¹)
         group) }, fun s => rfl, fun s => rfl⟩
  have hσR : (R.subgroupOf S).map (σ : S →* S) = R.subgroupOf S := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr
      rw [Subgroup.mem_subgroupOf]
      show ((σ r : S) : X) ∈ R
      rw [hσ]
      exact htR r hr
    · intro r hr
      refine ⟨σ.symm r, ?_, by simp⟩
      rw [Subgroup.mem_subgroupOf] at hr
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hσ']
      exact htR' r hr
  obtain ⟨τ, hτρ⟩ : ∃ τ : (S ⧸ R.subgroupOf S) ≃* (S ⧸ R.subgroupOf S),
      ∀ s : S, τ (ρ s) = ρ (σ s) :=
    ⟨QuotientGroup.congr (R.subgroupOf S) (R.subgroupOf S) σ hσR, fun s => by rw [hρ]; rfl⟩
  have hτn : ∀ n : ℕ, ∀ s : S,
      (τ ^ n) (ρ s) = ρ ⟨t ^ n * s * (t ^ n)⁻¹, conj_pow_mem htS n s s.2⟩ := by
    intro n
    induction n with
    | zero =>
      intro s
      rw [pow_zero, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      show (s : X) = t ^ 0 * s * (t ^ 0)⁻¹
      group
    | succ n ih =>
      intro s
      rw [pow_succ', MulAut.mul_apply, ih, hτρ]
      congr 1
      apply Subtype.ext
      rw [hσ]
      show t * (t ^ n * s * (t ^ n)⁻¹) * t⁻¹ = t ^ (n + 1) * s * (t ^ (n + 1))⁻¹
      rw [pow_succ']
      group
  have hτ2 : (τ ^ (2 ^ m) : _ ≃* _) = 1 := by
    apply MulEquiv.ext
    intro q
    obtain ⟨s, rfl⟩ := hρsurj q
    rw [hτn, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show t ^ (2 ^ m) * s * (t ^ (2 ^ m))⁻¹ = s
    rw [hm]
    group
  let sa : S := ⟨a, haS⟩
  let sb : S := ⟨b, hbS⟩
  let sz : S := ⟨z, hzS⟩
  let sw : S := ⟨w₁ * w₂, hwS⟩
  have sab : sa * sb = sb * sa := Subtype.ext (hcomm a ha b hb)
  have saz : sa * sz = sz * sa := Subtype.ext haz
  have sbz : sb * sz = sz * sb := Subtype.ext (hzc₂ b hb)
  have sa3 : sa ^ 3 = 1 := Subtype.ext h1.ha3
  have sb3 : sb ^ 3 = 1 := Subtype.ext h2.ha3
  have sz3 : sz ^ 3 = 1 := Subtype.ext h1.hz3
  have sw3 : sw ^ 3 = 1 := Subtype.ext (by
    show (w₁ * w₂) ^ 3 = 1
    rw [(show Commute w₁ w₂ from hw₁₂).mul_pow, hw₁3, hw₂3, one_mul])
  have swa : sw * sa * sw⁻¹ = sz * sa := Subtype.ext (by
    show w₁ * w₂ * a * (w₁ * w₂)⁻¹ = z * a
    calc w₁ * w₂ * a * (w₁ * w₂)⁻¹ = w₁ * (w₂ * a * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * a * w₁⁻¹ := by
          rw [(show Commute a w₂ from hcomm a ha w₂ hw₂U).symm.mul_inv_cancel]
      _ = z * a := hw₁a)
  have swb : sw * sb * sw⁻¹ = sz⁻¹ * sb := Subtype.ext (by
    show w₁ * w₂ * b * (w₁ * w₂)⁻¹ = z⁻¹ * b
    calc w₁ * w₂ * b * (w₁ * w₂)⁻¹ = w₁ * (w₂ * b * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * (z⁻¹ * b) * w₁⁻¹ := by rw [hw₂b]
      _ = z⁻¹ * b :=
          (show Commute w₁ (z⁻¹ * b) from hcomm w₁ hw₁U _ (mul_mem hzi₂ hb)).mul_inv_cancel)
  have swz : sw * sz = sz * sw := Subtype.ext (by
    show w₁ * w₂ * z = z * (w₁ * w₂)
    calc w₁ * w₂ * z = w₁ * (w₂ * z) := by group
      _ = w₁ * (z * w₂) := by rw [hzc₂ w₂ hw₂U]
      _ = (w₁ * z) * w₂ := by group
      _ = (z * w₁) * w₂ := by rw [hzc₁ w₁ hw₁U]
      _ = z * (w₁ * w₂) := by group)
  have σa : σ sa = sa := Subtype.ext (by rw [hσ]; exact hta)
  have σb : σ sb = sb := Subtype.ext (by rw [hσ]; exact htb)
  have σz : σ sz = sz⁻¹ := Subtype.ext (by rw [hσ]; exact htz)
  have htzi : t * z⁻¹ * t⁻¹ = z⁻¹⁻¹ := by
    calc t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ := by group
      _ = z⁻¹⁻¹ := by rw [htz]
  obtain ⟨v₁', hv₁', r₁', hr₁', ht₁⟩ := t_conj_w h1 hR₁dec htU₁ hta htz hw₁U hw₁a
  obtain ⟨v₂', hv₂', r₂', hr₂', ht₂⟩ := t_conj_w h2 hR₂dec htU₂ htb htzi hw₂U hw₂b
  obtain ⟨i, k, hv₁'eq⟩ := exists_zpow_of_mem_sup haz hv₁'
  obtain ⟨j, l, hv₂'eq⟩ := exists_zpow_of_mem_sup hbzi hv₂'
  have hv₂'U : v₂' ∈ U₂ := (sup_le (Subgroup.zpowers_le.2 hb) (Subgroup.zpowers_le.2 hzi₂)) hv₂'
  have htw : t * (w₁ * w₂) * t⁻¹ =
      a ^ i * z ^ k * r₁' * (b ^ j * z⁻¹ ^ l * r₂') * (w₁ * w₂)⁻¹ := by
    have hy₂ : v₂' * r₂' ∈ U₂ := mul_mem hv₂'U (hR₂U hr₂')
    have e1 : w₁⁻¹ * (v₂' * r₂') = (v₂' * r₂') * w₁⁻¹ := hcomm _ (inv_mem hw₁U) _ hy₂
    have e2 : w₁⁻¹ * w₂⁻¹ = (w₁ * w₂)⁻¹ := by
      rw [mul_inv_rev]
      exact hcomm _ (inv_mem hw₁U) _ (inv_mem hw₂U)
    calc t * (w₁ * w₂) * t⁻¹ = (t * w₁ * t⁻¹) * (t * w₂ * t⁻¹) := by group
      _ = v₁' * r₁' * w₁⁻¹ * (v₂' * r₂' * w₂⁻¹) := by rw [ht₁, ht₂]
      _ = v₁' * r₁' * (w₁⁻¹ * (v₂' * r₂')) * w₂⁻¹ := by group
      _ = v₁' * r₁' * ((v₂' * r₂') * w₁⁻¹) * w₂⁻¹ := by rw [e1]
      _ = v₁' * r₁' * (v₂' * r₂') * (w₁⁻¹ * w₂⁻¹) := by group
      _ = a ^ i * z ^ k * r₁' * (b ^ j * z⁻¹ ^ l * r₂') * (w₁ * w₂)⁻¹ := by
          rw [e2, hv₁'eq, hv₂'eq]
  let sr₁ : S := ⟨r₁', hR₁S hr₁'⟩
  let sr₂ : S := ⟨r₂', hR₂S hr₂'⟩
  have hρr₁ : ρ sr₁ = 1 := (hρone sr₁).2 (hR₁R hr₁')
  have hρr₂ : ρ sr₂ = 1 := (hρone sr₂).2 (hR₂R hr₂')
  have σw : σ sw = sa ^ i * sz ^ k * sr₁ * (sb ^ j * sz⁻¹ ^ l * sr₂) * sw⁻¹ :=
    Subtype.ext (by rw [hσ]; exact htw)
  have hZ1 : ρ sz ≠ 1 := by
    intro h
    have hzR : z ∈ R := (hρone sz).1 h
    have hcop : Nat.Coprime (Nat.card R) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hR3).symm
    exact h1.hz1 ((pow_eq_one_iff_of_coprime hcop).1 ⟨pow_card_eq_one_of_mem hzR, h1.hz3⟩)
  have hgen : Subgroup.closure ({ρ sa, ρ sb, ρ sz, ρ sw} : Set (S ⧸ R.subgroupOf S)) = ⊤ := by
    obtain ⟨C, hC⟩ : ∃ C : Subgroup (S ⧸ R.subgroupOf S),
        C = Subgroup.closure ({ρ sa, ρ sb, ρ sz, ρ sw} : Set (S ⧸ R.subgroupOf S)) :=
      ⟨_, rfl⟩
    rw [← hC]
    obtain ⟨P, hPdef⟩ : ∃ P : Subgroup X, P = (C.comap ρ).map S.subtype := ⟨_, rfl⟩
    have hP : ∀ s : S, (s : X) ∈ P → ρ s ∈ C := by
      intro s hs
      rw [hPdef] at hs
      obtain ⟨s', hs', hss'⟩ := Subgroup.mem_map.1 hs
      have h' : s' = s := Subtype.ext hss'
      rw [← h']
      exact hs'
    have hgP : ∀ s : S, ρ s ∈ C → (s : X) ∈ P := fun s hs => by
      rw [hPdef]
      exact ⟨s, hs, rfl⟩
    have haP : a ∈ P := hgP sa (hC ▸ Subgroup.subset_closure (by simp))
    have hbP : b ∈ P := hgP sb (hC ▸ Subgroup.subset_closure (by simp))
    have hzP : z ∈ P := hgP sz (hC ▸ Subgroup.subset_closure (by simp))
    have hwP : w₁ * w₂ ∈ P := hgP sw (hC ▸ Subgroup.subset_closure (by simp))
    have hRP : ∀ r ∈ R, r ∈ P := fun r hr =>
      hgP ⟨r, hRS hr⟩ (by rw [(hρone ⟨r, hRS hr⟩).2 hr]; exact one_mem C)
    rw [eq_top_iff]
    rintro q -
    obtain ⟨s, rfl⟩ := hρsurj q
    apply hP
    have hs := (hmemS s).1 s.2
    obtain ⟨u₁, hu₁, u₂, hu₂, e, hsu, hu₁a, hu₂b⟩ := S_decomp hcomm hU ha hb hs.1 hs.2
    obtain ⟨v₁, hv₁, r₁, hr₁, hu₁eq⟩ := decomp_factor h1 hR₁dec hw₁U hw₁a hu₁ hu₁a
    obtain ⟨v₂, hv₂, r₂, hr₂, hu₂eq⟩ := decomp_factor h2 hR₂dec hw₂U hw₂b hu₂ hu₂b
    have hv₂U : v₂ ∈ U₂ :=
      (sup_le (Subgroup.zpowers_le.2 hb) (Subgroup.zpowers_le.2 hzi₂)) hv₂
    have hs' : (s : X) = v₁ * r₁ * (v₂ * r₂) * (w₁ * w₂) ^ e := by
      rw [hsu, hu₁eq, hu₂eq]
      have e1 : w₁ ^ e * (v₂ * r₂) = (v₂ * r₂) * w₁ ^ e :=
        hcomm _ (zpow_mem hw₁U e) _ (mul_mem hv₂U (hR₂U hr₂))
      calc v₁ * r₁ * w₁ ^ e * (v₂ * r₂ * w₂ ^ e)
          = v₁ * r₁ * (w₁ ^ e * (v₂ * r₂)) * w₂ ^ e := by group
        _ = v₁ * r₁ * ((v₂ * r₂) * w₁ ^ e) * w₂ ^ e := by rw [e1]
        _ = v₁ * r₁ * (v₂ * r₂) * (w₁ ^ e * w₂ ^ e) := by group
        _ = v₁ * r₁ * (v₂ * r₂) * (w₁ * w₂) ^ e := by
            rw [(show Commute w₁ w₂ from hw₁₂).mul_zpow]
    rw [hs']
    have hv₁P : v₁ ∈ P := (sup_le (Subgroup.zpowers_le.2 haP) (Subgroup.zpowers_le.2 hzP)) hv₁
    have hv₂P : v₂ ∈ P :=
      (sup_le (Subgroup.zpowers_le.2 hbP) (Subgroup.zpowers_le.2 (inv_mem hzP))) hv₂
    exact mul_mem (mul_mem (mul_mem hv₁P (hRP r₁ (hR₁R hr₁)))
      (mul_mem hv₂P (hRP r₂ (hR₂R hr₂)))) (zpow_mem hwP e)
  have hAB : ρ sa * ρ sb = ρ sb * ρ sa := by rw [← map_mul, ← map_mul, sab]
  have hAZ : ρ sa * ρ sz = ρ sz * ρ sa := by rw [← map_mul, ← map_mul, saz]
  have hBZ : ρ sb * ρ sz = ρ sz * ρ sb := by rw [← map_mul, ← map_mul, sbz]
  have hA3 : ρ sa ^ 3 = 1 := by rw [← map_pow, sa3, map_one]
  have hB3 : ρ sb ^ 3 = 1 := by rw [← map_pow, sb3, map_one]
  have hZ3 : ρ sz ^ 3 = 1 := by rw [← map_pow, sz3, map_one]
  have hW3 : ρ sw ^ 3 = 1 := by rw [← map_pow, sw3, map_one]
  have hWA : ρ sw * ρ sa * (ρ sw)⁻¹ = ρ sz * ρ sa := by
    rw [← map_inv, ← map_mul, ← map_mul, swa, map_mul]
  have hWB : ρ sw * ρ sb * (ρ sw)⁻¹ = (ρ sz)⁻¹ * ρ sb := by
    rw [← map_inv, ← map_mul, ← map_mul, swb, map_mul, map_inv]
  have hWZ : ρ sw * ρ sz = ρ sz * ρ sw := by rw [← map_mul, ← map_mul, swz]
  have hτA : τ (ρ sa) = ρ sa := by rw [hτρ, σa]
  have hτB : τ (ρ sb) = ρ sb := by rw [hτρ, σb]
  have hτZ : τ (ρ sz) = (ρ sz)⁻¹ := by rw [hτρ, σz, map_inv]
  have hτW : τ (ρ sw) =
      ρ sa ^ i * ρ sz ^ k * (ρ sb ^ j * (ρ sz)⁻¹ ^ l) * (ρ sw)⁻¹ := by
    rw [hτρ, σw]
    simp only [map_mul, map_zpow, map_inv, hρr₁, hρr₂, mul_one]
  obtain ⟨hcard, hcommE, hexpE, hinvE, hzE⟩ := quot_algebra τ m hτ2 hAB hAZ hBZ hA3 hB3 hZ3
    hZ1 hW3 hWA hWB hWZ hτA hτB hτZ hτW hgen
  haveI := hRSn
  refine ⟨S, hzS, S ⧸ R.subgroupOf S, inferInstance, inferInstance, ρ, τ,
    fun s hs => ((hmemS s).1 hs).1, fun s hs => ((hmemS s).1 hs).2.symm,
    fun s hs => (hzU s ((hmemS s).1 hs).1).symm, htS, hρsurj, ?_, ?_, hcard, hcommE, hexpE,
    hinvE, hzE⟩
  · rw [hρ, QuotientGroup.ker_mk', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv]
    exact hR3
  · intro s hs
    rw [hτρ]
    congr 1
    exact Subtype.ext (hσ s).symm

end CFSG.RankThree.PartTwo.Sec12
