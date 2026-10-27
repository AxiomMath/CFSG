module

public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQTools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof

structure Loc2129 {G : Type} [Group G] (F H Q Y : Subgroup G) (e d : G) : Prop where
  comm_F : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  pow_F : ∀ x ∈ F, x ^ 3 = 1
  card_F : Nat.card F = 27
  le_H : H ≤ F
  card_H : Nat.card H = 9
  mem_e : e ∈ F
  not_mem_e : e ∉ H
  mem_d : d ∈ H
  ne_one_d : d ≠ 1
  le_Q : Q ≤ Y
  le_F_Q : F ≤ Q
  card_Q : Nat.card Q = 243
  extra_Q : IsExtraspecialPGroup 3 Q
  pow_Q : ∀ q ∈ Q, q ^ 3 = 1
  conj_d : ∀ q ∈ Q, q * d * q⁻¹ = d
  conj_e_Q : ∀ q ∈ Q, e⁻¹ * (q * e * q⁻¹) ∈ Subgroup.zpowers d
  le_normalizer : Y ≤ Subgroup.normalizer (F : Set G)
  triv : ∀ y ∈ Y, ∀ x ∈ F, x⁻¹ * (y * x * y⁻¹) ∈ H
  trans : ∀ v ∈ H, ∀ w ∈ H, v ≠ 1 → w ≠ 1 → ∃ m ∈ Y, m * e = e * m ∧ m * v * m⁻¹ = w
  le_F : ∀ X : Subgroup G, IsPGroup 3 X → X ≤ Subgroup.centralizer (F : Set G) → X ≤ F
  card_le_27 : ∀ X : Subgroup G, IsPGroup 3 X → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
    X ≤ Subgroup.centralizer ({e} : Set G) → Nat.card X ≤ 27
  card_le_729 : ∀ X : Subgroup G, IsPGroup 3 X → X ≤ Y → Nat.card X ≤ 729
  exists_t : ∃ t ∈ Y, ∀ h ∈ H, t * h * t⁻¹ = h⁻¹

namespace Loc2129

variable {G : Type} [Group G] {F H Q Y : Subgroup G} {e d : G}

theorem comm_H (hL : Loc2129 F H Q Y e d) : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x :=
  fun x hx y hy => hL.comm_F x (hL.le_H hx) y (hL.le_H hy)

theorem pow_H (hL : Loc2129 F H Q Y e d) : ∀ x ∈ H, x ^ 3 = 1 :=
  fun x hx => hL.pow_F x (hL.le_H hx)

theorem isPGroup_of_pow {X : Subgroup G} (hX : ∀ x ∈ X, x ^ 3 = 1) : IsPGroup 3 X :=
  fun g => ⟨1, Subtype.ext (by simpa using hX _ g.2)⟩

theorem isPGroup_zpowers {x : G} {n : ℕ} (hx : x ^ 3 ^ n = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  intro g
  refine ⟨n, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx,
    one_zpow, Subgroup.coe_one]

theorem isPGroup_F (hL : Loc2129 F H Q Y e d) : IsPGroup 3 F := isPGroup_of_pow hL.pow_F

theorem le_F_Y (hL : Loc2129 F H Q Y e d) : F ≤ Y := hL.le_F_Q.trans hL.le_Q

theorem le_F_centralizer (hL : Loc2129 F H Q Y e d) :
    F ≤ Subgroup.centralizer (H : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun h hh => hL.comm_F h (hL.le_H hh) x hx

theorem conj_mem_H (hL : Loc2129 F H Q Y e d) {y h : G} (hy : y ∈ Y) (hh : h ∈ H) :
    y * h * y⁻¹ ∈ H := by
  have e1 : y * h * y⁻¹ = h * (h⁻¹ * (y * h * y⁻¹)) := by group
  rw [e1]
  exact H.mul_mem hh (hL.triv y hy h (hL.le_H hh))

theorem conj_mem_F (hL : Loc2129 F H Q Y e d) {y x : G} (hy : y ∈ Y) (hx : x ∈ F) :
    y * x * y⁻¹ ∈ F :=
  (Subgroup.mem_normalizer_iff.mp (hL.le_normalizer hy) x).mp hx

theorem kap_mem (hL : Loc2129 F H Q Y e d) {y : G} (hy : y ∈ Y) :
    e⁻¹ * (y * e * y⁻¹) ∈ H :=
  hL.triv y hy e hL.mem_e

theorem sup_zpowers_e [Finite G] (hL : Loc2129 F H Q Y e d) :
    H ⊔ Subgroup.zpowers e = F := by
  have hle : H ⊔ Subgroup.zpowers e ≤ F := sup_le hL.le_H (Subgroup.zpowers_le.mpr hL.mem_e)
  have hlt : H < H ⊔ Subgroup.zpowers e := by
    refine lt_of_le_of_ne le_sup_left fun h => hL.not_mem_e ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := Subgroup.card_dvd_of_le hle
  rw [hL.card_H] at h1
  rw [hL.card_F] at h2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hL.card_F]
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card (H ⊔ Subgroup.zpowers e : Subgroup G) ∣ 3 ^ 3 by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact h2)
  rw [hke] at h1 ⊢
  interval_cases k <;> revert h1 <;> norm_num

theorem mem_centralizer_F [Finite G] (hL : Loc2129 F H Q Y e d) {x : G}
    (hxH : x ∈ Subgroup.centralizer (H : Set G)) (hxe : x * e = e * x) :
    x ∈ Subgroup.centralizer (F : Set G) := by
  have hle : H ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun h hh => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxH h hh)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxe.symm
  rw [hL.sup_zpowers_e] at hle
  exact Subgroup.mem_centralizer_iff.mpr fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hf)

theorem kap_mul (hL : Loc2129 F H Q Y e d) {x y : G} (hx : x ∈ Y)
    (hxH : x ∈ Subgroup.centralizer (H : Set G)) (hy : y ∈ Y) :
    e⁻¹ * (x * y * e * (x * y)⁻¹) = (e⁻¹ * (x * e * x⁻¹)) * (e⁻¹ * (y * e * y⁻¹)) := by
  set a := e⁻¹ * (y * e * y⁻¹) with ha
  have haH : a ∈ H := hL.kap_mem hy
  have hya : y * e * y⁻¹ = e * a := by rw [ha]; group
  have hxa : x * a * x⁻¹ = a := by
    rw [(Subgroup.mem_centralizer_iff.mp hxH a haH).symm]
    group
  have _ := hx
  calc e⁻¹ * (x * y * e * (x * y)⁻¹) = e⁻¹ * (x * (y * e * y⁻¹) * x⁻¹) := by group
    _ = e⁻¹ * (x * (e * a) * x⁻¹) := by rw [hya]
    _ = e⁻¹ * (x * e * x⁻¹) * (x * a * x⁻¹) := by group
    _ = e⁻¹ * (x * e * x⁻¹) * a := by rw [hxa]

@[expose] def kapHom (hL : Loc2129 F H Q Y e d) (X : Subgroup G) (hXY : X ≤ Y)
    (hXH : X ≤ Subgroup.centralizer (H : Set G)) : X →* H where
  toFun x := ⟨e⁻¹ * ((x : G) * e * (x : G)⁻¹), hL.kap_mem (hXY x.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hL.kap_mul (hXY x.2) (hXH x.2) (hXY y.2)

theorem kapHom_apply (hL : Loc2129 F H Q Y e d) {X : Subgroup G} (hXY : X ≤ Y)
    (hXH : X ≤ Subgroup.centralizer (H : Set G)) (x : X) :
    ((hL.kapHom X hXY hXH x : H) : G) = e⁻¹ * ((x : G) * e * (x : G)⁻¹) :=
  rfl

theorem kap_eq_one_iff {x : G} : e⁻¹ * (x * e * x⁻¹) = 1 ↔ x * e = e * x := by
  constructor
  · intro h
    have h1 : x * e * x⁻¹ = e := by
      calc x * e * x⁻¹ = e * (e⁻¹ * (x * e * x⁻¹)) := by group
        _ = e := by rw [h, mul_one]
    calc x * e = x * e * x⁻¹ * x := by group
      _ = e * x := by rw [h1]
  · intro h
    rw [h]
    group

theorem card_ker_le [Finite G] (hL : Loc2129 F H Q Y e d) {X : Subgroup G} (hX3 : IsPGroup 3 X)
    (hXY : X ≤ Y) (hXH : X ≤ Subgroup.centralizer (H : Set G)) :
    Nat.card (hL.kapHom X hXY hXH).ker ≤ 27 := by
  have hK3 : IsPGroup 3 ((hL.kapHom X hXY hXH).ker.map X.subtype) :=
    (hX3.to_subgroup _).map X.subtype
  have hKC : (hL.kapHom X hXY hXH).ker.map X.subtype ≤ Subgroup.centralizer (F : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : hL.kapHom X hXY hXH x = 1 := hx
    have hx2 : e⁻¹ * ((x : G) * e * (x : G)⁻¹) = 1 := by
      rw [← hL.kapHom_apply hXY hXH x, hx1, Subgroup.coe_one]
    exact hL.mem_centralizer_F (hXH x.2) (kap_eq_one_iff.mp hx2)
  have hKF := hL.le_F _ hK3 hKC
  rw [← hL.card_F, ← Subgroup.card_map_of_injective X.subtype_injective]
  exact Subgroup.card_le_of_le hKF

theorem card_le_243 [Finite G] (hL : Loc2129 F H Q Y e d) {X : Subgroup G} (hX3 : IsPGroup 3 X)
    (hXY : X ≤ Y) (hXH : X ≤ Subgroup.centralizer (H : Set G)) : Nat.card X ≤ 243 := by
  have h1 := Item2119End6Proof.card_eq_card_ker_mul_card_range (hL.kapHom X hXY hXH)
  have h2 := hL.card_ker_le hX3 hXY hXH
  have h3 : Nat.card (hL.kapHom X hXY hXH).range ≤ 9 := by
    rw [← hL.card_H]
    exact Subgroup.card_le_card_group _
  rw [h1]
  calc Nat.card (hL.kapHom X hXY hXH).ker * Nat.card (hL.kapHom X hXY hXH).range
      ≤ 27 * 9 := Nat.mul_le_mul h2 h3
    _ = 243 := by norm_num

theorem kap_conj (hL : Loc2129 F H Q Y e d) {x y : G} (hx : x ∈ Y)
    (hxH : x ∈ Subgroup.centralizer (H : Set G)) (hy : y ∈ Y) :
    e⁻¹ * (y * x * y⁻¹ * e * (y * x * y⁻¹)⁻¹) = y * (e⁻¹ * (x * e * x⁻¹)) * y⁻¹ := by
  set a := e⁻¹ * (x * e * x⁻¹) with ha
  set u := e⁻¹ * (y⁻¹ * e * y) with hu
  have haH : a ∈ H := hL.kap_mem hx
  have huH : u ∈ H := by
    have h := hL.kap_mem (Y.inv_mem hy)
    rwa [inv_inv] at h
  have hyu : y⁻¹ * e * y = e * u := by rw [hu]; group
  have hxe : x * e * x⁻¹ = e * a := by rw [ha]; group
  have hxu : x * u * x⁻¹ = u := by
    rw [(Subgroup.mem_centralizer_iff.mp hxH u huH).symm]
    group
  have hcomm : (y * u * y⁻¹) * (y * a * y⁻¹) = (y * a * y⁻¹) * (y * u * y⁻¹) :=
    hL.comm_H _ (hL.conj_mem_H hy huH) _ (hL.conj_mem_H hy haH)
  have hyeu : (y * e * y⁻¹) * (y * u * y⁻¹) = e := by
    calc (y * e * y⁻¹) * (y * u * y⁻¹) = y * (e * u) * y⁻¹ := by group
      _ = y * (y⁻¹ * e * y) * y⁻¹ := by rw [hyu]
      _ = e := by group
  calc e⁻¹ * (y * x * y⁻¹ * e * (y * x * y⁻¹)⁻¹)
      = e⁻¹ * (y * (x * (y⁻¹ * e * y) * x⁻¹) * y⁻¹) := by group
    _ = e⁻¹ * (y * (x * (e * u) * x⁻¹) * y⁻¹) := by rw [hyu]
    _ = e⁻¹ * (y * ((x * e * x⁻¹) * (x * u * x⁻¹)) * y⁻¹) := by group
    _ = e⁻¹ * (y * ((e * a) * u) * y⁻¹) := by rw [hxe, hxu]
    _ = e⁻¹ * ((y * e * y⁻¹) * ((y * a * y⁻¹) * (y * u * y⁻¹))) := by group
    _ = e⁻¹ * ((y * e * y⁻¹) * ((y * u * y⁻¹) * (y * a * y⁻¹))) := by rw [hcomm]
    _ = e⁻¹ * (((y * e * y⁻¹) * (y * u * y⁻¹)) * (y * a * y⁻¹)) := by group
    _ = e⁻¹ * (e * (y * a * y⁻¹)) := by rw [hyeu]
    _ = y * a * y⁻¹ := by group

theorem sup_zpowers_eq_H [Finite G] (hL : Loc2129 F H Q Y e d) {a : G} (ha : a ∈ H)
    (had : a ∉ Subgroup.zpowers d) : Subgroup.zpowers a ⊔ Subgroup.zpowers d = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hL.mem_d)
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hL.pow_H d hL.mem_d) hL.ne_one_d]
  have hlt : Subgroup.zpowers d < Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    refine lt_of_le_of_ne le_sup_right fun h => had ?_
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := Subgroup.card_dvd_of_le hle
  rw [hd3] at h1
  rw [hL.card_H] at h2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hL.card_H]
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers d : Subgroup G) ∣ 3 ^ 2 by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h2)
  rw [hke] at h1 ⊢
  interval_cases k <;> revert h1 <;> norm_num

theorem exists_mem_H_not_mem [Finite G] (hL : Loc2129 F H Q Y e d) :
    ∃ a ∈ H, a ∉ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h
  push Not at h
  have hle : H ≤ Subgroup.zpowers d := fun a ha => h a ha
  have h1 := Subgroup.card_le_of_le hle
  rw [hL.card_H, Nat.card_zpowers, orderOf_eq_prime (hL.pow_H d hL.mem_d) hL.ne_one_d] at h1
  omega

theorem mem_centralizer_H [Finite G] (hL : Loc2129 F H Q Y e d) {a x : G} (ha : a ∈ H)
    (had : a ∉ Subgroup.zpowers d) (hxa : x * a = a * x) (hxd : x * d = d * x) :
    x ∈ Subgroup.centralizer (H : Set G) := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le]
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxa.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxd.symm
  rw [hL.sup_zpowers_eq_H ha had] at hle
  exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

end Loc2129

end CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof
