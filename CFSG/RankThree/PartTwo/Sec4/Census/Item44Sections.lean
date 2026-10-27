module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Weights
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Subgroup

theorem exists_pow_mul_eq {Y : Type*} [Group Y] {R : Subgroup Y} [hR : R.Normal] (u : Y)
    {c : Y} (hc : c ∈ R) (k : ℕ) : ∃ c' ∈ R, (u * c) ^ k = u ^ k * c' := by
  induction k with
  | zero => exact ⟨1, one_mem R, by simp⟩
  | succ k ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨u⁻¹ * c' * u * c, mul_mem ?_ hc, ?_⟩
    · have := hR.conj_mem c' hc' u⁻¹
      rwa [inv_inv] at this
    · rw [pow_succ, h, pow_succ]
      group

theorem natCast_ne_zero_of_prime_ne {p r : ℕ} [Fact p.Prime] (hr : r.Prime) (hrp : r ≠ p) :
    ((r : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hrp ((Nat.prime_dvd_prime_iff_eq Fact.out hr).mp h).symm

theorem exists_pow_commute_of_normal {p r : ℕ} [Fact p.Prime] [hr : Fact r.Prime] (hr5 : 5 ≤ r)
    (hrp : r ≠ p) {X Y : Type*} [Group X] [Finite X] [Group Y]
    (ρ : X →* GL (Fin 4) (ZMod p)) (π : X →* Y) (hπ : Function.Surjective π)
    (hker : ρ.ker ≤ π.ker) {R : Subgroup Y} [hRn : R.Normal] (hR : IsPGroup r R) (g : Y) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ ∀ x ∈ R, g ^ k * x = x * g ^ k := by
  have hrF := natCast_ne_zero_of_prime_ne (p := p) hr.out hrp
  set M := R.comap π with hM
  have : M.Normal := hRn.comap π
  obtain ⟨P⟩ : Nonempty (Sylow r M) := inferInstance
  set Q := (P : Subgroup M).map M.subtype with hQ
  have hQr : IsPGroup r Q := P.isPGroup'.map _
  have hπQ : Q.map π = R := by
    have hf : Function.Surjective (π.subgroupComap R) := π.subgroupComap_surjective R hπ
    let P' := P.mapSurjective hf
    have hP' : (P' : Subgroup R) = ⊤ := (P'.3 (hR.to_subgroup ⊤) le_top).symm
    have h1 : (P' : Subgroup R).map R.subtype = Q.map π := by
      rw [Sylow.coe_mapSurjective, hQ, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [← h1, hP', ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hab := commute_of_isPGroup (F := ZMod p) hr5 hrF (Q := Q.map ρ) (hQr.map ρ)
  have hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    rw [← hπQ]
    rintro _ ⟨q₁, h₁, rfl⟩ _ ⟨q₂, h₂, rfl⟩
    have h := hab (ρ q₁) ⟨q₁, h₁, rfl⟩ (ρ q₂) ⟨q₂, h₂, rfl⟩
    have h3 : q₁ * q₂ * (q₂ * q₁)⁻¹ ∈ π.ker :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, h, mul_inv_cancel])
    rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h3
  obtain ⟨g₀, rfl⟩ := hπ g
  have hg₀ : g₀ ∈ normalizer Q ⊔ M := by
    rw [hQ, Sylow.normalizer_sup_eq_top P]
    exact mem_top g₀
  obtain ⟨n, hn, m, hm, rfl⟩ := mem_sup_of_normal_right.mp hg₀
  have hcard : (Nat.card (Q.map ρ) : ZMod p) ≠ 0 := by
    obtain ⟨j, hj⟩ := (hQr.map ρ).exists_card_eq
    rw [hj, Nat.cast_pow]
    exact pow_ne_zero j hrF
  obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_commute_of_mem_normalizer hab hcard
    (le_normalizer_map ρ ⟨n, hn, rfl⟩)
  refine ⟨k, hk1, hk4, ?_⟩
  have h1 : ∀ x ∈ R, π n ^ k * x = x * π n ^ k := by
    rw [← hπQ]
    rintro _ ⟨q, hq, rfl⟩
    have h := hk (ρ q) ⟨q, hq, rfl⟩
    have h3 : n ^ k * q * (q * n ^ k)⁻¹ ∈ π.ker :=
      hker (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_pow, h, mul_inv_cancel])
    rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, map_pow] at h3
  obtain ⟨c, hc, hgk⟩ := exists_pow_mul_eq (R := R) (π n) (show π m ∈ R from hm) k
  intro x hx
  rw [map_mul, hgk, mul_assoc, hRab c hc x hx, ← mul_assoc, h1 x hx, mul_assoc]

theorem exists_pow_commute {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hr5 : 5 ≤ r) (hrp : r ≠ p)
    {X Y : Type*} [Group X] [Finite X] [Group Y] (ρ : X →* GL (Fin 4) (ZMod p)) (π : X →* Y)
    (hπ : Function.Surjective π) (hker : ρ.ker ≤ π.ker) {R : Subgroup Y} (hR : IsPGroup r R)
    {g : Y} (hg : g ∈ normalizer R) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ ∀ x ∈ R, g ^ k * x = x * g ^ k := by
  set L := (normalizer R).comap π
  have hR' : IsPGroup r (R.subgroupOf (normalizer R)) :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe le_normalizer).symm
  have hker' : (ρ.comp L.subtype).ker ≤ (π.subgroupComap (normalizer R)).ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    exact Subtype.ext (hker hl)
  obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_commute_of_normal hr5 hrp (ρ.comp L.subtype)
    (π.subgroupComap (normalizer R)) (π.subgroupComap_surjective _ hπ) hker' hR' ⟨g, hg⟩
  exact ⟨k, hk1, hk4, fun x hx => congrArg Subtype.val (hk ⟨x, le_normalizer hx⟩ hx)⟩

theorem exists_pow_modEq_one {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hr5 : 5 ≤ r)
    (hrp : r ≠ p) {X Y : Type*} [Group X] [Finite X] [Group Y] (ρ : X →* GL (Fin 4) (ZMod p))
    (π : X →* Y) (hπ : Function.Surjective π) (hker : ρ.ker ≤ π.ker) {y g : Y} {a : ℕ}
    (hy : orderOf y = r) (hgy : g * y = y ^ a * g) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ a ^ k ≡ 1 [MOD r] := by
  have : Finite Y := Finite.of_surjective π hπ
  have hR : IsPGroup r (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hconj : g * y * g⁻¹ = y ^ a := by rw [hgy, mul_inv_cancel_right]
  have hg : g ∈ normalizer (zpowers y) := by
    apply mem_normalizer_of_forall_conj_mem
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow, hconj]
    exact zpow_mem (pow_mem (mem_zpowers y) a) n
  obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_commute hr5 hrp ρ π hπ hker hR hg
  refine ⟨k, hk1, hk4, ?_⟩
  have hgm : ∀ m : ℕ, g * y ^ m = y ^ (a * m) * g := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc g * y ^ (m + 1) = g * y ^ m * y := by rw [pow_succ, mul_assoc]
        _ = y ^ (a * m) * (g * y) := by rw [ih, mul_assoc]
        _ = y ^ (a * (m + 1)) * g := by rw [hgy, ← mul_assoc, ← pow_add, mul_add_one]
  have hgk : ∀ j : ℕ, g ^ j * y = y ^ (a ^ j) * g ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc g ^ (j + 1) * y = g * (g ^ j * y) := by rw [pow_succ', mul_assoc]
        _ = g * y ^ (a ^ j) * g ^ j := by rw [ih, mul_assoc]
        _ = y ^ (a ^ (j + 1)) * g ^ (j + 1) := by
          rw [hgm, mul_assoc, pow_succ a j, mul_comm (a ^ j) a, pow_succ' g j]
  have h1 := hk y (mem_zpowers y)
  rw [hgk k] at h1
  have h2 : y ^ (a ^ k) = y ^ 1 := by
    rw [pow_one]
    exact mul_right_cancel h1
  rwa [pow_eq_pow_iff_modEq, hy] at h2

theorem index_dvd_card_of_ker_le {X H : Type*} [Group X] [Group H] [Finite H] (ρ : X →* H)
    {N : Subgroup X} (hN : ρ.ker ≤ N) : N.index ∣ Nat.card H :=
  calc N.index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hN
    _ = Nat.card ρ.range := Subgroup.index_ker ρ
    _ ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _

theorem card_dvd_card_of_ker_le {X Y H : Type*} [Group X] [Group Y] [Group H] [Finite H]
    (ρ : X →* H) (π : X →* Y) (hπ : Function.Surjective π) (hker : ρ.ker ≤ π.ker) :
    Nat.card Y ∣ Nat.card H := by
  have h := index_dvd_card_of_ker_le ρ hker
  rwa [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top] at h

@[expose] def glToSL {X : Type*} [Group X] {n : ℕ} {R : Type*} [CommRing R]
    (ρ : X →* GL (Fin n) R) (hdet : ∀ x, (ρ x : Matrix (Fin n) (Fin n) R).det = 1) :
    X →* Matrix.SpecialLinearGroup (Fin n) R where
  toFun x := ⟨ρ x, hdet x⟩
  map_one' := Subtype.ext (by simp only [map_one, Units.val_one]; rfl)
  map_mul' x y := Subtype.ext (by simp only [map_mul, Units.val_mul]; rfl)

theorem ker_glToSL {X : Type*} [Group X] {n : ℕ} {R : Type*} [CommRing R]
    (ρ : X →* GL (Fin n) R) (hdet : ∀ x, (ρ x : Matrix (Fin n) (Fin n) R).det = 1) :
    (glToSL ρ hdet).ker = ρ.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    exact Units.ext (congrArg Subtype.val h)
  · intro h
    refine Subtype.ext ?_
    change ((ρ x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1
    rw [h, Units.val_one]

theorem isPGroup_closure_pair {G : Type*} [Group G] {r : ℕ} {a b : G} (hab : a * b = b * a)
    (ha : a ^ r = 1) (hb : b ^ r = 1) : IsPGroup r (closure ({a, b} : Set G)) := by
  have hpow : ∀ x ∈ closure ({a, b} : Set G), x ^ r = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem w hw =>
      rcases hw with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow r
    | mul v w hv' hw' hv hw =>
      rw [Commute.mul_pow (mul_comm_of_mem_closure_pair hab hv' hw'), hv, hw, one_mul]
    | inv v _ hv => rw [inv_pow, hv, inv_one]
  intro x
  exact ⟨1, Subtype.ext (by rw [pow_one]; exact hpow x x.2)⟩

theorem conj_mem_closure_pair {G : Type*} [Group G] {a b h : G}
    (ha : h * a * h⁻¹ ∈ closure ({a, b} : Set G)) (hb : h * b * h⁻¹ ∈ closure ({a, b} : Set G)) :
    ∀ x ∈ closure ({a, b} : Set G), h * x * h⁻¹ ∈ closure ({a, b} : Set G) := by
  intro x hx
  induction hx using closure_induction with
  | mem w hw =>
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul v w _ _ hv hw =>
    have : h * (v * w) * h⁻¹ = (h * v * h⁻¹) * (h * w * h⁻¹) := by group
    rw [this]
    exact mul_mem hv hw
  | inv v _ hv =>
    have : h * v⁻¹ * h⁻¹ = (h * v * h⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hv

end CFSG.RankThree.PartTwo.Sec4.Census
