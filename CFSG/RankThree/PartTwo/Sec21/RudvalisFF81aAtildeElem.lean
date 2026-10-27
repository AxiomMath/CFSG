module

public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.AtildeElem

section Abstract

variable {Q : Type*} [Group Q] {Z : Subgroup Q} {q : Fin 3 → Q} {θ : Fin 3 → Q →* Q}

theorem comm_and_exp_three (hZc : ∀ z ∈ Z, ∀ x : Q, z * x = x * z)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) (hcomm : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hcube : ∀ i, q i ^ 3 ∈ Z)
    (hgen : ∀ x : Q, ∃ l m n : ℕ, ∃ z ∈ Z, x = q 0 ^ l * q 1 ^ m * q 2 ^ n * z)
    (hθZ : ∀ i, ∀ z ∈ Z, θ i z = z) (hθii : ∀ i, θ i (q i) * q i ∈ Z)
    (hθij : ∀ i j, i ≠ j → θ i (q j) * (q j)⁻¹ ∈ Z) :
    (∀ x y : Q, x * y = y * x) ∧ ∀ x : Q, x ^ 3 = 1 := by
  have hZinv : ∀ c ∈ Z, c = c⁻¹ → c = 1 := by
    intro c hc e
    have hcc : c * c = 1 := by
      calc c * c = c⁻¹ * c := by rw [← e]
        _ = 1 := inv_mul_cancel c
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hZ3 c hc, hcc, inv_one, one_mul]
  have hqq : ∀ i j, q i * q j = q j * q i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    set c := q i * q j * (q i)⁻¹ * (q j)⁻¹ with hcdef
    have hcZ : c ∈ Z := hcomm _ _
    set u := θ i (q i) * q i with hudef
    set v := θ i (q j) * (q j)⁻¹ with hvdef
    have hu : u ∈ Z := hθii i
    have hv : v ∈ Z := hθij i j hij
    have hθqi : θ i (q i) = u * (q i)⁻¹ := by rw [hudef, mul_inv_cancel_right]
    have hθqj : θ i (q j) = v * q j := by rw [hvdef, inv_mul_cancel_right]
    have hu' := hZc u hu
    have hv' := hZc v hv
    have e1 : θ i c = c := hθZ i c hcZ
    have e2 : θ i c = (q i)⁻¹ * q j * q i * (q j)⁻¹ := by
      rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hθqi, hθqj]
      calc u * (q i)⁻¹ * (v * q j) * (u * (q i)⁻¹)⁻¹ * (v * q j)⁻¹
          = u * ((q i)⁻¹ * (v * (q j * q i * u⁻¹ * (q j)⁻¹)) * v⁻¹) := by group
        _ = u * ((q i)⁻¹ * ((q j * q i * u⁻¹ * (q j)⁻¹) * v) * v⁻¹) := by rw [hv']
        _ = u * ((q i)⁻¹ * q j * q i * u⁻¹) * (q j)⁻¹ := by group
        _ = ((q i)⁻¹ * q j * q i * u⁻¹) * u * (q j)⁻¹ := by rw [hu']
        _ = (q i)⁻¹ * q j * q i * (q j)⁻¹ := by group
    have e3 : (q i)⁻¹ * q j * q i * (q j)⁻¹ = c⁻¹ := by
      have hc' := hZc c⁻¹ (inv_mem hcZ) (q i)
      calc (q i)⁻¹ * q j * q i * (q j)⁻¹ = (q i)⁻¹ * (c⁻¹ * q i) := by rw [hcdef]; group
        _ = (q i)⁻¹ * (q i * c⁻¹) := by rw [hc']
        _ = c⁻¹ := by group
    have hc1 : c = 1 := hZinv c hcZ (e1.symm.trans (e2.trans e3))
    have : q i * q j * (q i)⁻¹ = q j := mul_inv_eq_one.mp hc1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcomQ : ∀ x y : Q, x * y = y * x := by
    have hP : ∀ (l m n : ℕ) (w : Q), (∀ i (a : ℕ), Commute (q i ^ a) w) →
        Commute (q 0 ^ l * q 1 ^ m * q 2 ^ n) w := fun l m n w h =>
      ((h 0 l).mul_left (h 1 m)).mul_left (h 2 n)
    intro x y
    obtain ⟨l, m, n, z, hz, rfl⟩ := hgen x
    obtain ⟨l', m', n', z', hz', rfl⟩ := hgen y
    have hzc : ∀ w : Q, Commute z w := fun w => hZc z hz w
    have hz'c : ∀ w : Q, Commute z' w := fun w => hZc z' hz' w
    have hqP : ∀ i (a : ℕ), Commute (q i ^ a) (q 0 ^ l' * q 1 ^ m' * q 2 ^ n') := by
      intro i a
      refine (((Commute.pow_pow (hqq i 0) a l').mul_right
        (Commute.pow_pow (hqq i 1) a m')).mul_right (Commute.pow_pow (hqq i 2) a n'))
    have hPP : Commute (q 0 ^ l * q 1 ^ m * q 2 ^ n) (q 0 ^ l' * q 1 ^ m' * q 2 ^ n') :=
      hP l m n _ hqP
    have hPz' : Commute (q 0 ^ l * q 1 ^ m * q 2 ^ n) z' := (hz'c _).symm
    exact ((hPP.mul_right hPz').mul_left ((hzc _))).eq
  refine ⟨hcomQ, ?_⟩
  have hq3 : ∀ i, q i ^ 3 = 1 := by
    intro i
    set w := q i ^ 3 with hwdef
    have hwZ : w ∈ Z := hcube i
    set u := θ i (q i) * q i with hudef
    have hu : u ∈ Z := hθii i
    have hθqi : θ i (q i) = u * (q i)⁻¹ := by rw [hudef, mul_inv_cancel_right]
    have e1 : θ i w = w := hθZ i w hwZ
    have e2 : θ i w = w⁻¹ := by
      rw [hwdef, map_pow, hθqi, (Commute.mul_pow (hcomQ u (q i)⁻¹) 3), hZ3 u hu, one_mul,
        inv_pow]
    exact hZinv w hwZ (e1.symm.trans e2)
  intro x
  obtain ⟨l, m, n, z, hz, rfl⟩ := hgen x
  have hc : ∀ a b : Q, Commute a b := fun a b => hcomQ a b
  rw [(hc _ _).mul_pow, (hc _ _).mul_pow, (hc _ _).mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
    mul_comm l 3, mul_comm m 3, mul_comm n 3, pow_mul, pow_mul, pow_mul, hq3 0, hq3 1, hq3 2,
    one_pow, one_pow, one_pow, hZ3 z hz]
  simp

end Abstract

section Quotient

variable {G : Type*} [Group G] {Ah M B : Subgroup G} {a t : Fin 3 → G}

theorem mem_of_quotient (hBA : B ≤ Ah) (haA : ∀ i, a i ∈ Ah)
    (hMn : ∀ x ∈ Ah, ∀ y ∈ M, x * y * x⁻¹ ∈ M) (hMA : M ≤ Ah)
    (hBc : ∀ z ∈ B, ∀ x ∈ Ah, z * x * z⁻¹ * x⁻¹ ∈ M) (hB3 : ∀ z ∈ B, z ^ 3 ∈ M)
    (hcomm : ∀ x ∈ Ah, ∀ y ∈ Ah, ∃ z ∈ B, z⁻¹ * (x * y * x⁻¹ * y⁻¹) ∈ M)
    (hcube : ∀ i, ∃ z ∈ B, z⁻¹ * a i ^ 3 ∈ M)
    (hgen : ∀ x ∈ Ah, ∃ l m n : ℕ, ∃ z ∈ B, (a 0 ^ l * a 1 ^ m * a 2 ^ n * z)⁻¹ * x ∈ M)
    (htA : ∀ i, ∀ x ∈ Ah, t i * x * (t i)⁻¹ ∈ Ah) (htM : ∀ i, ∀ y ∈ M, t i * y * (t i)⁻¹ ∈ M)
    (htB : ∀ i, ∀ z ∈ B, (t i * z * (t i)⁻¹)⁻¹ * z ∈ M)
    (htii : ∀ i, ∃ z ∈ B, z⁻¹ * (t i * a i * (t i)⁻¹ * a i) ∈ M)
    (htij : ∀ i j, i ≠ j → ∃ z ∈ B, z⁻¹ * (t i * a j * (t i)⁻¹ * (a j)⁻¹) ∈ M) :
    (∀ x ∈ Ah, ∀ y ∈ Ah, x * y * x⁻¹ * y⁻¹ ∈ M) ∧ ∀ x ∈ Ah, x ^ 3 ∈ M := by
  set M' : Subgroup ↥Ah := M.subgroupOf Ah with hM'def
  haveI hN : M'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hMn g g.2 n hn⟩
  let π : ↥Ah →* ↥Ah ⧸ M' := QuotientGroup.mk' M'
  have hπeq : ∀ x y : ↥Ah, π x = π y ↔ (x : G)⁻¹ * y ∈ M := by
    intro x y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    rfl
  have hπone : ∀ x : ↥Ah, π x = 1 ↔ (x : G) ∈ M := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπsurj : ∀ ξ : ↥Ah ⧸ M', ∃ x : ↥Ah, π x = ξ := fun ξ =>
    QuotientGroup.mk'_surjective M' ξ
  set Z : Subgroup (↥Ah ⧸ M') := (B.subgroupOf Ah).map π with hZdef
  have hZmem : ∀ x : ↥Ah, π x ∈ Z ↔ ∃ z ∈ B, z⁻¹ * (x : G) ∈ M := by
    intro x
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, Subgroup.mem_subgroupOf.mp hz, (hπeq z x).mp hzx⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨⟨z, hBA hz⟩, Subgroup.mem_subgroupOf.mpr hz, (hπeq ⟨z, hBA hz⟩ x).mpr hzx⟩
  have hZ' : ∀ ζ ∈ Z, ∃ z ∈ B, ∃ hz : z ∈ Ah, π ⟨z, hz⟩ = ζ := by
    rintro ζ ⟨z, hz, rfl⟩
    exact ⟨z, Subgroup.mem_subgroupOf.mp hz, z.2, rfl⟩
  let c : Fin 3 → ↥Ah →* ↥Ah := fun i =>
    { toFun := fun x => ⟨t i * x * (t i)⁻¹, htA i x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcM : ∀ i, M' ≤ M'.comap (c i) := by
    intro i x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact htM i x hx
  let θ : Fin 3 → (↥Ah ⧸ M') →* (↥Ah ⧸ M') := fun i => QuotientGroup.map M' M' (c i) (hcM i)
  have hθπ : ∀ i (x : ↥Ah), θ i (π x) = π (c i x) := fun i x => rfl
  let q : Fin 3 → ↥Ah ⧸ M' := fun i => π ⟨a i, haA i⟩
  have hres := comm_and_exp_three (Z := Z) (q := q) (θ := θ)
    (by
      intro ζ hζ ξ
      obtain ⟨z, hzB, hzA, rfl⟩ := hZ' ζ hζ
      obtain ⟨x, rfl⟩ := hπsurj ξ
      rw [← map_mul, ← map_mul, hπeq]
      have h1 := hBc z⁻¹ (inv_mem hzB) x x.2
      have h2 := hMn _ (inv_mem x.2) _ h1
      have e : ((⟨z, hzA⟩ * x : ↥Ah) : G)⁻¹ * ((x * ⟨z, hzA⟩ : ↥Ah) : G) =
          (x : G)⁻¹ * (z⁻¹ * x * z⁻¹⁻¹ * (x : G)⁻¹) * (x : G)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul]
        group
      rw [e]
      exact h2)
    (by
      intro ζ hζ
      obtain ⟨z, hzB, hzA, rfl⟩ := hZ' ζ hζ
      rw [← map_pow, hπone]
      exact hB3 z hzB)
    (by
      intro ξ η
      obtain ⟨x, rfl⟩ := hπsurj ξ
      obtain ⟨y, rfl⟩ := hπsurj η
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hZmem]
      exact hcomm x x.2 y y.2)
    (by
      intro i
      rw [← map_pow, hZmem]
      exact hcube i)
    (by
      intro ξ
      obtain ⟨x, rfl⟩ := hπsurj ξ
      obtain ⟨l, m, n, z, hzB, hx⟩ := hgen x x.2
      refine ⟨l, m, n, π ⟨z, hBA hzB⟩, (hZmem _).mpr ⟨z, hzB, by simp⟩, ?_⟩
      rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul, eq_comm, hπeq]
      exact hx)
    (by
      intro i ζ hζ
      obtain ⟨z, hzB, hzA, rfl⟩ := hZ' ζ hζ
      rw [hθπ, hπeq]
      exact htB i z hzB)
    (by
      intro i
      rw [hθπ, ← map_mul, hZmem]
      exact htii i)
    (by
      intro i j hij
      rw [hθπ, ← map_inv, ← map_mul, hZmem]
      exact htij i j hij)
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have e := hres.1 (π ⟨x, hx⟩) (π ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hπeq] at e
    have h2 := hMn _ (mul_mem hx hy) _ e
    have e' : x * y * (((⟨x, hx⟩ * ⟨y, hy⟩ : ↥Ah) : G)⁻¹ * ((⟨y, hy⟩ * ⟨x, hx⟩ : ↥Ah) : G)) *
        (x * y)⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e'] at h2
    simpa using inv_mem h2
  · have e := hres.2 (π ⟨x, hx⟩)
    rw [← map_pow, hπone] at e
    exact e

end Quotient

end CFSG.RankThree.PartTwo.Sec21.FF81.AtildeElem
