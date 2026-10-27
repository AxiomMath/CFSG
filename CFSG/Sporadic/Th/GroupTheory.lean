module

public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.GroupActions.PrimitiveCoprimeSimplicity
public import Mathlib.GroupTheory.GroupAction.Period

public section

namespace CFSG.Sporadic.Th

theorem isSimpleGroup_of_primitive_coprime_orders
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (hΩ : 2 ≤ Nat.card Ω) (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (ω : Ω)
    (hab : Nat.Coprime (orderOf a) (orderOf b))
    (hprod : Nat.Coprime (orderOf (a * b)) (Nat.card (MulAction.stabilizer G ω))) :
    IsSimpleGroup G :=
  CFSG.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders hΩ a b hgen ω
    hab hprod

theorem isSimpleGroup_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [IsSimpleGroup H] : IsSimpleGroup G :=
  e.isSimpleGroup

theorem isPreprimitive_of_suborbit_labels
    {G X : Type*} [Group G] [MulAction G X] [Fintype X] [DecidableEq X]
    [MulAction.IsPretransitive G X] (x : X) (H : Subgroup G)
    (hH : ∀ h ∈ H, h • x = x) {k : ℕ} (lab : X → Fin k)
    (_hinv : ∀ h ∈ H, ∀ p : X, lab (h • p) = lab p)
    (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (hdiv : ∀ S : Finset (Fin k), lab x ∈ S →
      (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X →
      S = {lab x} ∨ S = Finset.univ) :
    MulAction.IsPreprimitive G X := by
  classical
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  have hclosed : ∀ p q : X, p ∈ B → lab p = lab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := horb p q hpq
    have hhx : h • x ∈ B := by
      rw [hH h hh]
      exact hxB
    rw [← hB.smul_eq_of_mem hxB hhx]
    exact Set.smul_mem_smul_set hp
  let S : Finset (Fin k) := (Finset.univ.filter (· ∈ B)).image lab
  have hmemS : ∀ p, lab p ∈ S ↔ p ∈ B := by
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      exact hclosed q p (Finset.mem_filter.mp hq).2 hqp
    · intro hp
      exact Finset.mem_image_of_mem lab (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
  have hBS : B = ↑(Finset.univ.filter fun p => lab p ∈ S) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hmemS]
    exact ⟨fun hp => ⟨Finset.mem_univ p, hp⟩, fun hp => hp.2⟩
  have hdvd : (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X := by
    rw [Finset.sum_card_fiberwise_eq_card_filter, ← Set.ncard_coe_finset, ← hBS,
      ← Nat.card_eq_fintype_card]
    exact hB.ncard_dvd_card ⟨x, hxB⟩
  rcases hdiv S ((hmemS x).mpr hxB) hdvd with hS | hS
  · left
    have hx : ∀ r ∈ B, r = x := by
      intro r hr
      have hr' : lab r ∈ S := (hmemS r).mpr hr
      rw [hS, Finset.mem_singleton] at hr'
      obtain ⟨h, hh, hhr⟩ := horb x r hr'.symm
      rw [← hhr, hH h hh]
    intro p hp q hq
    rw [hx p hp, hx q hq]
  · right
    ext p
    refine ⟨fun _ => Set.mem_univ p, fun _ => (hmemS p).mp ?_⟩
    rw [hS]
    exact Finset.mem_univ (lab p)

theorem isPreprimitive_of_suborbit_labels_of_finite
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X] (x : X) (H : Subgroup G)
    (hH : ∀ h ∈ H, h • x = x) {k : ℕ} (lab : X → Fin k)
    (hinv : ∀ h ∈ H, ∀ p : X, lab (h • p) = lab p)
    (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (hdiv : ∀ S : Finset (Fin k), lab x ∈ S →
      (∑ i ∈ S, Nat.card {p : X // lab p = i}) ∣ Nat.card X →
      S = {lab x} ∨ S = Finset.univ) :
    MulAction.IsPreprimitive G X := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  refine isPreprimitive_of_suborbit_labels x H hH lab hinv horb fun S hxS hS => hdiv S hxS ?_
  have hcard : ∀ i, Nat.card {p : X // lab p = i} =
      (Finset.univ.filter (fun p => lab p = i)).card := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [hcard, Nat.card_eq_fintype_card]
  exact hS

section Schreier

variable {G X : Type*} [Group G] [MulAction G X]

theorem schreier_mul_eq (t : X → G) (g h : G) (x : X) :
    (t ((g * h) • x))⁻¹ * (g * h) * t x =
      (t (g • h • x))⁻¹ * g * t (h • x) * ((t (h • x))⁻¹ * h * t x) := by
  simp only [mul_smul, mul_assoc, mul_inv_cancel_left]

theorem schreier_inv_eq (t : X → G) (s : G) (x : X) :
    (t (s⁻¹ • x))⁻¹ * s⁻¹ * t x = ((t (s • s⁻¹ • x))⁻¹ * s * t (s⁻¹ • x))⁻¹ := by
  rw [smul_inv_smul]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem schreier_pow_mem (K : Subgroup G) (t : X → G) (s : G) (y : X) (n : ℕ)
    (h : ∀ j < n, (t (s • s ^ j • y))⁻¹ * s * t (s ^ j • y) ∈ K) :
    (t (s ^ n • y))⁻¹ * s ^ n * t y ∈ K := by
  induction n with
  | zero =>
    rw [pow_zero, one_smul, mul_one, inv_mul_cancel]
    exact K.one_mem
  | succ n ih =>
    rw [pow_succ', schreier_mul_eq]
    exact K.mul_mem (h n (by omega)) (ih fun j hj => h j (by omega))

theorem schreier_mem_of_cycle_tests (K : Subgroup G) (t : X → G) (s : G) {d : ℕ}
    (hd0 : 0 < d) (hd : s ^ d = 1) (E : Set X)
    (hE : ∀ x ∈ E, (t (s • x))⁻¹ * s * t x ∈ K)
    (hcyc : ∀ x, x ∈ E ∨ ∀ i, 0 < i → i < d → s ^ i • x ∈ E) (x : X) :
    (t (s • x))⁻¹ * s * t x ∈ K := by
  rcases hcyc x with hx | hx
  · exact hE x hx
  have hrest : (t (s ^ (d - 1) • s • x))⁻¹ * s ^ (d - 1) * t (s • x) ∈ K := by
    refine schreier_pow_mem K t s (s • x) (d - 1) fun j hj => hE _ ?_
    rw [smul_smul, ← pow_succ]
    exact hx (j + 1) (Nat.succ_pos j) (by omega)
  have hprod : (t (s ^ (d - 1) • s • x))⁻¹ * s ^ (d - 1) * t (s • x) *
      ((t (s • x))⁻¹ * s * t x) = 1 := by
    rw [← schreier_mul_eq, ← pow_succ, Nat.sub_add_cancel hd0, hd, one_smul, mul_one,
      inv_mul_cancel]
  rw [eq_inv_of_mul_eq_one_right hprod]
  exact K.inv_mem hrest

theorem stabilizer_le_of_schreier_mem (x₀ : X) {S : Set G} (hS : Subgroup.closure S = ⊤)
    (K : Subgroup G) (t : X → G) (ht : ∀ x, t x • x₀ = x) (ht1 : t x₀ = 1)
    (hK : ∀ s ∈ S, ∀ x, (t (s • x))⁻¹ * s * t x ∈ K) :
    MulAction.stabilizer G x₀ ≤ K := by
  let t' : MulAction.orbit G x₀ → G := fun y => t y
  rw [← CFSG.Certificates.schreier_stabilizer_generators x₀ S hS t' (fun y => ht y) ht1,
    Subgroup.closure_le]
  rintro _ ⟨y, s, hs, rfl⟩
  rcases hs with hs | ⟨r, hr, rfl⟩
  · exact hK s hs y
  · change (t (r⁻¹ • (y : X)))⁻¹ * r⁻¹ * t y ∈ K
    rw [schreier_inv_eq]
    exact K.inv_mem (hK r hr _)

theorem stabilizer_le_of_schreier_successors (x₀ : X) (S : Set G)
    (hgen : Subgroup.closure S = ⊤) (d : G → ℕ) (hdpos : ∀ s ∈ S, 0 < d s)
    (hd : ∀ s ∈ S, s ^ d s = 1) (K : Subgroup G) (t : X → G) (ht : ∀ x, t x • x₀ = x)
    (ht1 : t x₀ = 1) (E : G → Set X) (hE : ∀ s ∈ S, ∀ x ∈ E s, (t (s • x))⁻¹ * s * t x ∈ K)
    (hcyc : ∀ s ∈ S, ∀ x, x ∈ E s ∨ ∀ i, 0 < i → i < d s → s ^ i • x ∈ E s) :
    MulAction.stabilizer G x₀ ≤ K :=
  stabilizer_le_of_schreier_mem x₀ hgen K t ht ht1 fun s hs =>
    schreier_mem_of_cycle_tests K t s (hdpos s hs) (hd s hs) (E s) (hE s hs) (hcyc s hs)

theorem stabilizer_le_of_schreier_cycles (x₀ : X) (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (d : G → ℕ) (hdpos : ∀ s ∈ S, 0 < d s) (hd : ∀ s ∈ S, s ^ d s = 1)
    (K : Subgroup G) (t : X → G) (ht : ∀ x, t x • x₀ = x) (ht1 : t x₀ = 1)
    (E : G → Set X) (hE : ∀ s ∈ S, ∀ x ∈ E s, (t (s • x))⁻¹ * s * t x ∈ K)
    (hcyc : ∀ s ∈ S, ∀ x,
      (MulAction.period s x = d s ∧
        ∀ i j, s ^ i • x ∉ E s → s ^ j • x ∉ E s → s ^ i • x = s ^ j • x) ∨
      (MulAction.period s x < d s ∧ ∀ i, s ^ i • x ∈ E s)) :
    MulAction.stabilizer G x₀ ≤ K := by
  refine stabilizer_le_of_schreier_successors x₀ S hgen d hdpos hd K t ht ht1 E hE
    fun s hs x => ?_
  rcases hcyc s hs x with ⟨hper, hone⟩ | ⟨-, hall⟩
  · by_cases hx : x ∈ E s
    · exact Or.inl hx
    refine Or.inr fun i hi0 hid => ?_
    by_contra hix
    have hx' : s ^ 0 • x ∉ E s := by
      rwa [pow_zero, one_smul]
    have hfix := hone i 0 hix hx'
    rw [pow_zero, one_smul] at hfix
    exact MulAction.pow_smul_ne_of_lt_period hi0 (by rwa [hper]) hfix
  · left
    simpa only [pow_zero, one_smul] using hall 0

end Schreier

theorem stabilizer_le_of_schreier_two_three
    {G X : Type*} [Group G] [MulAction G X] (x₀ : X) (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (K : Subgroup G) (t : X → G) (ht : ∀ x, t x • x₀ = x) (ht1 : t x₀ = 1)
    (Ea Eb : Set X)
    (hEa : ∀ x ∈ Ea, (t (a • x))⁻¹ * a * t x ∈ K)
    (hEb : ∀ x ∈ Eb, (t (b • x))⁻¹ * b * t x ∈ K)
    (hca : ∀ x, x ∈ Ea ∨ (a • x ≠ x ∧ a • x ∈ Ea))
    (hcb : ∀ x, x ∈ Eb ∨ (b • x ≠ x ∧ b • x ∈ Eb ∧ b • (b • x) ∈ Eb)) :
    MulAction.stabilizer G x₀ ≤ K := by
  have hKa := schreier_mem_of_cycle_tests K t a (by norm_num) ha Ea hEa fun x => by
    rcases hca x with hx | ⟨-, hx⟩
    · exact Or.inl hx
    · refine Or.inr fun i hi0 hi2 => ?_
      obtain rfl : i = 1 := by omega
      rwa [pow_one]
  have hKb := schreier_mem_of_cycle_tests K t b (by norm_num) hb Eb hEb fun x => by
    rcases hcb x with hx | ⟨-, hx1, hx2⟩
    · exact Or.inl hx
    · refine Or.inr fun i hi0 hi3 => ?_
      obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
      · rwa [pow_one]
      · rwa [pow_two, mul_smul]
  refine stabilizer_le_of_schreier_mem x₀ hgen K t ht ht1 fun s hs x => ?_
  rcases hs with rfl | rfl
  · exact hKa x
  · exact hKb x

theorem card_eq_of_stabilizer_chain {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (H L : Subgroup G) (p q : X) (hLH : L ≤ H) (hLp : ∀ l ∈ L, l • p = p)
    (hHp : ∀ h ∈ H, h • p = p → h ∈ L) (hLq : ∀ l ∈ L, l • q = q → l = 1) :
    Nat.card H = Nat.card (MulAction.orbit H p) * Nat.card (MulAction.orbit L q) := by
  have hstabH : MulAction.stabilizer H p = L.subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun hh => hHp h h.2 hh, fun hh => hLp h hh⟩
  have hstabL : MulAction.stabilizer L q = ⊥ := by
    ext l
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    refine ⟨fun hl => Subtype.ext (hLq l l.2 hl), ?_⟩
    rintro rfl
    exact one_smul L q
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer H p)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hstabH,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv] at h1
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer L q)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hstabL, Subgroup.card_bot,
    one_mul] at h2
  rw [← h1, ← h2, mul_comm]

end CFSG.Sporadic.Th
