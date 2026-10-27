module

public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type*} [Group G]

structure Pair (X T M V : Subgroup G) (g : G) : Prop where
  sylow : IsSylowTwoOf T X
  le_T : V ≤ T
  normal_T : T ≤ Subgroup.normalizer (V : Set G)
  elem : IsElemAbelian 2 V
  normalizer_le : X ⊓ Subgroup.normalizer (V : Set G) ≤ M
  le_X : M ≤ X
  le_pCoreOf : V ≤ pCoreOf 2 M
  closed : IsSylowTwoOf (pCoreOf 2 (kerIn M X)) (kerIn M X)
  mem : g ∈ X
  gen : X = V ⊔ conjSub g V

theorem exists_two_part_odd_part [Finite G] (c : G) :
    ∃ a b : G, c = b * a ∧ a ∈ Subgroup.zpowers c ∧ b ∈ Subgroup.zpowers c ∧
      (∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Odd (orderOf b) := by
  obtain ⟨s, t, ht, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop : Nat.Coprime (2 ^ s) t := (Nat.coprime_two_left.2 ht).pow_left s
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨u, hu⟩ := (Nat.modEq_zero_iff_dvd).1 he0
  obtain ⟨w, hw⟩ := Nat.modEq_iff_dvd.1 he1
  refine ⟨c ^ ((1 : ℤ) - e), c ^ e, ?_, Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _,
    Subgroup.pow_mem _ (Subgroup.mem_zpowers c) e, ⟨s, ?_⟩, ?_⟩
  · rw [← zpow_natCast, ← zpow_add]
    simp
  · have hexp : ((1 : ℤ) - e) * ((2 ^ s : ℕ) : ℤ) = (orderOf c : ℤ) * w := by
      have h : (1 : ℤ) - e = t * w := by exact_mod_cast hw
      rw [h, hm]
      push_cast
      ring
    rw [← zpow_natCast, ← zpow_mul, hexp, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h1 : (c ^ e) ^ t = 1 := by
      rw [← pow_mul, hu, show 2 ^ s * u * t = orderOf c * u by rw [hm]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat ht (orderOf_dvd_of_pow_eq_one h1)

theorem mem_of_two_pow_of_odd_pow {N : Subgroup G} {y : G} {k n : ℕ} (hy : y ^ 2 ^ k = 1)
    (hn : Odd n) (hyn : y ^ n ∈ N) : y ∈ N := by
  have hcop : Nat.Coprime (orderOf y) n :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hy)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn))
  exact B6.mem_of_pow_mem_of_coprime hyn hcop

theorem eq_one_of_two_pow_of_odd {y : G} {k : ℕ} (hy : y ^ 2 ^ k = 1) (hodd : Odd (orderOf y)) :
    y = 1 := by
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hi] at hodd
  rcases i with _ | i
  · exact orderOf_eq_one_iff.mp (by simpa using hi)
  · exfalso
    rw [pow_succ] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (even_two.mul_left _)

namespace Pair

variable {X T M V : Subgroup G} {g : G}

theorem V_le (h : Pair X T M V g) : V ≤ X := h.le_T.trans h.sylow.1

theorem conj_le (h : Pair X T M V g) : conjSub g V ≤ X := by
  rw [h.gen]
  exact le_sup_right

theorem comm (h : Pair X T M V g) {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := by
  have := h.elem.1
  exact setLike_mul_comm ha hb

theorem comm_conj (h : Pair X T M V g) {a b : G} (ha : a ∈ conjSub g V)
    (hb : b ∈ conjSub g V) : a * b = b * a := by
  rw [mem_conjSub] at ha hb
  have := h.comm ha hb
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
    _ = b * a := by group

theorem mem_center (h : Pair X T M V g) {z : G} (hz : z ∈ V ⊓ conjSub g V) {x : G}
    (hx : x ∈ X) : z * x = x * z := by
  have hle : X ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [h.gen]
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h.comm hz.1 hv
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h.comm_conj hz.2 hv
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) z rfl)

section Finite

variable [Finite G]

theorem pCoreOf_le_T (h : Pair X T M V g) : pCoreOf 2 X ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf h.sylow

theorem pCoreOf_le_normalizer (h : Pair X T M V g) :
    pCoreOf 2 X ≤ Subgroup.normalizer (V : Set G) :=
  h.pCoreOf_le_T.trans h.normal_T

omit [Finite G] in
theorem conj_mem_pCoreOf {x q : G} (hx : x ∈ X) (hq : q ∈ pCoreOf 2 X) :
    x * q * x⁻¹ ∈ pCoreOf 2 X :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx) q).mp hq

omit [Finite G] in
theorem conjSub_pCoreOf (h : Pair X T M V g) : conjSub g (pCoreOf 2 X) = pCoreOf 2 X :=
  conjSub_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X h.mem)

theorem pCoreOf_le_normalizer_conj (h : Pair X T M V g) :
    pCoreOf 2 X ≤ Subgroup.normalizer (conjSub g V : Set G) := by
  intro q hq
  have hq' : g⁻¹ * q * g ∈ pCoreOf 2 X := by
    have := conj_mem_pCoreOf (X.inv_mem h.mem) hq
    simpa using this
  have hqN := h.pCoreOf_le_normalizer hq'
  refine mem_normalizer_of_forall_mem (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_conjSub] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp hqN _).mp hx
    simpa [mul_assoc] using this
  · rw [mem_conjSub] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hqN) _).mp hx
    simpa [mul_assoc] using this

theorem pCoreOf_le_kerIn (h : Pair X T M V g) : pCoreOf 2 X ≤ kerIn M X :=
  le_kerIn_of_le_normalizer
    (fun _ hq => h.normalizer_le ⟨h.sylow.1 (h.pCoreOf_le_T hq), h.pCoreOf_le_normalizer hq⟩)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

theorem pCoreOf_kerIn (h : Pair X T M V g) : pCoreOf 2 (kerIn M X) = pCoreOf 2 X := by
  have hJX : kerIn M X ≤ X := kerIn_le.trans h.le_X
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hJX)
      ((le_normalizer_kerIn M X).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.pCoreOf_le_kerIn
      (hJX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem le_pCoreOf_of_le_kerIn (h : Pair X T M V g) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSJ : S ≤ kerIn M X) : S ≤ pCoreOf 2 X := by
  rw [← h.pCoreOf_kerIn]
  obtain ⟨S', hS', hSS'⟩ := exists_isSylowTwoOf_ge hS hSJ
  obtain ⟨j, hj, hjS⟩ := isSylowTwoOf_exists_conj h.closed hS'
  rw [hjS, conjSub_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hj)] at hSS'
  exact hSS'

theorem kerIn_inf_eq (h : Pair X T M V g) : kerIn M X ⊓ V = V ⊓ pCoreOf 2 X := by
  apply le_antisymm
  · exact le_inf inf_le_right (h.le_pCoreOf_of_le_kerIn
      ((B6.isPGroup_of_isElemAbelian h.elem).to_le inf_le_right) inf_le_left)
  · exact le_inf (inf_le_right.trans h.pCoreOf_le_kerIn) inf_le_left

theorem conjSub_kerIn_inf_eq (h : Pair X T M V g) :
    conjSub g (kerIn M X ⊓ V) = conjSub g V ⊓ pCoreOf 2 X := by
  rw [h.kerIn_inf_eq]
  calc conjSub g (V ⊓ pCoreOf 2 X) = conjSub g V ⊓ conjSub g (pCoreOf 2 X) :=
        (conjSub g).map_inf _ _
    _ = conjSub g V ⊓ pCoreOf 2 X := by rw [h.conjSub_pCoreOf]

omit [Finite G] in
theorem le_normalizer_Z (h : Pair X T M V g) :
    X ≤ Subgroup.normalizer ((V ⊓ conjSub g V : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_forall_mem (fun z hz => ?_) (fun z hz => ?_)
  · rw [← h.mem_center hz hx]
    simpa using hz
  · rw [← h.mem_center hz (X.inv_mem hx)]
    simpa using hz

omit [Finite G] in
theorem inf_conj_le_pCoreOf (h : Pair X T M V g) : V ⊓ conjSub g V ≤ pCoreOf 2 X :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans h.V_le)
    h.le_normalizer_Z ((B6.isPGroup_of_isElemAbelian h.elem).to_le inf_le_left)

theorem inf_conj_le_kerIn_inf (h : Pair X T M V g) : V ⊓ conjSub g V ≤ kerIn M X ⊓ V := by
  rw [h.kerIn_inf_eq]
  exact le_inf inf_le_left h.inf_conj_le_pCoreOf

omit [Finite G] in
theorem conjSub_inf_conj (h : Pair X T M V g) {x : G} (hx : x ∈ X) :
    conjSub x (V ⊓ conjSub g V) = V ⊓ conjSub g V :=
  conjSub_eq_self (h.le_normalizer_Z hx)

theorem inf_conj_le_conjSub (h : Pair X T M V g) :
    V ⊓ conjSub g V ≤ conjSub g (kerIn M X ⊓ V) := by
  rw [← h.conjSub_inf_conj h.mem]
  exact (conjSub g).monotone h.inf_conj_le_kerIn_inf

theorem commutator_mem_B (h : Pair X T M V g) {v q : G} (hv : v ∈ V) (hq : q ∈ pCoreOf 2 X) :
    v * q * v⁻¹ * q⁻¹ ∈ kerIn M X ⊓ V := by
  rw [h.kerIn_inf_eq]
  constructor
  · have h1 : q * v⁻¹ * q⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.pCoreOf_le_normalizer hq) _).mp (V.inv_mem hv)
    have := V.mul_mem hv h1
    simpa [mul_assoc] using this
  · have h1 : v * q * v⁻¹ ∈ pCoreOf 2 X := conj_mem_pCoreOf (h.V_le hv) hq
    exact (pCoreOf 2 X).mul_mem h1 ((pCoreOf 2 X).inv_mem hq)

theorem commutator_mem_A (h : Pair X T M V g) {w q : G} (hw : w ∈ conjSub g V)
    (hq : q ∈ pCoreOf 2 X) : w * q * w⁻¹ * q⁻¹ ∈ conjSub g (kerIn M X ⊓ V) := by
  rw [h.conjSub_kerIn_inf_eq]
  constructor
  · have h1 : q * w⁻¹ * q⁻¹ ∈ conjSub g V :=
      (Subgroup.mem_normalizer_iff.mp (h.pCoreOf_le_normalizer_conj hq) _).mp
        ((conjSub g V).inv_mem hw)
    have := (conjSub g V).mul_mem hw h1
    simpa [mul_assoc] using this
  · have h1 : w * q * w⁻¹ ∈ pCoreOf 2 X := conj_mem_pCoreOf (h.conj_le hw) hq
    exact (pCoreOf 2 X).mul_mem h1 ((pCoreOf 2 X).inv_mem hq)

theorem B_le_pCoreOf (h : Pair X T M V g) : kerIn M X ⊓ V ≤ pCoreOf 2 X := by
  rw [h.kerIn_inf_eq]
  exact inf_le_right

theorem A_le_pCoreOf (h : Pair X T M V g) : conjSub g (kerIn M X ⊓ V) ≤ pCoreOf 2 X := by
  rw [h.conjSub_kerIn_inf_eq]
  exact inf_le_right

theorem P_le_pCoreOf (h : Pair X T M V g) :
    (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤ pCoreOf 2 X :=
  sup_le h.B_le_pCoreOf h.A_le_pCoreOf

theorem le_normalizer_P (h : Pair X T M V g) :
    X ≤ Subgroup.normalizer
      (((kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G) := by
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  have key : ∀ x ∈ V ⊔ conjSub g V, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    have hgen : ∀ x ∈ V ⊔ conjSub g V, x ∈ Subgroup.normalizer (P : Set G) := by
      refine fun x hx => (sup_le (fun v hv => ?_) (fun w hw => ?_) : V ⊔ conjSub g V ≤ _) hx
      · refine mem_normalizer_of_forall_mem (fun p hp => ?_) (fun p hp => ?_)
        · have h1 := h.commutator_mem_B hv (h.P_le_pCoreOf hp)
          have : v * p * v⁻¹ = (v * p * v⁻¹ * p⁻¹) * p := by group
          rw [this]
          exact P.mul_mem (Subgroup.mem_sup_left h1) hp
        · have h1 := h.commutator_mem_B (V.inv_mem hv) (h.P_le_pCoreOf hp)
          have : v⁻¹ * p * v = (v⁻¹ * p * v⁻¹⁻¹ * p⁻¹) * p := by group
          rw [this]
          exact P.mul_mem (Subgroup.mem_sup_left h1) hp
      · refine mem_normalizer_of_forall_mem (fun p hp => ?_) (fun p hp => ?_)
        · have h1 := h.commutator_mem_A hw (h.P_le_pCoreOf hp)
          have : w * p * w⁻¹ = (w * p * w⁻¹ * p⁻¹) * p := by group
          rw [this]
          exact P.mul_mem (Subgroup.mem_sup_right h1) hp
        · have h1 := h.commutator_mem_A ((conjSub g V).inv_mem hw) (h.P_le_pCoreOf hp)
          have : w⁻¹ * p * w = (w⁻¹ * p * w⁻¹⁻¹ * p⁻¹) * p := by group
          rw [this]
          exact P.mul_mem (Subgroup.mem_sup_right h1) hp
    intro x hx p hp
    exact (Subgroup.mem_normalizer_iff.mp (hgen x hx) p).mp hp
  intro x hx
  rw [h.gen] at hx
  refine mem_normalizer_of_forall_mem (fun p hp => key x hx p hp) (fun p hp => ?_)
  have := key x⁻¹ ((V ⊔ conjSub g V).inv_mem hx) p hp
  simpa using this

theorem P_le_normalizer_B (h : Pair X T M V g) :
    (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤
      Subgroup.normalizer ((kerIn M X ⊓ V : Subgroup G) : Set G) := by
  intro p hp
  have hpQ := h.P_le_pCoreOf hp
  rw [h.kerIn_inf_eq]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h.pCoreOf_le_normalizer hpQ,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (CFSG.LieType.BorelTits.pCoreOf_le 2 X hpQ)⟩

theorem P_le_normalizer_A (h : Pair X T M V g) :
    (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤
      Subgroup.normalizer ((conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G) := by
  intro p hp
  have hpQ := h.P_le_pCoreOf hp
  rw [h.conjSub_kerIn_inf_eq]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h.pCoreOf_le_normalizer_conj hpQ,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (CFSG.LieType.BorelTits.pCoreOf_le 2 X hpQ)⟩

theorem mem_P_iff (h : Pair X T M V g) {x : G} :
    x ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ↔
      ∃ b ∈ kerIn M X ⊓ V, ∃ a ∈ conjSub g (kerIn M X ⊓ V), b * a = x := by
  have hB : kerIn M X ⊓ V ≤ Subgroup.normalizer
      ((conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G) := le_sup_left.trans h.P_le_normalizer_A
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hB]
  rfl

theorem inf_conj_le_P (h : Pair X T M V g) :
    V ⊓ conjSub g V ≤ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) :=
  h.inf_conj_le_kerIn_inf.trans le_sup_left

omit [Finite G] in
theorem B_inf_A_le :
    (kerIn M X ⊓ V) ⊓ conjSub g (kerIn M X ⊓ V) ≤ V ⊓ conjSub g V :=
  inf_le_inf inf_le_right ((conjSub g).monotone inf_le_right)

theorem commutator_B_A (h : Pair X T M V g) {b a : G} (hb : b ∈ kerIn M X ⊓ V)
    (ha : a ∈ conjSub g (kerIn M X ⊓ V)) : b * a * b⁻¹ * a⁻¹ ∈ V ⊓ conjSub g V := by
  apply B_inf_A_le
  constructor
  · have h1 : a * b⁻¹ * a⁻¹ ∈ kerIn M X ⊓ V :=
      (Subgroup.mem_normalizer_iff.mp (h.P_le_normalizer_B (Subgroup.mem_sup_right ha)) _).mp
        ((kerIn M X ⊓ V).inv_mem hb)
    have := (kerIn M X ⊓ V).mul_mem hb h1
    simpa [mul_assoc] using this
  · have h1 : b * a * b⁻¹ ∈ conjSub g (kerIn M X ⊓ V) :=
      (Subgroup.mem_normalizer_iff.mp (h.P_le_normalizer_A (Subgroup.mem_sup_left hb)) _).mp ha
    exact (conjSub g (kerIn M X ⊓ V)).mul_mem h1 ((conjSub g (kerIn M X ⊓ V)).inv_mem ha)

theorem cubic (h : Pair X T M V g) {v a₁ a₂ a₃ : G} (hv : v ∈ V)
    (ha₁ : a₁ ∈ conjSub g (kerIn M X ⊓ V)) (ha₂ : a₂ ∈ conjSub g (kerIn M X ⊓ V))
    (ha₃ : a₃ ∈ conjSub g (kerIn M X ⊓ V)) :
    let c := fun (a x : G) => a * x * a⁻¹ * x⁻¹
    c a₃ (c a₂ (c a₁ v)) = 1 := by
  intro c
  have h1 : c a₁ v ∈ kerIn M X ⊓ V := by
    have := h.commutator_mem_B hv (h.A_le_pCoreOf ha₁)
    have e : c a₁ v = (v * a₁ * v⁻¹ * a₁⁻¹)⁻¹ := by simp only [c]; group
    rw [e]
    exact (kerIn M X ⊓ V).inv_mem this
  have h2 : c a₂ (c a₁ v) ∈ V ⊓ conjSub g V := by
    have := h.commutator_B_A h1 ha₂
    have e : c a₂ (c a₁ v) = (c a₁ v * a₂ * (c a₁ v)⁻¹ * a₂⁻¹)⁻¹ := by simp only [c]; group
    rw [e]
    exact (V ⊓ conjSub g V).inv_mem this
  have h3 := h.mem_center h2 (CFSG.LieType.BorelTits.pCoreOf_le 2 X (h.A_le_pCoreOf ha₃))
  show a₃ * c a₂ (c a₁ v) * a₃⁻¹ * (c a₂ (c a₁ v))⁻¹ = 1
  rw [← h3]
  group

theorem le_kerIn_of_isTwoQuotient (h : Pair X T M V g) {D : Subgroup G} (hDX : D ≤ X)
    (hXD : X ≤ Subgroup.normalizer (D : Set G)) (hJD : kerIn M X ≤ D)
    (h2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ kerIn M X) : D ≤ kerIn M X := by
  have hS : IsSylowTwoOf (T ⊓ D) D := isSylowTwoOf_inf_normal h.sylow hDX hXD
  have hJn : D ≤ Subgroup.normalizer ((kerIn M X : Subgroup G) : Set G) :=
    hDX.trans (le_normalizer_kerIn M X)
  have hsup := sup_eq_of_isTwoQuotient hJD hJn h2 hS
  have hDM : D ≤ M := by
    rw [← hsup]
    exact sup_le kerIn_le (fun t ht => h.normalizer_le ⟨h.sylow.1 ht.1, h.normal_T ht.1⟩)
  exact le_kerIn_of_le_normalizer hDM hXD

omit [Finite G] in
theorem mem_inf_conj_of_comm (h : Pair X T M V g) {a : G} (ha : a ∈ conjSub g (kerIn M X ⊓ V))
    (hav : ∀ v ∈ V, a * v = v * a) : a ∈ V ⊓ conjSub g V := by
  have haV : a ∈ conjSub g V := (conjSub g).monotone inf_le_right ha
  have hcent : X ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [h.gen]
    refine sup_le (fun v hv => ?_) (fun w hw => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hav v hv
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h.comm_conj haV hw
  have hga : g * a = a * g := (Subgroup.mem_centralizer_iff.mp (hcent h.mem) a rfl).symm
  have hB : g⁻¹ * a * g ∈ kerIn M X ⊓ V := mem_conjSub.mp ha
  have e : g⁻¹ * a * g = a := by rw [mul_assoc, ← hga]; group
  rw [e] at hB
  exact ⟨hB.2, haV⟩

theorem B_inf_A (h : Pair X T M V g) :
    (kerIn M X ⊓ V) ⊓ conjSub g (kerIn M X ⊓ V) = V ⊓ conjSub g V :=
  le_antisymm B_inf_A_le (le_inf h.inf_conj_le_kerIn_inf h.inf_conj_le_conjSub)

theorem exists_swap (h : Pair X T M V g) {b a : G} (hb : b ∈ kerIn M X ⊓ V)
    (ha : a ∈ conjSub g (kerIn M X ⊓ V)) : ∃ z ∈ V ⊓ conjSub g V, a * b = b * a * z := by
  have h1 := h.commutator_B_A ((kerIn M X ⊓ V).inv_mem hb) ((conjSub g (kerIn M X ⊓ V)).inv_mem ha)
  refine ⟨(b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹)⁻¹, (V ⊓ conjSub g V).inv_mem h1, by group⟩

theorem exists_comm_P (h : Pair X T M V g) {x y : G}
    (hx : x ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V))
    (hy : y ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)) :
    ∃ z ∈ V ⊓ conjSub g V, x * y = y * x * z := by
  have hPX : (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤ X :=
    h.P_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P_iff.mp hx
  obtain ⟨b', hb', a', ha', rfl⟩ := h.mem_P_iff.mp hy
  obtain ⟨z₁, hz₁, e₁⟩ := h.exists_swap hb' ha
  obtain ⟨z₂, hz₂, e₂⟩ := h.exists_swap hb ha'
  have hbb : b * b' = b' * b := h.comm hb.2 hb'.2
  have haa : a * a' = a' * a := h.comm_conj ((conjSub g).monotone inf_le_right ha)
    ((conjSub g).monotone inf_le_right ha')
  have hc₁ : ∀ w ∈ X, z₁ * w = w * z₁ := fun w hw => h.mem_center hz₁ hw
  refine ⟨z₂⁻¹ * z₁, (V ⊓ conjSub g V).mul_mem ((V ⊓ conjSub g V).inv_mem hz₂) hz₁, ?_⟩
  have hc₂ : ∀ w ∈ X, z₂⁻¹ * w = w * z₂⁻¹ := fun w hw =>
    h.mem_center ((V ⊓ conjSub g V).inv_mem hz₂) hw
  have hbX : b ∈ X := hPX (Subgroup.mem_sup_left hb)
  have haX : a ∈ X := hPX (Subgroup.mem_sup_right ha)
  have ha'X : a' ∈ X := hPX (Subgroup.mem_sup_right ha')
  have hb'X : b' ∈ X := hPX (Subgroup.mem_sup_left hb')
  have e₂' : b * a' = a' * b * z₂⁻¹ := by rw [e₂]; group
  calc b * a * (b' * a') = b * (a * b') * a' := by group
    _ = b * (b' * a * z₁) * a' := by rw [e₁]
    _ = b * b' * a * (z₁ * a') := by group
    _ = b * b' * a * (a' * z₁) := by rw [hc₁ a' ha'X]
    _ = b' * b * (a' * a) * z₁ := by rw [hbb, ← haa]; group
    _ = b' * (b * a') * a * z₁ := by group
    _ = b' * (a' * b * z₂⁻¹) * a * z₁ := by rw [e₂']
    _ = b' * a' * b * (z₂⁻¹ * a) * z₁ := by group
    _ = b' * a' * b * (a * z₂⁻¹) * z₁ := by rw [hc₂ a haX]
    _ = b' * a' * (b * a) * (z₂⁻¹ * z₁) := by group

theorem commutator_sq_mem_Z (h : Pair X T M V g) {x y : G}
    (hx : x ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V))
    (hy : y ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)) :
    x * y * x⁻¹ * y⁻¹ ∈ V ⊓ conjSub g V ∧ x ^ 2 ∈ V ⊓ conjSub g V := by
  have hPX : (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤ X :=
    h.P_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  constructor
  · obtain ⟨z, hz, e⟩ := h.exists_comm_P hx hy
    have hc := h.mem_center hz (X.mul_mem (hPX hy) (hPX hx))
    have : x * y * x⁻¹ * y⁻¹ = z := by
      rw [e, ← hc]
      group
    rw [this]
    exact hz
  · obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P_iff.mp hx
    obtain ⟨z, hz, e⟩ := h.exists_swap hb ha
    have hb2 : b ^ 2 = 1 := h.elem.2 b hb.2
    have ha2 : a ^ 2 = 1 := by
      have h1 := h.elem.2 _ (mem_conjSub.mp ((conjSub g).monotone inf_le_right ha))
      have h2 : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by
        have := conj_pow (a := g⁻¹) (b := a) (i := 2)
        simpa using this
      rw [h2] at h1
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
    have hc := fun w hw => h.mem_center (z := z) hz (x := w) hw
    have : (b * a) ^ 2 = z := by
      have hbX : b ∈ X := hPX (Subgroup.mem_sup_left hb)
      have haX : a ∈ X := hPX (Subgroup.mem_sup_right ha)
      calc (b * a) ^ 2 = b * (a * b) * a := by rw [pow_two]; group
        _ = b * (b * a * z) * a := by rw [e]
        _ = b * b * a * (z * a) := by group
        _ = b * b * a * (a * z) := by rw [hc a haX]
        _ = b ^ 2 * a ^ 2 * z := by rw [pow_two, pow_two]; group
        _ = z := by rw [hb2, ha2]; group
    rw [this]
    exact hz

theorem quadratic (h : Pair X T M V g) {x v₁ v₂ : G}
    (hx : x ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) :
    let c := fun (v y : G) => v * y * v⁻¹ * y⁻¹
    c v₂ (c v₁ x) = 1 := by
  intro c
  have h1 : c v₁ x ∈ kerIn M X ⊓ V := h.commutator_mem_B hv₁ (h.P_le_pCoreOf hx)
  have e := h.comm hv₂ h1.2
  show v₂ * c v₁ x * v₂⁻¹ * (c v₁ x)⁻¹ = 1
  rw [e]
  group

theorem mem_B_of_commutator_mem_Z (h : Pair X T M V g) {x : G}
    (hx : x ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V))
    (hxv : ∀ v ∈ V, v * x * v⁻¹ * x⁻¹ ∈ V ⊓ conjSub g V) : x ∈ kerIn M X ⊓ V := by
  set Z := V ⊓ conjSub g V with hZ
  have hPX : (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤ X :=
    h.P_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P_iff.mp hx
  have hbX : b ∈ X := hPX (Subgroup.mem_sup_left hb)
  have haX : a ∈ X := hPX (Subgroup.mem_sup_right ha)
  have haV : a ∈ conjSub g V := (conjSub g).monotone inf_le_right ha
  have hav : ∀ v ∈ V, v * a * v⁻¹ * a⁻¹ ∈ Z := by
    intro v hv
    have h1 := hxv v hv
    have hvb : v * b = b * v := h.comm hv hb.2
    have e : v * (b * a) * v⁻¹ * (b * a)⁻¹ = b * (v * a * v⁻¹ * a⁻¹) * b⁻¹ := by
      calc v * (b * a) * v⁻¹ * (b * a)⁻¹ = (v * b) * a * v⁻¹ * a⁻¹ * b⁻¹ := by group
        _ = (b * v) * a * v⁻¹ * a⁻¹ * b⁻¹ := by rw [hvb]
        _ = b * (v * a * v⁻¹ * a⁻¹) * b⁻¹ := by group
    rw [e] at h1
    have := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_Z (X.inv_mem hbX)) _).mp h1
    simpa [mul_assoc, hZ] using this
  let S : Subgroup G :=
    { carrier := {y | y ∈ X ∧ y * a * y⁻¹ * a⁻¹ ∈ Z}
      one_mem' := ⟨X.one_mem, by simp⟩
      mul_mem' := by
        rintro y y' ⟨hy, hya⟩ ⟨hy', hy'a⟩
        refine ⟨X.mul_mem hy hy', ?_⟩
        have e : y * y' * a * (y * y')⁻¹ * a⁻¹ =
            y * (y' * a * y'⁻¹ * a⁻¹) * y⁻¹ * (y * a * y⁻¹ * a⁻¹) := by group
        rw [e]
        refine Z.mul_mem ?_ hya
        have := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_Z hy) _).mp hy'a
        simpa [mul_assoc, hZ] using this
      inv_mem' := by
        rintro y ⟨hy, hya⟩
        refine ⟨X.inv_mem hy, ?_⟩
        have e : y⁻¹ * a * y⁻¹⁻¹ * a⁻¹ = y⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * y := by
          have hz := h.mem_center hya (X.inv_mem hy)
          calc y⁻¹ * a * y⁻¹⁻¹ * a⁻¹ = y⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * y * 1 := by
                  group
            _ = _ := by rw [mul_one]
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_Z (X.inv_mem hy)) _).mp
          (Z.inv_mem hya)
        simpa [mul_assoc, hZ] using this }
  have hXS : X ≤ S := by
    rw [h.gen]
    refine sup_le (fun v hv => ⟨h.V_le hv, hav v hv⟩) (fun w hw => ⟨h.conj_le hw, ?_⟩)
    rw [h.comm_conj hw haV]
    simp
  have hga := (hXS (X.inv_mem h.mem)).2
  have hBa : g⁻¹ * a * g ∈ kerIn M X ⊓ V := mem_conjSub.mp ha
  have haB : a ∈ kerIn M X ⊓ V := by
    have e : a = (g⁻¹ * a * g⁻¹⁻¹ * a⁻¹)⁻¹ * (g⁻¹ * a * g) := by group
    rw [e]
    exact (kerIn M X ⊓ V).mul_mem (h.inf_conj_le_kerIn_inf (Z.inv_mem hga)) hBa
  exact (kerIn M X ⊓ V).mul_mem hb haB

end Finite

end Pair

end E2

end CFSG.Quasithin
