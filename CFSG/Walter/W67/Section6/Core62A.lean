module

public import CFSG.Walter.Cited.HuppertPlane
public import CFSG.Walter.W67.Section6.Core61
public import CFSG.Walter.ReeOrder.JT.Section2

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G]

structure Hyp62 (r : ℕ) [Fact r.Prime] (J d x₀ y₀ : G) (P₀ P₁ M M₁ H₃ : Subgroup G) : Prop where
  r_ne_two : r ≠ 2
  perfect : commutator G = ⊤
  orderOf_J : orderOf J = 2
  P₀_cyc : IsCyclic P₀
  P₀_r : IsPGroup r P₀
  x₀_mem : x₀ ∈ P₀
  orderOf_x₀ : orderOf x₀ = r
  P₀_le : P₀ ≤ Subgroup.centralizer ({J} : Set G)
  normalizer_X : Subgroup.normalizer ((Subgroup.zpowers x₀ : Subgroup G) : Set G) = M
  M_le : M ≤ Subgroup.centralizer ({x₀} : Set G)
  P₁_cyc : IsCyclic P₁
  P₁_r : IsPGroup r P₁
  y₀_mem : y₀ ∈ P₁
  orderOf_y₀ : orderOf y₀ = r
  P₁_inv : ∀ y ∈ P₁, J * y * J⁻¹ = y⁻¹
  P₀_le_N : P₀ ≤ Subgroup.normalizer (P₁ : Set G)
  P₁_le_M : P₁ ≤ M
  P_card : Nat.card ↥(P₀ ⊔ P₁) = r ^ (Nat.card M).factorization r
  d_P₀ : d ∈ Subgroup.centralizer (P₀ : Set G)
  d_P₁ : d ∈ Subgroup.normalizer (P₁ : Set G)
  d_y₀ : d * y₀ * d⁻¹ ≠ y₀
  d_odd : Odd (orderOf d)
  M_pow : ∀ m ∈ M, m ^ Nat.card P₀ ∈ M₁
  P₀_M₁ : P₀ ⊓ M₁ = ⊥
  H_pow : ∀ h ∈ Subgroup.centralizer ({J} : Set G), h ^ Nat.card P₀ ∈ H₃
  P₀_H₃ : P₀ ⊓ H₃ = ⊥
  H_card : (Nat.card (Subgroup.centralizer ({J} : Set G))).factorization r =
    (Nat.card P₀).factorization r
  two_comm : ∀ T : Subgroup G, IsPGroup 2 T → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  two_sq : ∀ T : Subgroup G, IsPGroup 2 T → ∀ a ∈ T, a * a = 1
  no_real : ∀ u x t : G, orderOf u = 2 → x ∈ Subgroup.centralizer ({u} : Set G) →
    t ∈ Subgroup.centralizer ({u} : Set G) → t * t = 1 → t * x * t⁻¹ = x⁻¹ →
    IsPGroup r (Subgroup.zpowers x) → x = 1
  CP : ∀ t ∈ Subgroup.centralizer ((P₀ ⊔ P₁ : Subgroup G) : Set G), t * t = 1 → t = 1

theorem eq_of_le_cyclic {A H K : Subgroup G} [Finite A] (hA : IsCyclic A) (hH : H ≤ A)
    (hK : K ≤ A) (hc : Nat.card H = Nat.card K) : H = K := by
  have : Finite H := Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
  have : Finite K := Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)
  have h1 : H.subgroupOf A = K.subgroupOf A := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, hc]
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_of_le_left hH, inf_of_le_left hK] at h2

abbrev Vsub (x₀ y₀ : G) : Subgroup G := Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀

@[expose] def conjAut {S : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    MulAut S where
  toFun s := ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg s).mp s.2⟩
  invFun s := ⟨g⁻¹ * s * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * s * g)).mpr (by
    simp [mul_assoc])⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem conjAut_pow_apply {S : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    (n : ℕ) (s : S) : ((conjAut hg ^ n) s : G) = g ^ n * s * (g ^ n)⁻¹ := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    change g * ((conjAut hg ^ n) s : G) * g⁻¹ = _
    rw [ih, pow_succ']
    group

@[expose] def conjHom {N S : Subgroup G} (hN : N ≤ Subgroup.normalizer (S : Set G)) :
    N →* MulAut S where
  toFun n := conjAut (hN n.2)
  map_one' := MulEquiv.ext fun s => Subtype.ext (by simp [conjAut])
  map_mul' m n := MulEquiv.ext fun s => Subtype.ext (by simp [conjAut, mul_assoc])

theorem conjHom_apply {N S : Subgroup G} (hN : N ≤ Subgroup.normalizer (S : Set G)) (n : N)
    (s : S) : ((conjHom hN n s : S) : G) = n * s * (n : G)⁻¹ := rfl

section Finite

variable [Finite G]

theorem zpowers_eq_of_cyclic {A : Subgroup G} (hA : IsCyclic A) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) (hab : orderOf a = orderOf b) : Subgroup.zpowers a = Subgroup.zpowers b :=
  eq_of_le_cyclic hA (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hab])

theorem mem_centralizer_of_pow {r : ℕ} [Fact r.Prime] {S : Subgroup G} (hS : Nat.card S = r)
    {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) {k : ℕ} (hgk : g ^ r ^ k = 1) :
    g ∈ Subgroup.centralizer (S : Set G) := by
  have hσ : conjAut hg ^ r ^ k = 1 := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [conjAut_pow_apply, hgk, one_mul, inv_one, mul_one]
    rfl
  have h1 := Huppert.eq_one_of_card_dvd hσ (by rw [hS])
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨s, hs⟩)
  change g * s * g⁻¹ = s at h2
  calc s * g = g * s * g⁻¹ * g := by rw [h2]
    _ = g * s := by group

end Finite

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h


theorem J_mul_J : J * J = 1 := by rw [← pow_two, ← h.orderOf_J, pow_orderOf_eq_one]

theorem J_inv : J⁻¹ = J := inv_eq_of_mul_eq_one_right h.J_mul_J

theorem r_odd : Odd r := (Fact.out : r.Prime).odd_of_ne_two h.r_ne_two

theorem eq_one_of_sq {Q : Subgroup G} (hQ : IsPGroup r Q) {x : G} (hx : x ∈ Q)
    (hx2 : x * x = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx2])
  have h2 : Odd (orderOf x) := by rw [hk]; exact h.r_odd.pow
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · rw [h3] at h2
    exact absurd h2 (by decide)

theorem odd_orderOf {Q : Subgroup G} (hQ : IsPGroup r Q) {x : G} (hx : x ∈ Q) :
    Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact h.r_odd.pow

theorem inf_eq_bot : P₀ ⊓ P₁ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx₀, hx₁⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  have h1 := h.P₁_inv x hx₁
  have h2 : J * x * J⁻¹ = x := by
    rw [← (Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le hx₀)), mul_inv_cancel_right]
  rw [h2] at h1
  refine h.eq_one_of_sq h.P₀_r hx₀ ?_
  calc x * x = x * x⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel x

theorem mem_P {x : G} : x ∈ P₀ ⊔ P₁ ↔ ∃ b ∈ P₁, ∃ a ∈ P₀, b * a = x := by
  rw [sup_comm]
  exact mem_sup_iff_of_le_normalizer h.P₀_le_N

theorem J_mem_normalizer_P₀ : J ∈ Subgroup.normalizer (P₀ : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ ha =>
    (Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le ha)))

theorem d_mem_normalizer : d ∈ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) :=
  mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ h.d_P₀) h.d_P₁

theorem P₀_comm : ∀ a ∈ P₀, ∀ b ∈ P₀, a * b = b * a := comm_of_isCyclic h.P₀_cyc

theorem P₁_comm : ∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a := comm_of_isCyclic h.P₁_cyc

theorem x₀_mem_center : x₀ ∈ Subgroup.centralizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P.mp hp
  have hbx : b * x₀ = x₀ * b :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.M_le (h.P₁_le_M hb)))
  have hax : a * x₀ = x₀ * a := h.P₀_comm a ha x₀ h.x₀_mem
  calc b * a * x₀ = b * (a * x₀) := by group
    _ = b * (x₀ * a) := by rw [hax]
    _ = (b * x₀) * a := by group
    _ = (x₀ * b) * a := by rw [hbx]
    _ = x₀ * (b * a) := by group

theorem x₀_mem_P : x₀ ∈ P₀ ⊔ P₁ := Subgroup.mem_sup_left h.x₀_mem

theorem y₀_mem_P : y₀ ∈ P₀ ⊔ P₁ := Subgroup.mem_sup_right h.y₀_mem

theorem V_le_P : Vsub x₀ y₀ ≤ P₀ ⊔ P₁ :=
  sup_le (Subgroup.zpowers_le.mpr h.x₀_mem_P) (Subgroup.zpowers_le.mpr h.y₀_mem_P)

theorem X_inf_Y : Subgroup.zpowers x₀ ⊓ Subgroup.zpowers y₀ = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf (Subgroup.zpowers_le.mpr h.x₀_mem)
    (Subgroup.zpowers_le.mpr h.y₀_mem)).trans h.inf_eq_bot.le)

variable [Finite G]

theorem card_P : Nat.card ↥(P₀ ⊔ P₁) = Nat.card P₀ * Nat.card P₁ := by
  rw [sup_comm, card_sup_of_inf_eq_bot h.P₀_le_N (by rw [inf_comm]; exact h.inf_eq_bot),
    mul_comm]

theorem isPGroup_P : IsPGroup r ↥(P₀ ⊔ P₁) := by
  obtain ⟨a, ha⟩ := h.P₀_r.exists_card_eq
  obtain ⟨b, hb⟩ := h.P₁_r.exists_card_eq
  exact IsPGroup.of_card (n := a + b) (by rw [h.card_P, ha, hb, pow_add])

theorem J_mem_normalizer_P₁ : J ∈ Subgroup.normalizer (P₁ : Set G) := by
  apply JT.mem_normalizer_of_conj_mem
  intro y hy
  rw [h.P₁_inv y hy]
  exact P₁.inv_mem hy

theorem J_mem_normalizer : J ∈ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) :=
  mem_normalizer_sup h.J_mem_normalizer_P₀ h.J_mem_normalizer_P₁

theorem y₀_comm_P₀ {a : G} (ha : a ∈ P₀) : a * y₀ = y₀ * a := by
  have hz : Subgroup.zpowers (a * y₀ * a⁻¹) = Subgroup.zpowers y₀ := by
    have h1 : a * y₀ * a⁻¹ ∈ P₁ :=
      (Subgroup.mem_normalizer_iff.mp (h.P₀_le_N ha) y₀).mp h.y₀_mem
    exact zpowers_eq_of_cyclic h.P₁_cyc h1 h.y₀_mem (orderOf_conj_mul a y₀)
  have hN : a ∈ Subgroup.normalizer ((Subgroup.zpowers y₀ : Subgroup G) : Set G) := by
    apply JT.mem_normalizer_of_conj_mem
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, ← hz]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.P₀_r) ⟨a, ha⟩
  rw [Subgroup.orderOf_mk] at hk
  have hak : a ^ r ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
  have := mem_centralizer_of_pow (S := Subgroup.zpowers y₀)
    (by rw [Nat.card_zpowers, h.orderOf_y₀]) hN hak
  exact (Subgroup.mem_centralizer_iff.mp this y₀ (Subgroup.mem_zpowers y₀)).symm

theorem y₀_mem_center : y₀ ∈ Subgroup.centralizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P.mp hp
  have hby : b * y₀ = y₀ * b := h.P₁_comm b hb y₀ h.y₀_mem
  have hay := h.y₀_comm_P₀ ha
  calc b * a * y₀ = b * (a * y₀) := by group
    _ = b * (y₀ * a) := by rw [hay]
    _ = (b * y₀) * a := by group
    _ = (y₀ * b) * a := by rw [hby]
    _ = y₀ * (b * a) := by group

theorem x₀_comm_y₀ : x₀ * y₀ = y₀ * x₀ :=
  Subgroup.mem_centralizer_iff.mp h.y₀_mem_center x₀ h.x₀_mem_P

theorem V_le_center : Vsub x₀ y₀ ≤ Subgroup.centralizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) :=
  sup_le (Subgroup.zpowers_le.mpr h.x₀_mem_center) (Subgroup.zpowers_le.mpr h.y₀_mem_center)

theorem V_comm : ∀ a ∈ Vsub x₀ y₀, ∀ b ∈ Vsub x₀ y₀, a * b = b * a := fun a ha _ hb =>
  (Subgroup.mem_centralizer_iff.mp (h.V_le_center hb) a (h.V_le_P ha))

theorem Y_le_normalizer_X : Subgroup.zpowers y₀ ≤
    Subgroup.normalizer ((Subgroup.zpowers x₀ : Subgroup G) : Set G) := by
  rw [Subgroup.zpowers_le]
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Commute.zpow_left h.x₀_comm_y₀ n).eq

theorem card_V : Nat.card (Vsub x₀ y₀) = r ^ 2 := by
  rw [Vsub, card_sup_of_inf_eq_bot h.Y_le_normalizer_X h.X_inf_Y, Nat.card_zpowers,
    Nat.card_zpowers, h.orderOf_x₀, h.orderOf_y₀, sq]

theorem mem_V_iff {v : G} : v ∈ Vsub x₀ y₀ ↔
    ∃ a ∈ Subgroup.zpowers x₀, ∃ b ∈ Subgroup.zpowers y₀, a * b = v :=
  mem_sup_iff_of_le_normalizer h.Y_le_normalizer_X

theorem V_pow {v : G} (hv : v ∈ Vsub x₀ y₀) : v ^ r = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_V_iff.mp hv
  have hab : Commute a b := h.V_comm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)
  have key : ∀ (z : G) (n : ℤ), z ^ r = 1 → (z ^ n) ^ r = 1 := fun z n hz => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have hx : x₀ ^ r = 1 := by rw [← h.orderOf_x₀, pow_orderOf_eq_one]
  have hy : y₀ ^ r = 1 := by rw [← h.orderOf_y₀, pow_orderOf_eq_one]
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [hab.mul_pow, key x₀ i hx, key y₀ j hy, one_mul]

theorem plane : Huppert.Plane r (Vsub x₀ y₀) where
  comm a b := Subtype.ext (h.V_comm a a.2 b b.2)
  pow v := Subtype.ext (by rw [Subgroup.coe_pow, h.V_pow v.2]; rfl)
  card := h.card_V

theorem mem_X_of_pow {a : G} (ha : a ∈ P₀) (har : a ^ r = 1) : a ∈ Subgroup.zpowers x₀ := by
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp (orderOf_dvd_of_pow_eq_one har) with h1 | h1
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · rw [zpowers_eq_of_cyclic h.P₀_cyc h.x₀_mem ha (by rw [h1, h.orderOf_x₀])]
    exact Subgroup.mem_zpowers a

theorem mem_Y_of_pow {b : G} (hb : b ∈ P₁) (hbr : b ^ r = 1) : b ∈ Subgroup.zpowers y₀ := by
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp (orderOf_dvd_of_pow_eq_one hbr) with h1 | h1
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · rw [zpowers_eq_of_cyclic h.P₁_cyc h.y₀_mem hb (by rw [h1, h.orderOf_y₀])]
    exact Subgroup.mem_zpowers b

theorem mem_V_of {z : G} (hzP : z ∈ P₀ ⊔ P₁)
    (hzC : z ∈ Subgroup.centralizer ((P₀ ⊔ P₁ : Subgroup G) : Set G)) (hzr : z ^ r = 1) :
    z ∈ Vsub x₀ y₀ := by
  obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P.mp hzP
  have haC : ∀ y ∈ P₁, a * y = y * a := by
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp hzC y (Subgroup.mem_sup_right hy)
    have h2 := h.P₁_comm b hb y hy
    calc a * y = b⁻¹ * (b * a * y) := by group
      _ = b⁻¹ * (y * (b * a)) := by rw [h1]
      _ = b⁻¹ * ((y * b) * a) := by group
      _ = b⁻¹ * ((b * y) * a) := by rw [h2]
      _ = y * a := by group
  have hab : Commute a b := (haC b hb)
  have h1 : (b * a) ^ r = b ^ r * a ^ r := hab.symm.mul_pow r
  rw [h1] at hzr
  have hbr : b ^ r ∈ P₀ ⊓ P₁ := by
    refine Subgroup.mem_inf.mpr ⟨?_, P₁.pow_mem hb r⟩
    have : b ^ r = (a ^ r)⁻¹ := eq_inv_of_mul_eq_one_left hzr
    rw [this]
    exact P₀.inv_mem (P₀.pow_mem ha r)
  rw [h.inf_eq_bot, Subgroup.mem_bot] at hbr
  rw [hbr, one_mul] at hzr
  have hbY := h.mem_Y_of_pow hb hbr
  have haX := h.mem_X_of_pow ha hzr
  have : b * a = a * b := hab.eq.symm
  rw [this]
  exact h.mem_V_iff.mpr ⟨a, haX, b, hbY, rfl⟩

theorem normalizer_le : Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) ≤
    Subgroup.normalizer ((Vsub x₀ y₀ : Subgroup G) : Set G) := by
  intro n hn
  apply JT.mem_normalizer_of_conj_mem
  intro v hv
  refine h.mem_V_of ((Subgroup.mem_normalizer_iff.mp hn v).mp (h.V_le_P hv)) ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : n⁻¹ * p * n ∈ P₀ ⊔ P₁ :=
      (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * p * n)).mpr (by simpa [mul_assoc] using hp)
    have h1 := Subgroup.mem_centralizer_iff.mp (h.V_le_center hv) _ hp'
    calc p * (n * v * n⁻¹) = n * (n⁻¹ * p * n * v) * n⁻¹ := by group
      _ = n * (v * (n⁻¹ * p * n)) * n⁻¹ := by rw [h1]
      _ = n * v * n⁻¹ * p := by group
  · rw [conj_pow, h.V_pow hv]
    group

theorem inf_centralizer_eq {S : Subgroup G} (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S) :
    S ⊓ Subgroup.centralizer ({x₀} : Set G) = P₀ ⊔ P₁ := by
  have hle : P₀ ⊔ P₁ ≤ S ⊓ Subgroup.centralizer ({x₀} : Set G) := by
    refine le_inf hPS fun p hp => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h.x₀_mem_center p hp
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hM : S ⊓ Subgroup.centralizer ({x₀} : Set G) ≤ M := by
    rw [← h.normalizer_X]
    intro y hy
    have hy' : y ∈ Subgroup.centralizer ({x₀} : Set G) := (Subgroup.mem_inf.mp hy).2
    apply JT.mem_normalizer_of_conj_mem
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, Subgroup.mem_centralizer_singleton_iff.mp hy', mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  obtain ⟨k, hk⟩ := (hS.to_le (inf_le_left : S ⊓ Subgroup.centralizer ({x₀} : Set G) ≤ S)
    ).exists_card_eq
  have h1 : r ^ k ∣ Nat.card M := hk ▸ Subgroup.card_dvd_of_le hM
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h1
  rw [hk, h.P_card]
  exact Nat.pow_le_pow_right (Fact.out : r.Prime).pos h2

end Hyp62

end CFSG.Walter.W67.Sec6
