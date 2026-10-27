module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.RankThree.PartTwo.Sec11.Final1128Proof

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left' (y₁ y₂ w : G) :
    ⁅y₁ * y₂, w⁆ = y₁ * ⁅y₂, w⁆ * y₁⁻¹ * ⁅y₁, w⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right' (y w₁ w₂ : G) :
    ⁅y, w₁ * w₂⁆ = ⁅y, w₁⁆ * (w₁ * ⁅y, w₂⁆ * w₁⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_pow_left_of_commute {y w : G} (h : y * ⁅y, w⁆ = ⁅y, w⁆ * y)
    (k : ℕ) : ⁅y ^ k, w⁆ = ⁅y, w⁆ ^ k := by
  have hc : Commute y ⁅y, w⁆ := h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', commutatorElement_mul_left', ih, (hc.pow_right k).eq, mul_inv_cancel_right,
      pow_succ]

theorem commutatorElement_pow_right_of_commute {y w : G} (h : w * ⁅y, w⁆ = ⁅y, w⁆ * w)
    (k : ℕ) : ⁅y, w ^ k⁆ = ⁅y, w⁆ ^ k := by
  have hc : Commute w ⁅y, w⁆ := h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', commutatorElement_mul_right', ih, (hc.pow_right k).eq, mul_inv_cancel_right,
      pow_succ']

theorem conj_eq_commutatorElement_mul (y w : G) : y * w * y⁻¹ = ⁅y, w⁆ * w := by
  simp only [commutatorElement_def]
  group

theorem conj_commutatorElement (n y w : G) :
    n * ⁅y, w⁆ * n⁻¹ = ⁅n * y * n⁻¹, n * w * n⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_eq_one_of_commute {y w : G} (h : y * w = w * y) : ⁅y, w⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr h

theorem pow_mul_self_eq {δ : G} (hδ : δ ^ 3 = 1) {ρ : ℕ} (hρ : ¬ 3 ∣ ρ) : δ ^ (ρ * ρ) = δ := by
  have h1 : ρ * ρ % 3 = 1 := by
    have : ρ % 3 = 1 ∨ ρ % 3 = 2 := by omega
    rcases this with h | h <;> rw [Nat.mul_mod, h]
  calc δ ^ (ρ * ρ) = δ ^ (3 * (ρ * ρ / 3) + ρ * ρ % 3) := by rw [Nat.div_add_mod]
    _ = δ := by rw [pow_add, pow_mul, hδ, one_pow, one_mul, h1, pow_one]

theorem exists_pow_eq_of_orderOf_eq_three [Finite G] {d θ δ : G} (hd : orderOf d = 3)
    (hθ : θ ∈ Subgroup.zpowers d) (hθ1 : θ ≠ 1) (hδ : δ ∈ Subgroup.zpowers d) :
    ∃ m : ℕ, θ ^ m = δ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ3' : θ ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hθ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hd, pow_orderOf_eq_one,
      one_zpow]
  have hθ3 : orderOf θ = 3 := orderOf_eq_prime hθ3' hθ1
  have heq : Subgroup.zpowers θ = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hθ)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hd, hθ3])
  rw [← heq] at hδ
  obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers).mpr hδ
  exact ⟨m, hm⟩

structure Core (P A : Subgroup G) (c e d x g : G) : Prop where
  d_mem : d ∈ P
  d_comm : ∀ y ∈ P, y * d = d * y
  orderOf_d : orderOf d = 3
  le_P : A ≤ P
  c_mem : c ∈ A
  e_mem : e ∈ A
  d_mem_A : d ∈ A
  mul_comm_A : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y
  commutator_mem : ∀ y ∈ P, ∀ z ∈ A, ⁅y, z⁆ ∈ Subgroup.zpowers d
  x_mem : x ∈ P
  g_mem : g ∈ P
  commutator_eq : ⁅P, P⁆ = Subgroup.closure {e, d}
  x_e : ⁅x, e⁆ ≠ 1
  g_e : g * e = e * g
  theta_ne : ⁅x, ⁅x, g⁆⁆ ≠ 1
  centralizer_le : P ⊓ Subgroup.centralizer {e} ≤ Subgroup.zpowers g ⊔ A
  centralizer_c_le : P ⊓ Subgroup.centralizer {e} ⊓ Subgroup.centralizer {c} ≤ A
  centralizer_g_le : A ⊓ Subgroup.centralizer {g} ≤ Subgroup.closure {e, d}
  centralizer_x_le : Subgroup.closure {e, d} ⊓ Subgroup.centralizer {x} ≤ Subgroup.zpowers d

namespace Core

variable {P A : Subgroup G} {c e d x g : G}

theorem comm_of_mem_zpowers (h : Core P A c e d x g) {δ y : G} (hδ : δ ∈ Subgroup.zpowers d)
    (hy : y ∈ P) : y * δ = δ * y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
  exact ((show Commute y d from h.d_comm y hy).zpow_right k).eq

theorem closure_le_A (h : Core P A c e d x g) : Subgroup.closure {e, d} ≤ A := by
  rw [Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨h.e_mem, h.d_mem_A⟩

theorem commutator_mem_D (h : Core P A c e d x g) {y w : G} (hy : y ∈ P)
    (hw : w ∈ Subgroup.closure {e, d}) : ⁅y, w⁆ ∈ Subgroup.zpowers d :=
  h.commutator_mem y hy w (h.closure_le_A hw)

theorem commutatorElement_mem (h : Core P A c e d x g) {y w : G} (hy : y ∈ P) (hw : w ∈ P) :
    ⁅y, w⁆ ∈ Subgroup.closure {e, d} := by
  rw [← h.commutator_eq]
  exact Subgroup.commutator_mem_commutator hy hw

theorem comm_D (h : Core P A c e d x g) {y w : G} (hy : y ∈ P ⊓ Subgroup.centralizer {e})
    (hw : w ∈ Subgroup.closure {e, d}) : y * w = w * y := by
  obtain ⟨hyP, hye⟩ := Subgroup.mem_inf.mp hy
  have hye' : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.mp hye
  have hle : Subgroup.closure ({e, d} : Set G) ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hye'.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.d_comm y hyP).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm

theorem commutatorElement_zpowers (h : Core P A c e d x g) {y δ : G} (hy : y ∈ P)
    (hδ : δ ∈ Subgroup.zpowers d) : ⁅y, δ⁆ = 1 :=
  commutatorElement_eq_one_of_commute (h.comm_of_mem_zpowers hδ hy)

theorem x_not_mem (h : Core P A c e d x g) : x ∉ P ⊓ Subgroup.centralizer {e} := fun hx =>
  h.x_e (commutatorElement_eq_one_of_commute
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2))

theorem g_mem_C (h : Core P A c e d x g) : g ∈ P ⊓ Subgroup.centralizer {e} :=
  Subgroup.mem_inf.mpr ⟨h.g_mem, Subgroup.mem_centralizer_singleton_iff.mpr h.g_e⟩

theorem A_le_C (h : Core P A c e d x g) : A ≤ P ⊓ Subgroup.centralizer {e} := fun y hy =>
  Subgroup.mem_inf.mpr
    ⟨h.le_P hy, Subgroup.mem_centralizer_singleton_iff.mpr (h.mul_comm_A y hy e h.e_mem)⟩

theorem orderOf_x_e (h : Core P A c e d x g) : orderOf ⁅x, e⁆ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.commutator_mem x h.x_mem e h.e_mem)
  refine orderOf_eq_prime ?_ h.x_e
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    ← h.orderOf_d, pow_orderOf_eq_one, one_zpow]

theorem pow_three_of_mem (h : Core P A c e d x g) {δ : G} (hδ : δ ∈ Subgroup.zpowers d) :
    δ ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    ← h.orderOf_d, pow_orderOf_eq_one, one_zpow]

theorem exists_pow_eq [Finite G] (h : Core P A c e d x g) {θ δ : G}
    (hθ : θ ∈ Subgroup.zpowers d) (hθ1 : θ ≠ 1) (hδ : δ ∈ Subgroup.zpowers d) :
    ∃ m : ℕ, θ ^ m = δ :=
  exists_pow_eq_of_orderOf_eq_three h.orderOf_d hθ hθ1 hδ

theorem exists_mul_pow [Finite G] (h : Core P A c e d x g) {y : G} (hy : y ∈ P) :
    ∃ ρ : ℕ, y * (x ^ ρ)⁻¹ ∈ P ⊓ Subgroup.centralizer {e} ∧ ⁅y, e⁆ = ⁅x, e⁆ ^ ρ := by
  obtain ⟨ρ, hρ⟩ := h.exists_pow_eq (h.commutator_mem x h.x_mem e h.e_mem) h.x_e
    (h.commutator_mem y hy e h.e_mem)
  refine ⟨ρ, Subgroup.mem_inf.mpr ⟨P.mul_mem hy (P.inv_mem (P.pow_mem h.x_mem ρ)), ?_⟩,
    hρ.symm⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxe : x * ⁅x, e⁆ = ⁅x, e⁆ * x :=
    h.comm_of_mem_zpowers (h.commutator_mem x h.x_mem e h.e_mem) h.x_mem
  have hp : ⁅x ^ ρ, e⁆ = ⁅y, e⁆ := by rw [commutatorElement_pow_left_of_commute hxe, hρ]
  have hc : ⁅y * (x ^ ρ)⁻¹, e⁆ = 1 := by
    have e1 : ⁅y, e⁆ = ⁅y * (x ^ ρ)⁻¹ * x ^ ρ, e⁆ := by rw [inv_mul_cancel_right]
    rw [commutatorElement_mul_left', hp] at e1
    have hcen : y * (x ^ ρ)⁻¹ * ⁅y, e⁆ = ⁅y, e⁆ * (y * (x ^ ρ)⁻¹) :=
      h.comm_of_mem_zpowers (h.commutator_mem y hy e h.e_mem)
        (P.mul_mem hy (P.inv_mem (P.pow_mem h.x_mem ρ)))
    rw [hcen, mul_inv_cancel_right] at e1
    exact (mul_eq_left.mp e1.symm)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc)

theorem mem_normalizer_A [Finite G] (h : Core P A c e d x g) {y : G} (hy : y ∈ P) :
    y ∈ Subgroup.normalizer (A : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  rw [conj_eq_commutatorElement_mul]
  exact A.mul_mem (Subgroup.zpowers_le.mpr h.d_mem_A (h.commutator_mem y hy z hz)) hz

theorem exists_pow_mul [Finite G] (h : Core P A c e d x g) {y : G}
    (hy : y ∈ Subgroup.zpowers g ⊔ A) : ∃ m : ℕ, ∃ z ∈ A, y = g ^ m * z := by
  have hN : Subgroup.zpowers g ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr (h.mem_normalizer_A h.g_mem)
  have hy' : y ∈ ((Subgroup.zpowers g ⊔ A : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy'
  obtain ⟨u, hu, z, hz, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨m, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr hu
  exact ⟨m, z, hz, rfl⟩

theorem commutatorElement_mul_D (h : Core P A c e d x g) {y w₁ w₂ : G} (hy : y ∈ P)
    (hw₁ : w₁ ∈ Subgroup.closure {e, d}) (hw₂ : w₂ ∈ Subgroup.closure {e, d}) :
    ⁅y, w₁ * w₂⁆ = ⁅y, w₁⁆ * ⁅y, w₂⁆ := by
  rw [commutatorElement_mul_right',
    h.comm_of_mem_zpowers (h.commutator_mem_D hy hw₂) (h.le_P (h.closure_le_A hw₁)),
    mul_inv_cancel_right]

theorem commutatorElement_mul_zpowers (h : Core P A c e d x g) {y w δ : G} (hy : y ∈ P)
    (hw : w ∈ Subgroup.closure {e, d}) (hδ : δ ∈ Subgroup.zpowers d) : ⁅y, w * δ⁆ = ⁅y, w⁆ := by
  have hδD : δ ∈ Subgroup.closure {e, d} :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hδ
  rw [h.commutatorElement_mul_D hy hw hδD, h.commutatorElement_zpowers hy hδ, mul_one]

theorem commutator_g_mem [Finite G] (h : Core P A c e d x g) {γ : G}
    (hγ : γ ∈ P ⊓ Subgroup.centralizer {e}) : ⁅γ, g⁆ ∈ Subgroup.zpowers d := by
  obtain ⟨m, z, hz, rfl⟩ := h.exists_pow_mul (h.centralizer_le hγ)
  have hzg : ⁅z, g⁆ ∈ Subgroup.zpowers d := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (h.commutator_mem g h.g_mem z hz)
  rw [commutatorElement_mul_left', commutatorElement_eq_one_of_commute
    ((Commute.refl g).pow_left m).eq, mul_one,
    h.comm_of_mem_zpowers hzg (P.pow_mem h.g_mem m), mul_inv_cancel_right]
  exact hzg

theorem commutator_x_mul (h : Core P A c e d x g) {y₁ y₂ : G} (hy₁ : y₁ ∈ P) (hy₂ : y₂ ∈ P) :
    ⁅x, ⁅y₁ * y₂, g⁆⁆ = ⁅x, ⁅y₁, g⁆⁆ * ⁅x, ⁅y₂, g⁆⁆ := by
  have hw₁ := h.commutatorElement_mem hy₁ h.g_mem
  have hw₂ := h.commutatorElement_mem hy₂ h.g_mem
  have hδ := h.commutator_mem_D hy₁ hw₂
  have hδD : ⁅y₁, ⁅y₂, g⁆⁆ ∈ Subgroup.closure {e, d} :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hδ
  have e1 : ⁅y₁ * y₂, g⁆ = ⁅y₂, g⁆ * (⁅y₁, ⁅y₂, g⁆⁆ * ⁅y₁, g⁆) := by
    rw [commutatorElement_mul_left', conj_eq_commutatorElement_mul,
      (h.comm_of_mem_zpowers hδ (h.le_P (h.closure_le_A hw₂))).symm, mul_assoc]
  rw [e1, h.commutatorElement_mul_D h.x_mem hw₂ (Subgroup.mul_mem _ hδD hw₁),
    h.commutatorElement_mul_D h.x_mem hδD hw₁, h.commutatorElement_zpowers h.x_mem hδ, one_mul]
  exact (h.comm_of_mem_zpowers (h.commutator_mem_D h.x_mem hw₂)
    (h.le_P (h.closure_le_A (h.commutator_mem_D h.x_mem hw₁ |> fun hm =>
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hm)))).symm

theorem commutator_x_pow (h : Core P A c e d x g) (ρ : ℕ) :
    ⁅x, ⁅x ^ ρ, g⁆⁆ = ⁅x, ⁅x, g⁆⁆ ^ ρ := by
  induction ρ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, h.commutator_x_mul (P.pow_mem h.x_mem k) h.x_mem, ih, pow_succ]

theorem commutator_eq_pow (h : Core P A c e d x g) {γ w : G}
    (hγ : γ ∈ P ⊓ Subgroup.centralizer {e}) (hw : w ∈ Subgroup.closure {e, d}) (ρ : ℕ) :
    ⁅γ * x ^ ρ, w⁆ = ⁅x, w⁆ ^ ρ := by
  have hxw := h.commutator_mem_D h.x_mem hw
  have hxρ : ⁅x ^ ρ, w⁆ = ⁅x, w⁆ ^ ρ :=
    commutatorElement_pow_left_of_commute (h.comm_of_mem_zpowers hxw h.x_mem) ρ
  have hxρw : ⁅x ^ ρ, w⁆ ∈ Subgroup.zpowers d := h.commutator_mem_D (P.pow_mem h.x_mem ρ) hw
  rw [commutatorElement_mul_left', commutatorElement_eq_one_of_commute (h.comm_D hγ hw), mul_one,
    h.comm_of_mem_zpowers hxρw (Subgroup.mem_inf.mp hγ).1, mul_inv_cancel_right, hxρ]

theorem theta_eq [Finite G] (h : Core P A c e d x g) {y : G} (hy : y ∈ P)
    (hyC : y ∉ P ⊓ Subgroup.centralizer {e}) : ⁅y, ⁅y, g⁆⁆ = ⁅x, ⁅x, g⁆⁆ := by
  obtain ⟨ρ, hγ, hye⟩ := h.exists_mul_pow hy
  set γ := y * (x ^ ρ)⁻¹ with hγdef
  have hyγ : y = γ * x ^ ρ := by rw [hγdef, inv_mul_cancel_right]
  have hρ : ¬ 3 ∣ ρ := by
    rintro ⟨k, rfl⟩
    apply hyC
    refine Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : ⁅y, e⁆ = 1 := by
      rw [hye, pow_mul, ← h.orderOf_x_e, pow_orderOf_eq_one, one_pow]
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hθ := h.commutator_mem_D h.x_mem (h.commutatorElement_mem h.x_mem h.g_mem)
  have hwy := h.commutatorElement_mem hy h.g_mem
  have h1 : ⁅y, ⁅y, g⁆⁆ = ⁅x, ⁅y, g⁆⁆ ^ ρ := by
    have := h.commutator_eq_pow hγ hwy ρ
    rwa [← hyγ] at this
  have h2 : ⁅x, ⁅y, g⁆⁆ = ⁅x, ⁅x, g⁆⁆ ^ ρ := by
    rw [hyγ, h.commutator_x_mul (Subgroup.mem_inf.mp hγ).1 (P.pow_mem h.x_mem ρ),
      h.commutatorElement_zpowers h.x_mem (h.commutator_g_mem hγ), one_mul, h.commutator_x_pow]
  rw [h1, h2, ← pow_mul, pow_mul_self_eq (h.pow_three_of_mem hθ) hρ]

theorem exists_orient [Finite G] (h : Core P A c e d x g) :
    ∃ s₀ : ℕ, ⁅x, ⁅x, g⁆⁆ ^ s₀ = ⁅g, c⁆ :=
  h.exists_pow_eq (h.commutator_mem_D h.x_mem (h.commutatorElement_mem h.x_mem h.g_mem))
    h.theta_ne (h.commutator_mem g h.g_mem c h.c_mem)

theorem orient [Finite G] (h : Core P A c e d x g) {s₀ : ℕ}
    (hs₀ : ⁅x, ⁅x, g⁆⁆ ^ s₀ = ⁅g, c⁆) {y : G} (hy : y ∈ P)
    (hyC : y ∉ P ⊓ Subgroup.centralizer {e}) {h' : G} (hh' : h' ∈ P ⊓ Subgroup.centralizer {e}) :
    ⁅h', c⁆ = ⁅y, ⁅y, h'⁆⁆ ^ s₀ := by
  obtain ⟨m, z, hz, rfl⟩ := h.exists_pow_mul (h.centralizer_le hh')
  have hgc := h.commutator_mem g h.g_mem c h.c_mem
  have hyz := h.commutator_mem y hy z hz
  have hyg := h.commutatorElement_mem hy h.g_mem
  have hL : ⁅g ^ m * z, c⁆ = ⁅g, c⁆ ^ m := by
    rw [commutatorElement_mul_left', commutatorElement_eq_one_of_commute
      (h.mul_comm_A z hz c h.c_mem), mul_one, mul_inv_cancel, one_mul,
      commutatorElement_pow_left_of_commute (h.comm_of_mem_zpowers hgc h.g_mem)]
  have hgD : g * ⁅y, g⁆ = ⁅y, g⁆ * g := h.comm_D h.g_mem_C hyg
  have hygm : ⁅y, g ^ m⁆ = ⁅y, g⁆ ^ m := commutatorElement_pow_right_of_commute hgD m
  have hR1 : ⁅y, g ^ m * z⁆ = ⁅y, g ^ m⁆ * ⁅y, z⁆ := by
    rw [commutatorElement_mul_right', h.comm_of_mem_zpowers hyz (P.pow_mem h.g_mem m),
      mul_inv_cancel_right]
  have hygmD : ⁅y, g ^ m⁆ ∈ Subgroup.closure {e, d} :=
    h.commutatorElement_mem hy (P.pow_mem h.g_mem m)
  have hR2 : ⁅y, ⁅y, g ^ m * z⁆⁆ = ⁅y, ⁅y, g⁆⁆ ^ m := by
    rw [hR1, h.commutatorElement_mul_zpowers hy hygmD hyz, hygm]
    exact commutatorElement_pow_right_of_commute
      (h.comm_of_mem_zpowers (h.commutator_mem_D hy hyg) (h.le_P (h.closure_le_A hyg))) m
  rw [hL, hR2, h.theta_eq hy hyC, ← hs₀, ← pow_mul, ← pow_mul, mul_comm]

theorem conj_mem_commutator {n z : G} (hn : n ∈ Subgroup.normalizer (P : Set G))
    (hz : z ∈ ⁅P, P⁆) : n * z * n⁻¹ ∈ ⁅P, P⁆ := by
  have hP : P.map (MulAut.conj n).toMonoidHom = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hmap : (⁅P, P⁆ : Subgroup G).map (MulAut.conj n).toMonoidHom = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, hP]
  rw [← hmap]
  exact ⟨z, hz, by simp [MulAut.conj_apply]⟩

theorem conj_mem_C (h : Core P A c e d x g) {n y : G} (hn : n ∈ Subgroup.normalizer (P : Set G))
    (hy : y ∈ P ⊓ Subgroup.centralizer {e}) : n * y * n⁻¹ ∈ P ⊓ Subgroup.centralizer {e} := by
  have hn' : n⁻¹ ∈ Subgroup.normalizer (P : Set G) := inv_mem hn
  have hw : n⁻¹ * e * n⁻¹⁻¹ ∈ Subgroup.closure {e, d} := by
    rw [← h.commutator_eq]
    refine conj_mem_commutator hn' ?_
    rw [h.commutator_eq]
    exact Subgroup.subset_closure (by simp)
  have hyw := h.comm_D hy hw
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn y).mp (Subgroup.mem_inf.mp hy).1,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc n * y * n⁻¹ * e = n * (y * (n⁻¹ * e * n⁻¹⁻¹)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * e * n⁻¹⁻¹) * y) * n⁻¹ := by rw [hyw]
    _ = e * (n * y * n⁻¹) := by group

theorem conj_mem [Finite G] (h : Core P A c e d x g) {n : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G)) : c⁻¹ * (n * c * n⁻¹) ∈ Subgroup.closure {e, d} := by
  obtain ⟨s₀, hs₀⟩ := h.exists_orient
  have hn' : n⁻¹ ∈ Subgroup.normalizer (P : Set G) := inv_mem hn
  have hcC : c ∈ P ⊓ Subgroup.centralizer {e} := h.A_le_C h.c_mem
  have hxn : n * x * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn x).mp h.x_mem
  have hxnC : n * x * n⁻¹ ∉ P ⊓ Subgroup.centralizer {e} := by
    intro hm
    apply h.x_not_mem
    have := h.conj_mem_C hn' hm
    simpa [mul_assoc] using this
  have key : ∀ h' ∈ P ⊓ Subgroup.centralizer {e}, ⁅h', n * c * n⁻¹⁆ = ⁅h', c⁆ := by
    intro h' hh'
    have hh₀ : n⁻¹ * h' * n⁻¹⁻¹ ∈ P ⊓ Subgroup.centralizer {e} := h.conj_mem_C hn' hh'
    have h1 := h.orient hs₀ h.x_mem h.x_not_mem hh₀
    have h2 : n * ⁅n⁻¹ * h' * n⁻¹⁻¹, c⁆ * n⁻¹ =
        n * ⁅x, ⁅x, n⁻¹ * h' * n⁻¹⁻¹⁆⁆ ^ s₀ * n⁻¹ := by rw [h1]
    rw [conj_commutatorElement, ← conj_pow, conj_commutatorElement, conj_commutatorElement]
      at h2
    have e1 : n * (n⁻¹ * h' * n⁻¹⁻¹) * n⁻¹ = h' := by group
    rw [e1] at h2
    rw [h2, h.orient hs₀ hxn hxnC hh']
  set z := c⁻¹ * (n * c * n⁻¹) with hz
  have hzC : z ∈ P ⊓ Subgroup.centralizer {e} :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hcC) (h.conj_mem_C hn hcC)
  have hcomm : ∀ h' ∈ P ⊓ Subgroup.centralizer {e}, h' * z = z * h' := by
    intro h' hh'
    have h1 : ⁅h', z⁆ = ⁅h', c⁻¹ * c⁆ := by
      rw [hz, commutatorElement_mul_right', key h' hh', ← commutatorElement_mul_right']
    rw [inv_mul_cancel, commutatorElement_one_right] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hzA : z ∈ A := h.centralizer_c_le (Subgroup.mem_inf.mpr ⟨hzC,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcC).symm⟩)
  exact h.centralizer_g_le (Subgroup.mem_inf.mpr ⟨hzA,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm g h.g_mem_C).symm⟩)

theorem mem_zpowers_of_central (h : Core P A c e d x g) {y : G} (hy : y ∈ P)
    (hcen : ∀ z ∈ P, z * y = y * z) : y ∈ Subgroup.zpowers d := by
  have hyC : y ∈ P ⊓ Subgroup.centralizer {e} := Subgroup.mem_inf.mpr ⟨hy,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcen e (h.le_P h.e_mem)).symm⟩
  have hyA : y ∈ A := h.centralizer_c_le (Subgroup.mem_inf.mpr ⟨hyC,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcen c (h.le_P h.c_mem)).symm⟩)
  have hyD : y ∈ Subgroup.closure {e, d} := h.centralizer_g_le (Subgroup.mem_inf.mpr ⟨hyA,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcen g h.g_mem).symm⟩)
  exact h.centralizer_x_le (Subgroup.mem_inf.mpr ⟨hyD,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcen x h.x_mem).symm⟩)

end Core

section Norm

theorem mem_commutator_subtype_iff {P : Subgroup G} (z : P) :
    z ∈ commutator P ↔ (z : G) ∈ ⁅P, P⁆ := by
  have hmap : (commutator P).map P.subtype = ⁅P, P⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := Subtype.ext hwz
    rwa [← hwz']

variable [Finite G]

theorem mem_commutator_of_forall_conj {P : Subgroup G} (hP : IsPGroup 3 P)
    (hind : ¬ 3 ∣ P.relIndex (Subgroup.normalizer (P : Set G)))
    (hY : P = ⁅P, Subgroup.normalizer (P : Set G)⁆) {c : G} (hcP : c ∈ P) (hc3 : c ^ 3 = 1)
    (hfix : ∀ n ∈ Subgroup.normalizer (P : Set G), c⁻¹ * (n * c * n⁻¹) ∈ ⁅P, P⁆) :
    c ∈ ⁅P, P⁆ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (P : Set G) with hNdef
  set P' : Subgroup N := P.subgroupOf N with hP'def
  have hP'n : P'.Normal := Subgroup.normal_in_normalizer
  have hcard : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hcop3 : Nat.Coprime 3 P'.index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hind
  have hcop : Nat.Coprime (Nat.card P') P'.index := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rw [hcard, hk]
    exact Nat.Coprime.pow_left _ hcop3
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKcard : P'.index = Nat.card K := hK.symm.index_eq_card
  let ψ : N → (P →* Abelianization P) := fun n =>
    Abelianization.of.comp (P.normalizerMonoidHom n).toMonoidHom
  have hψ : ∀ (n : N) (y : P), ψ n y = Abelianization.of (P.normalizerMonoidHom n y) :=
    fun _ _ => rfl
  have hψmul : ∀ (n₁ n₂ : N) (y : P),
      ψ n₁ (P.normalizerMonoidHom n₂ y) = ψ (n₁ * n₂) y := by
    intro n₁ n₂ y
    rw [hψ, hψ, map_mul, MulAut.mul_apply]
  have hinner : ∀ p : N, (p : G) ∈ P → ∀ (n : N) (y : P), ψ (p * n) y = ψ n y := by
    intro p hp n y
    rw [← hψmul, hψ, hψ]
    have e : P.normalizerMonoidHom p (P.normalizerMonoidHom n y) =
        ⟨p, hp⟩ * P.normalizerMonoidHom n y * (⟨p, hp⟩ : P)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have : Fintype K := Fintype.ofFinite K
  let T : P →* Abelianization P := ∏ k : K, ψ (k : N)
  have hT : ∀ y : P, T y = ∏ k : K, ψ (k : N) y := fun y => by
    simp only [T, MonoidHom.finsetProd_apply]
  have hTp : ∀ p : N, (p : G) ∈ P → ∀ y : P, T (P.normalizerMonoidHom p y) = T y := by
    intro p hp y
    rw [hT, hT]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hkp : (k : N) * p * (k : N)⁻¹ ∈ P' :=
      hP'n.conj_mem p (Subgroup.mem_subgroupOf.mpr hp) (k : N)
    have e2 : (k : N) * p = ((k : N) * p * (k : N)⁻¹) * (k : N) := by group
    rw [hψmul, e2, hinner _ (Subgroup.mem_subgroupOf.mp hkp)]
  have hTk : ∀ (k₀ : K) (y : P), T (P.normalizerMonoidHom (k₀ : N) y) = T y := by
    intro k₀ y
    rw [hT, hT]
    have e1 : ∀ k : K, ψ (k : N) (P.normalizerMonoidHom (k₀ : N) y) = ψ ((k * k₀ : K) : N) y := by
      intro k
      rw [hψmul, Subgroup.coe_mul]
    simp_rw [e1]
    exact Fintype.prod_equiv (Equiv.mulRight k₀) _ _ (fun k => rfl)
  have hTn : ∀ (n : N) (y : P), T (P.normalizerMonoidHom n y) = T y := by
    intro n y
    obtain ⟨⟨p, k⟩, hpk, -⟩ := (Subgroup.isComplement'_def.mp hK).existsUnique n
    rw [← hpk, map_mul, MulAut.mul_apply, hTp (p : N) (Subgroup.mem_subgroupOf.mp p.2),
      hTk ⟨(k : N), k.2⟩ y]
  have hle : ⁅P, N⁆ ≤ (T.ker).map P.subtype := by
    rw [Subgroup.commutator_le]
    intro y hy n hn
    have hm' : n * y⁻¹ * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn y⁻¹).mp (P.inv_mem hy)
    have hm : ⁅y, n⁆ ∈ P := by
      rw [show ⁅y, n⁆ = y * (n * y⁻¹ * n⁻¹) by simp only [commutatorElement_def]; group]
      exact P.mul_mem hy hm'
    refine ⟨⟨⁅y, n⁆, hm⟩, ?_, rfl⟩
    have e : (⟨⁅y, n⁆, hm⟩ : P) = ⟨y, hy⟩ * P.normalizerMonoidHom ⟨n, hn⟩ (⟨y, hy⟩⁻¹) := by
      apply Subtype.ext
      change y * n * y⁻¹ * n⁻¹ = y * (n * y⁻¹ * n⁻¹)
      group
    change T ⟨⁅y, n⁆, hm⟩ = 1
    rw [e, map_mul, hTn, map_inv, mul_inv_cancel]
  have hcN : c ∈ ⁅P, N⁆ := by
    rw [← hY]
    exact hcP
  have hc1 : T ⟨c, hcP⟩ = 1 := by
    obtain ⟨w, hw, hwc⟩ := hle hcN
    have hwc' : w = ⟨c, hcP⟩ := Subtype.ext hwc
    rw [← hwc']
    exact hw
  have hfixk : ∀ k : K, ψ (k : N) ⟨c, hcP⟩ = Abelianization.of ⟨c, hcP⟩ := by
    intro k
    rw [hψ]
    have hmem : (⟨c, hcP⟩ : P)⁻¹ * P.normalizerMonoidHom (k : N) ⟨c, hcP⟩ ∈ commutator P := by
      rw [mem_commutator_subtype_iff]
      exact hfix _ (k : N).2
    have h1 : Abelianization.of ((⟨c, hcP⟩ : P)⁻¹ * P.normalizerMonoidHom (k : N) ⟨c, hcP⟩) =
        1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      exact hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hTc : T ⟨c, hcP⟩ = Abelianization.of ⟨c, hcP⟩ ^ Nat.card K := by
    rw [hT, Finset.prod_congr rfl (fun k _ => hfixk k), Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hpow3 : Abelianization.of (⟨c, hcP⟩ : P) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨c, hcP⟩ : P) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [h3, map_one]
  have hcopK : Nat.Coprime 3 (Nat.card K) := hKcard ▸ hcop3
  have hord : orderOf (Abelianization.of (⟨c, hcP⟩ : P)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopK (orderOf_dvd_of_pow_eq_one hpow3)
      (orderOf_dvd_of_pow_eq_one (hTc ▸ hc1))
  have hmem : (⟨c, hcP⟩ : P) ∈ commutator P := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp hord
  exact (mem_commutator_subtype_iff _).mp hmem

end Norm

end CFSG.RankThree.PartTwo.Sec11.Final1128Proof
