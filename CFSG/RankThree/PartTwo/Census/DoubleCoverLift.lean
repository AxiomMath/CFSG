module

public import CFSG.Foundations.Basic
public import CFSG.RankThree.PartOne.KP.CentralCoverThree
public import Mathlib.Order.CompletePartialOrder
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace DoubleCoverLift

open scoped commutatorElement IsMulCommutative

section Independent

noncomputable def elem2PowHom {C : Type*} [CommGroup C] {r : ℕ} (u : Fin r → C)
    (hu : ∀ i, u i ^ 2 = 1) : (Fin r → Multiplicative (ZMod 2)) →* C where
  toFun v := ∏ i, u i ^ (Multiplicative.toAdd (v i)).val
  map_one' := by simp
  map_mul' v w := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hu i), pow_add]

theorem exists_prodHom {G : Type*} [Group G] {r : ℕ} (u : Fin r → G)
    (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hind : ∀ v : Fin r → Fin 2, v ≠ 0 → (List.ofFn fun i => u i ^ (v i : ℕ)).prod ≠ 1) :
    ∃ φ : (Fin r → Multiplicative (ZMod 2)) →* G, Function.Injective φ ∧
      ∀ v, φ v = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (v i)).val).prod := by
  set C := Subgroup.closure (Set.range u)
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let w : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hw : ∀ i, w i ^ 2 = 1 := fun i => Subtype.ext (by simpa [w] using hsq i)
  let φ : (Fin r → Multiplicative (ZMod 2)) →* G := C.subtype.comp (elem2PowHom w hw)
  have hφ : ∀ v, φ v = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (v i)).val).prod := by
    intro v
    simp only [φ, MonoidHom.comp_apply, elem2PowHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  refine ⟨φ, ?_, hφ⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [MonoidHom.mem_ker, hφ] at hv
  rw [Subgroup.mem_bot]
  by_contra hne
  refine hind (fun i => Multiplicative.toAdd (v i)) (fun h0 => hne ?_) hv
  funext i
  exact Multiplicative.toAdd.injective (congrFun h0 i)

theorem pi_pow_two_eq_one {r : ℕ} (v : Fin r → Multiplicative (ZMod 2)) : v ^ 2 = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  generalize Multiplicative.toAdd (v i) = z
  revert z
  decide

theorem le_pRank_two_of_card {G : Type*} [Group G] [Finite G] {r : ℕ} (A : Subgroup G)
    (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 2 ^ r) : r ≤ CFSG.pRank 2 G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨A, hA, hcard⟩
  rintro k ⟨B, -, hB⟩
  calc k ≤ 2 ^ k := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

theorem le_pRank_two_of_independent {G : Type*} [Group G] [Finite G] {r : ℕ} (u : Fin r → G)
    (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hind : ∀ v : Fin r → Fin 2, v ≠ 0 → (List.ofFn fun i => u i ^ (v i : ℕ)).prod ≠ 1) :
    r ≤ CFSG.pRank 2 G := by
  obtain ⟨φ, hinj, -⟩ := exists_prodHom u hsq hcomm hind
  have hEA : CFSG.IsElementaryAbelian 2 φ.range :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
        apply Subtype.ext
        change (a : G) * b = b * a
        rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
        apply Subtype.ext
        change (a : G) ^ 2 = 1
        rw [← hx, ← map_pow, pi_pow_two_eq_one, map_one] }
  have hcard : Nat.card φ.range = 2 ^ r := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_eq_fintype_card]
  exact le_pRank_two_of_card φ.range hEA hcard

end Independent

section Datum

variable {X : Type*} [Group X]

structure E8Datum (a₁ a₂ a₃ n : X) : Prop where
  ne_one : a₁ ≠ 1
  sq : a₁ ^ 2 = 1
  comm₁₂ : Commute a₁ a₂
  comm₁₃ : Commute a₁ a₃
  conj₁ : n * a₁ * n⁻¹ = a₂
  conj₂ : n * a₂ * n⁻¹ = a₃
  conj₃ : n * a₃ * n⁻¹ = a₁ * a₂

namespace E8Datum

variable {a₁ a₂ a₃ n : X} (h : E8Datum a₁ a₂ a₃ n)
include h

theorem sq₂ : a₂ ^ 2 = 1 := by
  rw [← h.conj₁, conj_pow, h.sq, mul_one, mul_inv_cancel]

theorem sq₃ : a₃ ^ 2 = 1 := by
  rw [← h.conj₂, conj_pow, h.sq₂, mul_one, mul_inv_cancel]

theorem comm₂₃ : Commute a₂ a₃ := by
  have := h.comm₁₂.map (MulAut.conj n)
  simpa only [MulAut.conj_apply, h.conj₁, h.conj₂] using this

theorem map {Y : Type*} [Group Y] (f : X →* Y) (hf : Function.Injective f) :
    E8Datum (f a₁) (f a₂) (f a₃) (f n) where
  ne_one := fun e => h.ne_one (hf (by rw [e, map_one]))
  sq := by rw [← map_pow, h.sq, map_one]
  comm₁₂ := h.comm₁₂.map f
  comm₁₃ := h.comm₁₃.map f
  conj₁ := by rw [← map_inv, ← map_mul, ← map_mul, h.conj₁]
  conj₂ := by rw [← map_inv, ← map_mul, ← map_mul, h.conj₂]
  conj₃ := by rw [← map_inv, ← map_mul, ← map_mul, h.conj₃, map_mul]

omit h in
theorem of_map {Y : Type*} [Group Y] (f : X →* Y) (hf : Function.Injective f)
    (h : E8Datum (f a₁) (f a₂) (f a₃) (f n)) : E8Datum a₁ a₂ a₃ n where
  ne_one := fun e => h.ne_one (by rw [e, map_one])
  sq := hf (by rw [map_pow, h.sq, map_one])
  comm₁₂ := hf (by rw [map_mul, map_mul]; exact h.comm₁₂.eq)
  comm₁₃ := hf (by rw [map_mul, map_mul]; exact h.comm₁₃.eq)
  conj₁ := hf (by rw [map_mul, map_mul, map_inv]; exact h.conj₁)
  conj₂ := hf (by rw [map_mul, map_mul, map_inv]; exact h.conj₂)
  conj₃ := hf (by rw [map_mul, map_mul, map_inv, map_mul]; exact h.conj₃)

theorem prod_ne_one (i j k : Fin 2) (hijk : (i, j, k) ≠ (0, 0, 0)) :
    a₁ ^ (i : ℕ) * a₂ ^ (j : ℕ) * a₃ ^ (k : ℕ) ≠ 1 := by
  have hc : ∀ x : X, x ≠ 1 → n * x * n⁻¹ ≠ 1 := fun x hx e => hx (conj_eq_one_iff.mp e)
  have p₁ : a₁ ≠ 1 := h.ne_one
  have p₂ : a₂ ≠ 1 := h.conj₁ ▸ hc _ p₁
  have p₃ : a₃ ≠ 1 := h.conj₂ ▸ hc _ p₂
  have p₄ : a₁ * a₂ ≠ 1 := h.conj₃ ▸ hc _ p₃
  have p₅ : a₂ * a₃ ≠ 1 := by
    have e : n * (a₁ * a₂) * n⁻¹ = a₂ * a₃ := by
      calc n * (a₁ * a₂) * n⁻¹ = (n * a₁ * n⁻¹) * (n * a₂ * n⁻¹) := by group
        _ = a₂ * a₃ := by rw [h.conj₁, h.conj₂]
    exact e ▸ hc _ p₄
  have p₆ : a₁ * a₂ * a₃ ≠ 1 := by
    have e : n * (a₂ * a₃) * n⁻¹ = a₁ * a₂ * a₃ := by
      calc n * (a₂ * a₃) * n⁻¹ = (n * a₂ * n⁻¹) * (n * a₃ * n⁻¹) := by group
        _ = a₃ * (a₁ * a₂) := by rw [h.conj₂, h.conj₃]
        _ = a₁ * a₂ * a₃ := ((h.comm₁₃.mul_left h.comm₂₃).eq).symm
    exact e ▸ hc _ p₅
  have p₇ : a₁ * a₃ ≠ 1 := by
    have e : n * (a₁ * a₂ * a₃) * n⁻¹ = a₁ * a₃ := by
      have h22 : a₂ * a₂ = 1 := by rw [← pow_two]; exact h.sq₂
      calc n * (a₁ * a₂ * a₃) * n⁻¹
          = (n * a₁ * n⁻¹) * (n * a₂ * n⁻¹) * (n * a₃ * n⁻¹) := by group
        _ = a₂ * a₃ * (a₁ * a₂) := by rw [h.conj₁, h.conj₂, h.conj₃]
        _ = a₂ * (a₃ * a₁) * a₂ := by simp only [mul_assoc]
        _ = (a₂ * a₁) * a₃ * a₂ := by rw [← h.comm₁₃.eq]; simp only [mul_assoc]
        _ = a₁ * (a₂ * a₃) * a₂ := by rw [← h.comm₁₂.eq]; simp only [mul_assoc]
        _ = a₁ * a₃ * (a₂ * a₂) := by rw [h.comm₂₃.eq]; simp only [mul_assoc]
        _ = a₁ * a₃ := by rw [h22, mul_one]
    exact e ▸ hc _ p₆
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

end E8Datum

end Datum

section Lift

variable {X J : Type*} [Group X] [Group J] {φ : J →* X} {a₁ a₂ a₃ n : X}

open CFSG.RankThree.PartOne.CentralCoverThree in
theorem E8Datum.commutator_eq_one (h : E8Datum a₁ a₂ a₃ n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) {b₁ b₂ b₃ : J} (hb₁ : φ b₁ = a₁) (hb₂ : φ b₂ = a₂)
    (hb₃ : φ b₃ = a₃) : ⁅b₁, b₂⁆ = 1 ∧ ⁅b₁, b₃⁆ = 1 ∧ ⁅b₂, b₃⁆ = 1 := by
  obtain ⟨m, hm⟩ := hφ n
  have Z12 : ⁅b₁, b₂⁆ ∈ Subgroup.center J :=
    commutator_mem_center_of_commute hker (by rw [hb₁, hb₂]; exact h.comm₁₂)
  have Z13 : ⁅b₁, b₃⁆ ∈ Subgroup.center J :=
    commutator_mem_center_of_commute hker (by rw [hb₁, hb₃]; exact h.comm₁₃)
  have Z23 : ⁅b₂, b₃⁆ ∈ Subgroup.center J :=
    commutator_mem_center_of_commute hker (by rw [hb₂, hb₃]; exact h.comm₂₃)
  have Z32 : ⁅b₃, b₂⁆ ∈ Subgroup.center J :=
    commutator_mem_center_of_commute hker (by rw [hb₂, hb₃]; exact h.comm₂₃.symm)
  have hconj : ∀ x y : J, ⁅x, y⁆ ∈ Subgroup.center J → ⁅m * x * m⁻¹, m * y * m⁻¹⁆ = ⁅x, y⁆ :=
    fun x y hxy => by
      rw [← conjugate_commutatorElement, Subgroup.mem_center_iff.mp hxy m, mul_inv_cancel_right]
  have hm₁ : φ (m * b₁ * m⁻¹) = a₂ := by rw [map_mul, map_mul, map_inv, hm, hb₁, h.conj₁]
  have hm₂ : φ (m * b₂ * m⁻¹) = a₃ := by rw [map_mul, map_mul, map_inv, hm, hb₂, h.conj₂]
  have hm₃ : φ (m * b₃ * m⁻¹) = φ (b₁ * b₂) := by
    rw [map_mul, map_mul, map_inv, hm, hb₃, h.conj₃, map_mul, hb₁, hb₂]
  have E1 : ⁅b₂, b₃⁆ = ⁅b₁, b₂⁆ := by
    rw [← hconj b₁ b₂ Z12]
    exact commutator_eq_of_map_eq hker (by rw [hm₁, hb₂]) (by rw [hm₂, hb₃])
  have E2 : ⁅b₂, b₁ * b₂⁆ = ⁅b₁, b₃⁆ := by
    rw [← hconj b₁ b₃ Z13]
    exact commutator_eq_of_map_eq hker (by rw [hm₁, hb₂]) hm₃.symm
  have E3 : ⁅b₃, b₁ * b₂⁆ = ⁅b₂, b₃⁆ := by
    rw [← hconj b₂ b₃ Z23]
    exact commutator_eq_of_map_eq hker (by rw [hm₂, hb₃]) hm₃.symm
  have Z22 : ⁅b₂, b₂⁆ ∈ Subgroup.center J := by
    rw [commutatorElement_self]; exact Subgroup.one_mem _
  rw [commutator_mul_right_of_central Z22, commutatorElement_self, mul_one,
    ← commutatorElement_inv] at E2
  rw [commutator_mul_right_of_central Z32, ← commutatorElement_inv,
    ← commutatorElement_inv b₂ b₃] at E3
  rw [← E2, E1, inv_inv] at E3
  have h12 : ⁅b₁, b₂⁆ = 1 := by
    have := E3
    rwa [mul_inv_cancel, eq_comm] at this
  refine ⟨h12, ?_, ?_⟩
  · rw [← E2, h12, inv_one]
  · rw [E1, h12]

theorem E8Datum.exists_lift (h : E8Datum a₁ a₂ a₃ n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) :
    ∃ b₁ b₂ b₃ : J, φ b₁ = a₁ ∧ φ b₂ = a₂ ∧ φ b₃ = a₃ ∧ b₁ ^ 2 = 1 ∧ b₂ ^ 2 = 1 ∧
      b₃ ^ 2 = 1 ∧ Commute b₁ b₂ ∧ Commute b₁ b₃ ∧ Commute b₂ b₃ := by
  obtain ⟨b₁, hb₁⟩ := hφ a₁
  obtain ⟨b₂, hb₂⟩ := hφ a₂
  obtain ⟨b₃, hb₃⟩ := hφ a₃
  obtain ⟨m, hm⟩ := hφ n
  obtain ⟨c12, c13, c23⟩ := h.commutator_eq_one hφ hker hb₁ hb₂ hb₃
  have h12 : Commute b₁ b₂ := commutatorElement_eq_one_iff_commute.mp c12
  have h13 : Commute b₁ b₃ := commutatorElement_eq_one_iff_commute.mp c13
  have h23 : Commute b₂ b₃ := commutatorElement_eq_one_iff_commute.mp c23
  have hZ : ∀ x : J, φ x = 1 → x ∈ Subgroup.center J := fun x hx => hker hx
  set k₁ := b₂⁻¹ * (m * b₁ * m⁻¹) with hk₁
  set k₂ := b₃⁻¹ * (m * b₂ * m⁻¹) with hk₂
  set k₃ := (b₁ * b₂)⁻¹ * (m * b₃ * m⁻¹) with hk₃
  have Zk₁ : k₁ ∈ Subgroup.center J := hZ _ (by
    rw [hk₁, map_mul, map_inv, map_mul, map_mul, map_inv, hm, hb₁, hb₂, h.conj₁, inv_mul_cancel])
  have Zk₂ : k₂ ∈ Subgroup.center J := hZ _ (by
    rw [hk₂, map_mul, map_inv, map_mul, map_mul, map_inv, hm, hb₂, hb₃, h.conj₂, inv_mul_cancel])
  have Zk₃ : k₃ ∈ Subgroup.center J := hZ _ (by
    rw [hk₃, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hm, hb₁, hb₂, hb₃, h.conj₃,
      inv_mul_cancel])
  have Zs₁ : b₁ ^ 2 ∈ Subgroup.center J := hZ _ (by rw [map_pow, hb₁, h.sq])
  have Zs₂ : b₂ ^ 2 ∈ Subgroup.center J := hZ _ (by rw [map_pow, hb₂, h.sq₂])
  have Zs₃ : b₃ ^ 2 ∈ Subgroup.center J := hZ _ (by rw [map_pow, hb₃, h.sq₃])
  have hc : ∀ {x y : J}, y ∈ Subgroup.center J → Commute x y :=
    fun hy => (Subgroup.mem_center_iff.mp hy _)
  have hsq : ∀ {x : J}, x ^ 2 ∈ Subgroup.center J → (m * x * m⁻¹) ^ 2 = x ^ 2 := fun hx => by
    rw [conj_pow, Subgroup.mem_center_iff.mp hx m, mul_inv_cancel_right]
  have F1 : b₁ ^ 2 = b₂ ^ 2 * k₁ ^ 2 := by
    rw [← hsq Zs₁, show m * b₁ * m⁻¹ = b₂ * k₁ by rw [hk₁, mul_inv_cancel_left],
      (hc Zk₁).mul_pow]
  have F2 : b₂ ^ 2 = b₃ ^ 2 * k₂ ^ 2 := by
    rw [← hsq Zs₂, show m * b₂ * m⁻¹ = b₃ * k₂ by rw [hk₂, mul_inv_cancel_left],
      (hc Zk₂).mul_pow]
  have F3 : b₃ ^ 2 = b₁ ^ 2 * b₂ ^ 2 * k₃ ^ 2 := by
    rw [← hsq Zs₃, show m * b₃ * m⁻¹ = b₁ * b₂ * k₃ by rw [hk₃, mul_inv_cancel_left],
      (hc Zk₃).mul_pow, h12.mul_pow]
  set Z := Subgroup.center J
  let s₁ : Z := ⟨_, Zs₁⟩
  let s₂ : Z := ⟨_, Zs₂⟩
  let s₃ : Z := ⟨_, Zs₃⟩
  let κ₁ : Z := ⟨_, Zk₁⟩
  let κ₂ : Z := ⟨_, Zk₂⟩
  let κ₃ : Z := ⟨_, Zk₃⟩
  have G1 : s₁ = s₂ * κ₁ ^ 2 := Subtype.ext F1
  have G2 : s₂ = s₃ * κ₂ ^ 2 := Subtype.ext F2
  have G3 : s₃ = s₁ * s₂ * κ₃ ^ 2 := Subtype.ext F3
  set τ : Z := κ₁ * κ₂ * κ₃ with hτ
  have key : s₂ * τ ^ 2 = 1 := by
    have e := G2
    rw [G3, G1] at e
    have e2 : s₂ * 1 = s₂ * (s₂ * τ ^ 2) := by
      rw [mul_one]
      conv_lhs => rw [e]
      rw [hτ]
      simp only [mul_pow]
      ac_rfl
    exact (mul_left_cancel e2).symm
  have key₁ : s₁ * (κ₁⁻¹ * τ) ^ 2 = 1 := by
    rw [G1, mul_pow, inv_pow, ← key]
    group
  have key₃ : s₃ * (κ₂ * τ) ^ 2 = 1 := by
    rw [mul_pow, ← mul_assoc, ← G2, key]
  have Zτ : (τ : J) ∈ Z := τ.2
  have Kk₁ : φ k₁ = 1 := by
    rw [hk₁, map_mul, map_inv, map_mul, map_mul, map_inv, hm, hb₁, hb₂, h.conj₁, inv_mul_cancel]
  have Kk₂ : φ k₂ = 1 := by
    rw [hk₂, map_mul, map_inv, map_mul, map_mul, map_inv, hm, hb₂, hb₃, h.conj₂, inv_mul_cancel]
  have Kk₃ : φ k₃ = 1 := by
    rw [hk₃, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hm, hb₁, hb₂, hb₃, h.conj₃,
      inv_mul_cancel]
  have Kτ : φ (τ : J) = 1 := by
    change φ (k₁ * k₂ * k₃) = 1
    rw [map_mul, map_mul, Kk₁, Kk₂, Kk₃, one_mul, one_mul]
  have Z₁ : ((κ₁⁻¹ * τ : Z) : J) ∈ Z := (κ₁⁻¹ * τ).2
  have Z₃ : ((κ₂ * τ : Z) : J) ∈ Z := (κ₂ * τ).2
  refine ⟨b₁ * ((κ₁⁻¹ * τ : Z) : J), b₂ * (τ : J), b₃ * ((κ₂ * τ : Z) : J), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · change φ (b₁ * (k₁⁻¹ * (τ : J))) = a₁
    rw [map_mul, map_mul, map_inv, Kk₁, Kτ, hb₁]; group
  · rw [map_mul, Kτ, hb₂, mul_one]
  · change φ (b₃ * (k₂ * (τ : J))) = a₃
    rw [map_mul, map_mul, Kk₂, Kτ, hb₃]; group
  · rw [(hc Z₁).mul_pow]
    exact congrArg Subtype.val key₁
  · rw [(hc Zτ).mul_pow]
    exact congrArg Subtype.val key
  · rw [(hc Z₃).mul_pow]
    exact congrArg Subtype.val key₃
  · exact ((h12.mul_right (hc Zτ)).mul_left (hc Z₁).symm)
  · exact ((h13.mul_right (hc Z₃)).mul_left (hc Z₁).symm)
  · exact ((h23.mul_right (hc Z₃)).mul_left (hc Zτ).symm)

theorem E8Datum.four_le_pRank [Finite J] (h : E8Datum a₁ a₂ a₃ n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) {z : J} (hz : φ z = 1) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    4 ≤ CFSG.pRank 2 J := by
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, s₁, s₂, s₃, c₁₂, c₁₃, c₂₃⟩ := h.exists_lift hφ hker
  have hzc : ∀ x : J, Commute x z := fun x => Subgroup.mem_center_iff.mp (hker hz) x
  refine le_pRank_two_of_independent ![b₁, b₂, b₃, z] ?_ ?_ ?_
  · intro i
    fin_cases i <;> simpa
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
      first
        | exact Commute.refl _ | exact c₁₂ | exact c₁₂.symm | exact c₁₃ | exact c₁₃.symm
        | exact c₂₃ | exact c₂₃.symm | exact hzc _ | exact (hzc _).symm
  · intro v hv hprod
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two] at hprod
    have himg := congrArg φ hprod
    simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃, hz, one_pow, mul_one] at himg
    by_cases h0 : (v 0, v 1, v 2) = (0, 0, 0)
    · simp only [Prod.mk.injEq] at h0
      obtain ⟨h0, h1, h2⟩ := h0
      have h3 : v 3 ≠ 0 := by
        intro h3
        apply hv
        funext i
        fin_cases i
        exacts [h0, h1, h2, h3]
      have h3' : v 3 = 1 := by
        revert h3; generalize v 3 = w; revert w; decide
      rw [h0, h1, h2, show (Fin.succ 2 : Fin 4) = 3 from rfl, h3'] at hprod
      simp only [Fin.isValue, Fin.val_zero, pow_zero, Fin.val_one, pow_one, one_mul] at hprod
      exact hz1 hprod
    · exact h.prod_ne_one _ _ _ h0 (by rw [← himg]; group)

end Lift

section Subgroup

variable {X : Type*} [Group X]

theorem mul_comm_of_sq_eq_one {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1) {x y : X} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have hinv : ∀ w ∈ E, w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hE2 w hw)
  rw [← hinv _ (E.mul_mem hx hy), mul_inv_rev, hinv x hx, hinv y hy]

theorem eq_one_of_pow_conj {E : Subgroup X} {n : X} (hn7 : n ^ 7 = 1)
    (hfix : ∀ x ∈ E, n * x * n⁻¹ = x → x = 1) {x : X} (hx : x ∈ E) {k : ℕ} (l : ℕ)
    (hkl : k * l % 7 = 1) (hk : n ^ k * x * (n ^ k)⁻¹ = x) : x = 1 := by
  have hcomm : Commute (n ^ k) x := by
    rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul, hk]
  have hn' : (n ^ k) ^ l = n := by
    rw [← pow_mul, ← Nat.div_add_mod (k * l) 7, hkl, pow_add, pow_mul, hn7, one_pow, one_mul,
      pow_one]
  have := hcomm.pow_left l
  rw [hn'] at this
  exact hfix x hx (by rw [this.eq, mul_inv_cancel_right])

theorem inv_eq_self_of_sq_eq_one {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1) {w : X}
    (hw : w ∈ E) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hE2 w hw)

theorem eq_of_mul_eq_one_of_sq {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1) {x y : X}
    (hy : y ∈ E) (h : x * y = 1) : x = y := by
  rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_self_of_sq_eq_one hE2 hy]

set_option linter.unusedSimpArgs false in
theorem prod_ne_one_of_normalizer {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1) {n : X}
    (hn : ∀ x ∈ E, n * x * n⁻¹ ∈ E) (hn7 : n ^ 7 = 1)
    (hfix : ∀ x ∈ E, n * x * n⁻¹ = x → x = 1) {a₁ : X} (ha₁ : a₁ ∈ E) (h₁ : a₁ ≠ 1)
    (i j k : Fin 2) (hijk : (i, j, k) ≠ (0, 0, 0)) :
    a₁ ^ (i : ℕ) * (n * a₁ * n⁻¹) ^ (j : ℕ) * (n * (n * a₁ * n⁻¹) * n⁻¹) ^ (k : ℕ) ≠ 1 := by
  set a₂ := n * a₁ * n⁻¹ with ha₂def
  set a₃ := n * a₂ * n⁻¹ with ha₃def
  have ha₂ : a₂ ∈ E := hn _ ha₁
  have ha₃ : a₃ ∈ E := hn _ ha₂
  have h₂ : a₂ ≠ 1 := fun e => h₁ (conj_eq_one_iff.mp e)
  have h₃ : a₃ ≠ 1 := fun e => h₂ (conj_eq_one_iff.mp e)
  have hn2 : n ^ 2 * a₁ * (n ^ 2)⁻¹ = a₃ := by
    rw [ha₃def, ha₂def, pow_two, mul_inv_rev]; simp only [mul_assoc]
  have i₁₂ : a₁ * a₂ ≠ 1 := fun e => h₁ (hfix a₁ ha₁ (eq_of_mul_eq_one_of_sq hE2 ha₂ e).symm)
  have i₁₃ : a₁ * a₃ ≠ 1 := fun e => h₁ (eq_one_of_pow_conj hn7 hfix ha₁ 4 (by norm_num)
    (hn2.trans (eq_of_mul_eq_one_of_sq hE2 ha₃ e).symm))
  have i₂₃ : a₂ * a₃ ≠ 1 := fun e => h₂ (hfix a₂ ha₂ (eq_of_mul_eq_one_of_sq hE2 ha₃ e).symm)
  have i₁₂₃ : a₁ * a₂ * a₃ ≠ 1 := by
    intro e
    have e₃ : a₃ = a₁ * a₂ := (eq_of_mul_eq_one_of_sq hE2 ha₃ e).symm
    have e₄ : n ^ 3 * a₁ * (n ^ 3)⁻¹ = a₁ := by
      calc n ^ 3 * a₁ * (n ^ 3)⁻¹ = n * (a₁ * a₂) * n⁻¹ := by
            rw [← e₃, ha₃def, ha₂def, pow_succ, pow_two, mul_inv_rev, mul_inv_rev]
            simp only [mul_assoc]
        _ = (n * a₁ * n⁻¹) * (n * a₂ * n⁻¹) := by group
        _ = a₂ * (a₁ * a₂) := by rw [← e₃]
        _ = a₁ * (a₂ * a₂) := by
          rw [← mul_assoc, mul_comm_of_sq_eq_one hE2 ha₂ ha₁, mul_assoc]
        _ = a₁ := by rw [← pow_two, hE2 a₂ ha₂, mul_one]
    exact h₁ (eq_one_of_pow_conj hn7 hfix ha₁ 5 (by norm_num) e₄)
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero,
      pow_one, one_mul, mul_one] at hijk ⊢
  all_goals first
    | exact h₁ | exact h₂ | exact h₃ | exact i₁₂ | exact i₁₃ | exact i₂₃ | exact i₁₂₃
    | exact absurd rfl hijk

theorem exists_e8Datum_of_normalizer {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hE8 : Nat.card E = 8) {n : X} (hn : ∀ x ∈ E, n * x * n⁻¹ ∈ E) (hn7 : n ^ 7 = 1)
    (hfix : ∀ x ∈ E, n * x * n⁻¹ = x → x = 1) :
    ∃ a₁ a₂ a₃ m : X, E8Datum a₁ a₂ a₃ m ∧
      ∀ x ∈ E, ∃ i j k : Fin 2, x = a₁ ^ (i : ℕ) * a₂ ^ (j : ℕ) * a₃ ^ (k : ℕ) := by
  have hc : ∀ {x y : X}, x ∈ E → y ∈ E → x * y = y * x := fun hx hy =>
    mul_comm_of_sq_eq_one hE2 hx hy
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a₁, ha₁⟩, h₁⟩ := exists_ne (1 : E)
  have h₁' : a₁ ≠ 1 := fun e => h₁ (Subtype.ext e)
  have hind := prod_ne_one_of_normalizer hE2 hn hn7 hfix ha₁ h₁'
  set a₂ := n * a₁ * n⁻¹ with ha₂def
  set a₃ := n * a₂ * n⁻¹ with ha₃def
  set a₄ := n * a₃ * n⁻¹ with ha₄def
  have ha₂ : a₂ ∈ E := hn _ ha₁
  have ha₃ : a₃ ∈ E := hn _ ha₂
  have ha₄ : a₄ ∈ E := hn _ ha₃
  set u : Fin 3 → X := ![a₁, a₂, a₃]
  have hu : ∀ i, u i ∈ E := fun i => by fin_cases i <;> assumption
  have hprod : ∀ v : Fin 3 → Fin 2, (List.ofFn fun i => u i ^ (v i : ℕ)).prod =
      a₁ ^ (v 0 : ℕ) * a₂ ^ (v 1 : ℕ) * a₃ ^ (v 2 : ℕ) := fun v => by
    simp [u, List.ofFn_succ, mul_assoc]
  obtain ⟨ψ, hψi, hψ⟩ := exists_prodHom u (fun i => hE2 _ (hu i))
    (fun i j => hc (hu i) (hu j)) (fun v hv => by
      rw [hprod]
      refine hind (v 0) (v 1) (v 2) fun h => hv ?_
      simp only [Prod.mk.injEq] at h
      funext i
      fin_cases i
      exacts [h.1, h.2.1, h.2.2])
  have hψE : ψ.range = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨v, rfl⟩
      rw [hψ]
      refine Subgroup.list_prod_mem (K := E) fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact E.pow_mem (hu i) _
    · rw [hE8, ← Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv]
      simp [Nat.card_eq_fintype_card]
  have hdesc : ∀ x ∈ E, ∃ i j k : Fin 2, x = a₁ ^ (i : ℕ) * a₂ ^ (j : ℕ) * a₃ ^ (k : ℕ) := by
    intro x hx
    rw [← hψE] at hx
    obtain ⟨v, rfl⟩ := hx
    exact ⟨Multiplicative.toAdd (v 0), Multiplicative.toAdd (v 1), Multiplicative.toAdd (v 2),
      by rw [hψ, ← hprod (fun i => Multiplicative.toAdd (v i))]; rfl⟩
  have hn2' : n ^ 2 * a₂ * (n ^ 2)⁻¹ = a₄ := by
    rw [ha₄def, ha₃def, pow_two, mul_inv_rev]; simp only [mul_assoc]
  have hn3 : n ^ 3 * a₁ * (n ^ 3)⁻¹ = a₄ := by
    rw [ha₄def, ha₃def, ha₂def, pow_succ, pow_two, mul_inv_rev, mul_inv_rev]
    simp only [mul_assoc]
  have hcj : ∀ x y : X, n * x * n⁻¹ * (n * y * n⁻¹) = n * (x * y) * n⁻¹ := fun x y => by group
  have h₂ : a₂ ≠ 1 := by simpa using hind 0 1 0 (by decide)
  have h₃ : a₃ ≠ 1 := by simpa using hind 0 0 1 (by decide)
  have h₁₃ : a₁ * a₃ ≠ 1 := by simpa using hind 1 0 1 (by decide)
  have h₁₂₃ : a₁ * a₂ * a₃ ≠ 1 := by simpa using hind 1 1 1 (by decide)
  have h22 : a₂ * a₂ = 1 := by rw [← pow_two]; exact hE2 a₂ ha₂
  have h33 : a₃ * a₃ = 1 := by rw [← pow_two]; exact hE2 a₃ ha₃
  obtain ⟨i, j, k, e⟩ := hdesc a₄ ha₄
  set_option linter.unusedSimpArgs false in
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero,
      pow_one, one_mul, mul_one] at e
  ·
    exact absurd (conj_eq_one_iff.mp e) h₃
  ·
    exact absurd (hfix a₃ ha₃ e) h₃
  ·
    exact absurd (eq_one_of_pow_conj hn7 hfix ha₂ 4 (by norm_num) (hn2'.trans e)) h₂
  ·
    have e' : n * a₃ * n⁻¹ = n * (a₁ * a₂) * n⁻¹ := by
      rw [← ha₄def, e, ← hcj]
    have e₃ : a₃ = a₁ * a₂ := mul_left_cancel (mul_right_cancel e')
    exact (h₁₂₃ (by rw [← e₃]; exact h33)).elim
  ·
    exact absurd (eq_one_of_pow_conj hn7 hfix ha₁ 5 (by norm_num) (hn3.trans e)) h₁'
  ·
    have e₁ : a₁ = a₄ * a₃ := by rw [e, mul_assoc, h33, mul_one]
    have hA : n⁻¹ * a₄ * n = a₃ := by rw [ha₄def]; group
    have hB : n⁻¹ * a₃ * n = a₂ := by rw [ha₃def]; group
    refine ⟨a₃, a₂, a₁, n⁻¹, ⟨h₃, hE2 a₃ ha₃, hc ha₃ ha₂, hc ha₃ ha₁, by rw [inv_inv, hB],
      by rw [inv_inv, ha₂def]; group, ?_⟩, fun x hx => ?_⟩
    · calc n⁻¹ * a₁ * n⁻¹⁻¹ = (n⁻¹ * a₄ * n) * (n⁻¹ * a₃ * n) := by rw [e₁, inv_inv]; group
        _ = a₃ * a₂ := by rw [hA, hB]
    · obtain ⟨i, j, k, rfl⟩ := hdesc x hx
      refine ⟨k, j, i, ?_⟩
      have hp := E.pow_mem ha₁ (i : ℕ)
      have hq := E.pow_mem ha₂ (j : ℕ)
      have hr := E.pow_mem ha₃ (k : ℕ)
      rw [hc (E.mul_mem hp hq) hr, hc hp hq, mul_assoc]
  ·
    exact ⟨a₁, a₂, a₃, n, ⟨h₁', hE2 a₁ ha₁, hc ha₁ ha₂, hc ha₁ ha₃, rfl, rfl, e⟩, hdesc⟩
  ·
    have hfix₁₃ : n * (a₁ * a₃) * n⁻¹ = a₁ * a₃ := by
      calc n * (a₁ * a₃) * n⁻¹ = (n * a₁ * n⁻¹) * (n * a₃ * n⁻¹) := by group
        _ = a₂ * (a₁ * a₂ * a₃) := by rw [← ha₄def, e]
        _ = (a₂ * a₁) * a₂ * a₃ := by simp only [mul_assoc]
        _ = (a₁ * a₂) * a₂ * a₃ := by rw [hc ha₂ ha₁]
        _ = a₁ * (a₂ * a₂) * a₃ := by simp only [mul_assoc]
        _ = a₁ * a₃ := by rw [h22, mul_one]
    exact (h₁₃ (hfix _ (E.mul_mem ha₁ ha₃) hfix₁₃)).elim

variable {J : Type*} [Group J] {φ : J →* X}

theorem card_comap_of_surjective [Finite J] (hφ : Function.Surjective φ) (E : Subgroup X) :
    Nat.card (E.comap φ) = Nat.card E * Nat.card φ.ker := by
  have : Finite X := Finite.of_surjective φ hφ
  have h1 := Subgroup.card_mul_index (E.comap φ)
  have h2 := Subgroup.card_mul_index E
  rw [Subgroup.index_comap_of_surjective E hφ] at h1
  have h3 : Nat.card J = Nat.card X * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  have hpos : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (E.comap φ) * E.index = Nat.card E * Nat.card φ.ker * E.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h4

theorem isElementaryAbelian_comap [Finite J] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) (hK2 : Nat.card φ.ker = 2) {E : Subgroup X}
    (hE : CFSG.IsElementaryAbelian 2 E) (hE8 : Nat.card E = 8) {n : X}
    (hn : n ∈ Subgroup.normalizer (E : Set X)) (hn7 : n ^ 7 = 1)
    (hfix : ∀ x ∈ E, n * x * n⁻¹ = x → x = 1) :
    CFSG.IsElementaryAbelian 2 (E.comap φ) ∧ Nat.card (E.comap φ) = 16 := by
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hnE : ∀ x ∈ E, n * x * n⁻¹ ∈ E := fun x hx => (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  obtain ⟨a₁, a₂, a₃, m, hd, hdesc⟩ := exists_e8Datum_of_normalizer hE2 hE8 hnE hn7 hfix
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, s₁, s₂, s₃, c₁₂, c₁₃, c₂₃⟩ := hd.exists_lift hφ hker
  have hk2 : ∀ κ ∈ φ.ker, κ ^ 2 = 1 := fun κ hκ => by
    have := pow_card_eq_one' (G := φ.ker) (x := ⟨κ, hκ⟩)
    rw [hK2] at this
    exact congrArg Subtype.val this
  have hform : ∀ y ∈ E.comap φ, ∃ i j k : ℕ, ∃ κ ∈ φ.ker, y = b₁ ^ i * b₂ ^ j * b₃ ^ k * κ := by
    intro y hy
    obtain ⟨i, j, k, e⟩ := hdesc (φ y) hy
    refine ⟨i, j, k, (b₁ ^ (i : ℕ) * b₂ ^ (j : ℕ) * b₃ ^ (k : ℕ))⁻¹ * y, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_pow, map_pow, map_pow, hb₁,
      hb₂, hb₃, ← e, inv_mul_cancel]
  have hpow : ∀ i j k : ℕ, (b₁ ^ i * b₂ ^ j * b₃ ^ k) ^ 2 = 1 := fun i j k => by
    rw [((c₁₃.pow_pow i k).mul_left (c₂₃.pow_pow j k)).mul_pow, (c₁₂.pow_pow i j).mul_pow,
      ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, mul_comm k, pow_mul, pow_mul,
      pow_mul, s₁, s₂, s₃, one_pow, one_pow, one_pow, one_mul, one_mul]
  have hcomm : ∀ i j k i' j' k' : ℕ,
      Commute (b₁ ^ i * b₂ ^ j * b₃ ^ k) (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') := by
    intro i j k i' j' k'
    have h1 : ∀ i' j' k', Commute (b₁ ^ i) (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') := fun i' j' k' =>
      (((Commute.refl b₁).pow_pow i i').mul_right (c₁₂.pow_pow i j')).mul_right
        (c₁₃.pow_pow i k')
    have h2 : ∀ i' j' k', Commute (b₂ ^ j) (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') := fun i' j' k' =>
      ((c₁₂.symm.pow_pow j i').mul_right ((Commute.refl b₂).pow_pow j j')).mul_right
        (c₂₃.pow_pow j k')
    have h3 : ∀ i' j' k', Commute (b₃ ^ k) (b₁ ^ i' * b₂ ^ j' * b₃ ^ k') := fun i' j' k' =>
      ((c₁₃.symm.pow_pow k i').mul_right (c₂₃.symm.pow_pow k j')).mul_right
        ((Commute.refl b₃).pow_pow k k')
    exact ((h1 i' j' k').mul_left (h2 i' j' k')).mul_left (h3 i' j' k')
  have hcen : ∀ {κ : J} (y : J), κ ∈ φ.ker → Commute y κ := fun y hκ =>
    Subgroup.mem_center_iff.mp (hker hκ) y
  refine ⟨{ toIsMulCommutative := ⟨⟨fun y y' => Subtype.ext ?_⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
              Subtype.ext ?_ }, ?_⟩
  · obtain ⟨i, j, k, κ, hκ, hy⟩ := hform y y.2
    obtain ⟨i', j', k', κ', hκ', hy'⟩ := hform y' y'.2
    change (y : J) * y' = y' * y
    rw [hy, hy']
    exact (((hcomm i j k i' j' k').mul_right (hcen _ hκ')).mul_left
      ((hcen _ hκ).symm.mul_right (hcen κ' hκ).symm)).eq
  · obtain ⟨i, j, k, κ, hκ, hy⟩ := hform y y.2
    change (y : J) ^ 2 = 1
    rw [hy, (hcen _ hκ).mul_pow, hpow, hk2 κ hκ, one_mul]
  · rw [card_comap_of_surjective hφ, hE8, hK2]

theorem four_le_pRank_of_normalizer [Finite J] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) (hK2 : Nat.card φ.ker = 2) {E : Subgroup X}
    (hE : CFSG.IsElementaryAbelian 2 E) (hE8 : Nat.card E = 8) {n : X}
    (hn : n ∈ Subgroup.normalizer (E : Set X)) (hn7 : n ^ 7 = 1)
    (hfix : ∀ x ∈ E, n * x * n⁻¹ = x → x = 1) : 4 ≤ CFSG.pRank 2 J := by
  obtain ⟨hA, hcard⟩ := isElementaryAbelian_comap hφ hker hK2 hE hE8 hn hn7 hfix
  exact le_pRank_two_of_card _ hA (by rw [hcard]; norm_num)

end Subgroup

end DoubleCoverLift

end CFSG.RankThree.PartTwo.Sec4.Census
