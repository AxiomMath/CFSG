module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3BCoprime

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem B_comm_dbl (z : V) : z + z = 0 := by
  rw [← two_smul (ZMod 2) z]
  have h : (2 : ZMod 2) = 0 := rfl
  rw [h, zero_smul]

theorem B_comm_neg_dbl (z : V) : -z = z := neg_eq_of_add_eq_zero_right (B_comm_dbl z)

theorem B_comm_eq_add_of_three (a b c : V) (h : a + b + c = 0) : a = b + c := by
  have h' : a = -(b + c) := eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact h)
  rw [h', neg_add, B_comm_neg_dbl, B_comm_neg_dbl]

theorem B_comm_sum_cancel (a b c : V) : (a + c) + (a + b) = b + c := by
  rw [show (a + c) + (a + b) = (a + a) + b + c by abel, B_comm_dbl, zero_add]

theorem B_comm_rel_of_fpf (u : Module.End (ZMod 2) V) (hu3 : ∀ x, u (u (u x)) = x)
    (hu : ∀ x, u x = x → x = 0) (z : V) : u (u z) + u z + z = 0 := by
  apply hu
  rw [map_add, map_add, hu3]
  abel

theorem B_comm_eigen_zero (u v : Module.End (ZMod 2) V) (hu3 : ∀ x, u (u (u x)) = x)
    (hv3 : ∀ x, v (v (v x)) = x) (huv : ∀ x, u (v x) = v (u x))
    (hu : ∀ x, u x = x → x = 0) (hv : ∀ x, v x = x → x = 0)
    (huv1 : ∀ x, u (v x) = x → x = 0) (huv2 : ∀ x, u (v (v x)) = x → x = 0) (x : V) :
    x = 0 := by
  have Ru := B_comm_rel_of_fpf u hu3 hu
  have Rv := B_comm_rel_of_fpf v hv3 hv
  have hP₁ : u x + v x = 0 := by
    apply huv1
    have A1 : u (u (v x)) = u (v x) + v x := B_comm_eq_add_of_three _ _ _ (Ru (v x))
    have A2 : u (v (v x)) = u (v x) + u x := by
      have h := congrArg u (Rv x)
      rw [map_add, map_add, map_zero] at h
      exact B_comm_eq_add_of_three _ _ _ h
    simp only [map_add]
    rw [← huv x, A1, A2]
    exact B_comm_sum_cancel _ _ _
  have hP₂ : x + u x + v x = 0 := by
    apply huv2
    have hvv : v (v (u x)) = u (v (v x)) := by
      rw [huv (v x), ← huv x]
    have hw : u (v (v (v x))) = u x := by rw [hv3]
    have hR : v (v x) = v x + x := B_comm_eq_add_of_three _ _ _ (Rv x)
    have e : u (v (v (x + u x + v x))) = u (v (v x)) + u (u (v (v x))) + u x := by
      simp only [map_add]
      rw [hvv, hw]
    rw [e]
    have A3 : u (u (v (v x))) = u (v (v x)) + v (v x) :=
      B_comm_eq_add_of_three _ _ _ (B_comm_rel_of_fpf u hu3 hu (v (v x)))
    rw [A3]
    have key : ∀ a b c : V, a + (a + b) + c = b + c := fun a b c => by
      rw [show a + (a + b) + c = (a + a) + b + c by abel, B_comm_dbl, zero_add]
    rw [key, hR]
    abel
  have hsum : (x + u x + v x) + (u x + v x) = x := by
    have h1 := B_comm_dbl (u x)
    have h2 := B_comm_dbl (v x)
    calc (x + u x + v x) + (u x + v x) = x + (u x + u x) + (v x + v x) := by abel
      _ = x := by rw [h1, h2, add_zero, add_zero]
  rw [← hsum, hP₂, hP₁, add_zero]

def B_comm_cS {G : Type*} [Group G] (p q : G) : G := p⁻¹ * q⁻¹ * p * q

def B_comm_cj {G : Type*} [Group G] (g p : G) : G := g⁻¹ * p * g

theorem B_comm_hall_witt {G : Type*} [Group G] (x y z : G) :
    B_comm_cj y (B_comm_cS (B_comm_cS x y⁻¹) z) * B_comm_cj z (B_comm_cS (B_comm_cS y z⁻¹) x) *
      B_comm_cj x (B_comm_cS (B_comm_cS z x⁻¹) y) = 1 := by
  simp only [B_comm_cS, B_comm_cj]
  group

theorem B_comm_cS_of_commute {G : Type*} [Group G] {p q : G} (h : Commute p q) :
    B_comm_cS p q = 1 := by
  unfold B_comm_cS
  calc p⁻¹ * q⁻¹ * p * q = p⁻¹ * q⁻¹ * (p * q) := by group
    _ = p⁻¹ * q⁻¹ * (q * p) := by rw [h.eq]
    _ = 1 := by group

theorem B_comm_commute_of_cS {G : Type*} [Group G] {p a : G} (h : B_comm_cS p a = 1) :
    Commute p a := by
  unfold B_comm_cS at h
  have h2 : a⁻¹ * p * a = p := by
    calc a⁻¹ * p * a = p * (p⁻¹ * a⁻¹ * p * a) := by group
      _ = p := by rw [h, mul_one]
  show p * a = a * p
  calc p * a = a * (a⁻¹ * p * a) := by group
    _ = a * p := by rw [h2]

theorem B_comm_hw_core {G : Type*} [Group G] {A A' : Subgroup G} {h : G}
    (hA : ∀ a ∈ A, Commute a h) (hD : ∀ a ∈ A, ∀ b ∈ A', Commute (a⁻¹ * b * a * b⁻¹) h)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A') :
    Commute (b⁻¹ * h * b * h⁻¹) a := by
  have key := B_comm_hall_witt b h a
  have t2 : B_comm_cj a (B_comm_cS (B_comm_cS h a⁻¹) b) = 1 := by
    have hc : B_comm_cS h a⁻¹ = 1 := B_comm_cS_of_commute ((hA a ha).symm.inv_right)
    rw [hc]
    simp [B_comm_cS, B_comm_cj]
  have t3 : B_comm_cj b (B_comm_cS (B_comm_cS a b⁻¹) h) = 1 := by
    have e : B_comm_cS a b⁻¹ = a⁻¹ * b * a * b⁻¹ := by simp [B_comm_cS]
    rw [e, B_comm_cS_of_commute (hD a ha b hb)]
    simp [B_comm_cj]
  simp only [t2, t3, mul_one] at key
  have H : h⁻¹ * B_comm_cS (B_comm_cS b h⁻¹) a * h = 1 := key
  have h1 : B_comm_cS (B_comm_cS b h⁻¹) a = 1 := by
    calc B_comm_cS (B_comm_cS b h⁻¹) a
        = h * (h⁻¹ * B_comm_cS (B_comm_cS b h⁻¹) a * h) * h⁻¹ := by group
      _ = 1 := by rw [H]; group
  have e' : B_comm_cS b h⁻¹ = b⁻¹ * h * b * h⁻¹ := by simp [B_comm_cS]
  rw [← e']
  exact B_comm_commute_of_cS h1

theorem B_comm_hw {G : Type*} [Group G] {A A' : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, Commute a g) (hD : ∀ a ∈ A, ∀ b ∈ A', Commute (a⁻¹ * b * a * b⁻¹) g)
    (hA'g : ⁅A', Subgroup.zpowers g⁆ = A') : ∀ a ∈ A, ∀ b ∈ A', Commute a b := by
  intro a ha b hb
  have hsub : ⁅A', Subgroup.zpowers g⁆ ≤ Subgroup.centralizer {a} := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨b', hb', h', hh', rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh'
    have hcore := B_comm_hw_core (h := g ^ k)
      (fun c hc => (hA c hc).zpow_right k) (fun c hc d hd => (hD c hc d hd).zpow_right k)
      ha (A'.inv_mem hb')
    simp only [inv_inv] at hcore
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    exact hcore
  have hle : A' ≤ Subgroup.centralizer {a} := by
    rw [← hA'g]
    exact hsub
  exact ((Subgroup.mem_centralizer_singleton_iff).1 (hle hb)).symm

open scoped IsMulCommutative

@[expose] def B_comm_conjHom {K : Type*} [Group K] (M : Subgroup K) [M.Normal] (u : K) : M →* M where
  toFun m := ⟨u * m * u⁻¹, ‹M.Normal›.conj_mem (m : K) m.2 u⟩
  map_one' := Subtype.ext (by simp)
  map_mul' m n := Subtype.ext (by simp [mul_assoc])

theorem B_comm_conj_pow3 {K : Type*} [Group K] {u : K} (hu3 : u ^ 3 = 1) (m : K) :
    u * (u * (u * m * u⁻¹) * u⁻¹) * u⁻¹ = m := by
  have h3 : u * (u * u) = 1 := by rw [← pow_three]; exact hu3
  calc u * (u * (u * m * u⁻¹) * u⁻¹) * u⁻¹ = (u * (u * u)) * m * (u * (u * u))⁻¹ := by group
    _ = m := by rw [h3]; group

theorem B_comm_eigen_group {K : Type*} [Group K] (M : Subgroup K) [M.Normal]
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hexp : ∀ m ∈ M, m * m = 1) {u v : K}
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u)
    (hu : ∀ m ∈ M, u * m = m * u → m = 1) (hv : ∀ m ∈ M, v * m = m * v → m = 1)
    (huv1 : ∀ m ∈ M, (u * v) * m = m * (u * v) → m = 1)
    (huv2 : ∀ m ∈ M, (u * v ^ 2) * m = m * (u * v ^ 2) → m = 1) : M = ⊥ := by
  haveI : IsMulCommutative M := ⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩
  have hdbl : ∀ x : Additive M, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    exact congrArg Additive.ofMul (Subtype.ext (hexp _ (Additive.toMul x).2))
  letI : Module (ZMod 2) (Additive M) := AddCommGroup.zmodModule hdbl
  let uL : Module.End (ZMod 2) (Additive M) := (B_comm_conjHom M u).toAdditive.toZModLinearMap 2
  let vL : Module.End (ZMod 2) (Additive M) := (B_comm_conjHom M v).toAdditive.toZModLinearMap 2
  have hu3L : ∀ x, uL (uL (uL x)) = x := by
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact B_comm_conj_pow3 hu3 (Additive.toMul x).1
  have hv3L : ∀ x, vL (vL (vL x)) = x := by
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact B_comm_conj_pow3 hv3 (Additive.toMul x).1
  have huvL : ∀ x, uL (vL x) = vL (uL x) := by
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    change u * (v * (Additive.toMul x).1 * v⁻¹) * u⁻¹ = v * (u * (Additive.toMul x).1 * u⁻¹) * v⁻¹
    calc u * (v * (Additive.toMul x).1 * v⁻¹) * u⁻¹
        = (u * v) * (Additive.toMul x).1 * (u * v)⁻¹ := by group
      _ = (v * u) * (Additive.toMul x).1 * (v * u)⁻¹ := by rw [huv]
      _ = v * (u * (Additive.toMul x).1 * u⁻¹) * v⁻¹ := by group
  have hu' : ∀ x, uL x = x → x = 0 := by
    intro x hx
    have hm : u * (Additive.toMul x).1 * u⁻¹ = (Additive.toMul x).1 :=
      congrArg (fun y => (Additive.toMul y).1) hx
    have hc : u * (Additive.toMul x).1 = (Additive.toMul x).1 * u := by
      calc u * (Additive.toMul x).1 = (u * (Additive.toMul x).1 * u⁻¹) * u := by group
        _ = (Additive.toMul x).1 * u := by rw [hm]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hu _ (Additive.toMul x).2 hc
  have hv' : ∀ x, vL x = x → x = 0 := by
    intro x hx
    have hm : v * (Additive.toMul x).1 * v⁻¹ = (Additive.toMul x).1 :=
      congrArg (fun y => (Additive.toMul y).1) hx
    have hc : v * (Additive.toMul x).1 = (Additive.toMul x).1 * v := by
      calc v * (Additive.toMul x).1 = (v * (Additive.toMul x).1 * v⁻¹) * v := by group
        _ = (Additive.toMul x).1 * v := by rw [hm]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hv _ (Additive.toMul x).2 hc
  have huv1' : ∀ x, uL (vL x) = x → x = 0 := by
    intro x hx
    have hm : u * (v * (Additive.toMul x).1 * v⁻¹) * u⁻¹ = (Additive.toMul x).1 :=
      congrArg (fun y => (Additive.toMul y).1) hx
    have hc : (u * v) * (Additive.toMul x).1 = (Additive.toMul x).1 * (u * v) := by
      calc (u * v) * (Additive.toMul x).1
          = (u * (v * (Additive.toMul x).1 * v⁻¹) * u⁻¹) * (u * v) := by group
        _ = (Additive.toMul x).1 * (u * v) := by rw [hm]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact huv1 _ (Additive.toMul x).2 hc
  have huv2' : ∀ x, uL (vL (vL x)) = x → x = 0 := by
    intro x hx
    have hm : u * (v * (v * (Additive.toMul x).1 * v⁻¹) * v⁻¹) * u⁻¹ = (Additive.toMul x).1 :=
      congrArg (fun y => (Additive.toMul y).1) hx
    have hc : (u * v ^ 2) * (Additive.toMul x).1 = (Additive.toMul x).1 * (u * v ^ 2) := by
      calc (u * v ^ 2) * (Additive.toMul x).1
          = (u * (v * (v * (Additive.toMul x).1 * v⁻¹) * v⁻¹) * u⁻¹) * (u * v ^ 2) := by
            rw [pow_two]; group
        _ = (Additive.toMul x).1 * (u * v ^ 2) := by rw [hm]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact huv2 _ (Additive.toMul x).2 hc
  have hzero : ∀ x : Additive M, x = 0 :=
    fun x => B_comm_eigen_zero uL vL hu3L hv3L huvL hu' hv' huv1' huv2' x
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  have h0 : (Additive.ofMul (⟨m, hm⟩ : M)) = 0 := hzero _
  have h1 : (⟨m, hm⟩ : M) = 1 := congrArg Additive.toMul h0
  exact congrArg Subtype.val h1

section Minimal

variable {K : Type*} [Group K] [Finite K]

theorem B_comm_normal_centre_inf {X : Subgroup K} (hXn : X.Normal) :
    (Subgroup.centralizer (X : Set K) ⊓ X).Normal := by
  refine ⟨fun z hz g => ?_⟩
  have hcen : g * z * g⁻¹ ∈ Subgroup.centralizer (X : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ X := hXn.conj_mem x hx g⁻¹
    have hzy := (Subgroup.mem_centralizer_iff.1 hz.1) _ hy
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [hzy]
      _ = (g * z * g⁻¹) * x := by group
  exact Subgroup.mem_inf.2 ⟨hcen, hXn.conj_mem z hz.2 g⟩

theorem B_comm_minimal_centre {X M : Subgroup K} (hX : IsPGroup 2 X) (hXn : X.Normal)
    (hMn : M.Normal) (hMX : M ≤ X) (hM1 : M ≠ ⊥)
    (hmin : ∀ N : Subgroup K, N.Normal → N ≠ ⊥ → N ≤ M → N = M) :
    ∀ m ∈ M, ∀ x ∈ X, x * m = m * x := by
  have hZ := B_comm_normal_centre_inf hXn
  have hne : M ⊓ (Subgroup.centralizer (X : Set K) ⊓ X) ≠ ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent X := IsPGroup.isNilpotent hX
    have hne' : M.subgroupOf X ≠ ⊥ := by
      intro h
      apply hM1
      rw [Subgroup.eq_bot_iff_forall]
      intro m hm
      have h1 : (⟨m, hMX hm⟩ : ↥X) ∈ (⊥ : Subgroup ↥X) := h ▸ Subgroup.mem_subgroupOf.2 hm
      exact congrArg Subtype.val (Subgroup.mem_bot.1 h1)
    have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
    intro h0
    apply hc
    rw [eq_bot_iff]
    rintro y hy
    have hyM : (y : K) ∈ M := Subgroup.mem_subgroupOf.1 hy.1
    have hyC : (y : K) ∈ Subgroup.centralizer (X : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hc' := Subgroup.mem_center_iff.1 hy.2 ⟨x, hx⟩
      exact congrArg Subtype.val hc'
    have hmem : (y : K) ∈ M ⊓ (Subgroup.centralizer (X : Set K) ⊓ X) :=
      Subgroup.mem_inf.2 ⟨hyM, Subgroup.mem_inf.2 ⟨hyC, y.2⟩⟩
    rw [h0] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hmem))
  have hMZ := hmin (M ⊓ (Subgroup.centralizer (X : Set K) ⊓ X))
    ⟨fun n hn g => Subgroup.mem_inf.2
      ⟨hMn.conj_mem n (Subgroup.mem_inf.1 hn).1 g, hZ.conj_mem n (Subgroup.mem_inf.1 hn).2 g⟩⟩
    hne inf_le_left
  intro m hm x hx
  have hmZ : m ∈ M ⊓ (Subgroup.centralizer (X : Set K) ⊓ X) := by
    rw [hMZ]
    exact hm
  exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hmZ).2).1 x hx

theorem B_comm_minimal_exp {X M : Subgroup K} (hX : IsPGroup 2 X) (hMn : M.Normal)
    (hMX : M ≤ X) (hM1 : M ≠ ⊥) (hcen : ∀ m ∈ M, ∀ x ∈ X, x * m = m * x)
    (hmin : ∀ N : Subgroup K, N.Normal → N ≠ ⊥ → N ≤ M → N = M) :
    ∀ m ∈ M, m * m = 1 := by
  let Ω : Subgroup K :=
    { carrier := {m | m ∈ M ∧ m * m = 1}
      mul_mem' := fun {a b} ha hb => by
        have hab : a * b = b * a := hcen b hb.1 a (hMX ha.1)
        refine ⟨M.mul_mem ha.1 hb.1, ?_⟩
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]
      one_mem' := ⟨M.one_mem, by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨M.inv_mem ha.1, ?_⟩
        calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          _ = 1 := by rw [ha.2, inv_one] }
  have hΩn : Ω.Normal := by
    refine ⟨fun n hn g => ⟨hMn.conj_mem n hn.1 g, ?_⟩⟩
    calc (g * n * g⁻¹) * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
      _ = 1 := by rw [hn.2]; group
  have hΩle : Ω ≤ M := fun m hm => hm.1
  have hΩne : Ω ≠ ⊥ := by
    obtain ⟨m0, hm0, hm0ne⟩ : ∃ m0 ∈ M, m0 ≠ 1 := by
      by_contra hcon
      exact hM1 ((Subgroup.eq_bot_iff_forall M).2 fun m hm => by
        by_contra hne
        exact hcon ⟨m, hm, hne⟩)
    obtain ⟨k, hk⟩ := hX ⟨m0, hMX hm0⟩
    have hk' : m0 ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf m0 ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hord1 : orderOf m0 ≠ 1 := fun h => hm0ne (orderOf_eq_one_iff.1 h)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hord1 (by simpa using hjeq)
    have h2dvd : 2 ∣ orderOf m0 := by
      rw [hjeq]
      exact dvd_pow_self 2 hj0
    obtain ⟨m1, hm1⟩ : ∃ m1 : K, m1 = m0 ^ (orderOf m0 / 2) := ⟨_, rfl⟩
    have hm1sq : m1 * m1 = 1 := by
      rw [hm1, ← pow_add, ← two_mul, Nat.mul_div_cancel' h2dvd, pow_orderOf_eq_one]
    have hm1ne : m1 ≠ 1 := by
      intro h
      have hd : orderOf m0 ∣ orderOf m0 / 2 := orderOf_dvd_of_pow_eq_one (by rw [← hm1, h])
      have hpos : 0 < orderOf m0 := orderOf_pos m0
      exact absurd (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos h2dvd) (by norm_num)) hd)
        (not_le.2 (Nat.div_lt_self hpos (by norm_num)))
    intro h
    have hm1M : m1 ∈ M := by
      rw [hm1]
      exact M.pow_mem hm0 _
    have hmem : m1 ∈ Ω := ⟨hm1M, hm1sq⟩
    rw [h] at hmem
    exact hm1ne (Subgroup.mem_bot.1 hmem)
  have hΩM : Ω = M := hmin Ω hΩn hΩne hΩle
  intro m hm
  have : m ∈ Ω := hΩM ▸ hm
  exact this.2

end Minimal

section Cent

variable {K : Type*} [Group K]

theorem B_comm_commute_conj_iff {g w h : K} (hgw : Commute g w) :
    Commute h w ↔ Commute (g * h * g⁻¹) w := by
  have f1 : (g * h * g⁻¹) * w = g * (h * w) * g⁻¹ := by
    have hc : g⁻¹ * w = w * g⁻¹ := hgw.inv_left.eq
    calc (g * h * g⁻¹) * w = g * h * (g⁻¹ * w) := by group
      _ = g * h * (w * g⁻¹) := by rw [hc]
      _ = g * (h * w) * g⁻¹ := by group
  have f2 : w * (g * h * g⁻¹) = g * (w * h) * g⁻¹ := by
    calc w * (g * h * g⁻¹) = (w * g) * h * g⁻¹ := by group
      _ = (g * w) * h * g⁻¹ := by rw [← hgw.eq]
      _ = g * (w * h) * g⁻¹ := by group
  constructor
  · intro H
    have H' : h * w = w * h := H
    show (g * h * g⁻¹) * w = w * (g * h * g⁻¹)
    rw [f1, f2, H']
  · intro H
    have H' : (g * h * g⁻¹) * w = w * (g * h * g⁻¹) := H
    rw [f1, f2] at H'
    exact mul_left_cancel (mul_right_cancel H')

theorem B_comm_mem_normalizer_X {M X : Subgroup K} (hMn : M.Normal)
    (hcen : ∀ m ∈ M, ∀ x ∈ X, x * m = m * x) {w g : K} (hg : g ∈ X) :
    g ∈ Subgroup.normalizer ((M ⊓ Subgroup.centralizer {w} : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hM : h ∈ M
  · have e : g * h * g⁻¹ = h := by
      rw [hcen h hM g hg]
      group
    rw [e]
  · constructor
    · intro hh
      exact absurd (Subgroup.mem_inf.1 hh).1 hM
    · intro hh
      have hconj : g * h * g⁻¹ ∈ M := (Subgroup.mem_inf.1 hh).1
      have hback := hMn.conj_mem _ hconj g⁻¹
      have e' : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [e'] at hback
      exact absurd hback hM

theorem B_comm_mem_normalizer_cent {M : Subgroup K} (hMn : M.Normal) {w g : K}
    (hg : Commute g w) :
    g ∈ Subgroup.normalizer ((M ⊓ Subgroup.centralizer {w} : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨hhM, hhC⟩ := Subgroup.mem_inf.1 hh
    have hc : Commute h w := Subgroup.mem_centralizer_singleton_iff.1 hhC
    exact Subgroup.mem_inf.2 ⟨hMn.conj_mem h hhM g,
      Subgroup.mem_centralizer_singleton_iff.2 ((B_comm_commute_conj_iff hg).1 hc)⟩
  · intro hh
    obtain ⟨hhM, hhC⟩ := Subgroup.mem_inf.1 hh
    have hc : Commute (g * h * g⁻¹) w := Subgroup.mem_centralizer_singleton_iff.1 hhC
    have hback := hMn.conj_mem _ hhM g⁻¹
    have e' : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e'] at hback
    exact Subgroup.mem_inf.2 ⟨hback, Subgroup.mem_centralizer_singleton_iff.2
      ((B_comm_commute_conj_iff hg).2 hc)⟩

theorem B_comm_normal_cent {M X : Subgroup K} {u v w : K} (hMn : M.Normal)
    (hcen : ∀ m ∈ M, ∀ x ∈ X, x * m = m * x) (hgen : X ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers v = ⊤)
    (hw1 : Commute u w) (hw2 : Commute v w) :
    (M ⊓ Subgroup.centralizer {w}).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
  exact sup_le (sup_le (fun g hg => B_comm_mem_normalizer_X hMn hcen hg)
    (Subgroup.zpowers_le.2 (B_comm_mem_normalizer_cent hMn hw1)))
    (Subgroup.zpowers_le.2 (B_comm_mem_normalizer_cent hMn hw2))

end Cent

section Quot

variable {K : Type} [Group K] [Finite K]

theorem B_comm_quot_fix {X M : Subgroup K} (hX : IsPGroup 2 X)
    (hMX : M ≤ X) (hMn : M.Normal) {u a : K}
    (haX : a ∈ Subgroup.normalizer (X : Set K)) (ha2 : ¬ 2 ∣ orderOf a)
    (hfix : X ⊓ Subgroup.centralizer {a} ≤ Subgroup.centralizer {u}) :
    ∀ y ∈ X.map (QuotientGroup.mk' M) ⊓ Subgroup.centralizer {QuotientGroup.mk' M a},
      y ∈ Subgroup.centralizer {QuotientGroup.mk' M u} := by
  intro y hy
  obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hyX
  have hC : QuotientGroup.mk' M x * QuotientGroup.mk' M a =
      QuotientGroup.mk' M a * QuotientGroup.mk' M x := Subgroup.mem_centralizer_singleton_iff.1 hyC
  have hpi : QuotientGroup.mk' M (a * x * a⁻¹) = QuotientGroup.mk' M x := by
    rw [map_mul, map_mul, map_inv]
    have hC' : QuotientGroup.mk' M a * QuotientGroup.mk' M x =
        QuotientGroup.mk' M x * QuotientGroup.mk' M a := hC.symm
    rw [hC', mul_inv_cancel_right]
  have hn : x⁻¹ * (a * x * a⁻¹) ∈ M := QuotientGroup.eq.1 hpi.symm
  have haM : a ∈ Subgroup.normalizer (M : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hMn]
    exact Subgroup.mem_top _
  obtain ⟨q', hq'mem, n', hn', hxq⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF84.S3.B_coprime_quot 2 X M a hX hMX inferInstance haX haM
      ha2 x hx ⟨x⁻¹ * (a * x * a⁻¹), hn, by group⟩
  have hq'u : q' ∈ Subgroup.centralizer {u} := hfix hq'mem
  have hpx : QuotientGroup.mk' M x = QuotientGroup.mk' M q' := by
    have h1 : QuotientGroup.mk' M n' = 1 := (QuotientGroup.eq_one_iff n').2 hn'
    rw [hxq, map_mul, h1, mul_one]
  rw [Subgroup.mem_centralizer_singleton_iff, hpx]
  have hc : q' * u = u * q' := Subgroup.mem_centralizer_singleton_iff.1 hq'u
  rw [← map_mul, ← map_mul, hc]

theorem B_comm_not_two_dvd {a : K} (h3 : a ^ 3 = 1) : ¬ 2 ∣ orderOf a := by
  intro h2
  have hd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> rw [h] at h2 <;> norm_num at h2

end Quot

section Induction

theorem B_comm_three_bot {K : Type*} [Group K] (A A' : Subgroup K) (u : K)
    (hA : A ≤ Subgroup.centralizer {u}) (hD : ⁅A, A'⁆ ≤ Subgroup.centralizer {u})
    (hA'u : ⁅A', Subgroup.zpowers u⁆ = A') : ⁅A, A'⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  have hc : ∀ x ∈ A, ∀ y ∈ A', Commute x y := by
    refine B_comm_hw (A := A) (A' := A') (g := u)
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hA hx)) ?_ hA'u
    intro x hx y hy
    have hmem : x⁻¹ * y * x * y⁻¹ ∈ ⁅A, A'⁆ := by
      have := Subgroup.commutator_mem_commutator (A.inv_mem hx) hy
      rwa [commutatorElement_def, inv_inv] at this
    exact Subgroup.mem_centralizer_singleton_iff.1 (hD hmem)
  intro b hb
  exact (hc a ha b hb).symm

theorem B_comm_exists_min {K : Type} [Group K] [Finite K] {X : Subgroup K} (hXn : X.Normal)
    (hX1 : X ≠ ⊥) :
    ∃ M : Subgroup K, M.Normal ∧ M ≠ ⊥ ∧ M ≤ X ∧
      ∀ N : Subgroup K, N.Normal → N ≠ ⊥ → N ≤ M → N = M := by
  obtain ⟨M, ⟨hMn, hM1, hMX⟩, hmin⟩ :=
    (InvImage.wf (fun N : Subgroup K => Nat.card N) wellFounded_lt).has_min
      {N : Subgroup K | N.Normal ∧ N ≠ ⊥ ∧ N ≤ X} ⟨X, hXn, hX1, le_rfl⟩
  refine ⟨M, hMn, hM1, hMX, fun N hNn hN1 hNM => ?_⟩
  have hlt : ¬ Nat.card N < Nat.card M := hmin N ⟨hNn, hN1, hNM.trans hMX⟩
  exact Subgroup.eq_of_le_of_card_ge hNM (not_lt.1 hlt)

theorem B_comm_core (n : ℕ) : ∀ (K : Type) [Group K] [Finite K], Nat.card K = n →
    ∀ (X A A' : Subgroup K) (u v : K), IsPGroup 2 X → X.Normal → u ^ 3 = 1 → v ^ 3 = 1 →
    u * v = v * u → X ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers v = ⊤ →
    A ≤ X ⊓ Subgroup.centralizer {u} → A' ≤ X ⊓ Subgroup.centralizer {v} →
    ⁅A, Subgroup.zpowers v⁆ = A → ⁅A', Subgroup.zpowers u⁆ = A' →
    X ⊓ Subgroup.centralizer {u * v} ≤ Subgroup.centralizer {u} →
    X ⊓ Subgroup.centralizer {u * v ^ 2} ≤ Subgroup.centralizer {u} →
    ⁅A, A'⁆ = ⊥ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K _ _ hn X A A' u v hX hXn hu3 hv3 huv hgen hA hA' hAv hA'u hfix1 hfix2
  by_cases hX1 : X = ⊥
  · have hA0 : A = ⊥ := le_bot_iff.1 ((hA.trans inf_le_left).trans hX1.le)
    rw [hA0]
    simp
  obtain ⟨M, hMn, hM1, hMX, hmin⟩ := B_comm_exists_min hXn hX1
  haveI := hMn
  have hcard : Nat.card (K ⧸ M) < n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
    have h2 : 1 < Nat.card M := (Subgroup.one_lt_card_iff_ne_bot M).2 hM1
    have h3 : 0 < Nat.card (K ⧸ M) := Nat.card_pos
    rw [← hn, h1]
    exact lt_mul_of_one_lt_right h3 h2
  have hX' : IsPGroup 2 (X.map (QuotientGroup.mk' M)) := hX.map _
  have hXn' : (X.map (QuotientGroup.mk' M)).Normal :=
    hXn.map _ (QuotientGroup.mk'_surjective M)
  have hu3' : (QuotientGroup.mk' M u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hv3' : (QuotientGroup.mk' M v) ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
  have huv' : QuotientGroup.mk' M u * QuotientGroup.mk' M v =
      QuotientGroup.mk' M v * QuotientGroup.mk' M u := by
    rw [← map_mul, ← map_mul, huv]
  have hgen' : X.map (QuotientGroup.mk' M) ⊔ Subgroup.zpowers (QuotientGroup.mk' M u) ⊔
      Subgroup.zpowers (QuotientGroup.mk' M v) = ⊤ := by
    rw [← MonoidHom.map_zpowers (QuotientGroup.mk' M) u,
      ← MonoidHom.map_zpowers (QuotientGroup.mk' M) v, ← Subgroup.map_sup,
      ← Subgroup.map_sup, hgen, eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M y
    exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_top x, rfl⟩
  have hA'' : A.map (QuotientGroup.mk' M) ≤
      X.map (QuotientGroup.mk' M) ⊓ Subgroup.centralizer {QuotientGroup.mk' M u} := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 (hA hx)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨x, hxX, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    rw [← map_mul, ← map_mul, hxC]
  have hA''' : A'.map (QuotientGroup.mk' M) ≤
      X.map (QuotientGroup.mk' M) ⊓ Subgroup.centralizer {QuotientGroup.mk' M v} := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 (hA' hx)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨x, hxX, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    rw [← map_mul, ← map_mul, hxC]
  have hAv' : ⁅A.map (QuotientGroup.mk' M), Subgroup.zpowers (QuotientGroup.mk' M v)⁆ =
      A.map (QuotientGroup.mk' M) := by
    rw [← MonoidHom.map_zpowers (QuotientGroup.mk' M) v, ← Subgroup.map_commutator, hAv]
  have hA'u' : ⁅A'.map (QuotientGroup.mk' M), Subgroup.zpowers (QuotientGroup.mk' M u)⁆ =
      A'.map (QuotientGroup.mk' M) := by
    rw [← MonoidHom.map_zpowers (QuotientGroup.mk' M) u, ← Subgroup.map_commutator, hA'u]
  have huvX : u * v ∈ Subgroup.normalizer (X : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hXn]; exact Subgroup.mem_top _
  have hu2X : u * v ^ 2 ∈ Subgroup.normalizer (X : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hXn]; exact Subgroup.mem_top _
  have hcube1 : (u * v) ^ 3 = 1 := by
    rw [(show Commute u v from huv).mul_pow, hu3, hv3, one_mul]
  have hv6 : (v ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hv3, one_pow]
  have hcube2 : (u * v ^ 2) ^ 3 = 1 := by
    rw [(show Commute u (v ^ 2) from (show Commute u v from huv).pow_right 2).mul_pow, hu3,
      hv6, one_mul]
  have hfix1' : X.map (QuotientGroup.mk' M) ⊓
      Subgroup.centralizer {QuotientGroup.mk' M u * QuotientGroup.mk' M v} ≤
      Subgroup.centralizer {QuotientGroup.mk' M u} := by
    intro y hy
    exact B_comm_quot_fix hX hMX hMn (u := u) (a := u * v) huvX
      (B_comm_not_two_dvd hcube1) hfix1 y (by simpa only [map_mul] using hy)
  have hfix2' : X.map (QuotientGroup.mk' M) ⊓
      Subgroup.centralizer {QuotientGroup.mk' M u * QuotientGroup.mk' M v ^ 2} ≤
      Subgroup.centralizer {QuotientGroup.mk' M u} := by
    intro y hy
    exact B_comm_quot_fix hX hMX hMn (u := u) (a := u * v ^ 2) hu2X
      (B_comm_not_two_dvd hcube2) hfix2 y (by simpa only [map_mul, map_pow] using hy)
  have hIH := ih (Nat.card (K ⧸ M)) hcard (K ⧸ M) rfl (X.map (QuotientGroup.mk' M))
    (A.map (QuotientGroup.mk' M)) (A'.map (QuotientGroup.mk' M))
    (QuotientGroup.mk' M u) (QuotientGroup.mk' M v) hX' hXn' hu3' hv3' huv' hgen'
    hA'' hA''' hAv' hA'u' hfix1' hfix2'
  have hcM : ⁅A, A'⁆ ≤ M := by
    intro c hc
    have h1 : QuotientGroup.mk' M c ∈
        ⁅A.map (QuotientGroup.mk' M), A'.map (QuotientGroup.mk' M)⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem _ hc
    rw [hIH, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff c).1 h1
  have hcen := B_comm_minimal_centre hX hXn hMn hMX hM1 hmin
  have hexp := B_comm_minimal_exp hX hMn hMX hM1 hcen hmin
  have hw_u : (M ⊓ Subgroup.centralizer {u}).Normal :=
    B_comm_normal_cent hMn hcen hgen (Commute.refl u) (show Commute v u from huv.symm)
  have hw_v : (M ⊓ Subgroup.centralizer {v}).Normal :=
    B_comm_normal_cent hMn hcen hgen (show Commute u v from huv) (Commute.refl v)
  by_cases hu0 : M ⊓ Subgroup.centralizer {u} = ⊥
  · by_cases hv0 : M ⊓ Subgroup.centralizer {v} = ⊥
    · exfalso
      have hu : ∀ m ∈ M, u * m = m * u → m = 1 := fun m hm h => by
        have hm' : m ∈ M ⊓ Subgroup.centralizer {u} :=
          Subgroup.mem_inf.2 ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 h.symm⟩
        rw [hu0, Subgroup.mem_bot] at hm'
        exact hm'
      have hv : ∀ m ∈ M, v * m = m * v → m = 1 := fun m hm h => by
        have hm' : m ∈ M ⊓ Subgroup.centralizer {v} :=
          Subgroup.mem_inf.2 ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 h.symm⟩
        rw [hv0, Subgroup.mem_bot] at hm'
        exact hm'
      have huv1 : ∀ m ∈ M, (u * v) * m = m * (u * v) → m = 1 := fun m hm h => by
        have hmC : m ∈ X ⊓ Subgroup.centralizer {u * v} :=
          Subgroup.mem_inf.2 ⟨hMX hm, Subgroup.mem_centralizer_singleton_iff.2 h.symm⟩
        have hm' : m ∈ M ⊓ Subgroup.centralizer {u} :=
          Subgroup.mem_inf.2 ⟨hm, hfix1 hmC⟩
        rw [hu0, Subgroup.mem_bot] at hm'
        exact hm'
      have huv2 : ∀ m ∈ M, (u * v ^ 2) * m = m * (u * v ^ 2) → m = 1 := fun m hm h => by
        have hmC : m ∈ X ⊓ Subgroup.centralizer {u * v ^ 2} :=
          Subgroup.mem_inf.2 ⟨hMX hm, Subgroup.mem_centralizer_singleton_iff.2 h.symm⟩
        have hm' : m ∈ M ⊓ Subgroup.centralizer {u} :=
          Subgroup.mem_inf.2 ⟨hm, hfix2 hmC⟩
        rw [hu0, Subgroup.mem_bot] at hm'
        exact hm'
      have hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy =>
        (hcen x hx y (hMX hy)).symm
      exact hM1 (B_comm_eigen_group M hcomm hexp hu3 hv3 huv hu hv huv1 huv2)
    · have hMv : M ≤ Subgroup.centralizer {v} :=
        (le_of_eq (hmin _ hw_v hv0 inf_le_left).symm).trans inf_le_right
      have hcM' : ⁅A', A⁆ ≤ M := by rw [Subgroup.commutator_comm]; exact hcM
      rw [Subgroup.commutator_comm]
      exact B_comm_three_bot A' A v (hA'.trans inf_le_right) (hcM'.trans hMv) hAv
  · have hMu : M ≤ Subgroup.centralizer {u} :=
      (le_of_eq (hmin _ hw_u hu0 inf_le_left).symm).trans inf_le_right
    exact B_comm_three_bot A A' u (hA.trans inf_le_right) (hcM.trans hMu) hA'u

end Induction

section Final

theorem B_comm_of_fixed {G : Type} [Group G] [Finite G] {X A A' : Subgroup G} {u v : G}
    (hX : IsPGroup 2 X) (hu : orderOf u = 3) (hv : orderOf v = 3) (huv : u * v = v * u)
    (hEu : u ∈ Subgroup.normalizer (X : Set G)) (hEv : v ∈ Subgroup.normalizer (X : Set G))
    (hA : A ≤ X ⊓ Subgroup.centralizer {u}) (hA' : A' ≤ X ⊓ Subgroup.centralizer {v})
    (hAv : ⁅A, Subgroup.zpowers v⁆ = A) (hA'u : ⁅A', Subgroup.zpowers u⁆ = A')
    (hfix₁ : X ⊓ Subgroup.centralizer {u * v} ≤ Subgroup.centralizer {u})
    (hfix₂ : X ⊓ Subgroup.centralizer {u * v ^ 2} ≤ Subgroup.centralizer {u}) :
    ⁅A, A'⁆ = ⊥ := by
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hv3 : v ^ 3 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  set H : Subgroup G := X ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers v with hHdef
  have hXH : X ≤ H := le_sup_left.trans le_sup_left
  have hzuH : Subgroup.zpowers u ≤ H := le_sup_right.trans le_sup_left
  have hzvH : Subgroup.zpowers v ≤ H := le_sup_right
  have huH : u ∈ H := hzuH (Subgroup.mem_zpowers u)
  have hvH : v ∈ H := hzvH (Subgroup.mem_zpowers v)
  have hAH : A ≤ H := (hA.trans inf_le_left).trans hXH
  have hA'H : A' ≤ H := (hA'.trans inf_le_left).trans hXH
  have hHN : H ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (sup_le (fun x hx => Subgroup.le_normalizer hx) (Subgroup.zpowers_le.2 hEu))
      (Subgroup.zpowers_le.2 hEv)
  obtain ⟨u', hu'⟩ : ∃ u' : H, (u' : G) = u := ⟨⟨u, huH⟩, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v' : H, (v' : G) = v := ⟨⟨v, hvH⟩, rfl⟩
  have hXn : (X.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).2 hHN
  have hX' : IsPGroup 2 (X.subgroupOf H) :=
    hX.of_injective (Subgroup.subgroupOfEquivOfLe hXH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXH).injective
  have hu3' : u' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hu', Subgroup.coe_one]; exact hu3)
  have hv3' : v' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hv', Subgroup.coe_one]; exact hv3)
  have huv' : u' * v' = v' * u' :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hu', hv']; exact huv)
  obtain ⟨T, hT⟩ : ∃ T : Subgroup H, T = (X.subgroupOf H) ⊔ Subgroup.zpowers u' ⊔
      Subgroup.zpowers v' := ⟨_, rfl⟩
  have hgen' : (X.subgroupOf H) ⊔ Subgroup.zpowers u' ⊔ Subgroup.zpowers v' = ⊤ := by
    rw [← hT, eq_top_iff]
    have hTle : X.subgroupOf H ≤ T := by rw [hT]; exact le_sup_left.trans le_sup_left
    have hu'T : Subgroup.zpowers u' ≤ T := by rw [hT]; exact le_sup_right.trans le_sup_left
    have hv'T : Subgroup.zpowers v' ≤ T := by rw [hT]; exact le_sup_right
    have hXT : X ≤ T.map H.subtype := fun x hx =>
      Subgroup.mem_map.2 ⟨⟨x, hXH hx⟩, hTle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have huT : Subgroup.zpowers u ≤ T.map H.subtype :=
      Subgroup.zpowers_le.2 (Subgroup.mem_map.2 ⟨u', hu'T (Subgroup.mem_zpowers u'), hu'⟩)
    have hvT : Subgroup.zpowers v ≤ T.map H.subtype :=
      Subgroup.zpowers_le.2 (Subgroup.mem_map.2 ⟨v', hv'T (Subgroup.mem_zpowers v'), hv'⟩)
    have hHT : H ≤ T.map H.subtype := sup_le (sup_le hXT huT) hvT
    intro h _
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.1 (hHT h.2)
    have htq : t = h := Subtype.ext hteq
    subst htq
    exact ht
  have hAsub : (A.subgroupOf H).map H.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAH]
  have hA'sub : (A'.subgroupOf H).map H.subtype = A' := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA'H]
  have hinj : Function.Injective H.subtype := Subtype.coe_injective
  have hA'' : A.subgroupOf H ≤ X.subgroupOf H ⊓ Subgroup.centralizer {u'} := by
    intro a ha
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 (hA (Subgroup.mem_subgroupOf.1 ha))
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxX, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hu']
    exact Subgroup.mem_centralizer_singleton_iff.1 hxC
  have hA''' : A'.subgroupOf H ≤ X.subgroupOf H ⊓ Subgroup.centralizer {v'} := by
    intro a ha
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 (hA' (Subgroup.mem_subgroupOf.1 ha))
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxX, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hv']
    exact Subgroup.mem_centralizer_singleton_iff.1 hxC
  have hAv' : ⁅A.subgroupOf H, Subgroup.zpowers v'⁆ = A.subgroupOf H := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hAsub, MonoidHom.map_zpowers]
    have hvH' : H.subtype v' = v := hv'
    rw [hvH', hAv]
  have hA'u' : ⁅A'.subgroupOf H, Subgroup.zpowers u'⁆ = A'.subgroupOf H := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hA'sub, MonoidHom.map_zpowers]
    have huH' : H.subtype u' = u := hu'
    rw [huH', hA'u]
  have hfix1' : X.subgroupOf H ⊓ Subgroup.centralizer {u' * v'} ≤
      Subgroup.centralizer {u'} := by
    intro y hy
    obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
    have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hyC)
    simp only [Subgroup.coe_mul, hu', hv'] at hc
    have hyu := hfix₁ (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyX,
      Subgroup.mem_centralizer_singleton_iff.2 hc⟩)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hu']
    exact Subgroup.mem_centralizer_singleton_iff.1 hyu
  have hfix2' : X.subgroupOf H ⊓ Subgroup.centralizer {u' * v' ^ 2} ≤
      Subgroup.centralizer {u'} := by
    intro y hy
    obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
    have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hyC)
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hu', hv'] at hc
    have hyu := hfix₂ (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyX,
      Subgroup.mem_centralizer_singleton_iff.2 hc⟩)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hu']
    exact Subgroup.mem_centralizer_singleton_iff.1 hyu
  have hcore := B_comm_core (Nat.card H) (↥H) rfl (X.subgroupOf H) (A.subgroupOf H)
    (A'.subgroupOf H) u' v' hX' hXn hu3' hv3' huv' hgen' hA'' hA''' hAv' hA'u' hfix1' hfix2'
  have e : ⁅A, A'⁆ = (⁅A.subgroupOf H, A'.subgroupOf H⁆).map H.subtype := by
    rw [Subgroup.map_commutator, hAsub, hA'sub]
  rw [hcore, Subgroup.map_bot] at e
  exact e

end Final

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
