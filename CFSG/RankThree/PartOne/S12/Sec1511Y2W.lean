module

public import CFSG.RankThree.PartOne.S12.Sec15FA

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace Sec1511

variable {G : Type} [Group G]

theorem orderOf_perm4_le (σ : Equiv.Perm (Fin 4)) : orderOf σ ≤ 4 := by
  have h : ∀ τ : Equiv.Perm (Fin 4), τ ^ 4 = 1 ∨ τ ^ 3 = 1 := by decide +kernel
  rcases h σ with h4 | h3
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)).trans (by norm_num)

theorem orderOf_perm5_le (σ : Equiv.Perm (Fin 5)) : orderOf σ ≤ 6 := by
  have h : ∀ τ : Equiv.Perm (Fin 5), τ ^ 4 = 1 ∨ τ ^ 3 = 1 ∨ τ ^ 5 = 1 ∨ τ ^ 6 = 1 := by
    decide +kernel
  rcases h σ with h4 | h3 | h5 | h6
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)).trans (by norm_num)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)).trans (by norm_num)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h5)).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h6)

theorem hord_perm4 {X : Type*} [Group X] {W₀ : Subgroup X} (e : ↥W₀ ≃* Equiv.Perm (Fin 4)) :
    ∀ u ∈ W₀, orderOf u ≤ 4 := fun u hu => by
  have h1 : orderOf u = orderOf (⟨u, hu⟩ : ↥W₀) := Subgroup.orderOf_coe (⟨u, hu⟩ : ↥W₀)
  rw [h1, ← orderOf_injective e.toMonoidHom e.injective]
  exact orderOf_perm4_le _

theorem hord_perm5 {X : Type*} [Group X] {W₀ : Subgroup X} (e : ↥W₀ ≃* Equiv.Perm (Fin 5)) :
    ∀ u ∈ W₀, orderOf u ≤ 6 := fun u hu => by
  have h1 : orderOf u = orderOf (⟨u, hu⟩ : ↥W₀) := Subgroup.orderOf_coe (⟨u, hu⟩ : ↥W₀)
  rw [h1, ← orderOf_injective e.toMonoidHom e.injective]
  exact orderOf_perm5_le _

theorem scalar_pow_eq_one {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : ∀ e ∈ E, e ^ p = 1)
    (hE1 : ∃ e ∈ E, e ≠ 1) {z : MulAut ↥E} {k : ℤ} (hk : ∀ e : ↥E, z e = e ^ k) :
    z ^ (p - 1) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ (j : ℕ) (e : ↥E), (z ^ j) e = e ^ (k ^ j) := by
    intro j
    induction j with
    | zero => intro e; simp
    | succ j ih =>
      intro e
      have h1 : (z ^ (j + 1)) e = (z ^ j) (z e) := by rw [pow_succ]; rfl
      rw [h1, hk e, map_zpow, ih, ← zpow_mul, pow_succ]
  obtain ⟨e₀, he₀, he₀1⟩ := hE1
  set x₀ : ↥E := ⟨e₀, he₀⟩ with hx₀
  have hx₀1 : x₀ ≠ 1 := fun h => he₀1 (congrArg Subtype.val h)
  have hx₀p : x₀ ^ p = 1 := Subtype.ext (hE e₀ he₀)
  have hx₀ord : orderOf x₀ = p := orderOf_eq_prime hx₀p hx₀1
  have hkp : ¬ (p : ℤ) ∣ k := by
    intro hdvd
    have h1 : x₀ ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hx₀ord]
      exact hdvd
    have h2 : z x₀ = 1 := by rw [hk, h1]
    apply hx₀1
    apply z.injective
    rw [h2, map_one]
  have hk0 : (k : ZMod p) ≠ 0 := fun h => hkp ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).1 h)
  have hfermat : ((k ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one hk0, sub_self]
  have hdvd : (p : ℤ) ∣ k ^ (p - 1) - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hfermat
  ext e
  rw [hpow]
  have he : e ^ p = 1 := Subtype.ext (hE e e.2)
  have hdvd' : (orderOf e : ℤ) ∣ k ^ (p - 1) - 1 :=
    (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one he)).trans hdvd
  have h3 := orderOf_dvd_iff_zpow_eq_one.1 hdvd'
  rw [zpow_sub, zpow_one, mul_inv_eq_one] at h3
  rw [h3]
  rfl

theorem weyl_decomp {p : ℕ} {E : Subgroup G} {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (φ : MulAut ↥E) (hφ : φ ∈ torusWeyl E) :
    ∃ z u : MulAut ↥E, z ∈ torusWeyl E ∧ u ∈ W₀ ∧ φ = z * u ∧
      (∀ y ∈ torusWeyl E, z * y = y * z) ∧ ∃ k : ℤ, ∀ e : ↥E, z e = e ^ k := by
  obtain ⟨-, -, -, hsup, -, hscal⟩ := hW
  set Wt : Subgroup (MulAut E) := torusWeyl E with hWt
  set Zq : Subgroup ↥Wt := Subgroup.center ↥Wt with hZq
  set Zc : Subgroup (MulAut E) := Zq.map Wt.subtype with hZc
  have hW0le : W₀ ≤ Wt := hsup ▸ le_sup_right
  set W0 : Subgroup ↥Wt := W₀.subgroupOf Wt with hW0
  have hsupQ : Zq ⊔ W0 = ⊤ := by
    rw [eq_top_iff]
    intro q _
    have hq : q.1 ∈ (Zq ⊔ W0).map Wt.subtype := by
      rw [Subgroup.map_sup, ← hZc, hW0, Subgroup.subgroupOf_map_subtype, inf_of_le_left hW0le,
        ← hsup]
      exact q.2
    obtain ⟨q', hq', hq'q⟩ := hq
    have : q' = q := Subtype.ext hq'q
    exact this ▸ hq'
  have hq : (⟨φ, hφ⟩ : ↥Wt) ∈ Zq ⊔ W0 := hsupQ ▸ Subgroup.mem_top _
  obtain ⟨z, hz, w, hw, hzw⟩ := Subgroup.mem_sup_of_normal_left.1 hq
  refine ⟨(z : MulAut ↥E), (w : MulAut ↥E), z.2, Subgroup.mem_subgroupOf.1 hw,
    (congrArg Subtype.val hzw).symm, fun y hy => ?_, hscal z hz⟩
  have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
  exact (congrArg Subtype.val this).symm

theorem normalizer_le_normalizer_centralizer (B : Subgroup G) :
    Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
    have hxb : x⁻¹ * b * x ∈ B := by
      have hx' := (Subgroup.normalizer (B : Set G)).inv_mem hx
      have := (Subgroup.mem_normalizer_iff.1 hx' b).1 hb
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_centralizer_iff.1 hy _ hxb
    calc b * (x * y * x⁻¹) = x * ((x⁻¹ * b * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * b * x)) * x⁻¹ := by rw [h1]
      _ = (x * y * x⁻¹) * b := by group
  · intro hy
    refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
    have hxb : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hx b).1 hb
    have h1 := Subgroup.mem_centralizer_iff.1 hy _ hxb
    have : x * (b * y) * x⁻¹ = x * (y * b) * x⁻¹ := by
      calc x * (b * y) * x⁻¹ = (x * b * x⁻¹) * (x * y * x⁻¹) := by group
        _ = (x * y * x⁻¹) * (x * b * x⁻¹) := h1
        _ = x * (y * b) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)

theorem exists_mul_decomp [Finite G] {p : ℕ} (hp : p.Prime) {E B : Subgroup G}
    (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hBE : B ≤ E) {n : G} (hn : n ∈ Subgroup.normalizer (B : Set G)) :
    ∃ c ∈ Subgroup.centralizer (B : Set G),
      ∃ w ∈ Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (E : Set G), n = c * w := by
  have hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' => by
    have := hE
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨e, he⟩ : ↥E) ⟨e', he'⟩)
  have hEC : E ≤ Subgroup.centralizer (B : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm b (hBE hb) e he)
  have hfr := Sec15FA.frattini_torus hp hE hJ (H := Subgroup.normalizer (B : Set G))
    (H₁ := Subgroup.centralizer (B : Set G)) hEC (Subgroup.centralizer_le_normalizer _)
    (normalizer_le_normalizer_centralizer B)
  have hLE : Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (normalizer_le_normalizer_centralizer B)
  have hmem : n ∈ (↑(Subgroup.centralizer (B : Set G) ⊔
      (Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (E : Set G))) : Set G) := hfr hn
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLE] at hmem
  obtain ⟨c, hc, w, hw, rfl⟩ := hmem
  exact ⟨c, hc, w, hw, rfl⟩

theorem aut_ord [Finite G] {p : ℕ} (hp : p.Prime) {E B : Subgroup G} (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hBE : B ≤ E) (hB1 : B ≠ ⊥) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀) {M₁ : ℕ}
    (hord : ∀ u ∈ W₀, orderOf u ≤ M₁) {n : G} (hn : n ∈ Subgroup.normalizer (B : Set G)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M₁ ∧ n ^ Nat.lcm (p - 1) m ∈ Subgroup.centralizer (B : Set G) := by
  classical
  obtain ⟨c, hc, w, hw, rfl⟩ := exists_mul_decomp hp hE hJ hBE hn
  have hwB : w ∈ Subgroup.normalizer (B : Set G) := hw.1
  have hwE : w ∈ Subgroup.normalizer (E : Set G) := hw.2
  set φ : MulAut ↥E := E.normalizerMonoidHom ⟨w, hwE⟩ with hφ
  have hφW : φ ∈ torusWeyl E := ⟨⟨w, hwE⟩, rfl⟩
  obtain ⟨z, u, hzW, huW, hφzu, hzc, k, hk⟩ := weyl_decomp hW φ hφW
  have hEexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hE1 : ∃ e ∈ E, e ≠ 1 := by
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
    exact ⟨b, hBE b.2, fun h => hb1 (Subtype.ext h)⟩
  have hz1 : z ^ (p - 1) = 1 := scalar_pow_eq_one hp hEexp hE1 hk
  have hW0le : W₀ ≤ torusWeyl E := by
    obtain ⟨-, -, -, hsup, -, -⟩ := hW
    exact hsup ▸ le_sup_right
  have huz : z * u = u * z := hzc u (hW0le huW)
  set m := orderOf u with hm
  have hm1 : 1 ≤ m := orderOf_pos u
  set L := Nat.lcm (p - 1) m with hL
  have hu1 : u ^ L = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact Nat.dvd_lcm_right _ _
  have hz1' : z ^ L = 1 := by
    obtain ⟨t, ht⟩ := Nat.dvd_lcm_left (p - 1) m
    rw [← hL] at ht
    rw [ht, pow_mul, hz1, one_pow]
  have hφL : φ ^ L = 1 := by
    rw [hφzu, (Commute.mul_pow (show Commute z u from huz) L), hz1', hu1, one_mul]
  have hwL : w ^ L ∈ Subgroup.centralizer (E : Set G) := by
    have h1 : E.normalizerMonoidHom ((⟨w, hwE⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ L) = 1 := by
      rw [map_pow]
      exact hφL
    have h2 : (⟨w, hwE⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ L ∈ E.normalizerMonoidHom.ker := h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hwLB : w ^ L ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le (by exact_mod_cast hBE) hwL
  refine ⟨m, hm1, hord u huW, ?_⟩
  set ψ : ↥(Subgroup.normalizer (B : Set G)) →* MulAut ↥B := B.normalizerMonoidHom with hψ
  have hker : ∀ x : ↥(Subgroup.normalizer (B : Set G)),
      ψ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (B : Set G) := fun x => by
    rw [← MonoidHom.mem_ker, hψ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have hcB : c ∈ Subgroup.normalizer (B : Set G) := (Subgroup.centralizer_le_normalizer _) hc
  have hcw : (⟨c * w, hn⟩ : ↥(Subgroup.normalizer (B : Set G))) = ⟨c, hcB⟩ * ⟨w, hwB⟩ := rfl
  have hψc : ψ ⟨c, hcB⟩ = 1 := (hker _).2 hc
  have hψcw : ψ ⟨c * w, hn⟩ = ψ ⟨w, hwB⟩ := by rw [hcw, map_mul, hψc, one_mul]
  have hψwL : ψ ((⟨w, hwB⟩ : ↥(Subgroup.normalizer (B : Set G))) ^ L) = 1 :=
    (hker _).2 hwLB
  have : ψ ((⟨c * w, hn⟩ : ↥(Subgroup.normalizer (B : Set G))) ^ L) = 1 := by
    rw [map_pow, hψcw, ← map_pow]
    exact hψwL
  exact (hker _).1 this

@[expose] def autStab {E : Type*} [Group E] (B : Subgroup E) : Subgroup (MulAut E) where
  carrier := {u | ∀ x : E, x ∈ B ↔ u x ∈ B}
  one_mem' := fun x => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (hb x).trans (ha (b x))
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from by simp] at h
    exact h.symm

@[expose] def KFW4Plane : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ (E : Type) [Group E] [Finite E], IsElementaryAbelian p E →
    Nat.card E = p ^ 3 → ∀ W₀ : Subgroup (MulAut E), Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) →
      ∀ B : Subgroup E, Nat.card ↥B = p ^ 2 → Nat.card ↥(W₀ ⊓ autStab B) ≤ 8

theorem scalar_pow_apply {E : Type*} [Group E] {z : MulAut E} {k : ℤ} (hk : ∀ e : E, z e = e ^ k)
    (j : ℕ) (e : E) : (z ^ j) e = e ^ (k ^ j) := by
  induction j generalizing e with
  | zero => simp
  | succ j ih =>
    have h1 : (z ^ (j + 1)) e = (z ^ j) (z e) := by rw [pow_succ]; rfl
    rw [h1, hk e, map_zpow, ih, ← zpow_mul, pow_succ]

theorem scalar_mem_autStab {p : ℕ} (hp : p.Prime) {E : Type*} [Group E] {z : MulAut E} {k : ℤ}
    (hk : ∀ e : E, z e = e ^ k) (hz : z ^ (p - 1) = 1) (B : Subgroup E) : z ∈ autStab B := by
  intro x
  constructor
  · intro hx
    rw [hk]
    exact Subgroup.zpow_mem _ hx _
  · intro hzx
    have h1 : (z ^ (p - 2 + 1)) x = x := by
      have : p - 2 + 1 = p - 1 := by have := hp.two_le; omega
      rw [this, hz]; rfl
    have h2 : (z ^ (p - 2 + 1)) x = (z ^ (p - 2)) (z x) := by rw [pow_succ]; rfl
    rw [← h1, h2, scalar_pow_apply hk]
    exact Subgroup.zpow_mem _ hzx _

theorem decomp_data [Finite G] {p : ℕ} (hp : p.Prime) {E B : Subgroup G}
    (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hBE : B ≤ E) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀) {x : G}
    (hx : x ∈ Subgroup.normalizer (B : Set G)) :
    ∃ (c w : G) (z u : MulAut ↥E), c ∈ Subgroup.centralizer (B : Set G) ∧
      w ∈ Subgroup.normalizer (B : Set G) ∧ w ∈ Subgroup.normalizer (E : Set G) ∧ x = c * w ∧
      z ∈ torusWeyl E ∧ u ∈ W₀ ∧
      (∀ hwE : w ∈ Subgroup.normalizer (E : Set G), E.normalizerMonoidHom ⟨w, hwE⟩ = z * u) ∧
      ∃ k : ℤ, ∀ e : ↥E, z e = e ^ k := by
  obtain ⟨c, hc, w, hw, rfl⟩ := exists_mul_decomp hp hE hJ hBE hx
  have hwE : w ∈ Subgroup.normalizer (E : Set G) := hw.2
  have hφW : E.normalizerMonoidHom ⟨w, hwE⟩ ∈ torusWeyl E := ⟨⟨w, hwE⟩, rfl⟩
  obtain ⟨z, u, hzW, huW, hφzu, -, k, hk⟩ := weyl_decomp hW _ hφW
  exact ⟨c, w, z, u, hc, hw.1, hwE, rfl, hzW, huW, fun _ => hφzu, k, hk⟩

theorem normalizerMonoidHom_mul_centralizer {B : Subgroup G} {c w : G}
    (hc : c ∈ Subgroup.centralizer (B : Set G)) (hw : w ∈ Subgroup.normalizer (B : Set G)) :
    B.normalizerMonoidHom ⟨c * w, (Subgroup.normalizer (B : Set G)).mul_mem
      ((Subgroup.centralizer_le_normalizer _) hc) hw⟩ = B.normalizerMonoidHom ⟨w, hw⟩ := by
  have hcB : c ∈ Subgroup.normalizer (B : Set G) := (Subgroup.centralizer_le_normalizer _) hc
  have h1 : B.normalizerMonoidHom ⟨c, hcB⟩ = 1 := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact hc
  have : (⟨c * w, (Subgroup.normalizer (B : Set G)).mul_mem hcB hw⟩ :
      ↥(Subgroup.normalizer (B : Set G))) = ⟨c, hcB⟩ * ⟨w, hw⟩ := rfl
  rw [this, map_mul, h1, one_mul]

theorem normalizerMonoidHom_eq_one_iff {B : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (B : Set G)) :
    B.normalizerMonoidHom ⟨x, hx⟩ = 1 ↔ x ∈ Subgroup.centralizer (B : Set G) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem card_scalars_le {p : ℕ} (hp : p.Prime) {E : Type*} [Group E] [Finite E]
    (hE : ∀ e : E, e ^ p = 1) (hE1 : ∃ e : E, e ≠ 1) :
    {z : MulAut E | ∃ k : ℤ, ∀ e : E, z e = e ^ k}.ncard ≤ p - 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀1⟩ := hE1
  have hx₀ord : orderOf x₀ = p := orderOf_eq_prime (hE x₀) hx₀1
  set T : Set E := (Subgroup.zpowers x₀ : Set E) \ {1} with hT
  have hTcard : T.ncard = p - 1 := by
    rw [hT, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
    have : Nat.card ↥(Subgroup.zpowers x₀) = p := by rw [Nat.card_zpowers, hx₀ord]
    exact congrArg (· - 1) this
  rw [← hTcard]
  refine Set.ncard_le_ncard_of_injOn (fun z : MulAut E => z x₀) ?_ ?_ (Set.toFinite T)
  · rintro z ⟨k, hk⟩
    refine ⟨?_, ?_⟩
    · rw [hk]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x₀) k
    · intro h1
      have h2 : z x₀ = 1 := h1
      exact hx₀1 (z.injective (by rw [h2, map_one]))
  · rintro z ⟨k, hk⟩ z' ⟨k', hk'⟩ h
    have h1 : x₀ ^ k = x₀ ^ k' := by rw [← hk, ← hk']; exact h
    have h2 : (orderOf x₀ : ℤ) ∣ k - k' := by
      rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1, mul_inv_cancel]
    ext e
    rw [hk e, hk' e]
    have he : e ^ p = 1 := hE e
    have h3 : (orderOf e : ℤ) ∣ k - k' :=
      (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one he)).trans (hx₀ord ▸ h2)
    have h4 := orderOf_dvd_iff_zpow_eq_one.1 h3
    rwa [zpow_sub, mul_inv_eq_one] at h4

theorem aut_count [Finite G] (hK : KFW4Plane) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E B : Subgroup G} (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hE3 : Nat.card ↥E = p ^ 3) (hBE : B ≤ E) (hB2 : Nat.card ↥B = p ^ 2)
    {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀) (hW4 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)))
    (F : Finset G) (hFN : ∀ x ∈ F, x ∈ Subgroup.normalizer (B : Set G))
    (hFne : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → x⁻¹ * y ∉ Subgroup.centralizer (B : Set G)) :
    F.card ≤ (p - 1) * 8 := by
  classical
  have hB1 : B ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥B = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hB2] at h1
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hEexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hE1 : ∃ e ∈ E, e ≠ 1 := by
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
    exact ⟨b, hBE b.2, fun h => hb1 (Subtype.ext h)⟩
  have hdata : ∀ x ∈ Subgroup.normalizer (B : Set G), ∃ (c w : G) (z u : MulAut ↥E),
      c ∈ Subgroup.centralizer (B : Set G) ∧ w ∈ Subgroup.normalizer (B : Set G) ∧
      w ∈ Subgroup.normalizer (E : Set G) ∧ x = c * w ∧ z ∈ torusWeyl E ∧ u ∈ W₀ ∧
      (∀ hwE : w ∈ Subgroup.normalizer (E : Set G), E.normalizerMonoidHom ⟨w, hwE⟩ = z * u) ∧
      ∃ k : ℤ, ∀ e : ↥E, z e = e ^ k :=
    fun x hx => decomp_data hp hE hJ hBE hW hx
  choose! cf wf zf uf hc hwB hwE hxeq hzW huW hφ hk using hdata
  set B' : Subgroup ↥E := B.subgroupOf E with hB'
  have hB'card : Nat.card ↥B' = p ^ 2 := by
    rw [← hB2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv
  have hUcard : Nat.card ↥(W₀ ⊓ autStab B') ≤ 8 := hK p hp hp5 ↥E hE hE3 W₀ hW4 B' hB'card
  have hmemU : ∀ x ∈ Subgroup.normalizer (B : Set G), uf x ∈ W₀ ⊓ autStab B' := by
    intro x hx
    refine ⟨huW x hx, ?_⟩
    obtain ⟨k, hkx⟩ := hk x hx
    have hz1 : zf x ^ (p - 1) = 1 :=
      scalar_pow_eq_one hp hEexp hE1 hkx
    have hzst : zf x ∈ autStab B' := scalar_mem_autStab hp hkx hz1 B'
    have hφst : E.normalizerMonoidHom ⟨wf x, hwE x hx⟩ ∈ autStab B' := by
      intro e
      show e ∈ B' ↔ (E.normalizerMonoidHom ⟨wf x, hwE x hx⟩ e) ∈ B'
      have h1 := Subgroup.mem_normalizer_iff.1 (hwB x hx) (e : G)
      exact h1
    have hu : uf x = (zf x)⁻¹ * E.normalizerMonoidHom ⟨wf x, hwE x hx⟩ := by
      rw [hφ x hx (hwE x hx)]; group
    rw [hu]
    exact (autStab B').mul_mem ((autStab B').inv_mem hzst) hφst
  have hψ : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (B : Set G)),
      B.normalizerMonoidHom ⟨x, hx⟩ = B.normalizerMonoidHom ⟨wf x, hwB x hx⟩ := by
    intro x hx
    have := normalizerMonoidHom_mul_centralizer (hc x hx) (hwB x hx)
    have hxe : x = cf x * wf x := hxeq x hx
    simp only [← hxe] at this
    exact this
  have hinj : Set.InjOn (fun x : G => (zf x, uf x)) (F : Set G) := by
    intro x hxF y hyF hxy
    have hx := hFN x hxF
    have hy := hFN y hyF
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hz, hu⟩ := hxy
    by_contra hne
    apply hFne x hxF y hyF hne
    have hφxy : E.normalizerMonoidHom ⟨wf x, hwE x hx⟩ = E.normalizerMonoidHom ⟨wf y, hwE y hy⟩ := by
      rw [hφ x hx (hwE x hx), hφ y hy (hwE y hy), hz, hu]
    have hwxy : (wf x)⁻¹ * wf y ∈ Subgroup.centralizer (E : Set G) := by
      have h1 : (⟨(wf x)⁻¹ * wf y, (Subgroup.normalizer (E : Set G)).mul_mem
          ((Subgroup.normalizer (E : Set G)).inv_mem (hwE x hx)) (hwE y hy)⟩ :
          ↥(Subgroup.normalizer (E : Set G))) =
          (⟨wf x, hwE x hx⟩ : ↥(Subgroup.normalizer (E : Set G)))⁻¹ * ⟨wf y, hwE y hy⟩ := rfl
      have h2 := (normalizerMonoidHom_eq_one_iff (B := E) ((Subgroup.normalizer (E : Set G)).mul_mem
          ((Subgroup.normalizer (E : Set G)).inv_mem (hwE x hx)) (hwE y hy))).1 (by
        rw [h1, map_mul, map_inv, hφxy]; simp)
      exact h2
    have hwxyB : (wf x)⁻¹ * wf y ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast hBE) hwxy
    have hxyN : x⁻¹ * y ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).mul_mem ((Subgroup.normalizer (B : Set G)).inv_mem hx) hy
    refine (normalizerMonoidHom_eq_one_iff hxyN).1 ?_
    have h1 : (⟨x⁻¹ * y, hxyN⟩ : ↥(Subgroup.normalizer (B : Set G))) =
        (⟨x, hx⟩ : ↥(Subgroup.normalizer (B : Set G)))⁻¹ * ⟨y, hy⟩ := rfl
    rw [h1, map_mul, map_inv, hψ x hx, hψ y hy, ← map_inv, ← map_mul]
    exact (normalizerMonoidHom_eq_one_iff
      ((Subgroup.normalizer (B : Set G)).mul_mem ((Subgroup.normalizer (B : Set G)).inv_mem (hwB x hx))
        (hwB y hy))).2 hwxyB
  have : Finite (MulAut ↥E) :=
    Finite.of_injective (fun f : MulAut ↥E => (f : ↥E → ↥E)) (fun f g h => MulEquiv.ext (congrFun h))
  set Zs : Set (MulAut ↥E) := {z | ∃ k : ℤ, ∀ e : ↥E, z e = e ^ k} with hZs
  have hZsc : Zs.ncard ≤ p - 1 :=
    card_scalars_le hp (fun e => Subtype.ext (hEexp e e.2)) (by
      obtain ⟨e, he, he1⟩ := hE1
      exact ⟨⟨e, he⟩, fun h => he1 (congrArg Subtype.val h)⟩)
  set ZF : Finset (MulAut ↥E) := (Set.toFinite Zs).toFinset with hZF
  set UF : Finset (MulAut ↥E) := (Set.toFinite ((W₀ ⊓ autStab B' : Subgroup (MulAut ↥E)) :
    Set (MulAut ↥E))).toFinset with hUF
  have hZFc : ZF.card ≤ p - 1 := by
    rw [hZF, ← Set.ncard_eq_toFinset_card Zs (Set.toFinite Zs)]
    exact hZsc
  have hUFc : UF.card ≤ 8 := by
    rw [hUF, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _), ← Nat.card_coe_set_eq]
    exact hUcard
  have hmaps : ∀ x ∈ F, (zf x, uf x) ∈ ZF ×ˢ UF := by
    intro x hxF
    have hx := hFN x hxF
    rw [Finset.mem_product, hZF, hUF, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact ⟨hk x hx, hmemU x hx⟩
  calc F.card ≤ (ZF ×ˢ UF).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ZF.card * UF.card := Finset.card_product _ _
    _ ≤ (p - 1) * 8 := Nat.mul_le_mul hZFc hUFc

end Sec1511

end CFSG.RankThree.PartOne
