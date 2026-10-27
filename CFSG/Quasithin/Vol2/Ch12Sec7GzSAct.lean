module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSAb1

public section

namespace CFSG.Quasithin.H13.I1277

open Subgroup

@[expose] def Sig (d : ℕ) (φ : ℕ → ℕ) : Subgroup (Equiv.Perm (Fin (2 ^ d))) where
  carrier := {σ | (∀ a b c : Fin (2 ^ d), a.1 ^^^ b.1 = c.1 → (σ a).1 ^^^ (σ b).1 = (σ c).1) ∧
    ∀ a : Fin (2 ^ d), φ (σ a).1 = φ a.1}
  one_mem' := ⟨fun a b c h => by simpa using h, fun a => rfl⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, hσφ⟩ ⟨hτ, hτφ⟩
    refine ⟨fun a b c h => ?_, fun a => ?_⟩
    · have h1 := hτ a b c h
      exact hσ _ _ _ h1
    · show φ (σ (τ a)).1 = φ a.1
      rw [hσφ, hτφ]
  inv_mem' := by
    rintro σ ⟨hσ, hσφ⟩
    refine ⟨fun a b c h => ?_, fun a => ?_⟩
    ·
      have hx : (σ⁻¹ a).1 ^^^ (σ⁻¹ b).1 < 2 ^ d := Nat.xor_lt_two_pow (σ⁻¹ a).2 (σ⁻¹ b).2
      have h1 := hσ (σ⁻¹ a) (σ⁻¹ b) ⟨(σ⁻¹ a).1 ^^^ (σ⁻¹ b).1, hx⟩ rfl
      have e1 : σ (σ⁻¹ a) = a := by simp
      have e2 : σ (σ⁻¹ b) = b := by simp
      rw [e1, e2, h] at h1
      have : σ ⟨(σ⁻¹ a).1 ^^^ (σ⁻¹ b).1, hx⟩ = c := Fin.ext h1.symm
      have h3 : (⟨(σ⁻¹ a).1 ^^^ (σ⁻¹ b).1, hx⟩ : Fin (2 ^ d)) = σ⁻¹ c := by
        rw [← this]; simp
      have h4 := congrArg Fin.val h3
      exact h4
    · have := hσφ (σ⁻¹ a)
      rw [show σ (σ⁻¹ a) = a by simp] at this
      exact this.symm

structure FrData {G : Type} [Group G] (H Q N : Subgroup G) (d : ℕ) where
  wc : G → ℕ
  hQH : Q ≤ H
  hNQ : N ≤ Q
  hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  hNn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N
  hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ N
  wc_lt : ∀ x ∈ Q, wc x < 2 ^ d
  wc_mul : ∀ x ∈ Q, ∀ y ∈ Q, wc (x * y) = wc x ^^^ wc y
  wc_surj : ∀ e < 2 ^ d, ∃ x ∈ Q, wc x = e
  wc_ker : ∀ x ∈ Q, wc x = 0 ↔ x ∈ N

namespace FrData

variable {G : Type} [Group G] {H Q N : Subgroup G} {d : ℕ} (D : FrData H Q N d)

theorem wc_one : D.wc 1 = 0 := by
  have h := D.wc_mul 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  have h2 : D.wc 1 ^^^ D.wc 1 = 0 := Nat.xor_self _
  rw [← h] at h2
  exact h2

theorem wc_inv {x : G} (hx : x ∈ Q) : D.wc x⁻¹ = D.wc x := by
  have h := D.wc_mul x hx x⁻¹ (Q.inv_mem hx)
  rw [mul_inv_cancel, D.wc_one] at h
  have := congrArg (fun y => D.wc x ^^^ y) h
  simp only [Nat.xor_zero] at this
  rw [this, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem wc_eq_iff {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : D.wc x = D.wc y ↔ x⁻¹ * y ∈ N := by
  rw [← D.wc_ker _ (Q.mul_mem (Q.inv_mem hx) hy), D.wc_mul _ (Q.inv_mem hx) _ hy, D.wc_inv hx]
  constructor
  · intro h; rw [h, Nat.xor_self]
  · intro h
    have := congrArg (fun z => D.wc x ^^^ z) h
    simpa [← Nat.xor_assoc, Nat.xor_zero] using this.symm

theorem wc_conj_congr {h : G} (hh : h ∈ H) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : D.wc x = D.wc y) : D.wc (h * x * h⁻¹) = D.wc (h * y * h⁻¹) := by
  have h1 : x⁻¹ * y ∈ N := (D.wc_eq_iff hx hy).1 hxy
  have h2 := D.hNn h hh _ h1
  have h3 : (h * x * h⁻¹)⁻¹ * (h * y * h⁻¹) ∈ N := by
    have e : (h * x * h⁻¹)⁻¹ * (h * y * h⁻¹) = h * (x⁻¹ * y) * h⁻¹ := by group
    rw [e]; exact h2
  exact (D.wc_eq_iff (D.hQn h hh x hx) (D.hQn h hh y hy)).2 h3


@[expose] noncomputable def rep (e : Fin (2 ^ d)) : G := Classical.choose (D.wc_surj e.1 e.2)

theorem rep_mem (e : Fin (2 ^ d)) : D.rep e ∈ Q := (Classical.choose_spec (D.wc_surj e.1 e.2)).1

theorem wc_rep (e : Fin (2 ^ d)) : D.wc (D.rep e) = e.1 :=
  (Classical.choose_spec (D.wc_surj e.1 e.2)).2

@[expose] noncomputable def actFun (h : ↥H) (e : Fin (2 ^ d)) : Fin (2 ^ d) :=
  ⟨D.wc ((h : G) * D.rep e * (h : G)⁻¹), D.wc_lt _ (D.hQn h h.2 _ (D.rep_mem e))⟩

theorem actFun_of_mem (h : ↥H) {x : G} (hx : x ∈ Q) :
    D.actFun h ⟨D.wc x, D.wc_lt x hx⟩ = ⟨D.wc ((h : G) * x * (h : G)⁻¹),
      D.wc_lt _ (D.hQn h h.2 _ hx)⟩ := by
  apply Fin.ext
  show D.wc ((h : G) * D.rep ⟨D.wc x, D.wc_lt x hx⟩ * (h : G)⁻¹) = D.wc ((h : G) * x * (h : G)⁻¹)
  exact D.wc_conj_congr h.2 (D.rep_mem _) hx (D.wc_rep _)

theorem actFun_mul (h h' : ↥H) (e : Fin (2 ^ d)) :
    D.actFun (h * h') e = D.actFun h (D.actFun h' e) := by
  have hx : D.rep e ∈ Q := D.rep_mem e
  have h1 : D.actFun h' e = ⟨D.wc ((h' : G) * D.rep e * (h' : G)⁻¹),
      D.wc_lt _ (D.hQn h' h'.2 _ hx)⟩ := by
    have := D.actFun_of_mem h' hx
    have e' : (⟨D.wc (D.rep e), D.wc_lt _ hx⟩ : Fin (2 ^ d)) = e := Fin.ext (D.wc_rep e)
    rw [e'] at this
    exact this
  rw [h1, D.actFun_of_mem h (D.hQn h' h'.2 _ hx)]
  apply Fin.ext
  show D.wc (((h * h' : ↥H) : G) * D.rep e * ((h * h' : ↥H) : G)⁻¹) =
    D.wc ((h : G) * ((h' : G) * D.rep e * (h' : G)⁻¹) * (h : G)⁻¹)
  congr 1
  simp only [Subgroup.coe_mul, mul_inv_rev]
  group

theorem actFun_one (e : Fin (2 ^ d)) : D.actFun 1 e = e := by
  apply Fin.ext
  show D.wc (((1 : ↥H) : G) * D.rep e * ((1 : ↥H) : G)⁻¹) = e.1
  simpa using D.wc_rep e

@[expose] noncomputable def rho : ↥H →* Equiv.Perm (Fin (2 ^ d)) :=
  MonoidHom.mk'
    (fun h => ⟨D.actFun h, D.actFun h⁻¹,
      fun e => by rw [← D.actFun_mul, inv_mul_cancel, D.actFun_one],
      fun e => by rw [← D.actFun_mul, mul_inv_cancel, D.actFun_one]⟩)
    (fun h h' => Equiv.ext fun e => D.actFun_mul h h' e)

theorem rho_apply (h : ↥H) (e : Fin (2 ^ d)) : D.rho h e = D.actFun h e := rfl

theorem rho_of_mem (h : ↥H) {x : G} (hx : x ∈ Q) :
    (D.rho h ⟨D.wc x, D.wc_lt x hx⟩).1 = D.wc ((h : G) * x * (h : G)⁻¹) := by
  rw [D.rho_apply, D.actFun_of_mem h hx]

theorem rho_eq_one_of_mem {h : ↥H} (hh : (h : G) ∈ Q) : D.rho h = 1 := by
  apply Equiv.ext
  intro e
  apply Fin.ext
  have hx : D.rep e ∈ Q := D.rep_mem e
  have e' : (⟨D.wc (D.rep e), D.wc_lt _ hx⟩ : Fin (2 ^ d)) = e := Fin.ext (D.wc_rep e)
  have h1 := D.rho_of_mem h hx
  rw [e'] at h1
  rw [h1]
  show D.wc ((h : G) * D.rep e * (h : G)⁻¹) = e.1
  rw [← D.wc_rep e]
  symm
  rw [D.wc_eq_iff hx (D.hQn h h.2 _ hx)]
  have := D.hcomm _ (Q.inv_mem hx) _ hh
  simpa [mul_assoc] using this

theorem mem_of_rho_eq_one
    (hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X →
      X ≤ Q)
    (hQ2 : IsPGroup 2 ↥Q) (hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    (hNfr : ∀ n (hn : n ∈ N), (⟨n, D.hNQ hn⟩ : ↥Q) ∈ frattini ↥Q) [Finite G]
    {h : ↥H} (h1 : D.rho h = 1) : (h : G) ∈ Q := by
  refine mem_of_trivial_action hQmax D.hQH D.hQn hQ2 hC D.hNQ D.hNn hNfr h.2 ?_
  intro x hx
  have h2 := D.rho_of_mem h hx
  rw [h1] at h2
  have h3 : D.wc ((h : G) * x * (h : G)⁻¹) = D.wc x := by
    have : (1 : Equiv.Perm (Fin (2 ^ d))) ⟨D.wc x, D.wc_lt x hx⟩ = ⟨D.wc x, D.wc_lt x hx⟩ := rfl
    rw [this] at h2
    exact h2.symm
  have h4 : (x)⁻¹ * ((h : G) * x * (h : G)⁻¹) ∈ N :=
    (D.wc_eq_iff hx (D.hQn h h.2 _ hx)).1 h3.symm
  have h5 := D.hNn x (D.hQH hx) _ h4
  have e : x * (x⁻¹ * ((h : G) * x * (h : G)⁻¹)) * x⁻¹ = (h : G) * x * (h : G)⁻¹ * x⁻¹ := by
    group
  rw [e] at h5
  exact h5

theorem ker_rho_iff
    (hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X →
      X ≤ Q)
    (hQ2 : IsPGroup 2 ↥Q) (hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    (hNfr : ∀ n (hn : n ∈ N), (⟨n, D.hNQ hn⟩ : ↥Q) ∈ frattini ↥Q) [Finite G] (h : ↥H) :
    D.rho h = 1 ↔ (h : G) ∈ Q :=
  ⟨D.mem_of_rho_eq_one hQmax hQ2 hC hNfr, D.rho_eq_one_of_mem⟩

theorem rho_add (h : ↥H) (a b c : Fin (2 ^ d)) (habc : a.1 ^^^ b.1 = c.1) :
    (D.rho h a).1 ^^^ (D.rho h b).1 = (D.rho h c).1 := by
  have hx : D.rep a ∈ Q := D.rep_mem a
  have hy : D.rep b ∈ Q := D.rep_mem b
  have hxy : D.rep a * D.rep b ∈ Q := Q.mul_mem hx hy
  have ea : (⟨D.wc (D.rep a), D.wc_lt _ hx⟩ : Fin (2 ^ d)) = a := Fin.ext (D.wc_rep a)
  have eb : (⟨D.wc (D.rep b), D.wc_lt _ hy⟩ : Fin (2 ^ d)) = b := Fin.ext (D.wc_rep b)
  have ec : (⟨D.wc (D.rep a * D.rep b), D.wc_lt _ hxy⟩ : Fin (2 ^ d)) = c := by
    apply Fin.ext
    show D.wc (D.rep a * D.rep b) = c.1
    rw [D.wc_mul _ hx _ hy, D.wc_rep, D.wc_rep, habc]
  have h1 := D.rho_of_mem h hx
  have h2 := D.rho_of_mem h hy
  have h3 := D.rho_of_mem h hxy
  rw [ea] at h1
  rw [eb] at h2
  rw [ec] at h3
  rw [h1, h2, h3]
  have e : (h : G) * (D.rep a * D.rep b) * (h : G)⁻¹ =
      ((h : G) * D.rep a * (h : G)⁻¹) * ((h : G) * D.rep b * (h : G)⁻¹) := by group
  rw [e, D.wc_mul _ (D.hQn h h.2 _ hx) _ (D.hQn h h.2 _ hy)]

theorem range_le_Sig (phi : ℕ → ℕ) (lam : G → ℕ) (hphi : ∀ x ∈ Q, phi (D.wc x) = lam x)
    (hlam : ∀ h ∈ H, ∀ x ∈ Q, lam (h * x * h⁻¹) = lam x) : D.rho.range ≤ Sig d phi := by
  rintro _ ⟨h, rfl⟩
  refine ⟨fun a b c habc => D.rho_add h a b c habc, fun a => ?_⟩
  have hx : D.rep a ∈ Q := D.rep_mem a
  have ea : (⟨D.wc (D.rep a), D.wc_lt _ hx⟩ : Fin (2 ^ d)) = a := Fin.ext (D.wc_rep a)
  have h1 := D.rho_of_mem h hx
  rw [ea] at h1
  rw [h1, hphi _ (D.hQn h h.2 _ hx), hlam h h.2 _ hx, ← hphi _ hx, D.wc_rep]

theorem card_H
    (hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X →
      X ≤ Q)
    (hQ2 : IsPGroup 2 ↥Q) (hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    (hNfr : ∀ n (hn : n ∈ N), (⟨n, D.hNQ hn⟩ : ↥Q) ∈ frattini ↥Q) [Finite G] :
    Nat.card ↥H = Nat.card ↥Q * Nat.card ↥D.rho.range := by
  have hker : D.rho.ker = Q.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, D.ker_rho_iff hQmax hQ2 hC hNfr, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_ker_mul_card_range D.rho
  rw [hker] at h1
  have h2 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.hQH).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem eq_bot_of_normal_two
    (hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X →
      X ≤ Q)
    (hQ2 : IsPGroup 2 ↥Q) (hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    (hNfr : ∀ n (hn : n ∈ N), (⟨n, D.hNQ hn⟩ : ↥Q) ∈ frattini ↥Q) [Finite G]
    {X : Subgroup (Equiv.Perm (Fin (2 ^ d)))} (hXR : X ≤ D.rho.range)
    (hXn : ∀ r ∈ D.rho.range, ∀ x ∈ X, r * x * r⁻¹ ∈ X) (hX2 : IsPGroup 2 ↥X) : X = ⊥ := by
  classical
  set Y : Subgroup G := (X.comap D.rho).map H.subtype with hY
  have hYH : Y ≤ H := Subgroup.map_subtype_le _
  have hYmem : ∀ y, y ∈ Y ↔ ∃ k : ↥H, D.rho k ∈ X ∧ (k : G) = y := by
    intro y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
  have hYn : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y := by
    intro h hh y hy
    obtain ⟨k, hk, rfl⟩ := (hYmem y).1 hy
    refine (hYmem _).2 ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact hXn _ ⟨⟨h, hh⟩, rfl⟩ _ hk
  have hY2 : IsPGroup 2 ↥Y := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, rfl⟩ := (hYmem y).1 hy
    obtain ⟨a, ha⟩ := hX2 ⟨D.rho k, hk⟩
    have ha' : D.rho k ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hkq : (k ^ 2 ^ a : ↥H) ∈ D.rho.ker := by
      rw [MonoidHom.mem_ker, map_pow]; exact ha'
    have hkq' : ((k ^ 2 ^ a : ↥H) : G) ∈ Q := by
      have := (D.ker_rho_iff hQmax hQ2 hC hNfr (k ^ 2 ^ a)).1 hkq
      exact this
    obtain ⟨b, hb⟩ := hQ2 ⟨_, hkq'⟩
    have hb' : ((k : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    refine ⟨a + b, Subtype.ext ?_⟩
    show (k : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul, hb']
  have hYQ : Y ≤ Q := hQmax Y hYH hYn hY2
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := hXR hx
  have hkY : (k : G) ∈ Y := (hYmem _).2 ⟨k, hx, rfl⟩
  have := D.rho_eq_one_of_mem (hYQ hkY)
  rw [this]
  exact Subgroup.one_mem _

end FrData

end CFSG.Quasithin.H13.I1277

end
