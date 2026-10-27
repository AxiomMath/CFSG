module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G]

structure MulData (V U Q : Subgroup G) (K : Type) [Field K] where
  γ : G → K
  ψ : G → K
  t : G → K
  γ_add : ∀ a ∈ V, ∀ b ∈ V, γ (a * b) = γ a + γ b
  γ_inj : ∀ a ∈ V, γ a = 0 → a = 1
  γ_surj : ∀ s : K, ∃ a ∈ V, γ a = s
  ψ_add : ∀ a ∈ U, ∀ b ∈ U, ψ (a * b) = ψ a + ψ b
  ψ_inj : ∀ a ∈ U, ψ a = 0 → a = 1
  ψ_surj : ∀ s : K, ∃ a ∈ U, ψ a = s
  t_add : ∀ a ∈ Q, ∀ b ∈ Q, t (a * b) = t a + t b
  t_surj : ∀ s : K, ∃ a ∈ Q, t a = s
  t_ker : ∀ a ∈ Q, t a = 0 ↔ a ∈ Subgroup.centralizer (U : Set G)
  comm : ∀ y ∈ Q, ∀ u ∈ U, ⁅y, u⁆ ∈ V ∧ γ ⁅y, u⁆ = t y * ψ u

section Additive

variable {S : Subgroup G} {K : Type} [Field K] {f : G → K}

theorem map_one_of_additive (hadd : ∀ a ∈ S, ∀ b ∈ S, f (a * b) = f a + f b) : f 1 = 0 := by
  have h := hadd 1 S.one_mem 1 S.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem map_inv_of_additive (hadd : ∀ a ∈ S, ∀ b ∈ S, f (a * b) = f a + f b) {a : G}
    (ha : a ∈ S) : f a⁻¹ = - f a := by
  have h := hadd a ha a⁻¹ (S.inv_mem ha)
  rw [mul_inv_cancel, map_one_of_additive hadd] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem eq_of_map_eq_of_additive (hadd : ∀ a ∈ S, ∀ b ∈ S, f (a * b) = f a + f b)
    (hinj : ∀ a ∈ S, f a = 0 → a = 1) {a b : G} (ha : a ∈ S) (hb : b ∈ S)
    (h : f a = f b) : a = b := by
  have h1 := hinj (a * b⁻¹) (S.mul_mem ha (S.inv_mem hb)) (by
    rw [hadd a ha b⁻¹ (S.inv_mem hb), map_inv_of_additive hadd hb, h, add_neg_cancel])
  exact mul_inv_eq_one.mp h1

theorem mul_comm_of_additive (hadd : ∀ a ∈ S, ∀ b ∈ S, f (a * b) = f a + f b)
    (hinj : ∀ a ∈ S, f a = 0 → a = 1) {a b : G} (ha : a ∈ S) (hb : b ∈ S) : a * b = b * a :=
  eq_of_map_eq_of_additive hadd hinj (S.mul_mem ha hb) (S.mul_mem hb ha)
    (by rw [hadd a ha b hb, hadd b hb a ha, add_comm])

end Additive

namespace MulData

variable {V U Q : Subgroup G} {K : Type} [Field K] (D : MulData V U Q K)

theorem γ_one : D.γ 1 = 0 := map_one_of_additive D.γ_add

theorem ψ_one : D.ψ 1 = 0 := map_one_of_additive D.ψ_add

theorem t_one : D.t 1 = 0 := map_one_of_additive D.t_add

theorem γ_inv {v : G} (hv : v ∈ V) : D.γ v⁻¹ = - D.γ v := map_inv_of_additive D.γ_add hv

theorem t_inv {y : G} (hy : y ∈ Q) : D.t y⁻¹ = - D.t y := map_inv_of_additive D.t_add hy

theorem eq_of_γ_eq {a b : G} (ha : a ∈ V) (hb : b ∈ V) (h : D.γ a = D.γ b) : a = b :=
  eq_of_map_eq_of_additive D.γ_add D.γ_inj ha hb h

theorem eq_of_ψ_eq {a b : G} (ha : a ∈ U) (hb : b ∈ U) (h : D.ψ a = D.ψ b) : a = b :=
  eq_of_map_eq_of_additive D.ψ_add D.ψ_inj ha hb h

include D in
theorem mul_comm_U {a b : G} (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a :=
  mul_comm_of_additive D.ψ_add D.ψ_inj ha hb

noncomputable def vinv (s : K) : G := Classical.choose (D.γ_surj s)

theorem vinv_mem (s : K) : D.vinv s ∈ V := (Classical.choose_spec (D.γ_surj s)).1

theorem γ_vinv (s : K) : D.γ (D.vinv s) = s := (Classical.choose_spec (D.γ_surj s)).2

theorem vinv_γ {v : G} (hv : v ∈ V) : D.vinv (D.γ v) = v :=
  D.eq_of_γ_eq (D.vinv_mem _) hv (D.γ_vinv _)

theorem vinv_add (s s' : K) : D.vinv (s + s') = D.vinv s * D.vinv s' :=
  D.eq_of_γ_eq (D.vinv_mem _) (V.mul_mem (D.vinv_mem _) (D.vinv_mem _))
    (by rw [D.γ_vinv, D.γ_add _ (D.vinv_mem s) _ (D.vinv_mem s'), D.γ_vinv, D.γ_vinv])

theorem vinv_zero : D.vinv 0 = 1 :=
  D.eq_of_γ_eq (D.vinv_mem _) V.one_mem (by rw [D.γ_vinv, D.γ_one])

noncomputable def uinv (s : K) : G := Classical.choose (D.ψ_surj s)

theorem uinv_mem (s : K) : D.uinv s ∈ U := (Classical.choose_spec (D.ψ_surj s)).1

theorem ψ_uinv (s : K) : D.ψ (D.uinv s) = s := (Classical.choose_spec (D.ψ_surj s)).2

theorem uinv_ψ {u : G} (hu : u ∈ U) : D.uinv (D.ψ u) = u :=
  D.eq_of_ψ_eq (D.uinv_mem _) hu (D.ψ_uinv _)

theorem uinv_add (s s' : K) : D.uinv (s + s') = D.uinv s * D.uinv s' :=
  D.eq_of_ψ_eq (D.uinv_mem _) (U.mul_mem (D.uinv_mem _) (D.uinv_mem _))
    (by rw [D.ψ_uinv, D.ψ_add _ (D.uinv_mem s) _ (D.uinv_mem s'), D.ψ_uinv, D.ψ_uinv])

theorem uinv_zero : D.uinv 0 = 1 :=
  D.eq_of_ψ_eq (D.uinv_mem _) U.one_mem (by rw [D.ψ_uinv, D.ψ_one])

noncomputable def tinv (s : K) : G := Classical.choose (D.t_surj s)

theorem tinv_mem (s : K) : D.tinv s ∈ Q := (Classical.choose_spec (D.t_surj s)).1

theorem t_tinv (s : K) : D.t (D.tinv s) = s := (Classical.choose_spec (D.t_surj s)).2

theorem t_eq_of_t_eq {D' : MulData V U Q K} {y y' : G} (hy : y ∈ Q) (hy' : y' ∈ Q)
    (h : D.t y = D.t y') : D'.t y = D'.t y' := by
  have h1 : D.t (y * y'⁻¹) = 0 := by
    rw [D.t_add y hy y'⁻¹ (Q.inv_mem hy'), D.t_inv hy', h, add_neg_cancel]
  have h2 := (D'.t_ker _ (Q.mul_mem hy (Q.inv_mem hy'))).mpr ((D.t_ker _ (Q.mul_mem hy
    (Q.inv_mem hy'))).mp h1)
  rw [D'.t_add y hy y'⁻¹ (Q.inv_mem hy'), D'.t_inv hy'] at h2
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h2)

end MulData

theorem exists_ringEquiv_of_mul_eq {K : Type*} [Field K] (θ f g : K →+ K)
    (hθ : Function.Bijective θ) (h : ∀ x y, θ (x * y) = f x * g y) :
    ∃ σ : K ≃+* K, ∀ x, θ x = θ 1 * σ x := by
  have h1 : θ 1 ≠ 0 := fun h0 => one_ne_zero (hθ.1 (by rw [h0, map_zero]))
  have hf1 : ∀ x, θ x = f x * g 1 := fun x => by rw [← h x 1, mul_one]
  have hg1 : ∀ y, θ y = f 1 * g y := fun y => by rw [← h 1 y, one_mul]
  have hθ11 : θ 1 = f 1 * g 1 := by rw [← h 1 1, mul_one]
  have hmul : ∀ x y, θ (x * y) * θ 1 = θ x * θ y := by
    intro x y
    rw [h x y, hf1 x, hg1 y, hθ11]
    ring
  let σ₀ : K →+* K :=
    { toFun := fun x => θ x / θ 1
      map_one' := div_self h1
      map_mul' := fun x y => by
        have := hmul x y
        field_simp
        linear_combination this
      map_zero' := by simp
      map_add' := fun x y => by rw [map_add, add_div] }
  have hbij : Function.Bijective σ₀ := by
    constructor
    · intro x y hxy
      apply hθ.1
      have : θ x / θ 1 = θ y / θ 1 := hxy
      exact (div_left_inj' h1).mp this
    · intro r
      obtain ⟨x, hx⟩ := hθ.2 (r * θ 1)
      exact ⟨x, by show θ x / θ 1 = r; rw [hx]; field_simp⟩
  refine ⟨RingEquiv.ofBijective σ₀ hbij, fun x => ?_⟩
  show θ x = θ 1 * (θ x / θ 1)
  field_simp

namespace MulData

variable {V U Q U' Q' : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def thetaHom (D : MulData V U Q K) (D' : MulData V U' Q' K) : K →+ K :=
  AddMonoidHom.mk' (fun s => D'.γ (D.vinv s)) (fun s s' => by
    rw [D.vinv_add, D'.γ_add _ (D.vinv_mem s) _ (D.vinv_mem s')])

theorem thetaHom_apply (D : MulData V U Q K) (D' : MulData V U' Q' K) (s : K) :
    thetaHom D D' s = D'.γ (D.vinv s) := rfl

theorem thetaHom_γ (D : MulData V U Q K) (D' : MulData V U' Q' K) {v : G} (hv : v ∈ V) :
    thetaHom D D' (D.γ v) = D'.γ v := by
  rw [thetaHom_apply, D.vinv_γ hv]

theorem thetaHom_bijective (D : MulData V U Q K) (D' : MulData V U' Q' K) :
    Function.Bijective (thetaHom D D') := by
  constructor
  · intro s s' h
    have h1 := D'.eq_of_γ_eq (D.vinv_mem s) (D.vinv_mem s') h
    rw [← D.γ_vinv s, ← D.γ_vinv s', h1]
  · intro r
    obtain ⟨a, ha, hr⟩ := D'.γ_surj r
    exact ⟨D.γ a, by rw [thetaHom_γ D D' ha, hr]⟩

theorem compat_same (D D' : MulData V U Q K) :
    ∃ (c : K) (σ : K ≃+* K), c ≠ 0 ∧ ∀ v ∈ V, D'.γ v = c * σ (D.γ v) := by
  let f : K →+ K := AddMonoidHom.mk' (fun s => D'.t (D.tinv s)) (fun s s' => by
    have h1 : D.t (D.tinv (s + s')) = D.t (D.tinv s * D.tinv s') := by
      rw [D.t_tinv, D.t_add _ (D.tinv_mem s) _ (D.tinv_mem s'), D.t_tinv, D.t_tinv]
    rw [D.t_eq_of_t_eq (D' := D') (D.tinv_mem _)
      (Q.mul_mem (D.tinv_mem s) (D.tinv_mem s')) h1,
      D'.t_add _ (D.tinv_mem s) _ (D.tinv_mem s')])
  let g : K →+ K := AddMonoidHom.mk' (fun r => D'.ψ (D.uinv r)) (fun r r' => by
    rw [D.uinv_add, D'.ψ_add _ (D.uinv_mem r) _ (D.uinv_mem r')])
  have heq : ∀ x y, thetaHom D D' (x * y) = f x * g y := by
    intro x y
    obtain ⟨hV, hγ⟩ := D.comm (D.tinv x) (D.tinv_mem x) (D.uinv y) (D.uinv_mem y)
    obtain ⟨-, hγ'⟩ := D'.comm (D.tinv x) (D.tinv_mem x) (D.uinv y) (D.uinv_mem y)
    rw [D.t_tinv, D.ψ_uinv] at hγ
    have h1 : D.vinv (x * y) = ⁅D.tinv x, D.uinv y⁆ :=
      D.eq_of_γ_eq (D.vinv_mem _) hV (by rw [D.γ_vinv, hγ])
    rw [thetaHom_apply, h1, hγ']
    rfl
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_mul_eq (thetaHom D D') f g (thetaHom_bijective D D') heq
  refine ⟨thetaHom D D' 1, σ, ?_, fun v hv => ?_⟩
  · intro h0
    exact one_ne_zero ((thetaHom_bijective D D').1 (h0.trans (map_zero _).symm))
  · rw [← thetaHom_γ D D' hv, hσ]

end MulData


namespace MulData

variable {V U U₁ U₂ Q : Subgroup G} {K : Type} [Field K]

theorem card_U (D : MulData V U Q K) : Nat.card U = Nat.card K := by
  refine Nat.card_congr (Equiv.ofBijective (fun u : U => D.ψ u) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (D.eq_of_ψ_eq a.2 b.2 h)
  · intro s
    obtain ⟨a, ha, hs⟩ := D.ψ_surj s
    exact ⟨⟨a, ha⟩, hs⟩

theorem V_le_Q (D : MulData V U Q K) (hU : U ≤ Q) : V ≤ Q := by
  intro v hv
  obtain ⟨hV, hγ⟩ := D.comm (D.tinv (D.γ v)) (D.tinv_mem _) (D.uinv 1) (D.uinv_mem 1)
  rw [D.t_tinv, D.ψ_uinv, mul_one] at hγ
  have h1 : ⁅D.tinv (D.γ v), D.uinv 1⁆ = v := D.eq_of_γ_eq hV hv hγ
  rw [← h1, commutatorElement_def]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem (D.tinv_mem _) (hU (D.uinv_mem 1)))
    (Q.inv_mem (D.tinv_mem _))) (Q.inv_mem (hU (D.uinv_mem 1)))

theorem eq_one_of_mem_V (D : MulData V U Q K) (hVc : ∀ v ∈ V, ∀ y ∈ Q, v * y = y * v) {u : G}
    (hu : u ∈ U) (hv : u ∈ V) : u = 1 := by
  obtain ⟨-, hγ⟩ := D.comm (D.tinv 1) (D.tinv_mem 1) u hu
  have h1 : ⁅D.tinv 1, u⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hVc u hv _ (D.tinv_mem 1)).symm
  rw [h1, D.γ_one, D.t_tinv, one_mul] at hγ
  exact D.ψ_inj u hu hγ.symm

theorem eq_one_of_t_eq_zero_of_noncomm (hU₁ : U₁ ≤ Q) (hU₂ : U₂ ≤ Q) (D₁ : MulData V U₁ Q K)
    (D₂ : MulData V U₂ Q K) (hnc : ∃ a ∈ U₁, ∃ b ∈ U₂, a * b ≠ b * a) {u : G} (hu : u ∈ U₂)
    (h : D₁.t u = 0) : u = 1 := by
  by_contra hne
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  apply hab
  have hcent := (D₁.t_ker u (hU₂ hu)).mp h
  have hψ : D₂.ψ u ≠ 0 := fun h0 => hne (D₂.ψ_inj u hu h0)
  have h2 : ∀ a' ∈ U₁, D₂.t a' = 0 := by
    intro a' ha'
    have hc := (D₂.comm a' (hU₁ ha') u hu).2
    have h3 : ⁅a', u⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hcent a' ha')
    rw [h3, D₂.γ_one] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_right hψ
  have h4 := (D₂.t_ker a (hU₁ ha)).mp (h2 a ha)
  exact (Subgroup.mem_centralizer_iff.mp h4 b hb).symm

theorem exists_sections [Finite K] (hU₁ : U₁ ≤ Q) (hU₂ : U₂ ≤ Q) (D₁ : MulData V U₁ Q K)
    (D₂ : MulData V U₂ Q K) (hnc : ∃ a ∈ U₁, ∃ b ∈ U₂, a * b ≠ b * a) :
    ∃ S₂ : K → G, (∀ x, S₂ x ∈ U₂) ∧ (∀ x, D₁.t (S₂ x) = x) ∧
      ∀ x x', S₂ (x + x') = S₂ x * S₂ x' := by
  have hinj : ∀ a ∈ U₂, ∀ b ∈ U₂, D₁.t a = D₁.t b → a = b := fun a ha b hb h =>
    eq_of_map_eq_of_additive (S := U₂) (fun a ha b hb => D₁.t_add a (hU₂ ha) b (hU₂ hb))
      (fun a ha h0 => eq_one_of_t_eq_zero_of_noncomm hU₁ hU₂ D₁ D₂ hnc ha h0) ha hb h
  have hsurj : ∀ x : K, ∃ u ∈ U₂, D₁.t u = x := by
    have hcard : Nat.card K ≤ Nat.card U₂ := (card_U D₂).symm.le
    have hinj' : Function.Injective (fun u : U₂ => D₁.t u) := fun a b h =>
      Subtype.ext (hinj a a.2 b b.2 h)
    have hbij := hinj'.bijective_of_nat_card_le hcard
    intro x
    obtain ⟨u, hu⟩ := hbij.2 x
    exact ⟨u, u.2, hu⟩
  choose S₂ hS₂ hS₂t using hsurj
  refine ⟨S₂, hS₂, hS₂t, fun x x' => hinj _ (hS₂ _) _ (U₂.mul_mem (hS₂ x) (hS₂ x')) ?_⟩
  rw [hS₂t, D₁.t_add _ (hU₂ (hS₂ x)) _ (hU₂ (hS₂ x')), hS₂t, hS₂t]

theorem compat_of_noncomm [Finite K] (hU₁ : U₁ ≤ Q) (hU₂ : U₂ ≤ Q) (D₁ : MulData V U₁ Q K)
    (D₂ : MulData V U₂ Q K) (hnc : ∃ a ∈ U₁, ∃ b ∈ U₂, a * b ≠ b * a) :
    ∃ (c : K) (σ : K ≃+* K), c ≠ 0 ∧ ∀ v ∈ V, D₂.γ v = c * σ (D₁.γ v) := by
  obtain ⟨S₂, hS₂mem, hS₂t, hS₂add⟩ := exists_sections hU₁ hU₂ D₁ D₂ hnc
  have hnc' : ∃ b ∈ U₂, ∃ a ∈ U₁, b * a ≠ a * b := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact ⟨b, hb, a, ha, fun h => hab h.symm⟩
  have hw : ∀ x y, ⁅S₂ x, D₁.uinv y⁆ = D₁.vinv (x * y) := by
    intro x y
    obtain ⟨hV, hγ⟩ := D₁.comm (S₂ x) (hU₂ (hS₂mem x)) (D₁.uinv y) (D₁.uinv_mem y)
    rw [hS₂t, D₁.ψ_uinv] at hγ
    exact D₁.eq_of_γ_eq hV (D₁.vinv_mem _) (by rw [hγ, D₁.γ_vinv])
  have hcomm₂ : ∀ x y, D₂.γ (D₁.vinv (x * y)) = - (D₂.t (D₁.uinv y) * D₂.ψ (S₂ x)) := by
    intro x y
    obtain ⟨hV, hγ⟩ := D₂.comm (D₁.uinv y) (hU₁ (D₁.uinv_mem y)) (S₂ x) (hS₂mem x)
    rw [← hw x y, ← commutatorElement_inv, D₂.γ_inv hV, hγ]
  let F : K →+ K := AddMonoidHom.mk' (fun y => D₂.t (D₁.uinv y)) (fun y y' => by
    rw [D₁.uinv_add, D₂.t_add _ (hU₁ (D₁.uinv_mem y)) _ (hU₁ (D₁.uinv_mem y'))])
  let G' : K →+ K := AddMonoidHom.mk' (fun x => D₂.ψ (S₂ x)) (fun x x' => by
    rw [hS₂add, D₂.ψ_add _ (hS₂mem x) _ (hS₂mem x')])
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : D₁.uinv y = 1 := eq_one_of_t_eq_zero_of_noncomm hU₂ hU₁ D₂ D₁ hnc' (D₁.uinv_mem y) hy
    rw [← D₁.ψ_uinv y, h1, D₁.ψ_one]
  have hGinj : Function.Injective G' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : S₂ x = 1 := D₂.ψ_inj _ (hS₂mem x) hx
    rw [← hS₂t x, h1, D₁.t_one]
  have hθ := thetaHom_bijective D₁ D₂
  have heq : ∀ x y, thetaHom D₁ D₂ (x * y) = (-G') x * F y := by
    intro x y
    rw [thetaHom_apply, hcomm₂]
    show _ = - D₂.ψ (S₂ x) * D₂.t (D₁.uinv y)
    ring
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_mul_eq (thetaHom D₁ D₂) (-G') F hθ heq
  refine ⟨thetaHom D₁ D₂ 1, σ, ?_, fun v hv => ?_⟩
  · intro h0
    exact one_ne_zero (hθ.1 (h0.trans (map_zero _).symm))
  · rw [← thetaHom_γ D₁ D₂ hv, hσ]

end MulData

private theorem ut3_mul_aux {Γ : Type} [Group Γ] (Z Z' W a a' b b' : Γ)
    (haZ' : a * Z' = Z' * a) (hbZ' : b * Z' = Z' * b) (haW : a * W = W * a)
    (hba : b * a' = W * (a' * b)) :
    Z * (a * b) * (Z' * (a' * b')) = Z * Z' * W * (a * a' * (b * b')) := by
  calc Z * (a * b) * (Z' * (a' * b')) = Z * (a * (b * Z') * (a' * b')) := by
        simp only [mul_assoc]
    _ = Z * (a * (Z' * b) * (a' * b')) := by rw [hbZ']
    _ = Z * ((a * Z') * (b * (a' * b'))) := by simp only [mul_assoc]
    _ = Z * ((Z' * a) * (b * (a' * b'))) := by rw [haZ']
    _ = Z * Z' * (a * ((b * a') * b')) := by simp only [mul_assoc]
    _ = Z * Z' * (a * ((W * (a' * b)) * b')) := by rw [hba]
    _ = Z * Z' * ((a * W) * (a' * (b * b'))) := by simp only [mul_assoc]
    _ = Z * Z' * ((W * a) * (a' * (b * b'))) := by rw [haW]
    _ = Z * Z' * W * (a * a' * (b * b')) := by simp only [mul_assoc]

namespace MulData

variable {V U₁ U₂ Q : Subgroup G} {K : Type} [Field K]

theorem unitri_of_noncomm [Finite K] (hVc : ∀ v ∈ V, ∀ y ∈ Q, v * y = y * v) (hU₁ : U₁ ≤ Q)
    (hU₂ : U₂ ≤ Q) (D₁ : MulData V U₁ Q K) (D₂ : MulData V U₂ Q K)
    (hnc : ∃ a ∈ U₁, ∃ b ∈ U₂, a * b ≠ b * a) : Nonempty (↥(U₁ ⊔ U₂) ≃* UT3 K) := by
  obtain ⟨S₂, hS₂mem, hS₂t, hS₂add⟩ := exists_sections hU₁ hU₂ D₁ D₂ hnc
  have hVQ : V ≤ Q := D₁.V_le_Q hU₁
  have hw : ∀ x y, ⁅S₂ x, D₁.uinv y⁆ = D₁.vinv (x * y) := by
    intro x y
    obtain ⟨hV, hγ⟩ := D₁.comm (S₂ x) (hU₂ (hS₂mem x)) (D₁.uinv y) (D₁.uinv_mem y)
    rw [hS₂t, D₁.ψ_uinv] at hγ
    exact D₁.eq_of_γ_eq hV (D₁.vinv_mem _) (by rw [hγ, D₁.γ_vinv])
  have hrel : ∀ x y, S₂ x * D₁.uinv y = D₁.vinv (x * y) * (D₁.uinv y * S₂ x) := by
    intro x y
    rw [← hw x y, commutatorElement_def]
    group
  have hS₂zero : S₂ 0 = 1 := by
    have h := hS₂add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  let Ψ : UT3 K →* G :=
    { toFun := fun u => D₁.vinv u.c * (D₁.uinv u.b * S₂ u.a)
      map_one' := by
        rw [UT3.one_def]
        simp only [D₁.vinv_zero, D₁.uinv_zero, hS₂zero, one_mul, mul_one]
      map_mul' := fun u u' => by
        rw [UT3.mul_def]
        simp only
        rw [D₁.vinv_add (u.c + u'.c) (u.a * u'.b), D₁.vinv_add u.c u'.c, D₁.uinv_add, hS₂add]
        exact (ut3_mul_aux (D₁.vinv u.c) (D₁.vinv u'.c) (D₁.vinv (u.a * u'.b)) (D₁.uinv u.b)
          (D₁.uinv u'.b) (S₂ u.a) (S₂ u'.a)
          (hVc _ (D₁.vinv_mem _) _ (hU₁ (D₁.uinv_mem _))).symm
          (hVc _ (D₁.vinv_mem _) _ (hU₂ (hS₂mem _))).symm
          (hVc _ (D₁.vinv_mem _) _ (hU₁ (D₁.uinv_mem _))).symm (hrel u.a u'.b)).symm }
  have hΨ : ∀ u, Ψ u = D₁.vinv u.c * (D₁.uinv u.b * S₂ u.a) := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    rw [hΨ] at hu
    have hZ : D₁.vinv u.c ∈ Q := hVQ (D₁.vinv_mem _)
    have hA : D₁.uinv u.b ∈ Q := hU₁ (D₁.uinv_mem _)
    have hB : S₂ u.a ∈ Q := hU₂ (hS₂mem _)
    have h1 : D₁.t (D₁.vinv u.c * (D₁.uinv u.b * S₂ u.a)) = 0 := by rw [hu, D₁.t_one]
    rw [D₁.t_add _ hZ _ (Q.mul_mem hA hB), D₁.t_add _ hA _ hB, hS₂t] at h1
    have hZ0 : D₁.t (D₁.vinv u.c) = 0 := (D₁.t_ker _ hZ).mpr
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hVc _ (D₁.vinv_mem _) y (hU₁ hy)).symm)
    have hA0 : D₁.t (D₁.uinv u.b) = 0 := (D₁.t_ker _ hA).mpr
      (Subgroup.mem_centralizer_iff.mpr fun y hy => D₁.mul_comm_U hy (D₁.uinv_mem _))
    rw [hZ0, hA0, zero_add, zero_add] at h1
    rw [h1, hS₂zero, mul_one] at hu
    have hAV : D₁.uinv u.b ∈ V := by
      have : D₁.uinv u.b = (D₁.vinv u.c)⁻¹ := eq_inv_of_mul_eq_one_right hu
      rw [this]
      exact V.inv_mem (D₁.vinv_mem _)
    have hA1 : D₁.uinv u.b = 1 := D₁.eq_one_of_mem_V hVc (D₁.uinv_mem _) hAV
    have hb0 : u.b = 0 := by rw [← D₁.ψ_uinv u.b, hA1, D₁.ψ_one]
    rw [hA1, mul_one] at hu
    have hc0 : u.c = 0 := by rw [← D₁.γ_vinv u.c, hu, D₁.γ_one]
    rw [UT3.one_def]
    ext
    · exact h1
    · exact hb0
    · exact hc0
  have hVU : V ≤ U₁ ⊔ U₂ := by
    intro v hv
    have h1 : ⁅S₂ (D₁.γ v), D₁.uinv 1⁆ = v := by
      rw [hw, mul_one, D₁.vinv_γ hv]
    rw [← h1, commutatorElement_def]
    have ha : S₂ (D₁.γ v) ∈ U₁ ⊔ U₂ := Subgroup.mem_sup_right (hS₂mem _)
    have hb : D₁.uinv 1 ∈ U₁ ⊔ U₂ := Subgroup.mem_sup_left (D₁.uinv_mem _)
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hrange : Ψ.range = U₁ ⊔ U₂ := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      rw [hΨ]
      exact mul_mem (hVU (D₁.vinv_mem _)) (mul_mem (Subgroup.mem_sup_left (D₁.uinv_mem _))
        (Subgroup.mem_sup_right (hS₂mem _)))
    · refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · refine ⟨⟨0, D₁.ψ u, 0⟩, ?_⟩
        rw [hΨ]
        simp only [D₁.vinv_zero, hS₂zero, one_mul, mul_one, D₁.uinv_ψ hu]
      · refine ⟨⟨D₁.t u, 0, 0⟩, ?_⟩
        rw [hΨ]
        have h2 : S₂ (D₁.t u) = u := by
          refine eq_of_map_eq_of_additive (S := U₂)
            (fun a ha b hb => D₁.t_add a (hU₂ ha) b (hU₂ hb))
            (fun a ha h0 => eq_one_of_t_eq_zero_of_noncomm hU₁ hU₂ D₁ D₂ hnc ha h0)
            (hS₂mem _) hu ?_
          rw [hS₂t]
        simp only [D₁.vinv_zero, D₁.uinv_zero, one_mul, h2, one_mul]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end MulData

theorem card_ut3 (R : Type*) [CommRing R] : Nat.card (UT3 R) = Nat.card R ^ 3 := by
  let e : UT3 R ≃ R × R × R :=
    { toFun := fun u => (u.a, u.b, u.c)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun u => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

end CFSG.RankThree.GF2n.Tim79
