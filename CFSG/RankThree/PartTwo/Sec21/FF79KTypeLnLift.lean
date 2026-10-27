module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnAut
import CFSG.GH74.GLS.LU.Local.Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Subgroup

structure LiftData {G : Type} [Group G] (J P : Subgroup G) (S : Type) [Group S]
    (R : Subgroup S) where
  e : (↥J ⧸ Subgroup.center ↥J) ≃* S
  ϕ : ↥J →* S
  ϕ_eq : ∀ j : ↥J, ϕ j = e (QuotientGroup.mk j)
  perf : ⁅J, J⁆ = J
  surj : Function.Surjective ϕ
  ker_eq : ϕ.ker = Subgroup.center ↥J
  cop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J))
  pgrp : IsPGroup 3 P
  le : P ≤ J
  img : ∀ x : S, x ∈ R ↔ ∃ p : ↥J, (p : G) ∈ P ∧ ϕ p = x

variable {G : Type} [Group G] {J P : Subgroup G} {S : Type} [Group S] {R : Subgroup S}

theorem exists_conj_of_card {S : Type} [Group S] [Finite S] {R R' : Subgroup S}
    (h : Nat.card R = 3 ^ (Nat.card S).factorization 3)
    (h' : Nat.card R' = 3 ^ (Nat.card S).factorization 3) :
    ∃ s : S, ∀ x : S, x ∈ R' ↔ s⁻¹ * x * s ∈ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S (Sylow.ofCard R h) (Sylow.ofCard R' h')
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • Sylow.ofCard R h : Sylow 3 S) : Subgroup S) = R' := by
    rw [hg]; rfl
  rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

@[expose] def CentAlphaS (S : Type) [Group S] (R : Subgroup S) (n : ℕ) : Prop :=
  ∀ a₀ ∈ R, a₀ ≠ 1 → ∀ Y₀ : Subgroup (MulAut S), (∀ σ ∈ Y₀, σ a₀ = a₀) →
    (∀ σ ∈ Y₀, Nat.Coprime 3 (orderOf σ)) →
    (∀ c : S, c * a₀ = a₀ * c → ∀ σ ∈ Y₀, MulAut.conj c * σ * (MulAut.conj c)⁻¹ ∈ Y₀) →
    (∀ σ ∈ Y₀, ∀ x ∈ R, σ x = x) ∧ (n = 5 → ∀ σ ∈ Y₀, σ = 1)

theorem three_pow_of_coe {u : ↥J} (h : ∃ k : ℕ, (u : G) ^ (3 ^ k) = 1) :
    ∃ k : ℕ, u ^ (3 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem three_pow_conj {p : G} (c : G) (h : ∃ k : ℕ, p ^ (3 ^ k) = 1) :
    ∃ k : ℕ, (c * p * c⁻¹) ^ (3 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [conj_pow, hk]; group⟩

theorem eq_of_inv_mul_mem_center {J : Type} [Group J]
    (hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center J))) {u v : J}
    (hz : v⁻¹ * u ∈ Subgroup.center J) (hu : ∃ a : ℕ, u ^ (3 ^ a) = 1)
    (hv : ∃ b : ℕ, v ^ (3 ^ b) = 1) : u = v := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have hcomm : Commute v u := by
    have hz' := Subgroup.mem_center_iff.mp hz
    have : Commute v (v⁻¹ * u) := hz' v
    have h2 : u = v * (v⁻¹ * u) := by group
    rw [h2]
    exact (Commute.refl v).mul_right this
  have hm : (v⁻¹ * u) ^ (3 ^ (a + b)) = 1 := by
    rw [(hcomm.inv_left).mul_pow]
    have h1 : u ^ (3 ^ (a + b)) = 1 := by
      rw [pow_add, pow_mul, ha, one_pow]
    have h2 : v ^ (3 ^ (a + b)) = 1 := by
      rw [pow_add, mul_comm, pow_mul, hb, one_pow]
    rw [inv_pow, h1, h2, inv_one, one_mul]
  have hord : orderOf (v⁻¹ * u) ∣ 3 ^ (a + b) := orderOf_dvd_of_pow_eq_one hm
  have hord2 : orderOf (v⁻¹ * u) ∣ Nat.card ↥(Subgroup.center J) := by
    have := orderOf_dvd_natCard (⟨v⁻¹ * u, hz⟩ : ↥(Subgroup.center J))
    simpa using this
  have hcop : Nat.Coprime (3 ^ (a + b)) (Nat.card ↥(Subgroup.center J)) :=
    Nat.Coprime.pow_left _ hcop
  have h1 : orderOf (v⁻¹ * u) = 1 := by
    have := Nat.dvd_gcd hord hord2
    rwa [hcop, Nat.dvd_one] at this
  have : v⁻¹ * u = 1 := orderOf_eq_one_iff.mp h1
  exact (inv_mul_eq_one.mp this).symm



namespace LiftData

variable (L : LiftData J P S R)

include L

theorem three_pow_of_mem {p : ↥J} (hp : (p : G) ∈ P) : ∃ k : ℕ, p ^ (3 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := L.pgrp (⟨p, hp⟩ : P)
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun x : P => (x : G)) hk
  simpa using this

theorem key3 {u v : ↥J} (h : L.ϕ u = L.ϕ v) (hu : ∃ a : ℕ, u ^ (3 ^ a) = 1)
    (hv : ∃ b : ℕ, v ^ (3 ^ b) = 1) : u = v :=
  eq_of_inv_mul_mem_center L.cop (by
    rw [← L.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]) hu hv

theorem img_of_mem {x : G} (hx : x ∈ P) : L.ϕ ⟨x, L.le hx⟩ ∈ R :=
  (L.img _).mpr ⟨⟨x, L.le hx⟩, hx, rfl⟩

theorem inj_on_P {x y : G} (hx : x ∈ P) (hy : y ∈ P) (h : L.ϕ ⟨x, L.le hx⟩ = L.ϕ ⟨y, L.le hy⟩) :
    x = y := by
  have := L.key3 h (L.three_pow_of_mem (p := ⟨x, L.le hx⟩) hx)
    (L.three_pow_of_mem (p := ⟨y, L.le hy⟩) hy)
  exact congrArg Subtype.val this

theorem conj_mem_of_image {j : ↥J} (hj : L.ϕ j ∈ Subgroup.normalizer (R : Set S)) {p : G}
    (hp : p ∈ P) : (j : G) * p * (j : G)⁻¹ ∈ P := by
  have hJ : (j : G) * p * (j : G)⁻¹ ∈ J := by
    exact J.mul_mem (J.mul_mem j.2 (L.le hp)) (J.inv_mem j.2)
  have hu : L.ϕ ⟨(j : G) * p * (j : G)⁻¹, hJ⟩ ∈ R := by
    have : L.ϕ ⟨(j : G) * p * (j : G)⁻¹, hJ⟩ = L.ϕ j * L.ϕ ⟨p, L.le hp⟩ * (L.ϕ j)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp hj _).mp (L.img_of_mem hp)
  obtain ⟨q, hqP, hq⟩ := (L.img _).mp hu
  have hq' : (q : G) = (j : G) * p * (j : G)⁻¹ := by
    refine congrArg Subtype.val (L.key3 hq ?_ ?_)
    · exact L.three_pow_of_mem (p := q) hqP
    · obtain ⟨k, hk⟩ := L.three_pow_of_mem (p := ⟨p, L.le hp⟩) hp
      refine ⟨k, ?_⟩
      have : (⟨(j : G) * p * (j : G)⁻¹, hJ⟩ : ↥J) = j * ⟨p, L.le hp⟩ * j⁻¹ := rfl
      rw [this]
      have h2 : (j * (⟨p, L.le hp⟩ : ↥J) * j⁻¹) ^ (3 ^ k) =
          j * (⟨p, L.le hp⟩ : ↥J) ^ (3 ^ k) * j⁻¹ := by
        simpa [MulAut.conj_apply] using (map_pow (MulAut.conj j) (⟨p, L.le hp⟩ : ↥J) (3 ^ k))
      rw [h2, hk]; group
  rw [← hq']
  exact hqP

variable [Finite G]

theorem mem_nor_of_image {j : ↥J} (hj : L.ϕ j ∈ Subgroup.normalizer (R : Set S)) :
    (j : G) ∈ Subgroup.normalizer (P : Set G) :=
  mem_normalizer_of_forall_conj_mem fun p hp => L.conj_mem_of_image hj hp

theorem image_mem_nor {j : ↥J} (hj : (j : G) ∈ Subgroup.normalizer (P : Set G)) :
    L.ϕ j ∈ Subgroup.normalizer (R : Set S) := by
  haveI : Finite S := Finite.of_surjective L.ϕ L.surj
  refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
  obtain ⟨p, hpP, rfl⟩ := (L.img x).mp hx
  have hpP' : (p : G) ∈ P := hpP
  have hc : (j : G) * p * (j : G)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hj _).mp hpP'
  rw [L.img]
  refine ⟨⟨(j : G) * p * (j : G)⁻¹, J.mul_mem (J.mul_mem j.2 p.2) (J.inv_mem j.2)⟩, hc, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl


theorem tau_lift (M : TModel S R) :
    ∃ τ ∈ J, τ ∈ Subgroup.normalizer (P : Set G) ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹ := by
  obtain ⟨τs, hτN, hτ⟩ := M.tau
  obtain ⟨j, rfl⟩ := L.surj τs
  have hjN := L.mem_nor_of_image hτN
  refine ⟨j, j.2, hjN, fun x hx => ?_⟩
  have hc : (j : G) * x * (j : G)⁻¹ ∈ P := L.conj_mem_of_image hτN hx
  have hxi : x⁻¹ ∈ P := P.inv_mem hx
  refine L.inj_on_P hc hxi ?_
  have h1 : L.ϕ ⟨(j : G) * x * (j : G)⁻¹, L.le hc⟩ = L.ϕ j * L.ϕ ⟨x, L.le hx⟩ * (L.ϕ j)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  have h2 : L.ϕ ⟨x⁻¹, L.le hxi⟩ = (L.ϕ ⟨x, L.le hx⟩)⁻¹ := by
    rw [← map_inv]; rfl
  rw [h1, h2]
  exact hτ _ (L.img_of_mem hx)

theorem noncomm_lift (M : TModel S R) :
    ∃ j₁ ∈ J, ∃ j₂ ∈ J, j₁ ∈ Subgroup.normalizer (P : Set G) ∧
      j₂ ∈ Subgroup.normalizer (P : Set G) ∧ ∃ x ∈ P,
        j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹ ≠ j₂ * (j₁ * x * j₁⁻¹) * j₂⁻¹ := by
  obtain ⟨xs, hxs, s₁, hs₁, s₂, hs₂, hne⟩ := M.noncomm
  obtain ⟨j₁, rfl⟩ := L.surj s₁
  obtain ⟨j₂, rfl⟩ := L.surj s₂
  obtain ⟨x, hxP, rfl⟩ := (L.img xs).mp hxs
  refine ⟨j₁, j₁.2, j₂, j₂.2, L.mem_nor_of_image hs₁, L.mem_nor_of_image hs₂, x, hxP, ?_⟩
  intro h
  apply hne
  have := congrArg (fun g : G => g) h
  have hJ : ∀ g₁ g₂ g₃ : ↥J, (g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ : ↥J) =
      g₂ * (g₁ * x * g₁⁻¹) * g₂⁻¹ → L.ϕ (g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹) =
        L.ϕ (g₂ * (g₁ * x * g₁⁻¹) * g₂⁻¹) := fun _ _ _ h => congrArg L.ϕ h
  have hEq : (j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹ : ↥J) = j₂ * (j₁ * x * j₁⁻¹) * j₂⁻¹ :=
    Subtype.ext h
  have := hJ j₁ j₂ j₁ hEq
  simpa [map_mul, map_inv] using this


theorem count_lift (M : TModel S R) :
    {f : P → G | ∃ j ∈ J, j ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ x : P, f x = j * x * j⁻¹}.ncard = 8 := by
  classical
  let Qf : P → R := fun x => ⟨L.ϕ ⟨x, L.le x.2⟩, L.img_of_mem x.2⟩
  have hQ : Function.Bijective Qf := by
    constructor
    · intro x y hxy
      exact Subtype.ext (L.inj_on_P x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨p, hpP, hp⟩ := (L.img y).mp y.2
      exact ⟨⟨p, hpP⟩, Subtype.ext hp⟩
  let Q : P ≃ R := Equiv.ofBijective Qf hQ
  let ϕ' : G → S := fun g => if h : g ∈ J then L.ϕ ⟨g, h⟩ else 1
  have hϕ' : ∀ (g : ↥J), ϕ' g = L.ϕ g := fun g => by simp [ϕ', g.2]
  let Ψ : (P → G) → (R → S) := fun f y => ϕ' (f (Q.symm y))
  set F := {f : P → G | ∃ j ∈ J, j ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ x : P, f x = j * x * j⁻¹} with hF
  have hΨ : ∀ (j : ↥J) (f : P → G), (∀ x : P, f x = (j : G) * x * (j : G)⁻¹) →
      ∀ y : R, Ψ f y = L.ϕ j * y * (L.ϕ j)⁻¹ := by
    intro j f hf y
    have hx : Q (Q.symm y) = y := Q.apply_symm_apply y
    have hy : (y : S) = L.ϕ ⟨(Q.symm y : G), L.le (Q.symm y).2⟩ := by
      exact (congrArg Subtype.val hx).symm
    show ϕ' (f (Q.symm y)) = _
    rw [hf]
    have hJ : (j : G) * (Q.symm y : G) * (j : G)⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem j.2 (L.le (Q.symm y).2)) (J.inv_mem j.2)
    have : ϕ' ((j : G) * (Q.symm y : G) * (j : G)⁻¹) =
        L.ϕ ⟨(j : G) * (Q.symm y : G) * (j : G)⁻¹, hJ⟩ := by
      simp [ϕ', hJ]
    rw [this, hy]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have himg : Ψ '' F = {f : R → S | ∃ s ∈ Subgroup.normalizer (R : Set S),
      ∀ x : R, f x = s * x * s⁻¹} := by
    ext f'
    constructor
    · rintro ⟨f, ⟨j, hjJ, hjN, hf⟩, rfl⟩
      refine ⟨L.ϕ ⟨j, hjJ⟩, L.image_mem_nor (j := ⟨j, hjJ⟩) hjN, fun y => ?_⟩
      exact hΨ ⟨j, hjJ⟩ f hf y
    · rintro ⟨s, hs, hf'⟩
      obtain ⟨j, rfl⟩ := L.surj s
      refine ⟨fun x => (j : G) * x * (j : G)⁻¹, ⟨j, j.2, L.mem_nor_of_image hs, fun x => rfl⟩, ?_⟩
      funext y
      rw [hf' y]
      exact hΨ j _ (fun x => rfl) y
  have hinj : Set.InjOn Ψ F := by
    rintro f ⟨j, hjJ, hjN, hf⟩ f' ⟨j', hjJ', hjN', hf'⟩ hΨf
    funext x
    have hxP : (f x) ∈ P := by
      rw [hf]; exact (Subgroup.mem_normalizer_iff.mp hjN _).mp x.2
    have hxP' : (f' x) ∈ P := by
      rw [hf']; exact (Subgroup.mem_normalizer_iff.mp hjN' _).mp x.2
    refine L.inj_on_P hxP hxP' ?_
    have h1 := congrFun hΨf (Q x)
    simp only [Ψ, Equiv.symm_apply_apply] at h1
    rw [← hϕ' ⟨f x, L.le hxP⟩, ← hϕ' ⟨f' x, L.le hxP'⟩]
    simpa [ϕ', L.le hxP, L.le hxP'] using h1
  rw [← hinj.ncard_image, himg]
  exact M.count


private def conjSub (J : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    J ≃* J where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) (x : G)).mp x.2⟩
  left_inv x := Subtype.ext <| by
    show g⁻¹ * (g * (x : G) * g⁻¹) * g = x
    group
  right_inv x := Subtype.ext <| by
    show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x
    group
  map_mul' x y := Subtype.ext <| by
    show g * ((x : G) * (y : G)) * g⁻¹ = (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
    group

private def conjQuot (J : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    MulAut (↥J ⧸ Subgroup.center ↥J) :=
  QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J) (conjSub J g hg)
    (Subgroup.map_center_eq (conjSub J g hg))

@[expose] def Acts (g : G) (α : MulAut S) : Prop :=
  ∀ j : ↥J, ∃ h : g * (j : G) * g⁻¹ ∈ J, α (L.ϕ j) = L.ϕ ⟨g * (j : G) * g⁻¹, h⟩

theorem acts_exists {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    ∃ α : MulAut S, L.Acts g α := by
  refine ⟨MulAut.congr L.e (conjQuot J g hg),
    fun j => ⟨(Subgroup.mem_normalizer_iff.mp hg _).mp j.2, ?_⟩⟩
  rw [L.ϕ_eq, L.ϕ_eq, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem acts_unique {g : G} {α β : MulAut S} (hα : L.Acts g α) (hβ : L.Acts g β) : α = β := by
  ext s
  obtain ⟨j, rfl⟩ := L.surj s
  obtain ⟨h1, e1⟩ := hα j
  obtain ⟨h2, e2⟩ := hβ j
  rw [e1, e2]

theorem acts_one : L.Acts 1 (1 : MulAut S) := fun j => ⟨by simp, by simp⟩

theorem acts_mul {g h : G} {α β : MulAut S} (hα : L.Acts g α) (hβ : L.Acts h β) :
    L.Acts (g * h) (α * β) := by
  intro j
  obtain ⟨h2, e2⟩ := hβ j
  obtain ⟨h1, e1⟩ := hα ⟨h * (j : G) * h⁻¹, h2⟩
  have hmem : g * h * (j : G) * (g * h)⁻¹ = g * (h * (j : G) * h⁻¹) * g⁻¹ := by group
  refine ⟨by rw [hmem]; exact h1, ?_⟩
  rw [MulAut.mul_apply, e2, e1]
  congr 1
  exact Subtype.ext hmem.symm

theorem acts_conj (j₀ : ↥J) : L.Acts (j₀ : G) (MulAut.conj (L.ϕ j₀)) := by
  intro j
  refine ⟨J.mul_mem (J.mul_mem j₀.2 j.2) (J.inv_mem j₀.2), ?_⟩
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem acts_inv {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) {α : MulAut S}
    (h : L.Acts g α) : L.Acts g⁻¹ α⁻¹ := by
  obtain ⟨β, hβ⟩ := L.acts_exists (inv_mem hg)
  have h1 := L.acts_mul hβ h
  rw [inv_mul_cancel] at h1
  have := L.acts_unique h1 L.acts_one
  have hβ' : β = α⁻¹ := by
    have := congrArg (fun x => x * α⁻¹) this
    simpa using this
  rwa [← hβ']

theorem centralizes_of_acts_one {g : G} (h : L.Acts g (1 : MulAut S)) :
    g ∈ Subgroup.centralizer (J : Set G) := by
  have hcond : ∀ j ∈ J, ∃ c ∈ J, (∀ g' ∈ J, c * g' = g' * c) ∧ g * j * g⁻¹ = c * j := by
    intro j hj
    obtain ⟨hJ, e⟩ := h ⟨j, hj⟩
    simp only [MulAut.one_apply] at e
    have hz : (⟨j, hj⟩ : ↥J)⁻¹ * ⟨g * j * g⁻¹, hJ⟩ ∈ Subgroup.center ↥J := by
      rw [← L.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, ← e, inv_mul_cancel]
    have hzc := Subgroup.mem_center_iff.mp hz
    refine ⟨((⟨j, hj⟩ : ↥J)⁻¹ * ⟨g * j * g⁻¹, hJ⟩ : ↥J), ?_, ?_, ?_⟩
    · exact ((⟨j, hj⟩ : ↥J)⁻¹ * ⟨g * j * g⁻¹, hJ⟩ : ↥J).2
    · intro g' hg'
      exact congrArg Subtype.val (hzc ⟨g', hg'⟩).symm
    · have h1 : ((⟨j, hj⟩ : ↥J)⁻¹ * ⟨g * j * g⁻¹, hJ⟩ : ↥J) * ⟨j, hj⟩ =
          ⟨g * j * g⁻¹, hJ⟩ := by
        rw [← hzc ⟨j, hj⟩]; group
      exact (congrArg Subtype.val h1).symm
  have := CFSG.GH74.GLS.LU.Local.centralizes_of_perfect_mod_center L.perf hcond
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (mul_inv_eq_iff_eq_mul.mp (this h hh)).symm


theorem ϕ_conj (j : ↥J) {x : G} (hx : x ∈ J) (hJ : (j : G) * x * (j : G)⁻¹ ∈ J) :
    L.ϕ ⟨(j : G) * x * (j : G)⁻¹, hJ⟩ = L.ϕ j * L.ϕ ⟨x, hx⟩ * (L.ϕ j)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem nor_act_lift (M : TModel S R) {g : G} (hgJ : g ∈ Subgroup.normalizer (J : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) :
    ∃ j : ↥J, (j : G) ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ x ∈ P, g * x * g⁻¹ = (j : G) * x * (j : G)⁻¹ := by
  obtain ⟨α, hα⟩ := L.acts_exists hgJ
  have hgc : ∀ p ∈ P, g * p * g⁻¹ ∈ P := fun p hp => (Subgroup.mem_normalizer_iff.mp hgP p).mp hp
  have hmem : ∀ x ∈ R, α x ∈ R := by
    intro x hx
    obtain ⟨p, hpP, rfl⟩ := (L.img x).mp hx
    obtain ⟨hJ, e⟩ := hα p
    rw [e]
    exact L.img_of_mem (hgc _ hpP)
  obtain ⟨k, hk, hkx⟩ := M.aute α hmem
  obtain ⟨j, rfl⟩ := L.surj k
  refine ⟨j, L.mem_nor_of_image hk, fun x hx => ?_⟩
  refine L.inj_on_P (hgc x hx) (L.conj_mem_of_image hk hx) ?_
  obtain ⟨hJ, e⟩ := hα ⟨x, L.le hx⟩
  have hJ' : (j : G) * x * (j : G)⁻¹ ∈ J := J.mul_mem (J.mul_mem j.2 (L.le hx)) (J.inv_mem j.2)
  rw [← e, hkx _ (L.img_of_mem hx)]
  exact (L.ϕ_conj j (L.le hx) hJ').symm


theorem exists_cent_lift [Finite G] (M : TModel S R)
    (hsyl : Nat.card R = 3 ^ (Nat.card S).factorization 3) {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    ∃ j : ↥J, (j : G)⁻¹ * g ∈ Subgroup.centralizer (P : Set G) := by
  haveI : Finite S := Finite.of_surjective L.ϕ L.surj
  obtain ⟨α, hα⟩ := L.acts_exists hg
  have hcard : Nat.card (R.map α.toMonoidHom) = 3 ^ (Nat.card S).factorization 3 := by
    rw [Subgroup.card_map_of_injective α.injective]; exact hsyl
  obtain ⟨s, hs⟩ := exists_conj_of_card hsyl hcard
  set β : MulAut S := MulAut.conj s⁻¹ * α with hβ
  have hβx : ∀ x, β x = s⁻¹ * α x * s := fun x => by
    simp [hβ, MulAut.conj_apply]
  have hmem : ∀ x ∈ R, β x ∈ R := by
    intro x hx
    rw [hβx]
    exact (hs (α x)).mp ⟨x, hx, rfl⟩
  obtain ⟨k, hk, hkx⟩ := M.aute β hmem
  obtain ⟨j₀, rfl⟩ := L.surj s
  obtain ⟨j₁, rfl⟩ := L.surj k
  refine ⟨j₀ * j₁, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hpJ : p ∈ J := L.le hp
  obtain ⟨hJ, e⟩ := hα ⟨p, hpJ⟩
  set jj : ↥J := j₀ * j₁ with hjj
  set u : ↥J := jj⁻¹ * ⟨g * p * g⁻¹, hJ⟩ * jj with hu
  have hcoe : (u : G) = ((jj : G)⁻¹ * g) * p * ((jj : G)⁻¹ * g)⁻¹ := by
    simp only [hu, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hϕu : L.ϕ u = L.ϕ ⟨p, hpJ⟩ := by
    have h1 : L.ϕ u = (L.ϕ jj)⁻¹ * α (L.ϕ ⟨p, hpJ⟩) * L.ϕ jj := by
      rw [hu, map_mul, map_mul, map_inv, e]
    have h2 : β (L.ϕ ⟨p, hpJ⟩) = L.ϕ j₁ * L.ϕ ⟨p, hpJ⟩ * (L.ϕ j₁)⁻¹ := hkx _ (L.img_of_mem hp)
    rw [hβx] at h2
    have h3 : α (L.ϕ ⟨p, hpJ⟩) = L.ϕ j₀ * (L.ϕ j₁ * L.ϕ ⟨p, hpJ⟩ * (L.ϕ j₁)⁻¹) * (L.ϕ j₀)⁻¹ := by
      rw [← h2]; group
    rw [h1, h3, hjj, map_mul]
    group
  have hu3 : ∃ k : ℕ, u ^ (3 ^ k) = 1 := by
    apply three_pow_of_coe
    rw [hcoe]
    exact three_pow_conj _ (by
      obtain ⟨k, hk⟩ := L.three_pow_of_mem (p := ⟨p, hpJ⟩) hp
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
  have hp3 : ∃ k : ℕ, (⟨p, hpJ⟩ : ↥J) ^ (3 ^ k) = 1 := L.three_pow_of_mem (p := ⟨p, hpJ⟩) hp
  have hup := L.key3 hϕu hu3 hp3
  have : ((jj : G)⁻¹ * g) * p * ((jj : G)⁻¹ * g)⁻¹ = p := by
    rw [← hcoe, hup]
  have h5 := congrArg (fun x => x * ((jj : G)⁻¹ * g)) this
  simp only [inv_mul_cancel_right] at h5
  exact h5.symm

theorem mem_sup_of_acts_conj {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) {r : S}
    (hr : r ∈ R) {α : MulAut S} (hα : L.Acts g α) (hαr : α = MulAut.conj r) :
    g ∈ P ⊔ Subgroup.centralizer (J : Set G) := by
  obtain ⟨p, hpP, hpr⟩ := (L.img r).mp hr
  have hpN : (p : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer p.2
  have h1 := L.acts_conj p
  have h2 := L.acts_inv hpN h1
  have h3 := L.acts_mul hα h2
  have h0 : α * (MulAut.conj (L.ϕ p))⁻¹ = 1 := by rw [hαr, hpr]; exact mul_inv_cancel _
  rw [h0] at h3
  have h5 := L.centralizes_of_acts_one h3
  have : g = (g * (p : G)⁻¹) * (p : G) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h5) (Subgroup.mem_sup_left hpP)

theorem fix_of_cent {g : G} (hg : g ∈ Subgroup.centralizer (P : Set G)) {α : MulAut S}
    (hα : L.Acts g α) : ∀ x ∈ R, α x = x := by
  intro x hx
  obtain ⟨p, hpP, rfl⟩ := (L.img x).mp hx
  obtain ⟨hJ, e⟩ := hα p
  rw [e]
  have : g * (p : G) * g⁻¹ = p := by
    have := Subgroup.mem_centralizer_iff.mp hg p hpP
    rw [mul_inv_eq_iff_eq_mul]; exact this.symm
  congr 1
  exact Subtype.ext this

theorem relIndex_le_two [Finite G] (M : TModel S R) :
    (P ⊔ Subgroup.centralizer (J : Set G)).relIndex
      (Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (P : Set G)) ≤ 2 := by
  obtain ⟨γ, hγ, hγ'⟩ := M.autf
  set H0 : Subgroup G := P ⊔ Subgroup.centralizer (J : Set G) with hH0
  set X : Subgroup G := Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (P : Set G)
    with hX
  have hγinv : ∀ x ∈ R, γ⁻¹ x = x := fun x hx => by
    rw [MulAut.inv_apply]
    exact (Equiv.symm_apply_eq _).mpr (hγ x hx).symm
  have hdich : ∀ g ∈ X, ∀ α : MulAut S, L.Acts g α →
      (∃ r ∈ R, α = MulAut.conj r) ∨ (∃ r ∈ R, α = MulAut.conj r * γ) := by
    intro g hg α hα
    obtain ⟨r, hr, h | h⟩ := hγ' α (L.fix_of_cent hg.2 hα)
    · exact Or.inl ⟨r, hr, h⟩
    · exact Or.inr ⟨r, hr, h⟩
  have hA : ∀ g ∈ X, ∀ α : MulAut S, L.Acts g α → (∃ r ∈ R, α = MulAut.conj r) → g ∈ H0 := by
    intro g hg α hα ⟨r, hr, h⟩
    exact L.mem_sup_of_acts_conj hg.1 hr hα h
  have hC : ∀ g ∈ X, ∀ g' ∈ X, ∀ α α' : MulAut S, L.Acts g α → L.Acts g' α' →
      (∃ r ∈ R, α = MulAut.conj r * γ) → (∃ r ∈ R, α' = MulAut.conj r * γ) →
      g'⁻¹ * g ∈ H0 := by
    intro g hg g' hg' α α' hα hα' ⟨r, hr, h⟩ ⟨r', hr', h'⟩
    have heq : α = α' * MulAut.conj (r'⁻¹ * r) := by
      ext t
      rw [h, h']
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      simp only [map_mul, map_inv, hγ r hr, hγ r' hr']
      group
    have h1 := L.acts_inv hg'.1 hα'
    have h2 := L.acts_mul h1 hα
    rw [heq, inv_mul_cancel_left] at h2
    refine hA _ (X.mul_mem (X.inv_mem hg') hg) _ h2
      ⟨r'⁻¹ * r, R.mul_mem (R.inv_mem hr') hr, rfl⟩
  have key : ∃ g₀ : ↥X, ∀ x : ↥X, (x : G) ∈ H0 ∨ ((g₀ : G)⁻¹ * x) ∈ H0 := by
    by_cases hex : ∃ g ∈ X, ∃ α : MulAut S, L.Acts g α ∧ ∃ r ∈ R, α = MulAut.conj r * γ
    · obtain ⟨g, hg, α', hα', hr'⟩ := hex
      refine ⟨⟨g, hg⟩, fun x => ?_⟩
      obtain ⟨α, hα⟩ := L.acts_exists x.2.1
      rcases hdich x x.2 α hα with h | h
      · exact Or.inl (hA x x.2 α hα h)
      · exact Or.inr (hC x x.2 g hg α α' hα hα' h hr')
    · refine ⟨1, fun x => Or.inl ?_⟩
      obtain ⟨α, hα⟩ := L.acts_exists x.2.1
      rcases hdich x x.2 α hα with h | h
      · exact hA x x.2 α hα h
      · exact absurd ⟨x, x.2, α, hα, h⟩ hex
  obtain ⟨g₀, hg₀⟩ := key
  unfold Subgroup.relIndex Subgroup.index
  have hsurj : Function.Surjective
      (fun b : Bool => if b then (QuotientGroup.mk g₀ : ↥X ⧸ H0.subgroupOf X)
        else QuotientGroup.mk 1) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rcases hg₀ x with h | h
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, if_false]
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using inv_mem h
      · refine ⟨true, ?_⟩
        simp only [if_true]
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using h
  have := Nat.card_le_card_of_surjective _ hsurj
  simpa using this

theorem cube_P (M : TModel S R) {x : G} (hx : x ∈ P) : x ^ 3 = 1 := by
  have h3 := L.three_pow_of_mem (p := ⟨x, L.le hx⟩) hx
  have h1 : L.ϕ ((⟨x, L.le hx⟩ : ↥J) ^ 3) = L.ϕ 1 := by
    rw [map_pow, map_one]; exact M.cube _ (L.img_of_mem hx)
  have := L.key3 h1 (by
    obtain ⟨k, hk⟩ := h3
    exact ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩) ⟨0, by simp⟩
  simpa using congrArg Subtype.val this

theorem comm_P (M : TModel S R) {x y : G} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  have h1 : L.ϕ (⟨x, L.le hx⟩ * ⟨y, L.le hy⟩) = L.ϕ (⟨y, L.le hy⟩ * ⟨x, L.le hx⟩) := by
    rw [map_mul, map_mul]; exact M.comm _ (L.img_of_mem hx) _ (L.img_of_mem hy)
  have := L.key3 h1 (L.three_pow_of_mem (p := ⟨x, L.le hx⟩ * ⟨y, L.le hy⟩) (P.mul_mem hx hy))
    (L.three_pow_of_mem (p := ⟨y, L.le hy⟩ * ⟨x, L.le hx⟩) (P.mul_mem hy hx))
  exact congrArg Subtype.val this

theorem acts_pow {g : G} {α : MulAut S} (h : L.Acts g α) (k : ℕ) : L.Acts (g ^ k) (α ^ k) := by
  induction k with
  | zero => simpa using L.acts_one
  | succ k ih => rw [pow_succ, pow_succ]; exact L.acts_mul ih h

theorem centAlpha_lift {n : ℕ} (M : TModel S R) (hS : CentAlphaS S R n) {α : G} (hα : α ∈ P)
    (hα3 : orderOf α = 3) {Y : Subgroup G} (hY1 : Y ≤ Subgroup.normalizer (J : Set G))
    (hY2 : Y ≤ Subgroup.centralizer ({α} : Set G)) (hcop : Nat.Coprime 3 (Nat.card Y))
    (hnorm : ∀ j ∈ J ⊓ Subgroup.centralizer ({α} : Set G), ∀ y ∈ Y, j * y * j⁻¹ ∈ Y) :
    Y ≤ Subgroup.centralizer (P : Set G) ∧ (n = 5 → Y ≤ Subgroup.centralizer (J : Set G)) := by
  set a : ↥J := ⟨α, L.le hα⟩ with ha
  have ha3 : ∃ k : ℕ, a ^ (3 ^ k) = 1 := L.three_pow_of_mem hα
  have hyα : ∀ y ∈ Y, y * α * y⁻¹ = α := fun y hy => by
    have := Subgroup.mem_centralizer_iff.mp (hY2 hy) α rfl
    rw [mul_inv_eq_iff_eq_mul]; exact this.symm
  let Yb : Subgroup (MulAut S) :=
    { carrier := {σ | ∃ y ∈ Y, L.Acts y σ}
      mul_mem' := by
        rintro _ _ ⟨y, hy, h1⟩ ⟨z, hz, h2⟩
        exact ⟨y * z, Y.mul_mem hy hz, L.acts_mul h1 h2⟩
      one_mem' := ⟨1, Y.one_mem, L.acts_one⟩
      inv_mem' := by
        rintro _ ⟨y, hy, h1⟩
        exact ⟨y⁻¹, Y.inv_mem hy, L.acts_inv (hY1 hy) h1⟩ }
  have hmemYb : ∀ σ, σ ∈ Yb ↔ ∃ y ∈ Y, L.Acts y σ := fun σ => Iff.rfl
  have hfix : ∀ σ ∈ Yb, σ (L.ϕ a) = L.ϕ a := by
    rintro σ ⟨y, hy, hσ⟩
    obtain ⟨hJ, e⟩ := hσ a
    rw [e]
    congr 1
    exact Subtype.ext (hyα y hy)
  have hord : ∀ σ ∈ Yb, Nat.Coprime 3 (orderOf σ) := by
    rintro σ ⟨y, hy, hσ⟩
    have h1 := L.acts_pow hσ (orderOf y)
    have hy1 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
    rw [hy1] at h1
    have h2 := L.acts_unique h1 L.acts_one
    have h3 : orderOf σ ∣ orderOf y := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf y ∣ Nat.card Y := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : Y)
      simpa using this
    exact Nat.Coprime.coprime_dvd_right (h3.trans h4) hcop
  have hnormb : ∀ c : S, c * L.ϕ a = L.ϕ a * c → ∀ σ ∈ Yb,
      MulAut.conj c * σ * (MulAut.conj c)⁻¹ ∈ Yb := by
    intro c hc σ ⟨y, hy, hσ⟩
    obtain ⟨j, rfl⟩ := L.surj c
    have hja : j * a * j⁻¹ = a := by
      refine L.key3 ?_ ?_ ha3
      · rw [map_mul, map_mul, map_inv, hc]; group
      · obtain ⟨k, hk⟩ := ha3
        exact ⟨k, by
          have : (j * a * j⁻¹) ^ (3 ^ k) = j * a ^ (3 ^ k) * j⁻¹ := by
            simpa [MulAut.conj_apply] using (map_pow (MulAut.conj j) a (3 ^ k))
          rw [this, hk]; group⟩
    have hjα : (j : G) ∈ J ⊓ Subgroup.centralizer ({α} : Set G) := by
      refine ⟨j.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := congrArg Subtype.val hja
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    refine ⟨(j : G) * y * (j : G)⁻¹, hnorm _ hjα y hy, ?_⟩
    have hjN : (j : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer j.2
    exact L.acts_mul (L.acts_mul (L.acts_conj j) hσ) (L.acts_inv hjN (L.acts_conj j))
  have hne : L.ϕ a ≠ 1 := by
    intro h1
    have hz : a ∈ Subgroup.center ↥J := by rw [← L.ker_eq]; exact h1
    have hd : orderOf a ∣ Nat.card ↥(Subgroup.center ↥J) := by
      have := orderOf_dvd_natCard (⟨a, hz⟩ : ↥(Subgroup.center ↥J))
      simpa using this
    obtain ⟨k, hk⟩ := ha3
    have hd2 : orderOf a ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf a = 1 := by
      have := Nat.dvd_gcd hd2 hd
      rwa [Nat.Coprime.pow_left _ L.cop, Nat.dvd_one] at this
    have h4 : a = 1 := orderOf_eq_one_iff.mp h3
    have h5 : α = 1 := congrArg Subtype.val h4
    rw [h5, orderOf_one] at hα3
    omega
  obtain ⟨hR, hT⟩ := hS (L.ϕ a) (L.img_of_mem hα) hne Yb hfix hord hnormb
  refine ⟨fun y hy => ?_, fun h5 y hy => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨σ, hσ⟩ := L.acts_exists (hY1 hy)
    have hσY : σ ∈ Yb := ⟨y, hy, hσ⟩
    obtain ⟨hJ, e⟩ := hσ ⟨p, L.le hp⟩
    have h1 := hR σ hσY _ (L.img_of_mem hp)
    rw [e] at h1
    have h2 : (⟨y * p * y⁻¹, hJ⟩ : ↥J) = ⟨p, L.le hp⟩ := by
      refine L.key3 h1 ?_ (L.three_pow_of_mem (p := ⟨p, L.le hp⟩) hp)
      obtain ⟨k, hk⟩ := L.three_pow_of_mem (p := ⟨p, L.le hp⟩) hp
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [conj_pow, this]; group
    have h3 := congrArg Subtype.val h2
    simp only at h3
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · obtain ⟨σ, hσ⟩ := L.acts_exists (hY1 hy)
    have hσ1 : σ = 1 := hT h5 σ ⟨y, hy, hσ⟩
    subst hσ1
    exact L.centralizes_of_acts_one hσ

end LiftData

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
