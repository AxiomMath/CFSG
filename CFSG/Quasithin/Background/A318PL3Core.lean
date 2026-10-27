module

public import CFSG.Quasithin.Background.A318PSkel

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace A318P

theorem commute_of_card_three {M : Type*} [Group M] {N : Subgroup M} [N.Normal]
    (hN : Nat.card N = 3) {m : M} {k : ℕ} (hm : m ^ 3 ^ k = 1) {n : M} (hn : n ∈ N) :
    m * n * m⁻¹ = n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have hcyc : IsCyclic N := isCyclic_of_prime_card hN
  have hcard : Nat.card (MulAut N) = 2 := by
    rw [IsCyclic.card_mulAut, hN]
    rfl
  have h1 : orderOf ((MulAut.conjNormal m : MulAut ↥N)) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hm, map_one]
  have h2 : orderOf ((MulAut.conjNormal m : MulAut ↥N)) ∣ 2 := hcard ▸ orderOf_dvd_natCard _
  have h3 : orderOf ((MulAut.conjNormal m : MulAut ↥N)) = 1 := by
    have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  have := congrArg (fun φ : MulAut N => (φ ⟨n, hn⟩ : M)) h3
  simpa using this


structure L3Frame (Y : Type) [Group Y] (C : Type) [Group C] where
  D : Subgroup (MulAut Y)
  fld : C →* MulAut Y
  inner_le : inner Y ≤ D
  fld_norm : ∀ (c : C) (d : MulAut Y), d ∈ D → fld c * d * (fld c)⁻¹ ∈ D
  fld_inter : ∀ c : C, fld c ∈ D → c = 1
  three_mem : ∀ (α : MulAut Y) (k : ℕ), orderOf α = 3 ^ k → ∃ d ∈ D, ∃ c : C, α = d * fld c
  card_DI : (inner Y).relIndex D = 3
  lang : ∀ α : MulAut Y, α ^ 3 = 1 → (∃ d ∈ D, ∃ c : C, α = d * fld c) → α ∉ D →
    ∃ h ∈ D, ∃ c : C, orderOf c = 3 ∧ α = h * fld c * h⁻¹
  nine : ∀ c : C, orderOf c = 3 → ∃ E : Subgroup Y, Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
    ∀ y ∈ E, fld c y = y

namespace L3Frame

variable {Y : Type} [Group Y] {C : Type} [Group C] (F : L3Frame Y C)

theorem fld_injective : Function.Injective F.fld := by
  rw [injective_iff_map_eq_one]
  intro c hc
  exact F.fld_inter c (hc ▸ F.D.one_mem)

@[expose] def E : Subgroup (MulAut Y) where
  carrier := {α | ∃ d ∈ F.D, ∃ c : C, α = d * F.fld c}
  mul_mem' := by
    rintro _ _ ⟨d₁, hd₁, c₁, rfl⟩ ⟨d₂, hd₂, c₂, rfl⟩
    refine ⟨d₁ * (F.fld c₁ * d₂ * (F.fld c₁)⁻¹), F.D.mul_mem hd₁ (F.fld_norm c₁ d₂ hd₂),
      c₁ * c₂, ?_⟩
    rw [map_mul]
    group
  one_mem' := ⟨1, F.D.one_mem, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨d, hd, c, rfl⟩
    refine ⟨(F.fld c)⁻¹ * d⁻¹ * ((F.fld c)⁻¹)⁻¹, ?_, c⁻¹, ?_⟩
    · have := F.fld_norm c⁻¹ d⁻¹ (F.D.inv_mem hd)
      simpa [map_inv] using this
    · rw [map_inv]
      group

theorem mem_E {α : MulAut Y} : α ∈ F.E ↔ ∃ d ∈ F.D, ∃ c : C, α = d * F.fld c := Iff.rfl

theorem D_le_E : F.D ≤ F.E := fun d hd => ⟨d, hd, 1, by simp⟩

theorem fld_mem_E (c : C) : F.fld c ∈ F.E := ⟨1, F.D.one_mem, c, by simp⟩

theorem E_conj_D {e : MulAut Y} (he : e ∈ F.E) {d : MulAut Y} (hd : d ∈ F.D) :
    e * d * e⁻¹ ∈ F.D := by
  obtain ⟨d', hd', c, rfl⟩ := he
  have h1 := F.fld_norm c d hd
  have h2 : d' * (F.fld c * d * (F.fld c)⁻¹) * d'⁻¹ ∈ F.D :=
    F.D.mul_mem (F.D.mul_mem hd' h1) (F.D.inv_mem hd')
  have h3 : d' * F.fld c * d * (d' * F.fld c)⁻¹ =
      d' * (F.fld c * d * (F.fld c)⁻¹) * d'⁻¹ := by group
  rw [h3]
  exact h2

theorem unique_c {d₁ d₂ : MulAut Y} (hd₁ : d₁ ∈ F.D) (hd₂ : d₂ ∈ F.D) {c₁ c₂ : C}
    (h : d₁ * F.fld c₁ = d₂ * F.fld c₂) : c₁ = c₂ := by
  have h1 : F.fld (c₂ * c₁⁻¹) = d₂⁻¹ * d₁ := by
    rw [map_mul, map_inv]
    calc F.fld c₂ * (F.fld c₁)⁻¹ = d₂⁻¹ * (d₂ * F.fld c₂) * (F.fld c₁)⁻¹ := by group
      _ = d₂⁻¹ * (d₁ * F.fld c₁) * (F.fld c₁)⁻¹ := by rw [h]
      _ = d₂⁻¹ * d₁ := by group
  have h2 : F.fld (c₂ * c₁⁻¹) ∈ F.D := by
    rw [h1]
    exact F.D.mul_mem (F.D.inv_mem hd₂) hd₁
  have h3 := F.fld_inter _ h2
  exact (mul_inv_eq_one.1 h3).symm

theorem exists_decomp (α : ↥F.E) : ∃ c : C, ∃ d ∈ F.D, (α : MulAut Y) = d * F.fld c := by
  obtain ⟨d, hd, c, h⟩ := α.2
  exact ⟨c, d, hd, h⟩

@[expose] noncomputable def rhoFun (α : ↥F.E) : C := Classical.choose (F.exists_decomp α)

theorem rhoFun_spec (α : ↥F.E) : ∃ d ∈ F.D, (α : MulAut Y) = d * F.fld (F.rhoFun α) :=
  Classical.choose_spec (F.exists_decomp α)

theorem rhoFun_eq (α : ↥F.E) {d : MulAut Y} (hd : d ∈ F.D) {c : C}
    (h : (α : MulAut Y) = d * F.fld c) : F.rhoFun α = c := by
  obtain ⟨d', hd', h'⟩ := F.rhoFun_spec α
  exact F.unique_c hd' hd (h'.symm.trans h)

@[expose] noncomputable def rho : ↥F.E →* C where
  toFun := F.rhoFun
  map_one' := F.rhoFun_eq 1 F.D.one_mem (c := 1) (by simp)
  map_mul' α β := by
    obtain ⟨d₁, hd₁, h₁⟩ := F.rhoFun_spec α
    obtain ⟨d₂, hd₂, h₂⟩ := F.rhoFun_spec β
    refine F.rhoFun_eq (α * β) (d := d₁ * (F.fld (F.rhoFun α) * d₂ * (F.fld (F.rhoFun α))⁻¹))
      (F.D.mul_mem hd₁ (F.fld_norm _ _ hd₂)) ?_
    rw [Subgroup.coe_mul, h₁, h₂, map_mul]
    group

theorem rho_apply (α : ↥F.E) : F.rho α = F.rhoFun α := rfl

theorem rho_eq {α : ↥F.E} {d : MulAut Y} (hd : d ∈ F.D) {c : C}
    (h : (α : MulAut Y) = d * F.fld c) : F.rho α = c := F.rhoFun_eq α hd h

theorem rho_eq_one_iff (α : ↥F.E) : F.rho α = 1 ↔ (α : MulAut Y) ∈ F.D := by
  constructor
  · intro h
    obtain ⟨d, hd, h'⟩ := F.rhoFun_spec α
    rw [← rho_apply, h, map_one, mul_one] at h'
    rw [h']
    exact hd
  · intro h
    exact F.rho_eq h (c := 1) (by simp)

theorem rho_fld (c : C) : F.rho ⟨F.fld c, F.fld_mem_E c⟩ = c :=
  F.rho_eq F.D.one_mem (by simp)

theorem rho_D {d : MulAut Y} (hd : d ∈ F.D) : F.rho ⟨d, F.D_le_E hd⟩ = 1 :=
  (F.rho_eq_one_iff _).2 hd

theorem eq_or_eq_of_between {K : Subgroup (MulAut Y)}
    (h1 : inner Y ≤ K) (h2 : K ≤ F.D) : K = inner Y ∨ K = F.D := by
  have hmul := Subgroup.relIndex_mul_relIndex (inner Y) K F.D h1 h2
  have h3 : (inner Y).relIndex F.D = 3 := F.card_DI
  rw [h3] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hmul) with h | h
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h) h1
  · right
    rw [h] at hmul
    have h4 : K.relIndex F.D = 1 := by omega
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.1 h4)

theorem comm_mem_inner (c : C) {k : ℕ} (hc : c ^ 3 ^ k = 1) {d : MulAut Y} (hd : d ∈ F.D) :
    F.fld c * d * (F.fld c)⁻¹ * d⁻¹ ∈ inner Y := by
  classical
  set π : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y) with hπ
  set Ē : Subgroup (Outer Y) := F.E.map π with hĒ
  set DD : Subgroup (Outer Y) := F.D.map π with hDD
  have hDDĒ : DD ≤ Ē := Subgroup.map_mono F.D_le_E
  have hnorm : (DD.subgroupOf Ē).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨d₀, hd₀, hn'⟩ := Subgroup.mem_map.1 hn
    obtain ⟨e, he, hg'⟩ := Subgroup.mem_map.1 g.2
    refine Subgroup.mem_map.2 ⟨e * d₀ * e⁻¹, F.E_conj_D he hd₀, ?_⟩
    rw [map_mul, map_mul, map_inv, hn', hg']
    rfl
  have hcard : Nat.card (DD.subgroupOf Ē) = 3 := by
    have h1 : Nat.card (DD.subgroupOf Ē) = Nat.card DD :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDDĒ).toEquiv
    have h2 : Nat.card DD = Nat.card (F.D ⧸ (inner Y).subgroupOf F.D) := by
      have hker : (π.comp F.D.subtype).ker = (inner Y).subgroupOf F.D := by
        ext x
        simp [hπ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
      have hrange : (π.comp F.D.subtype).range = DD := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hker, ← hrange]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange (π.comp F.D.subtype)).toEquiv).symm
    rw [h1, h2]
    exact F.card_DI
  have hm : (⟨π (F.fld c), Subgroup.mem_map_of_mem π (F.fld_mem_E c)⟩ : ↥Ē) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    change π (F.fld c) ^ 3 ^ k = 1
    rw [← map_pow, ← map_pow, hc, map_one, map_one]
  have hn : (⟨π d, Subgroup.mem_map_of_mem π (F.D_le_E hd)⟩ : ↥Ē) ∈ DD.subgroupOf Ē :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem π hd)
  have key := commute_of_card_three hcard hm hn
  have key' : π (F.fld c) * π d * (π (F.fld c))⁻¹ = π d := congrArg Subtype.val key
  rw [← map_inv, ← map_mul, ← map_mul] at key'
  have : π (F.fld c * d * (F.fld c)⁻¹ * d⁻¹) = 1 := by
    rw [map_mul, key', map_inv, mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff _).1 this


theorem cube_mem_inner (hd3 : ∀ d ∈ F.D, d ^ 3 ∈ (inner Y : Subgroup (MulAut Y))) (c : C) {k : ℕ}
    (hc : c ^ 3 ^ k = 1) {d : MulAut Y} (hd : d ∈ F.D) :
    d * (F.fld c * d * (F.fld c)⁻¹) * (F.fld c ^ 2 * d * (F.fld c ^ 2)⁻¹) ∈ inner Y := by
  have h1 := F.comm_mem_inner c hc hd
  have hc2 : (c ^ 2) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hc, one_pow]
  have h2 := F.comm_mem_inner (c ^ 2) hc2 hd
  rw [map_pow] at h2
  have hN : (inner Y : Subgroup (MulAut Y)).Normal := inferInstance
  have h3 := hN.conj_mem _ h1 d
  have h4 := hN.conj_mem _ h2 (d ^ 2)
  have h5 := hd3 d hd
  have : d * (F.fld c * d * (F.fld c)⁻¹) * (F.fld c ^ 2 * d * (F.fld c ^ 2)⁻¹) =
      (d * (F.fld c * d * (F.fld c)⁻¹ * d⁻¹) * d⁻¹) *
      (d ^ 2 * (F.fld c ^ 2 * d * (F.fld c ^ 2)⁻¹ * d⁻¹) * (d ^ 2)⁻¹) * d ^ 3 := by group
  rw [this]
  exact mul_mem (mul_mem h3 h4) h5

theorem mul_pow_three (d φ : MulAut Y) :
    (d * φ) ^ 3 = (d * (φ * d * φ⁻¹) * (φ ^ 2 * d * (φ ^ 2)⁻¹)) * φ ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul]
  group

end L3Frame

section Action

variable {X : Type} [Group X] {Y : Subgroup X} [Y.Normal]

theorem conjNormal_coe (s : ↥Y) : (MulAut.conjNormal (s : X) : MulAut ↥Y) = MulAut.conj s := by
  ext y
  simp [MulAut.conjNormal_apply]

theorem conjNormal_injective (hC : ∀ c : X, (∀ s ∈ Y, c * s = s * c) → c = 1) :
    Function.Injective (MulAut.conjNormal : X →* MulAut ↥Y) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply hC
  intro s hs
  have := congrArg (fun φ : MulAut ↥Y => (φ ⟨s, hs⟩ : X)) hx
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  calc x * s = x * s * x⁻¹ * x := by group
    _ = s * x := by rw [this]

theorem map_conjNormal_eq_inner : Y.map (MulAut.conjNormal : X →* MulAut ↥Y) = inner ↥Y := by
  ext α
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, (conjNormal_coe ⟨s, hs⟩).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.2, conjNormal_coe s⟩

end Action

namespace L3Frame

variable {Y : Type} [Group Y] {C : Type} [Group C] (F : L3Frame Y C)

theorem fld_not_induced {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) (F : L3Frame ↥S C)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {c : C} (hc : orderOf c = 3) (x₀ : X) :
    (MulAut.conjNormal x₀ : MulAut ↥S) ≠ F.fld c := by
  intro hx₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := conjNormal_injective hC
  have hord : orderOf x₀ = 3 := by
    rw [← orderOf_injective _ hinj x₀, hx₀, orderOf_injective _ F.fld_injective c, hc]
  have hx₀S : x₀ ∉ S := by
    intro hy
    have h1 : (MulAut.conjNormal x₀ : MulAut ↥S) ∈ inner ↥S := by
      refine ⟨⟨x₀, hy⟩, ?_⟩
      exact (conjNormal_coe ⟨x₀, hy⟩).symm
    rw [hx₀] at h1
    have h2 := F.fld_inter c (F.inner_le h1)
    rw [h2, orderOf_one] at hc
    omega
  obtain ⟨E, hE9, hEel, hEfix⟩ := F.nine c hc
  have hE' : IsElemAbelian 3 (E.map S.subtype) := CFSG.SectionRank.isElemAbelian_map hEel S.subtype
  have hcard : Nat.card (E.map S.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hE9]
    norm_num
  have h3 := A318P.three_le_pRank_of_centralizes (S := S) hord hx₀S (E := E.map S.subtype)
    (by rintro _ ⟨e, -, rfl⟩; exact e.2) hE' hcard (fun e he => by
      obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.1 he
      have h4 := hEfix e₀ he₀
      rw [← hx₀] at h4
      have h5 := congrArg (fun y : ↥S => (y : X)) h4
      simp only [MulAut.conjNormal_apply] at h5
      calc x₀ * (e₀ : X) = x₀ * e₀ * x₀⁻¹ * x₀ := by group
        _ = e₀ * x₀ := by rw [h5]
        )
  omega

end L3Frame


section Core

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} [Y.Normal]
  {C : Type} [Group C] [IsCyclic C]

theorem l3_core [IsSimpleGroup ↥Y] (hC : ∀ c : X, (∀ s ∈ Y, c * s = s * c) → c = 1)
    (h3Y : 3 ∣ Nat.card Y) (F : L3Frame ↥Y C)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hx : ∃ x : X, x ∉ Y ∧ ∃ k : ℕ, orderOf x = 3 ^ k) :
    (oPrimeResidualOf 3 (⊤ : Subgroup X)).map (MulAut.conjNormal : X →* MulAut ↥Y) = F.D ∨
      (Nat.card (↥(oPrimeResidualOf 3 (⊤ : Subgroup X)) ⧸
          Y.subgroupOf (oPrimeResidualOf 3 (⊤ : Subgroup X))) = 3 ∧
        (∀ a ∈ oPrimeResidualOf 3 (⊤ : Subgroup X), orderOf a = 3 → a ∈ Y) ∧
        ∃ c : C, orderOf c = 3) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : CommGroup C := IsCyclic.commGroup
  set θ : X →* MulAut ↥Y := MulAut.conjNormal with hθ
  have hinj : Function.Injective θ := conjNormal_injective hC
  set T : Subgroup X := oPrimeResidualOf 3 (⊤ : Subgroup X) with hT
  set H : Subgroup (MulAut ↥Y) := T.map θ with hH
  have hYT : Y ≤ T := A318P.le_oPrimeResidualOf_of_isSimpleGroup Nat.prime_three h3Y
  have hmemT : ∀ x : X, ∀ k : ℕ, orderOf x = 3 ^ k → x ∈ T :=
    fun x k hk => Subgroup.subset_closure ⟨Subgroup.mem_top _, k, hk⟩
  have hgenE : ∀ x : X, ∀ k : ℕ, orderOf x = 3 ^ k → θ x ∈ F.E := fun x k hk =>
    F.three_mem (θ x) k (by rw [orderOf_injective θ hinj x]; exact hk)
  have hTE : H ≤ F.E := by
    rw [hH, hT, oPrimeResidualOf, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, ⟨-, k, hk⟩, rfl⟩
    exact hgenE x k hk
  have hIH : (inner ↥Y : Subgroup (MulAut ↥Y)) ≤ H := by
    rw [← map_conjNormal_eq_inner]
    exact Subgroup.map_mono hYT
  have hρ3 : ∀ β : ↥F.E, (β : MulAut ↥Y) ∈ H → ∃ n : ℕ, F.rho β ^ 3 ^ n = 1 := by
    have hHK : H ≤ ((CommGroup.primaryComponent C 3).comap F.rho).map F.E.subtype := by
      rw [hH, hT, oPrimeResidualOf, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, ⟨-, k, hk⟩, rfl⟩
      refine ⟨⟨θ x, hgenE x k hk⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, CommGroup.mem_primaryComponent]
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : (⟨θ x, hgenE x k hk⟩ : ↥F.E) ^ 3 ^ k = 1 := by
        apply Subtype.ext
        change θ x ^ 3 ^ k = 1
        rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
      rw [this, map_one]
    intro β hβ
    obtain ⟨γ, hγ, hγβ⟩ := Subgroup.mem_map.1 (hHK hβ)
    have : γ = β := Subtype.ext hγβ
    subst this
    rw [Subgroup.mem_comap, CommGroup.mem_primaryComponent] at hγ
    exact hγ
  have hd3 : ∀ d ∈ F.D, d ^ 3 ∈ (inner ↥Y : Subgroup (MulAut ↥Y)) := by
    intro d hd
    have h1 : (QuotientGroup.mk (⟨d, hd⟩ : ↥F.D) : F.D ⧸ (inner ↥Y).subgroupOf F.D) ^ 3 = 1 := by
      have hc : Nat.card (F.D ⧸ (inner ↥Y).subgroupOf F.D) = 3 := F.card_DI
      rw [← hc]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hA : ∀ c : C, orderOf c = 3 → F.fld c ∉ H := by
    intro c hc hmem
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 hmem
    exact L3Frame.fld_not_induced hC F hX3 hc x hx
  by_cases hHD : H ≤ F.D
  · left
    have hne : ¬ H ≤ (inner ↥Y : Subgroup (MulAut ↥Y)) := by
      obtain ⟨x, hxY, k, hk⟩ := hx
      intro hle
      apply hxY
      apply mem_of_conjNormal_inner hC
      exact hle (Subgroup.mem_map_of_mem θ (hmemT x k hk))
    rcases F.eq_or_eq_of_between hIH hHD with h | h
    · exact absurd h.le hne
    · exact h
  right
  obtain ⟨α, hαH, hαD⟩ : ∃ α ∈ H, α ∉ F.D := by
    by_contra h
    push Not at h
    exact hHD fun α hα => h α hα
  have hαE : α ∈ F.E := hTE hαH
  have hρα : F.rho ⟨α, hαE⟩ ≠ 1 := fun h => hαD ((F.rho_eq_one_iff _).1 h)
  obtain ⟨n, hn⟩ := hρ3 ⟨α, hαE⟩ hαH
  obtain ⟨m, hm⟩ := exists_orderOf_eq_prime_pow_iff.2 ⟨n, hn⟩
  have hm1 : 1 ≤ m := by
    by_contra hlt
    have : m = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hm
    exact hρα hm
  set w : MulAut ↥Y := α ^ 3 ^ (m - 1) with hw
  have hwH : w ∈ H := H.pow_mem hαH _
  have hwE : w ∈ F.E := hTE hwH
  have hρw : F.rho ⟨w, hwE⟩ = F.rho ⟨α, hαE⟩ ^ 3 ^ (m - 1) := by
    rw [← map_pow]
    rfl
  have hc₀ord : orderOf (F.rho ⟨w, hwE⟩) = 3 := by
    rw [hρw, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hm]; exact pow_dvd_pow 3 (by omega)), hm]
    have h1 : 3 ^ m = 3 ^ (m - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : C, c₀ = F.rho ⟨w, hwE⟩ := ⟨_, rfl⟩
  rw [← hc₀] at hc₀ord
  obtain ⟨d_w, hdw, hwdec⟩ := F.rhoFun_spec ⟨w, hwE⟩
  have hwdec' : w = d_w * F.fld c₀ := by rw [hc₀]; exact hwdec
  have hHD' : H ⊓ F.D = (inner ↥Y : Subgroup (MulAut ↥Y)) := by
    rcases F.eq_or_eq_of_between (K := H ⊓ F.D) (le_inf hIH F.inner_le) inf_le_right with h | h
    · exact h
    · exfalso
      have hDH : F.D ≤ H := h ▸ inf_le_left
      apply hA c₀ hc₀ord
      have : F.fld c₀ = d_w⁻¹ * w := by rw [hwdec']; group
      rw [this]
      exact H.mul_mem (H.inv_mem (hDH hdw)) hwH
  have hN : (inner ↥Y : Subgroup (MulAut ↥Y)).Normal := inferInstance
  have hexp : ∀ β : ↥F.E, (β : MulAut ↥Y) ∈ H → F.rho β ^ 3 = 1 := by
    intro β hβ
    by_contra hne
    obtain ⟨n, hn⟩ := hρ3 β hβ
    obtain ⟨m', hm'⟩ := exists_orderOf_eq_prime_pow_iff.2 ⟨n, hn⟩
    have hm2 : 2 ≤ m' := by
      by_contra hlt
      apply hne
      have h3 : orderOf (F.rho β) ∣ 3 := by
        rw [hm']
        calc 3 ^ m' ∣ 3 ^ 1 := pow_dvd_pow 3 (by omega)
          _ = 3 := pow_one 3
      exact orderOf_dvd_iff_pow_eq_one.1 h3
    obtain ⟨z, hz⟩ : ∃ z : ↥F.E, z = β ^ 3 ^ (m' - 2) := ⟨_, rfl⟩
    have hzH : (z : MulAut ↥Y) ∈ H := by
      rw [hz, Subgroup.coe_pow]
      exact H.pow_mem hβ _
    obtain ⟨r', hr'⟩ : ∃ r' : C, r' = F.rho z := ⟨_, rfl⟩
    have hr'ord : orderOf r' = 9 := by
      rw [hr', hz, map_pow, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
        (by rw [hm']; exact pow_dvd_pow 3 (by omega)), hm']
      have h1 : 3 ^ m' = 3 ^ (m' - 2) * 9 := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
    obtain ⟨d_z, hdz, hzdec⟩ := F.rhoFun_spec z
    have hzdec' : (z : MulAut ↥Y) = d_z * F.fld r' := by rw [hr']; exact hzdec
    have hr'k : r' ^ 3 ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hr'ord]
      norm_num
    have he := F.cube_mem_inner hd3 r' hr'k hdz
    have hmem : F.fld (r' ^ 3) ∈ H := by
      have : F.fld (r' ^ 3) = (d_z * (F.fld r' * d_z * (F.fld r')⁻¹) *
          (F.fld r' ^ 2 * d_z * (F.fld r' ^ 2)⁻¹))⁻¹ * (z : MulAut ↥Y) ^ 3 := by
        rw [hzdec', L3Frame.mul_pow_three, map_pow]
        group
      rw [this]
      exact H.mul_mem (H.inv_mem (hIH he)) (H.pow_mem hzH 3)
    refine hA (r' ^ 3) ?_ hmem
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hr'ord]; norm_num), hr'ord]
  set ρH : ↥H →* C := F.rho.comp (Subgroup.inclusion hTE) with hρH
  have hker : ρH.ker = (inner ↥Y : Subgroup (MulAut ↥Y)).subgroupOf H := by
    ext β
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hD : (β : MulAut ↥Y) ∈ F.D := (F.rho_eq_one_iff ⟨β, hTE β.2⟩).1 h
      have : (β : MulAut ↥Y) ∈ H ⊓ F.D := ⟨β.2, hD⟩
      rw [hHD'] at this
      exact this
    · intro h
      exact (F.rho_eq_one_iff ⟨β, hTE β.2⟩).2 (F.inner_le h)
  have hRcard : Nat.card ρH.range = 3 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ρH.range)
    have hord : orderOf g = Nat.card ρH.range := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg3 : (g : C) ^ 3 = 1 := by
      obtain ⟨β, hβ⟩ := g.2
      rw [← hβ]
      exact hexp ⟨β, hTE β.2⟩ β.2
    have hdvd : orderOf g ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext hg3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exfalso
      have hg1 : g = 1 := orderOf_eq_one_iff.1 h
      have hmem : F.rho ⟨α, hαE⟩ ∈ ρH.range := ⟨⟨α, hαH⟩, rfl⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨_, hmem⟩)
      rw [hg1, one_zpow] at hj
      exact hρα (congrArg Subtype.val hj).symm
    · rw [← hord, h]
  have hidxH : Nat.card (↥H ⧸ (inner ↥Y : Subgroup (MulAut ↥Y)).subgroupOf H) = 3 := by
    rw [← hker, ← hRcard]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ρH).toEquiv
  have hidx : Nat.card (↥T ⧸ Y.subgroupOf T) = 3 := by
    have h1 : Y.relIndex T = (Y.map θ).relIndex (T.map θ) :=
      (Subgroup.relIndex_map_map_of_injective Y T hinj).symm
    rw [hθ, map_conjNormal_eq_inner] at h1
    change Y.relIndex T = 3
    rw [h1]
    exact hidxH
  have hnoA : ∀ a ∈ T, orderOf a = 3 → a ∈ Y := by
    intro a haT ha3
    by_contra haY
    have hα'H : θ a ∈ H := Subgroup.mem_map_of_mem θ haT
    have hα'E : θ a ∈ F.E := hTE hα'H
    have hα'3 : θ a ^ 3 = 1 := by
      rw [← map_pow, ← ha3, pow_orderOf_eq_one, map_one]
    have hα'D : θ a ∉ F.D := by
      intro hD
      have : θ a ∈ H ⊓ F.D := ⟨hα'H, hD⟩
      rw [hHD'] at this
      exact haY (mem_of_conjNormal_inner hC this)
    obtain ⟨h, hh, c, hc3, hα'eq⟩ := F.lang (θ a) hα'3 hα'E hα'D
    have hc3' : c ^ 3 ^ 1 = 1 := by rw [pow_one, ← hc3, pow_orderOf_eq_one]
    have hcomm := F.comm_mem_inner c hc3' (F.D.inv_mem hh)
    have hu : θ a * (F.fld c)⁻¹ ∈ (inner ↥Y : Subgroup (MulAut ↥Y)) := by
      have : θ a * (F.fld c)⁻¹ = h * (F.fld c * h⁻¹ * (F.fld c)⁻¹ * h⁻¹⁻¹) * h⁻¹ := by
        rw [hα'eq]
        group
      rw [this]
      exact hN.conj_mem _ hcomm h
    have hfld : F.fld c = (θ a * (F.fld c)⁻¹)⁻¹ * θ a := by group
    exact hA c hc3 (hfld ▸ H.mul_mem (H.inv_mem (hIH hu)) hα'H)
  exact ⟨hidx, hnoA, c₀, hc₀ord⟩

end Core

@[expose] def L3Frame.transport {Y Y' : Type} [Group Y] [Group Y'] {C : Type} [Group C]
    (F : L3Frame Y' C) (Φ : MulAut Y ≃* MulAut Y') (ψ : Y ≃* Y')
    (hin : (inner Y).map Φ.toMonoidHom = inner Y')
    (hact : ∀ (α : MulAut Y) (y : Y), Φ α (ψ y) = ψ (α y)) : L3Frame Y C where
  D := F.D.comap Φ.toMonoidHom
  fld := Φ.symm.toMonoidHom.comp F.fld
  inner_le := by
    intro α hα
    have h1 : Φ α ∈ inner Y' := by
      rw [← hin]
      exact ⟨α, hα, rfl⟩
    exact F.inner_le h1
  fld_norm := by
    intro c d hd
    change Φ (Φ.symm (F.fld c) * d * (Φ.symm (F.fld c))⁻¹) ∈ F.D
    rw [map_mul, map_mul, map_inv, Φ.apply_symm_apply]
    exact F.fld_norm c _ hd
  fld_inter := by
    intro c hc
    apply F.fld_inter
    have : Φ (Φ.symm (F.fld c)) ∈ F.D := hc
    rwa [Φ.apply_symm_apply] at this
  three_mem := by
    intro α k hα
    have hα' : orderOf (Φ α) = 3 ^ k := by rw [MulEquiv.orderOf_eq]; exact hα
    obtain ⟨d, hd, c, h⟩ := F.three_mem _ k hα'
    refine ⟨Φ.symm d, ?_, c, ?_⟩
    · change Φ (Φ.symm d) ∈ F.D
      rwa [Φ.apply_symm_apply]
    · apply Φ.injective
      change Φ α = Φ (Φ.symm d * Φ.symm (F.fld c))
      rw [map_mul, Φ.apply_symm_apply, Φ.apply_symm_apply]
      exact h
  card_DI := by
    have h1 := Subgroup.relIndex_map_map_of_injective (f := Φ.toMonoidHom) (inner Y)
      (F.D.comap Φ.toMonoidHom) Φ.injective
    rw [hin, Subgroup.map_comap_eq_self_of_surjective Φ.surjective] at h1
    rw [← h1]
    exact F.card_DI
  lang := by
    intro α hα3 hdec hαD
    have hα3' : (Φ α) ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    obtain ⟨d, hd, c, h⟩ := hdec
    have hdec' : ∃ d' ∈ F.D, ∃ c : C, Φ α = d' * F.fld c := by
      refine ⟨Φ d, hd, c, ?_⟩
      rw [h, map_mul]
      change Φ d * Φ (Φ.symm (F.fld c)) = Φ d * F.fld c
      rw [Φ.apply_symm_apply]
    obtain ⟨h', hh', c', hc', hα⟩ := F.lang _ hα3' hdec' hαD
    refine ⟨Φ.symm h', ?_, c', hc', ?_⟩
    · change Φ (Φ.symm h') ∈ F.D
      rwa [Φ.apply_symm_apply]
    · apply Φ.injective
      change Φ α = Φ (Φ.symm h' * Φ.symm (F.fld c') * (Φ.symm h')⁻¹)
      simp only [map_mul, map_inv, Φ.apply_symm_apply]
      exact hα
  nine := by
    intro c hc
    obtain ⟨E, hE9, hEel, hEfix⟩ := F.nine c hc
    refine ⟨E.map ψ.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective ψ.symm.injective, hE9]
    · exact CFSG.SectionRank.isElemAbelian_map hEel ψ.symm.toMonoidHom
    · rintro _ ⟨e, he, rfl⟩
      have h1 : ψ ((Φ.symm (F.fld c)) (ψ.symm e)) = F.fld c e := by
        rw [← hact, Φ.apply_symm_apply, MulEquiv.apply_symm_apply]
      have h2 := hEfix e he
      change (Φ.symm (F.fld c)) (ψ.symm e) = ψ.symm e
      apply ψ.injective
      rw [h1, h2, MulEquiv.apply_symm_apply]

@[expose] def L3Frame.ofMulEquiv {Y Y' : Type} [Group Y] [Group Y'] {C : Type} [Group C]
    (F : L3Frame Y' C) (ψ : Y ≃* Y') : L3Frame Y C :=
  F.transport (MulAut.congr ψ) ψ
    (CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ψ)
    (fun α y => by simp [MulAut.congr_apply])

end A318P

end CFSG.Quasithin
