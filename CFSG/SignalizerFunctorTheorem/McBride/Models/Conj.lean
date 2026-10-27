module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem isPGroup_of_forall_coprime_orderOf_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : ∀ g : G, Nat.Coprime p (orderOf g) → g = 1) : IsPGroup p G := by
  have := Fact.mk hp
  refine IsPGroup.iff_card.mpr ⟨(Nat.card G).primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd => ?_
  by_contra hne
  have := Fact.mk hq
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqd
  have h1 : g = 1 := h g (by rw [hg]; exact (Nat.coprime_primes hp hq).mpr (Ne.symm hne))
  rw [h1, orderOf_one] at hg
  exact hq.one_lt.ne hg

private theorem apply_eq_of_mem_zpowers {Y : Type*} [Group Y] {a b : MulAut Y}
    (hb : b ∈ Subgroup.zpowers a) {x : Y} (hx : a x = x) : b x = x := by
  have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut Y) x := by
    rw [Subgroup.zpowers_le]
    exact hx
  exact hle hb

private theorem exists_sylow_eq_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hbound : ∀ P : Subgroup G, IsPGroup p P → Nat.card P ∣ p) {g : G} (hg : orderOf g = p) :
    ∃ S : Sylow p G, (S : Subgroup G) = Subgroup.zpowers g := by
  have hzp : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  refine ⟨S, (Subgroup.eq_of_le_of_card_ge hS ?_).symm⟩
  have h1 : Nat.card (S : Subgroup G) ≤ p :=
    Nat.le_of_dvd (Fact.out : p.Prime).pos (hbound _ S.isPGroup')
  rwa [Nat.card_zpowers, hg]

theorem exists_fixed_conj {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {f φ : MulAut Y} (hf : orderOf f = p) (hφ : orderOf φ = p) :
    ∃ g : MulAut Y, signalizerFixedSubgroup f = signalizerFixedSubgroup (MulAut.congr g φ) := by
  have := Fact.mk hp
  obtain ⟨Sf, hSf⟩ := exists_sylow_eq_zpowers hbound hf
  obtain ⟨Sφ, hSφ⟩ := exists_sylow_eq_zpowers hbound hφ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut Y) Sφ Sf
  have hconj : ∀ y : MulAut Y, y ∈ Subgroup.zpowers f ↔ g⁻¹ * y * g ∈ Subgroup.zpowers φ := by
    intro y
    rw [← hSf, ← hSφ, ← hg, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have key : ∀ x : Y, f x = x ↔ φ (g.symm x) = g.symm x := by
    intro x
    constructor
    · intro hx
      have hmem : g * φ * g⁻¹ ∈ Subgroup.zpowers f := by
        rw [hconj, show g⁻¹ * (g * φ * g⁻¹) * g = φ by group]
        exact Subgroup.mem_zpowers φ
      have h : g (φ (g.symm x)) = x := apply_eq_of_mem_zpowers hmem hx
      simpa using congrArg g.symm h
    · intro hx
      have hmem : g⁻¹ * f * g ∈ Subgroup.zpowers φ := (hconj f).mp (Subgroup.mem_zpowers f)
      have h : g.symm (f (g (g.symm x))) = g.symm x := apply_eq_of_mem_zpowers hmem hx
      simpa using h
  refine ⟨g, ?_⟩
  ext y
  change f y = y ↔ g (φ (g.symm y)) = y
  rw [key y]
  exact g.eq_symm_apply

section ForallOfOne

variable {p : ℕ} {Y : Type*} [Group Y] [Finite Y]

theorem Frame.forall_of_one {ℓ : ℕ}
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : Frame p ℓ φ) :
    ∀ f : MulAut Y, orderOf f = p → Frame p ℓ f := by
  intro f hf
  obtain ⟨g, hg⟩ := exists_fixed_conj h.prime hbound hf hφ
  refine Frame.of_fixed_eq hg (by rw [orderOf_congr, hf, hφ]) (Frame.of_congr g.symm ?_)
  rwa [congr_symm_congr]

theorem ItemC.forall_of_one (hp : p.Prime)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : ItemC p φ) :
    ∀ f : MulAut Y, orderOf f = p → ItemC p f := by
  intro f hf
  obtain ⟨g, hg⟩ := exists_fixed_conj hp hbound hf hφ
  refine ItemC.of_fixed_eq hg (ItemC.of_congr g.symm ?_)
  rwa [congr_symm_congr]

theorem ItemG.forall_of_one (hp : p.Prime)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : ItemG p φ) :
    ∀ f : MulAut Y, orderOf f = p → ItemG p f := by
  intro f hf
  obtain ⟨g, hg⟩ := exists_fixed_conj hp hbound hf hφ
  refine ItemG.of_fixed_eq hg (ItemG.of_congr g.symm ?_)
  rwa [congr_symm_congr]

theorem ItemO.forall_of_one (hp : p.Prime)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : ItemO φ) :
    ∀ f : MulAut Y, orderOf f = p → ItemO f := by
  intro f hf
  obtain ⟨g, hg⟩ := exists_fixed_conj hp hbound hf hφ
  refine ItemO.of_fixed_eq hg (ItemO.of_congr g.symm ?_)
  rwa [congr_symm_congr]

end ForallOfOne

section OfModel

variable {p : ℕ} {X Y : Type*} [Group X] [Group Y]

theorem Frame.of_model {ℓ : ℕ} [Finite X] [Finite Y] (e : X ≃* Y)
    (hY : ∀ f' : MulAut Y, orderOf f' = p → Frame p ℓ f') {f : MulAut X} (hf : orderOf f = p) :
    Frame p ℓ f :=
  Frame.of_congr e (hY _ (by rw [orderOf_congr, hf]))

theorem ItemC.of_model (e : X ≃* Y) (hY : ∀ f' : MulAut Y, orderOf f' = p → ItemC p f')
    {f : MulAut X} (hf : orderOf f = p) : ItemC p f :=
  ItemC.of_congr e (hY _ (by rw [orderOf_congr, hf]))

theorem ItemG.of_model (e : X ≃* Y) (hY : ∀ f' : MulAut Y, orderOf f' = p → ItemG p f')
    {f : MulAut X} (hf : orderOf f = p) : ItemG p f :=
  ItemG.of_congr e (hY _ (by rw [orderOf_congr, hf]))

theorem ItemO.of_model [Finite X] [Finite Y] (e : X ≃* Y)
    (hY : ∀ f' : MulAut Y, orderOf f' = p → ItemO f') {f : MulAut X} (hf : orderOf f = p) :
    ItemO f :=
  ItemO.of_congr e (hY _ (by rw [orderOf_congr, hf]))

theorem Frame.of_model_of_one {ℓ : ℕ} [Finite X] [Finite Y] (e : X ≃* Y)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : Frame p ℓ φ) {f : MulAut X} (hf : orderOf f = p) :
    Frame p ℓ f :=
  Frame.of_model e (Frame.forall_of_one hbound hφ h) hf

theorem ItemC.of_model_of_one [Finite Y] (hp : p.Prime) (e : X ≃* Y)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : ItemC p φ) {f : MulAut X} (hf : orderOf f = p) :
    ItemC p f :=
  ItemC.of_model e (ItemC.forall_of_one hp hbound hφ h) hf

theorem ItemG.of_model_of_one [Finite Y] (hp : p.Prime) (e : X ≃* Y)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : ItemG p φ) {f : MulAut X} (hf : orderOf f = p) :
    ItemG p f :=
  ItemG.of_model e (ItemG.forall_of_one hp hbound hφ h) hf

theorem ItemO.of_model_of_one [Finite X] [Finite Y] (hp : p.Prime) (e : X ≃* Y)
    (hbound : ∀ P : Subgroup (MulAut Y), IsPGroup p P → Nat.card P ∣ p)
    {φ : MulAut Y} (hφ : orderOf φ = p) (h : ItemO φ) {f : MulAut X} (hf : orderOf f = p) :
    ItemO f :=
  ItemO.of_model e (ItemO.forall_of_one hp hbound hφ h) hf

end OfModel

end CFSG.SignalizerFunctorTheorem.McBride
