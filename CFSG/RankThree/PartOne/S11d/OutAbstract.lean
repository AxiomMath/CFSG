module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Subgroup
open scoped commutatorElement

noncomputable abbrev Inn (X : Type*) [Group X] : Subgroup (MulAut X) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner X

instance instFiniteMulAut' (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun α : MulAut X => (α : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

@[expose] def OutPNice (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∃ D E : Subgroup (MulAut X), Inn X ≤ D ∧
    (∀ δ ∈ D, ∀ k : ℕ, δ ^ (p ^ k) ∈ Inn X → δ ∈ Inn X) ∧
    (∀ α : MulAut X, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → α ∈ E) ∧
    (∀ γ α : MulAut X, α ∈ E → ⁅γ, α⁆ ∈ D) ∧
    ∀ α ∈ E, ∀ β ∈ E, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → (∃ k : ℕ, β ^ (p ^ k) ∈ D) →
      (∃ m : ℤ, α * β ^ m ∈ D) ∨ ∃ m : ℤ, β * α ^ m ∈ D

@[expose] def OutPChain (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∃ D E : Subgroup (MulAut X), Inn X ≤ D ∧
    (∀ δ ∈ D, ∀ k : ℕ, δ ^ (p ^ k) ∈ Inn X → δ ∈ Inn X) ∧
    (∀ α : MulAut X, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → α ∈ E) ∧
    ∀ α ∈ E, ∀ β ∈ E, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → (∃ k : ℕ, β ^ (p ^ k) ∈ D) →
      (∃ m : ℤ, α * β ^ m ∈ D) ∨ ∃ m : ℤ, β * α ^ m ∈ D

theorem OutPNice.toChain {X : Type*} [Group X] {p : ℕ} (h : OutPNice p X) : OutPChain p X := by
  obtain ⟨D, E, h1, h2, h3, -, h5⟩ := h
  exact ⟨D, E, h1, h2, h3, h5⟩

section Abstract

variable {X : Type*} [Group X] {p : ℕ}

theorem OutPChain.comparable (h : OutPChain p X) {α β : MulAut X} (hαβ : α * β = β * α)
    {k l : ℕ} (hα : α ^ (p ^ k) ∈ Inn X) (hβ : β ^ (p ^ l) ∈ Inn X) :
    (∃ m : ℤ, α * β ^ m ∈ Inn X) ∨ ∃ m : ℤ, β * α ^ m ∈ Inn X := by
  obtain ⟨D, E, hID, hD2, hpE, hD4⟩ := h
  have hcomm : Commute α β := hαβ
  have key : ∀ {α β : MulAut X} {k l : ℕ}, Commute α β → α ^ (p ^ k) ∈ Inn X →
      β ^ (p ^ l) ∈ Inn X → ∀ m : ℤ, α * β ^ m ∈ D → α * β ^ m ∈ Inn X := by
    intro α β k l hc hα hβ m hm
    refine hD2 _ hm (k + l) ?_
    have hc' : Commute α (β ^ m) := hc.zpow_right m
    rw [hc'.mul_pow]
    refine mul_mem ?_ ?_
    · have : α ^ (p ^ (k + l)) = (α ^ (p ^ k)) ^ (p ^ l) := by
        rw [← pow_mul, ← pow_add]
      rw [this]
      exact (Inn X).pow_mem hα _
    · have e1 : (β ^ m) ^ (p ^ (k + l)) = (β ^ (p ^ (k + l))) ^ m := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have e2 : β ^ (p ^ (k + l)) = (β ^ (p ^ l)) ^ (p ^ k) := by
        rw [← pow_mul, ← pow_add, add_comm]
      rw [e1, e2]
      exact (Inn X).zpow_mem ((Inn X).pow_mem hβ _) m
  rcases hD4 α (hpE α ⟨k, hID hα⟩) β (hpE β ⟨l, hID hβ⟩) ⟨k, hID hα⟩ ⟨l, hID hβ⟩ with
    ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl ⟨m, key hcomm hα hβ m hm⟩
  · exact Or.inr ⟨m, key hcomm.symm hβ hα m hm⟩

theorem OutPNice.dvd_sub_one (h : OutPNice p X) (hp : p.Prime) {α γ : MulAut X}
    (hα : α ^ p ∈ Inn X) (hα1 : α ∉ Inn X) {m : ℤ}
    (hm : γ * α * γ⁻¹ * α ^ (-m) ∈ Inn X) : (p : ℤ) ∣ m - 1 := by
  obtain ⟨D, E, hID, hD2, hpE, hD3, -⟩ := h
  have hαE : α ∈ E := hpE α ⟨1, by rw [pow_one]; exact hID hα⟩
  have h1 : α ^ (1 - m) ∈ D := by
    have e : α ^ (1 - m) = (⁅γ, α⁆)⁻¹ * (γ * α * γ⁻¹ * α ^ (-m)) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem (hD3 γ α hαE)) (hID hm)
  have h2 : (α ^ (1 - m)) ^ (p ^ 1) ∈ Inn X := by
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    exact (Inn X).zpow_mem hα _
  have h3 : α ^ (1 - m) ∈ Inn X := hD2 _ h1 1 h2
  by_contra hndvd
  have hcop : IsCoprime (1 - m) (p : ℤ) := by
    have : IsCoprime (p : ℤ) (1 - m) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rw [Int.gcd_comm]
      have hnd : ¬ (p : ℤ) ∣ 1 - m := by
        intro hd
        apply hndvd
        have : m - 1 = -(1 - m) := by ring
        rw [this]
        exact (dvd_neg).mpr hd
      have hg : Int.gcd (1 - m) (p : ℤ) ∣ p := by
        have := Int.gcd_dvd_right (a := 1 - m) (b := (p : ℤ))
        exact_mod_cast this
      rcases (Nat.dvd_prime hp).mp hg with hg1 | hgp
      · exact hg1
      · exfalso
        apply hnd
        have := Int.gcd_dvd_left (a := 1 - m) (b := (p : ℤ))
        rw [hgp] at this
        exact this
    exact this.symm
  obtain ⟨s, t, hst⟩ := hcop
  have : α = (α ^ (1 - m)) ^ s * (α ^ p) ^ t := by
    rw [← zpow_natCast α p, ← zpow_mul, ← zpow_mul, ← zpow_add]
    nth_rewrite 1 [← zpow_one α]
    congr 1
    linarith
  apply hα1
  rw [this]
  exact mul_mem ((Inn X).zpow_mem h3 s) ((Inn X).zpow_mem hα t)

theorem mem_of_pow_mem_of_not_dvd {Γ : Type*} [Group Γ] {I : Subgroup Γ} (hp : p.Prime) {α : Γ}
    (hα : α ^ p ∈ I) {m : ℤ} (h1 : α ^ m ∈ I) (hm : ¬ (p : ℤ) ∣ m) : α ∈ I := by
  have hcop : IsCoprime m (p : ℤ) := by
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact ((Prime.coprime_iff_not_dvd hpp).mpr hm).symm.symm.symm
  obtain ⟨s, t, hst⟩ := hcop
  have : α = (α ^ m) ^ s * (α ^ p) ^ t := by
    rw [← zpow_natCast α p, ← zpow_mul, ← zpow_mul, ← zpow_add]
    nth_rewrite 1 [← zpow_one α]
    congr 1
    linarith
  rw [this]
  exact mul_mem (I.zpow_mem h1 s) (I.zpow_mem hα t)

@[expose] def OutPCentral (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ γ α : MulAut X, α ^ p ∈ Inn X → ⁅γ, α⁆ ∈ Inn X

theorem OutPCentral.dvd_sub_one (h : OutPCentral p X) (hp : p.Prime) {α γ : MulAut X}
    (hα : α ^ p ∈ Inn X) (hα1 : α ∉ Inn X) {m : ℤ}
    (hm : γ * α * γ⁻¹ * α ^ (-m) ∈ Inn X) : (p : ℤ) ∣ m - 1 := by
  have h1 : α ^ (1 - m) ∈ Inn X := by
    have e : α ^ (1 - m) = (⁅γ, α⁆)⁻¹ * (γ * α * γ⁻¹ * α ^ (-m)) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem (h γ α hα)) hm
  by_contra hnd
  apply hα1
  refine mem_of_pow_mem_of_not_dvd hp hα h1 ?_
  intro hd
  apply hnd
  have : m - 1 = -(1 - m) := by ring
  rw [this]
  exact (dvd_neg).mpr hd

def PChain (p : ℕ) (C : Type*) [Group C] : Prop :=
  ∀ x y : C, (∃ k : ℕ, x ^ (p ^ k) = 1) → (∃ k : ℕ, y ^ (p ^ k) = 1) →
    (∃ m : ℤ, x * y ^ m = 1) ∨ ∃ m : ℤ, y * x ^ m = 1

theorem outPNice_of_hom {C : Type*} [Group C] (Θ : MulAut X →* C)
    (hcomm : ∀ x y : C, x * y = y * x) (hinner : Inn X ≤ Θ.ker)
    (hp : ∀ δ ∈ Θ.ker, ∀ k : ℕ, δ ^ (p ^ k) ∈ Inn X → δ ∈ Inn X) (hchain : PChain p C) :
    OutPNice p X := by
  refine ⟨Θ.ker, ⊤, hinner, hp, fun α _ => trivial, fun α β _ => ?_,
    fun α _ β _ ⟨k, hk⟩ ⟨l, hl⟩ => ?_⟩
  · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
    have h1 : Θ α * Θ β * (Θ α)⁻¹ * (Θ β)⁻¹ = 1 := by
      rw [hcomm (Θ α) (Θ β)]
      group
    exact h1
  · have hk' : (Θ α) ^ (p ^ k) = 1 := by rw [← map_pow]; exact hk
    have hl' : (Θ β) ^ (p ^ l) = 1 := by rw [← map_pow]; exact hl
    rcases hchain (Θ α) (Θ β) ⟨k, hk'⟩ ⟨l, hl'⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨m, by rw [MonoidHom.mem_ker, map_mul, map_zpow]; exact hm⟩
    · exact Or.inr ⟨m, by rw [MonoidHom.mem_ker, map_mul, map_zpow]; exact hm⟩

theorem pChain_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] (hp : p.Prime) :
    PChain p C := by
  intro x y ⟨k, hk⟩ ⟨l, hl⟩
  have hx : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hy : orderOf y ∣ p ^ l := orderOf_dvd_of_pow_eq_one hl
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hy
  have key : ∀ {x y : C} {i j : ℕ}, orderOf x = p ^ i → orderOf y = p ^ j → i ≤ j →
      ∃ m : ℤ, x * y ^ m = 1 := by
    intro x y i j hi hj hij
    have hdvd : Nat.card (zpowers x) ∣ Nat.card (zpowers y) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hi, hj]
      exact pow_dvd_pow p hij
    have hle : zpowers x ≤ zpowers y := IsCyclic.subgroup_le_iff_card_dvd.mpr hdvd
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hle (mem_zpowers x))
    exact ⟨-m, by rw [zpow_neg, ← hm]; simp⟩
  rcases le_total i j with hij | hij
  · exact Or.inl (key hi hj hij)
  · exact Or.inr (key hj hi hij)

theorem outPNice_of_hom_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] (hp : p.Prime)
    (Θ : MulAut X →* C) (hker : Θ.ker = Inn X) : OutPNice p X :=
  outPNice_of_hom Θ (fun x y => IsMulCommutative.is_comm.comm x y) hker.ge
    (fun _ hδ _ _ => hker ▸ hδ) (pChain_of_isCyclic hp)

theorem outPNice_of_isCyclic_outer [Finite X] (hp : p.Prime)
    (h : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) : OutPNice p X :=
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    Quotient.finite _
  outPNice_of_hom_cyclic hp (QuotientGroup.mk' (Inn X)) (QuotientGroup.ker_mk' _)

theorem chain_of_cyclic_quotient {Γ : Type*} [Group Γ] [Finite Γ] (hp : p.Prime)
    {D : Subgroup Γ} [D.Normal] (g : Γ) (hE : ∀ α : Γ, ∃ k : ℤ, g ^ k * α ∈ D) (α β : Γ)
    (hα : ∃ k : ℕ, α ^ (p ^ k) ∈ D) (hβ : ∃ k : ℕ, β ^ (p ^ k) ∈ D) :
    (∃ m : ℤ, α * β ^ m ∈ D) ∨ ∃ m : ℤ, β * α ^ m ∈ D := by
  obtain ⟨k, hk⟩ := hα
  obtain ⟨l, hl⟩ := hβ
  obtain ⟨a, ha⟩ := hE α
  obtain ⟨b, hb⟩ := hE β
  set ζ : Γ ⧸ D := QuotientGroup.mk g with hζ
  have hα : (QuotientGroup.mk α : Γ ⧸ D) = ζ ^ (-a) := by
    have h1 : (QuotientGroup.mk (g ^ a * α) : Γ ⧸ D) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hβ : (QuotientGroup.mk β : Γ ⧸ D) = ζ ^ (-b) := by
    have h1 : (QuotientGroup.mk (g ^ b * β) : Γ ⧸ D) = 1 := (QuotientGroup.eq_one_iff _).mpr hb
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have : Finite (Γ ⧸ D) := Quotient.finite _
  have : Finite (Subgroup.zpowers ζ) := inferInstance
  let x : Subgroup.zpowers ζ := ⟨ζ ^ (-a), zpow_mem (mem_zpowers ζ) _⟩
  let y : Subgroup.zpowers ζ := ⟨ζ ^ (-b), zpow_mem (mem_zpowers ζ) _⟩
  have hx : x ^ (p ^ k) = 1 := by
    apply Subtype.ext
    show (ζ ^ (-a)) ^ (p ^ k) = 1
    rw [← hα, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hy : y ^ (p ^ l) = 1 := by
    apply Subtype.ext
    show (ζ ^ (-b)) ^ (p ^ l) = 1
    rw [← hβ, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hl
  rcases pChain_of_isCyclic (C := Subgroup.zpowers ζ) hp x y ⟨k, hx⟩ ⟨l, hy⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hα, hβ]
    exact congrArg Subtype.val hm
  · right
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hα, hβ]
    exact congrArg Subtype.val hm

theorem outPNice_of_tower [Finite X] (hp : p.Prime) {D E : Subgroup (MulAut X)} (g : MulAut X)
    (hID : Inn X ≤ D) (hD2 : ∀ δ ∈ D, ∀ k : ℕ, δ ^ (p ^ k) ∈ Inn X → δ ∈ Inn X)
    (hpE : ∀ α : MulAut X, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → α ∈ E)
    (hD3 : ∀ γ α : MulAut X, α ∈ E → ⁅γ, α⁆ ∈ D)
    (hE : ∀ α ∈ E, ∃ k : ℤ, g ^ k * α ∈ D) : OutPNice p X := by
  refine ⟨D, E, hID, hD2, hpE, hD3, ?_⟩
  have hDE : D ≤ E := fun δ hδ => hpE δ ⟨0, by rw [pow_zero, pow_one]; exact hδ⟩
  have hDn : D.Normal := ⟨fun d hd α => by
    have : α * d * α⁻¹ = ⁅α, d⁆ * d := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem (hD3 α d (hDE hd)) hd⟩
  intro α hαE β hβE ⟨k, hk⟩ ⟨l, hl⟩
  obtain ⟨a, ha⟩ := hE α hαE
  obtain ⟨b, hb⟩ := hE β hβE
  set ζ : MulAut X ⧸ D := QuotientGroup.mk g with hζ
  have hα : (QuotientGroup.mk α : MulAut X ⧸ D) = ζ ^ (-a) := by
    have h1 : (QuotientGroup.mk (g ^ a * α) : MulAut X ⧸ D) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ha
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hβ : (QuotientGroup.mk β : MulAut X ⧸ D) = ζ ^ (-b) := by
    have h1 : (QuotientGroup.mk (g ^ b * β) : MulAut X ⧸ D) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hb
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have : Finite (MulAut X ⧸ D) := Quotient.finite _
  have : Finite (Subgroup.zpowers ζ) := inferInstance
  let x : Subgroup.zpowers ζ := ⟨ζ ^ (-a), zpow_mem (mem_zpowers ζ) _⟩
  let y : Subgroup.zpowers ζ := ⟨ζ ^ (-b), zpow_mem (mem_zpowers ζ) _⟩
  have hx : x ^ (p ^ k) = 1 := by
    apply Subtype.ext
    show (ζ ^ (-a)) ^ (p ^ k) = 1
    rw [← hα, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hy : y ^ (p ^ l) = 1 := by
    apply Subtype.ext
    show (ζ ^ (-b)) ^ (p ^ l) = 1
    rw [← hβ, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hl
  rcases pChain_of_isCyclic (C := Subgroup.zpowers ζ) hp x y ⟨k, hx⟩ ⟨l, hy⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hα, hβ]
    exact congrArg Subtype.val hm
  · right
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hα, hβ]
    exact congrArg Subtype.val hm

theorem commutator_mem_of_cyclic_quotient {Γ : Type*} [Group Γ] {D : Subgroup Γ} [D.Normal]
    (g : Γ) (h : ∀ α : Γ, ∃ k : ℤ, g ^ k * α ∈ D) (α β : Γ) : ⁅α, β⁆ ∈ D := by
  obtain ⟨a, ha⟩ := h α
  obtain ⟨b, hb⟩ := h β
  have hα : (QuotientGroup.mk α : Γ ⧸ D) = (QuotientGroup.mk g) ^ (-a) := by
    have h1 : (QuotientGroup.mk (g ^ a * α) : Γ ⧸ D) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hβ : (QuotientGroup.mk β : Γ ⧸ D) = (QuotientGroup.mk g) ^ (-b) := by
    have h1 : (QuotientGroup.mk (g ^ b * β) : Γ ⧸ D) = 1 := (QuotientGroup.eq_one_iff _).mpr hb
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hα, hβ]
  have hc : Commute ((QuotientGroup.mk g : Γ ⧸ D) ^ (-a)) ((QuotientGroup.mk g : Γ ⧸ D) ^ (-b)) :=
    Commute.zpow_zpow_self _ _ _
  rw [hc.eq]
  group

theorem pChain_prod {C₁ C₂ : Type*} [Group C₁] [Group C₂] (h1 : PChain p C₁)
    (h2 : ∀ y : C₂, (∃ k : ℕ, y ^ (p ^ k) = 1) → y = 1) : PChain p (C₁ × C₂) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨k, hk⟩ ⟨l, hl⟩
  have hk' : x₁ ^ (p ^ k) = 1 ∧ x₂ ^ (p ^ k) = 1 := Prod.ext_iff.mp hk
  have hl' : y₁ ^ (p ^ l) = 1 ∧ y₂ ^ (p ^ l) = 1 := Prod.ext_iff.mp hl
  have hx2 : x₂ = 1 := h2 x₂ ⟨k, hk'.2⟩
  have hy2 : y₂ = 1 := h2 y₂ ⟨l, hl'.2⟩
  rcases h1 x₁ y₁ ⟨k, hk'.1⟩ ⟨l, hl'.1⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine Or.inl ⟨m, ?_⟩
    rw [hx2, hy2]
    simp [Prod.mk_mul_mk, hm]
  · refine Or.inr ⟨m, ?_⟩
    rw [hx2, hy2]
    simp [Prod.mk_mul_mk, hm]

theorem mem_of_pow_mem_of_exponent {Γ : Type*} [Group Γ] {D N : Subgroup Γ} [N.Normal]
    (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n)
    (hexp : ∀ x : D ⧸ N.subgroupOf D, x ^ n = 1) {δ : Γ} (hδ : δ ∈ D) {k : ℕ}
    (hk : δ ^ (p ^ k) ∈ N) : δ ∈ N := by
  set x : D ⧸ N.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
  have hxk : x ^ (p ^ k) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have hdvd1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one (hexp x)
  have hcop : Nat.Coprime (p ^ k) n :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : x = 1 := orderOf_eq_one_iff.mp hx1
  have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
  exact Subgroup.mem_subgroupOf.mp hmem

theorem mem_of_pow_mem_of_index_le_three {Γ : Type*} [Group Γ] [Finite Γ] (E : Subgroup Γ)
    (h : E.index ≤ 3) {p k : ℕ} (hp : p.Prime) (hp3 : 3 < p) {α : Γ} (hα : α ^ (p ^ k) ∈ E) :
    α ∈ E := by
  classical
  have h0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : Fintype (Γ ⧸ E) := Fintype.ofFinite _
  set N : ℕ := (E.index).factorial with hN
  have hNdvd : N ∣ 6 := by
    have : (E.index).factorial ∣ (3 : ℕ).factorial := Nat.factorial_dvd_factorial h
    simpa [Nat.factorial] using this
  have hαN : α ^ N ∈ E := by
    have hker : α ^ N ∈ (MulAction.toPermHom Γ (Γ ⧸ E)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      have hc := pow_card_eq_one (x := (MulAction.toPermHom Γ (Γ ⧸ E)) α)
      rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hc
      exact hc
    exact (Subgroup.normalCore_le E) (by rwa [Subgroup.normalCore_eq_ker])
  have hcop : Nat.Coprime (p ^ k) N := by
    refine Nat.Coprime.coprime_dvd_right hNdvd (Nat.Coprime.pow_left k ?_)
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have : α = (α ^ (p ^ k)) ^ u * (α ^ N) ^ v := by
    rw [← zpow_natCast α (p ^ k), ← zpow_natCast α N, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← zpow_add]
    nth_rewrite 1 [← zpow_one α]
    congr 1
    linarith
  rw [this]
  exact mul_mem (E.zpow_mem hα u) (E.zpow_mem hαN v)

end Abstract

section FieldAut

open CFSG.LocalAnalysis.ComponentInitial in
theorem ringAut_comm (K : Type) [Field K] [Finite K] (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨-, hcyc⟩ := card_ringAut_and_isCyclic hℓ K hK
  exact IsMulCommutative.is_comm.comm σ τ

end FieldAut

section Arith

theorem exists_pow_eq_of_pow_eq {Z : Type*} [CommGroup Z] [Finite Z] [IsCyclic Z] {p : ℕ}
    (hp : p.Prime) {n k : ℕ} (hn : ¬ p ∣ Nat.gcd n (Nat.card Z)) {d u : Z}
    (h : d ^ (p ^ k) = u ^ n) : ∃ μ : Z, μ ^ n = d := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Z)
  have hord : orderOf γ = Nat.card Z := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨s, hs⟩ := mem_zpowers_iff.mp (hγ d)
  obtain ⟨t, ht⟩ := mem_zpowers_iff.mp (hγ u)
  have h1 : γ ^ (s * ((p ^ k : ℕ) : ℤ) - t * (n : ℤ)) = 1 := by
    rw [zpow_sub, zpow_mul, zpow_mul, hs, ht, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  have h2 : ((Nat.card Z : ℕ) : ℤ) ∣ s * ((p ^ k : ℕ) : ℤ) - t * (n : ℤ) := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  set g := Nat.gcd n (Nat.card Z) with hg
  have hgn : (g : ℤ) ∣ n := by exact_mod_cast Nat.gcd_dvd_left n _
  have hgN : (g : ℤ) ∣ ((Nat.card Z : ℕ) : ℤ) := by exact_mod_cast Nat.gcd_dvd_right n _
  have h3 : (g : ℤ) ∣ s * ((p ^ k : ℕ) : ℤ) := by
    have : s * ((p ^ k : ℕ) : ℤ) = (s * ((p ^ k : ℕ) : ℤ) - t * n) + t * n := by ring
    rw [this]
    exact dvd_add (hgN.trans h2) (dvd_mul_of_dvd_right hgn t)
  have hcop : IsCoprime (g : ℤ) ((p ^ k : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn).symm
  obtain ⟨s', hs'⟩ := hcop.dvd_of_dvd_mul_right h3
  have hbez : (g : ℤ) = n * Nat.gcdA n (Nat.card Z) + ((Nat.card Z : ℕ) : ℤ) *
      Nat.gcdB n (Nat.card Z) := Nat.gcd_eq_gcd_ab n (Nat.card Z)
  refine ⟨γ ^ (Nat.gcdA n (Nat.card Z) * s'), ?_⟩
  have hs2 : s = (Nat.gcdA n (Nat.card Z) * s') * (n : ℤ) +
      ((Nat.card Z : ℕ) : ℤ) * (Nat.gcdB n (Nat.card Z) * s') := by
    rw [hs', hbez]
    ring
  rw [← zpow_natCast, ← zpow_mul, ← hs, hs2, zpow_add, zpow_mul γ ((Nat.card Z : ℕ) : ℤ),
    zpow_natCast, ← hord, pow_orderOf_eq_one, one_zpow, mul_one]

end Arith

section Equiv

variable {X Y : Type*} [Group X] [Group Y] {p : ℕ}

theorem OutPNice.of_mulEquiv (e : X ≃* Y) (h : OutPNice p Y) : OutPNice p X := by
  obtain ⟨D, E, hID, hD2, hpE, hD3, hD4⟩ := h
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  have hinner : (Inn X).map φ.toMonoidHom = Inn Y :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hmem : ∀ α : MulAut X, α ∈ Inn X ↔ φ α ∈ Inn Y := by
    intro α
    rw [← hinner]
    constructor
    · exact fun h => ⟨α, h, rfl⟩
    · rintro ⟨β, hβ, hβα⟩
      have : β = α := φ.injective hβα
      exact this ▸ hβ
  refine ⟨D.comap φ.toMonoidHom, E.comap φ.toMonoidHom, fun α hα => hID ((hmem α).mp hα), ?_,
    ?_, ?_, ?_⟩
  · intro δ hδ k hk
    rw [hmem]
    refine hD2 (φ δ) hδ k ?_
    rw [← map_pow]
    exact (hmem _).mp hk
  · intro α ⟨k, hk⟩
    show φ α ∈ E
    exact hpE (φ α) ⟨k, by rw [← map_pow]; exact hk⟩
  · intro γ α hα
    show φ ⁅γ, α⁆ ∈ D
    rw [map_commutatorElement]
    exact hD3 (φ γ) (φ α) hα
  · intro α hαE β hβE ⟨k, hk⟩ ⟨l, hl⟩
    have hk' : (φ α) ^ (p ^ k) ∈ D := by rw [← map_pow]; exact hk
    have hl' : (φ β) ^ (p ^ l) ∈ D := by rw [← map_pow]; exact hl
    rcases hD4 (φ α) hαE (φ β) hβE ⟨k, hk'⟩ ⟨l, hl'⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine Or.inl ⟨m, ?_⟩
      show φ (α * β ^ m) ∈ D
      rw [map_mul, map_zpow]
      exact hm
    · refine Or.inr ⟨m, ?_⟩
      show φ (β * α ^ m) ∈ D
      rw [map_mul, map_zpow]
      exact hm

theorem OutPChain.of_mulEquiv (e : X ≃* Y) (h : OutPChain p Y) : OutPChain p X := by
  obtain ⟨D, E, hID, hD2, hpE, hD4⟩ := h
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  have hinner : (Inn X).map φ.toMonoidHom = Inn Y :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hmem : ∀ α : MulAut X, α ∈ Inn X ↔ φ α ∈ Inn Y := by
    intro α
    rw [← hinner]
    constructor
    · exact fun h => ⟨α, h, rfl⟩
    · rintro ⟨β, hβ, hβα⟩
      have : β = α := φ.injective hβα
      exact this ▸ hβ
  refine ⟨D.comap φ.toMonoidHom, E.comap φ.toMonoidHom, fun α hα => hID ((hmem α).mp hα), ?_,
    ?_, ?_⟩
  · intro δ hδ k hk
    rw [hmem]
    refine hD2 (φ δ) hδ k ?_
    rw [← map_pow]
    exact (hmem _).mp hk
  · intro α ⟨k, hk⟩
    show φ α ∈ E
    exact hpE (φ α) ⟨k, by rw [← map_pow]; exact hk⟩
  · intro α hαE β hβE ⟨k, hk⟩ ⟨l, hl⟩
    have hk' : (φ α) ^ (p ^ k) ∈ D := by rw [← map_pow]; exact hk
    have hl' : (φ β) ^ (p ^ l) ∈ D := by rw [← map_pow]; exact hl
    rcases hD4 (φ α) hαE (φ β) hβE ⟨k, hk'⟩ ⟨l, hl'⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine Or.inl ⟨m, ?_⟩
      show φ (α * β ^ m) ∈ D
      rw [map_mul, map_zpow]
      exact hm
    · refine Or.inr ⟨m, ?_⟩
      show φ (β * α ^ m) ∈ D
      rw [map_mul, map_zpow]
      exact hm

end Equiv

section Transfer

variable {G : Type} [Group G]

theorem mem_sup_centralizer_iff (J : Subgroup G) {g : G} :
    g ∈ J ⊔ centralizer (J : Set G) ↔ ∃ j ∈ J, ∃ z ∈ centralizer (J : Set G), g = j * z := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ j ∈ J, ∃ z ∈ centralizer (J : Set G), g = j * z}
        one_mem' := ⟨1, J.one_mem, 1, Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨j, hj, z, hz, rfl⟩ ⟨j', hj', z', hz', rfl⟩
          refine ⟨j * j', J.mul_mem hj hj', z * z', Subgroup.mul_mem _ hz hz', ?_⟩
          have hc : z * j' = j' * z := (mem_centralizer_iff.mp hz) j' hj' |>.symm
          calc j * z * (j' * z') = j * (z * j') * z' := by group
            _ = j * (j' * z) * z' := by rw [hc]
            _ = j * j' * (z * z') := by group
        inv_mem' := by
          rintro _ ⟨j, hj, z, hz, rfl⟩
          refine ⟨j⁻¹, J.inv_mem hj, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
          have hc : z * j = j * z := (mem_centralizer_iff.mp hz) j hj |>.symm
          have hc' : z⁻¹ * j⁻¹ = j⁻¹ * z⁻¹ := by
            have := congrArg (·⁻¹) hc
            simpa [mul_inv_rev] using this.symm
          calc (j * z)⁻¹ = z⁻¹ * j⁻¹ := by group
            _ = j⁻¹ * z⁻¹ := hc' }
    have hle : J ⊔ centralizer (J : Set G) ≤ S :=
      sup_le (fun j hj => ⟨j, hj, 1, Subgroup.one_mem _, by simp⟩)
        (fun z hz => ⟨1, J.one_mem, z, hz, by simp⟩)
    exact hle hg
  · rintro ⟨j, hj, z, hz, rfl⟩
    exact Subgroup.mul_mem _ (mem_sup_left hj) (mem_sup_right hz)

noncomputable def actionOnQuot (J : Subgroup G) :
    normalizer (J : Set G) →* MulAut (J ⧸ Subgroup.center J) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J).comp
    J.normalizerMonoidHom

theorem actionOnQuot_mem_inner_iff (J : Subgroup G) [Group.IsPerfect J] {g : G}
    (hg : g ∈ normalizer (J : Set G)) :
    actionOnQuot J ⟨g, hg⟩ ∈ Inn (J ⧸ Subgroup.center J) ↔ g ∈ J ⊔ centralizer (J : Set G) := by
  rw [mem_sup_centralizer_iff]
  constructor
  · intro h
    have hα : J.normalizerMonoidHom ⟨g, hg⟩ ∈ Inn J := by
      have h1 : (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J)
          (J.normalizerMonoidHom ⟨g, hg⟩) ∈ Inn (J ⧸ Subgroup.center J) := h
      have h2 : CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom J
          (QuotientGroup.mk (J.normalizerMonoidHom ⟨g, hg⟩)) = 1 := by
        rw [CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom,
          QuotientGroup.map_mk]
        exact (QuotientGroup.eq_one_iff _).mpr h1
      have h3 := CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective J
        (h2.trans (map_one _).symm)
      exact (QuotientGroup.eq_one_iff _).mp h3
    obtain ⟨j, hj⟩ := hα
    refine ⟨j, j.2, (j : G)⁻¹ * g, ?_, by simp⟩
    rw [mem_centralizer_iff]
    intro y hy
    have h4 := congrArg (fun f : MulAut J => ((f ⟨y, hy⟩ : J) : G)) hj
    rw [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h4
    have h5 : (j : G) * y * (j : G)⁻¹ = g * y * g⁻¹ := by
      simpa using h4
    calc y * ((j : G)⁻¹ * g) = (j : G)⁻¹ * ((j : G) * y * (j : G)⁻¹) * g := by group
      _ = (j : G)⁻¹ * (g * y * g⁻¹) * g := by rw [h5]
      _ = (j : G)⁻¹ * g * y := by group
  · rintro ⟨j, hj, z, hz, rfl⟩
    have hjN : j ∈ normalizer (J : Set G) := Subgroup.le_normalizer hj
    have hα : J.normalizerMonoidHom ⟨j * z, hg⟩ = MulAut.conj (⟨j, hj⟩ : J) := by
      ext y
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      have hzy : z * (y : G) = (y : G) * z := (mem_centralizer_iff.mp hz) y y.2 |>.symm
      show j * z * y * (j * z)⁻¹ = j * y * j⁻¹
      calc j * z * (y : G) * (j * z)⁻¹ = j * (z * (y : G)) * z⁻¹ * j⁻¹ := by group
        _ = j * ((y : G) * z) * z⁻¹ * j⁻¹ := by rw [hzy]
        _ = j * y * j⁻¹ := by group
    show (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J)
      (J.normalizerMonoidHom ⟨j * z, hg⟩) ∈ Inn (J ⧸ Subgroup.center J)
    rw [hα, CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj]
    exact ⟨_, rfl⟩

variable {p : ℕ}

theorem commuting_pElements_of_outPChain (J : Subgroup G) [Group.IsPerfect J]
    (h : OutPChain p (J ⧸ Subgroup.center J)) {u v : G} (hu : u ∈ normalizer (J : Set G))
    (hv : v ∈ normalizer (J : Set G)) (huv : u * v = v * u) (hup : ∃ k : ℕ, orderOf u = p ^ k)
    (hvp : ∃ k : ℕ, orderOf v = p ^ k) :
    u ∈ zpowers v ⊔ (J ⊔ centralizer (J : Set G)) ∨
      v ∈ zpowers u ⊔ (J ⊔ centralizer (J : Set G)) := by
  obtain ⟨k, hk⟩ := hup
  obtain ⟨l, hl⟩ := hvp
  set ρ := actionOnQuot J with hρ
  have hρk : (ρ ⟨u, hu⟩) ^ (p ^ k) ∈ Inn (J ⧸ Subgroup.center J) := by
    rw [← map_pow]
    have : (⟨u, hu⟩ : normalizer (J : Set G)) ^ (p ^ k) = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hk, pow_orderOf_eq_one]
    rw [this, map_one]
    exact (Inn _).one_mem
  have hρl : (ρ ⟨v, hv⟩) ^ (p ^ l) ∈ Inn (J ⧸ Subgroup.center J) := by
    rw [← map_pow]
    have : (⟨v, hv⟩ : normalizer (J : Set G)) ^ (p ^ l) = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hl, pow_orderOf_eq_one]
    rw [this, map_one]
    exact (Inn _).one_mem
  have hc : ρ ⟨u, hu⟩ * ρ ⟨v, hv⟩ = ρ ⟨v, hv⟩ * ρ ⟨u, hu⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext huv
  have hmem : ∀ {a b : G} (ha : a ∈ normalizer (J : Set G)) (hb : b ∈ normalizer (J : Set G))
      (m : ℤ), ρ ⟨a, ha⟩ * (ρ ⟨b, hb⟩) ^ m ∈ Inn (J ⧸ Subgroup.center J) →
      a * b ^ m ∈ J ⊔ centralizer (J : Set G) := by
    intro a b ha hb m hm
    have hbm : b ^ m ∈ normalizer (J : Set G) := (normalizer (J : Set G)).zpow_mem hb m
    have : ρ ⟨a * b ^ m, (normalizer (J : Set G)).mul_mem ha hbm⟩ =
        ρ ⟨a, ha⟩ * (ρ ⟨b, hb⟩) ^ m := by
      rw [← map_zpow, ← map_mul]
      rfl
    exact (actionOnQuot_mem_inner_iff J _).mp (this ▸ hm)
  rcases h.comparable hc hρk hρl with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    have h1 := hmem hu hv m hm
    have : u = (u * v ^ m) * (v ^ (-m)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_right h1) (mem_sup_left (zpow_mem (mem_zpowers v) _))
  · right
    have h1 := hmem hv hu m hm
    have : v = (v * u ^ m) * (u ^ (-m)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_right h1) (mem_sup_left (zpow_mem (mem_zpowers u) _))

theorem normalizer_power_of_outPNice (hp : p.Prime) (J : Subgroup G) [Group.IsPerfect J]
    (h : OutPNice p (J ⧸ Subgroup.center J)) {a x : G} (ha : a ∈ normalizer (J : Set G))
    (hx : x ∈ normalizer (J : Set G)) (hap : a ^ p ∈ J ⊔ centralizer (J : Set G))
    (ha1 : a ∉ J ⊔ centralizer (J : Set G)) {m : ℤ}
    (hm : x * a * x⁻¹ * a ^ (-m) ∈ J ⊔ centralizer (J : Set G)) : (p : ℤ) ∣ m - 1 := by
  set ρ := actionOnQuot J with hρ
  have hmem : ∀ {a : G} (ha : a ∈ normalizer (J : Set G)),
      ρ ⟨a, ha⟩ ∈ Inn (J ⧸ Subgroup.center J) ↔ a ∈ J ⊔ centralizer (J : Set G) :=
    fun ha => actionOnQuot_mem_inner_iff J ha
  refine h.dvd_sub_one hp (α := ρ ⟨a, ha⟩) (γ := ρ ⟨x, hx⟩) ?_ ?_ ?_
  · have : ρ ⟨a, ha⟩ ^ p = ρ ⟨a ^ p, (normalizer (J : Set G)).pow_mem ha p⟩ := by
      rw [← map_pow]
      rfl
    rw [this, hmem]
    exact hap
  · rw [hmem]
    exact ha1
  · have hxinv : x⁻¹ ∈ normalizer (J : Set G) := (normalizer (J : Set G)).inv_mem hx
    have hapm : a ^ (-m) ∈ normalizer (J : Set G) := (normalizer (J : Set G)).zpow_mem ha _
    have e : ρ ⟨x, hx⟩ * ρ ⟨a, ha⟩ * (ρ ⟨x, hx⟩)⁻¹ * (ρ ⟨a, ha⟩) ^ (-m) =
        ρ ⟨x * a * x⁻¹ * a ^ (-m),
          (normalizer (J : Set G)).mul_mem ((normalizer (J : Set G)).mul_mem
            ((normalizer (J : Set G)).mul_mem hx ha) hxinv) hapm⟩ := by
      rw [show (⟨x * a * x⁻¹ * a ^ (-m), _⟩ : normalizer (J : Set G)) =
          ⟨x, hx⟩ * ⟨a, ha⟩ * ⟨x, hx⟩⁻¹ * ⟨a, ha⟩ ^ (-m) from rfl, map_mul, map_mul, map_mul,
        map_zpow, map_inv]
    rw [e, hmem]
    exact hm

theorem normalizer_power_of_outPCentral (hp : p.Prime) (J : Subgroup G) [Group.IsPerfect J]
    (h : OutPCentral p (J ⧸ Subgroup.center J)) {a x : G} (ha : a ∈ normalizer (J : Set G))
    (hx : x ∈ normalizer (J : Set G)) (hap : a ^ p ∈ J ⊔ centralizer (J : Set G))
    (ha1 : a ∉ J ⊔ centralizer (J : Set G)) {m : ℤ}
    (hm : x * a * x⁻¹ * a ^ (-m) ∈ J ⊔ centralizer (J : Set G)) : (p : ℤ) ∣ m - 1 := by
  set ρ := actionOnQuot J with hρ
  have hmem : ∀ {a : G} (ha : a ∈ normalizer (J : Set G)),
      ρ ⟨a, ha⟩ ∈ Inn (J ⧸ Subgroup.center J) ↔ a ∈ J ⊔ centralizer (J : Set G) :=
    fun ha => actionOnQuot_mem_inner_iff J ha
  refine h.dvd_sub_one hp (α := ρ ⟨a, ha⟩) (γ := ρ ⟨x, hx⟩) ?_ ?_ ?_
  · have : ρ ⟨a, ha⟩ ^ p = ρ ⟨a ^ p, (normalizer (J : Set G)).pow_mem ha p⟩ := by
      rw [← map_pow]
      rfl
    rw [this, hmem]
    exact hap
  · rw [hmem]
    exact ha1
  · have hxinv : x⁻¹ ∈ normalizer (J : Set G) := (normalizer (J : Set G)).inv_mem hx
    have hapm : a ^ (-m) ∈ normalizer (J : Set G) := (normalizer (J : Set G)).zpow_mem ha _
    have e : ρ ⟨x, hx⟩ * ρ ⟨a, ha⟩ * (ρ ⟨x, hx⟩)⁻¹ * (ρ ⟨a, ha⟩) ^ (-m) =
        ρ ⟨x * a * x⁻¹ * a ^ (-m),
          (normalizer (J : Set G)).mul_mem ((normalizer (J : Set G)).mul_mem
            ((normalizer (J : Set G)).mul_mem hx ha) hxinv) hapm⟩ := by
      rw [show (⟨x * a * x⁻¹ * a ^ (-m), _⟩ : normalizer (J : Set G)) =
          ⟨x, hx⟩ * ⟨a, ha⟩ * ⟨x, hx⟩⁻¹ * ⟨a, ha⟩ ^ (-m) from rfl, map_mul, map_mul, map_mul,
        map_zpow, map_inv]
    rw [e, hmem]
    exact hm

end Transfer

end CFSG.RankThree.PartOne.OutStructure
