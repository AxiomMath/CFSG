module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.SzN28P

open Equiv

theorem card_le_pow_of_isPGroup {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    {X : Subgroup Γ} (hX : IsPGroup p X) :
    Nat.card X ≤ p ^ (Nat.card Γ).factorization p := by
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  have h1 : Nat.card X ≤ Nat.card Q := Subgroup.card_le_of_le hQ
  rwa [Sylow.card_eq_multiplicity] at h1

theorem card_lt_pow_of_abelian_of_nonabelian {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] {P X : Subgroup Γ} (hP : IsPGroup p P) (hPn : ¬ IsMulCommutative ↥P)
    (hX : IsPGroup p X) (hXc : IsMulCommutative ↥X) :
    Nat.card X < p ^ (Nat.card Γ).factorization p := by
  by_contra hge
  push Not at hge
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  have hcardQ : Nat.card Q = p ^ (Nat.card Γ).factorization p := Sylow.card_eq_multiplicity Q
  have hXeq : X = Q := Subgroup.eq_of_le_of_card_ge hXQ (by rw [hcardQ]; exact hge)
  obtain ⟨Q', hPQ'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q Q'
  apply hPn
  have key : ∀ y : Γ, y ∈ (Q' : Subgroup Γ) → ∃ s ∈ (Q : Subgroup Γ), y = g * s * g⁻¹ := by
    intro y hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨s, hs, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨s, hs, hsa⟩ := key a (hPQ' a.2)
  obtain ⟨t, ht, htb⟩ := key b (hPQ' b.2)
  have hst : s * t = t * s := by
    have := hXc.is_comm.comm (⟨s, hXeq ▸ hs⟩ : X) (⟨t, hXeq ▸ ht⟩ : X)
    exact congrArg Subtype.val this
  apply Subtype.ext
  show (a : Γ) * b = b * a
  rw [hsa, htb]
  calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
    _ = g * (t * s) * g⁻¹ := by rw [hst]
    _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group

theorem isPGroup_two_of_sq_eq_one {Γ : Type*} [Group Γ] {X : Subgroup Γ}
    (hX : ∀ x ∈ X, x * x = 1) : IsPGroup 2 X := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := hX x x.2
  simpa [pow_two] using this

theorem isMulCommutative_of_comm {Γ : Type*} [Group Γ] {X : Subgroup Γ}
    (h : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : IsMulCommutative ↥X :=
  ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

theorem card_le_of_elemAbelian {Γ : Type*} [Group Γ] [Finite Γ] {P X : Subgroup Γ}
    (hP : IsPGroup 2 P) (hPn : ¬ IsMulCommutative ↥P) (hX2 : ∀ x ∈ X, x * x = 1)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {m : ℕ}
    (hm : (Nat.card Γ).factorization 2 = m + 1) : Nat.card X ≤ 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXp := isPGroup_two_of_sq_eq_one hX2
  have hlt := card_lt_pow_of_abelian_of_nonabelian hP hPn hXp (isMulCommutative_of_comm hXc)
  rw [hm] at hlt
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  rw [hn] at hlt ⊢
  have : n < m + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

def finsetSubgroup {Γ : Type*} [Group Γ] (F : Finset Γ) (h1 : (1 : Γ) ∈ F)
    (hm : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) (hi : ∀ x ∈ F, x⁻¹ ∈ F) : Subgroup Γ where
  carrier := (F : Set Γ)
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha

theorem card_finsetSubgroup {Γ : Type*} [Group Γ] (F : Finset Γ) (h1 : (1 : Γ) ∈ F)
    (hm : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) (hi : ∀ x ∈ F, x⁻¹ ∈ F) :
    Nat.card (finsetSubgroup F h1 hm hi) = F.card := by
  have : Nat.card (finsetSubgroup F h1 hm hi) = Nat.card ((F : Set Γ)) := rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

def d8Set (n : ℕ) [NeZero n] (t : Perm (Fin n)) : Finset (Perm (Fin n)) :=
  let r : Perm (Fin n) := (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) * t
  let s : Perm (Fin n) := Equiv.swap 0 2 * t
  {1, r, r * r, r * r * r, s, r * s, r * r * s, r * r * r * s}

theorem d8Set5_mul : ∀ x ∈ d8Set 5 1, ∀ y ∈ d8Set 5 1, x * y ∈ d8Set 5 1 := by decide +kernel

theorem d8Set5_inv : ∀ x ∈ d8Set 5 1, x⁻¹ ∈ d8Set 5 1 := by decide +kernel

theorem d8Set5_card : (d8Set 5 1).card = 8 := by decide +kernel

def d8Sub5 : Subgroup (Perm (Fin 5)) :=
  finsetSubgroup (d8Set 5 1) (by decide +kernel) d8Set5_mul d8Set5_inv

theorem d8Sub5_card : Nat.card d8Sub5 = 8 :=
  (card_finsetSubgroup _ _ _ _).trans d8Set5_card

theorem d8Sub5_isPGroup : IsPGroup 2 d8Sub5 :=
  IsPGroup.of_card (n := 3) (by rw [d8Sub5_card]; norm_num)

theorem d8Sub5_nonabelian : ¬ IsMulCommutative ↥d8Sub5 := by
  intro h
  have h1 : (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 : Perm (Fin 5)) ∈ d8Sub5 := by
    show _ ∈ (d8Set 5 1 : Set (Perm (Fin 5)))
    simp only [Finset.mem_coe]
    decide +kernel
  have h2 : (Equiv.swap 0 2 : Perm (Fin 5)) ∈ d8Sub5 := by
    show _ ∈ (d8Set 5 1 : Set (Perm (Fin 5)))
    simp only [Finset.mem_coe]
    decide +kernel
  have h3 := congrArg Subtype.val (h.is_comm.comm ⟨_, h1⟩ ⟨_, h2⟩)
  simp only [Subgroup.coe_mul] at h3
  revert h3
  decide +kernel

theorem d8Set6_mul : ∀ x ∈ d8Set 6 (Equiv.swap 4 5), ∀ y ∈ d8Set 6 (Equiv.swap 4 5),
    x * y ∈ d8Set 6 (Equiv.swap 4 5) := by decide +kernel

theorem d8Set6_inv : ∀ x ∈ d8Set 6 (Equiv.swap 4 5), x⁻¹ ∈ d8Set 6 (Equiv.swap 4 5) := by
  decide +kernel

theorem d8Set6_card : (d8Set 6 (Equiv.swap 4 5)).card = 8 := by decide +kernel

theorem d8Set6_even : ∀ x ∈ d8Set 6 (Equiv.swap 4 5), Equiv.Perm.sign x = 1 := by
  decide +kernel

def d8Sub6 : Subgroup (Perm (Fin 6)) :=
  finsetSubgroup (d8Set 6 (Equiv.swap 4 5)) (by decide +kernel) d8Set6_mul d8Set6_inv

theorem d8Sub6_le : d8Sub6 ≤ alternatingGroup (Fin 6) := fun x hx => by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact d8Set6_even x hx

def d8Alt6 : Subgroup ↥(alternatingGroup (Fin 6)) :=
  d8Sub6.subgroupOf (alternatingGroup (Fin 6))

theorem d8Alt6_card : Nat.card d8Alt6 = 8 := by
  rw [d8Alt6, Nat.card_congr (Subgroup.subgroupOfEquivOfLe d8Sub6_le).toEquiv]
  exact (card_finsetSubgroup _ _ _ _).trans d8Set6_card

theorem d8Alt6_isPGroup : IsPGroup 2 d8Alt6 :=
  IsPGroup.of_card (n := 3) (by rw [d8Alt6_card]; norm_num)

theorem d8Alt6_nonabelian : ¬ IsMulCommutative ↥d8Alt6 := by
  intro h
  have hr : ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) * Equiv.swap 4 5 :
      Perm (Fin 6)) ∈ d8Sub6 := by
    show _ ∈ (d8Set 6 (Equiv.swap 4 5) : Set (Perm (Fin 6)))
    simp only [Finset.mem_coe]
    decide +kernel
  have hs : (Equiv.swap 0 2 * Equiv.swap 4 5 : Perm (Fin 6)) ∈ d8Sub6 := by
    show _ ∈ (d8Set 6 (Equiv.swap 4 5) : Set (Perm (Fin 6)))
    simp only [Finset.mem_coe]
    decide +kernel
  have h1 : (⟨_, d8Sub6_le hr⟩ : ↥(alternatingGroup (Fin 6))) ∈ d8Alt6 := hr
  have h2 : (⟨_, d8Sub6_le hs⟩ : ↥(alternatingGroup (Fin 6))) ∈ d8Alt6 := hs
  have h3 := congrArg (fun z : d8Alt6 => ((z : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)))
    (h.is_comm.comm ⟨_, h1⟩ ⟨_, h2⟩)
  simp only [Subgroup.coe_mul] at h3
  revert h3
  decide +kernel

theorem map_nonabelian {Q Γ : Type*} [Group Q] [Group Γ] (f : Q →* Γ)
    (hf : Function.Injective f) {P : Subgroup Q} (hP : IsPGroup 2 P)
    (hPn : ¬ IsMulCommutative ↥P) :
    IsPGroup 2 (P.map f) ∧ ¬ IsMulCommutative ↥(P.map f) := by
  refine ⟨hP.of_surjective (f.subgroupMap P) (f.subgroupMap_surjective P), fun h => hPn ?_⟩
  refine ⟨⟨fun a b => ?_⟩⟩
  have h3 := congrArg Subtype.val
    (h.is_comm.comm ⟨f a, ⟨a, a.2, rfl⟩⟩ ⟨f b, ⟨b, b.2, rfl⟩⟩)
  apply Subtype.ext
  apply hf
  simpa using h3

theorem factorization_two_720 : Nat.factorization 720 2 = 4 := by
  rw [Nat.factorization_def _ Nat.prime_two]; decide +kernel

theorem factorization_two_360 : Nat.factorization 360 2 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_two]; decide +kernel

theorem factorization_two_2160 : Nat.factorization 2160 2 = 4 := by
  rw [Nat.factorization_def _ Nat.prime_two]; decide +kernel

theorem card_le_eight_of_S3S5 {Γ : Type*} [Group Γ] [Finite Γ]
    (e : Γ ≃* Perm (Fin 3) × Perm (Fin 5)) {X : Subgroup Γ} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : Nat.card X ≤ 8 := by
  have hcard : Nat.card Γ = 720 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm]
    simp [Nat.factorial]
  have hm : (Nat.card Γ).factorization 2 = 3 + 1 := by
    rw [hcard, factorization_two_720]
  let f : Perm (Fin 5) →* Γ := e.symm.toMonoidHom.comp (MonoidHom.inr _ _)
  have hf : Function.Injective f := e.symm.injective.comp (fun a b hab => by
    simpa [MonoidHom.inr] using congrArg Prod.snd hab)
  obtain ⟨hP, hPn⟩ := map_nonabelian f hf d8Sub5_isPGroup d8Sub5_nonabelian
  have := card_le_of_elemAbelian hP hPn hX2 hXc hm
  simpa using this

theorem card_le_eight_of_S3A5 {Γ : Type*} [Group Γ] [Finite Γ]
    (e : Γ ≃* Perm (Fin 3) × ↥(alternatingGroup (Fin 5))) {X : Subgroup Γ}
    (hX2 : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hcard : Nat.card Γ = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, hA5]
    simp [Nat.factorial]
  have := card_le_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hX2)
  rw [hcard, factorization_two_360] at this
  simpa using this

theorem card_le_eight_of_A6 {Γ : Type*} [Group Γ] [Finite Γ] (hcard : Nat.card Γ = 2160)
    (N : Subgroup Γ) (e : ↥N ≃* ↥(alternatingGroup (Fin 6))) {X : Subgroup Γ}
    (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X ≤ 8 := by
  have hm : (Nat.card Γ).factorization 2 = 3 + 1 := by
    rw [hcard, factorization_two_2160]
  let f : ↥(alternatingGroup (Fin 6)) →* Γ := N.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp e.symm.injective
  obtain ⟨hP, hPn⟩ := map_nonabelian f hf d8Alt6_isPGroup d8Alt6_nonabelian
  have := card_le_of_elemAbelian hP hPn hX2 hXc hm
  simpa using this

end CFSG.Quasithin.SzN28P
