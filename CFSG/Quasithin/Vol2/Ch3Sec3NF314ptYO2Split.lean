module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.NF314pt

section Split

variable {Q : Type} [Group Q] {A A' : Subgroup Q}

lemma yo2_commute (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (m : ↥A) (n : ↥A') :
    Commute (A.subtype m) (A'.subtype n) :=
  hc m m.2 n n.2

@[expose] noncomputable def yo2_prod (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) :
    ↥A × ↥A' →* Q :=
  A.subtype.noncommCoprod A'.subtype (yo2_commute hc)

@[expose] def yo2_fst : ↥A × ↥A' →* Q :=
  A.subtype.comp (MonoidHom.fst _ _)

@[expose] def yo2_snd : ↥A × ↥A' →* Q :=
  A'.subtype.comp (MonoidHom.snd _ _)

lemma yo2_fst_apply (p : ↥A × ↥A') : yo2_fst p = (p.1 : Q) := rfl

lemma yo2_snd_apply (p : ↥A × ↥A') : yo2_snd p = (p.2 : Q) := rfl

lemma yo2_prod_eq (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (p : ↥A × ↥A') :
    yo2_prod hc p = yo2_fst p * yo2_snd p := rfl

lemma yo2_prod_injective (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥) :
    Function.Injective (yo2_prod hc) := by
  rw [yo2_prod, MonoidHom.noncommCoprod_injective]
  refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
  exact hi

lemma yo2_prod_range (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) :
    (yo2_prod hc).range = A ⊔ A' := by
  rw [yo2_prod, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

end Split

theorem yo2_split_nine {Q : Type} [Group Q] [Finite Q] {A A' P : Subgroup Q}
    (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥)
    (hcyc : ∀ B : Subgroup Q, B ≤ A → IsPGroup 3 B → IsCyclic B)
    (hcyc' : ∀ B : Subgroup Q, B ≤ A' → IsPGroup 3 B → IsCyclic B)
    (hPA : P ≤ A ⊔ A') (hP9 : Nat.card P = 9) (hP3 : ∀ y ∈ P, y ^ 3 = 1) :
    ∃ x₁ ∈ P ⊓ A, ∃ x₂ ∈ P ⊓ A', orderOf x₁ = 3 ∧ orderOf x₂ = 3 ∧
      ∀ y ∈ P, ∃ i j : ℕ, y = x₁ ^ i * x₂ ^ j := by
  have hinj : Function.Injective (yo2_prod hc) := yo2_prod_injective hc hi
  have hrange : (yo2_prod hc).range = A ⊔ A' := yo2_prod_range hc
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup (↥A × ↥A'), P' = P.comap (yo2_prod hc) := ⟨_, rfl⟩
  have hmemP' : ∀ p : ↥A × ↥A', p ∈ P' ↔ yo2_prod hc p ∈ P := fun p => by
    rw [hP', Subgroup.mem_comap]
  have hPmap : P'.map (yo2_prod hc) = P := by
    rw [hP', Subgroup.map_comap_eq, hrange, inf_eq_right.mpr hPA]
  have hP'card : Nat.card P' = 9 := by
    have e := Nat.card_congr (Subgroup.equivMapOfInjective P' (yo2_prod hc) hinj).toEquiv
    rw [hPmap, hP9] at e
    exact e
  have hcube : ∀ p ∈ P', p ^ 3 = 1 := by
    intro p hp
    apply hinj
    rw [map_pow, map_one]
    exact hP3 _ ((hmemP' p).mp hp)
  obtain ⟨R₁, hR₁⟩ : ∃ R : Subgroup Q, R = P'.map yo2_fst := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R : Subgroup Q, R = P'.map yo2_snd := ⟨_, rfl⟩
  have hmemR₁ : ∀ x, x ∈ R₁ ↔ ∃ p ∈ P', yo2_fst p = x := fun x => by
    rw [hR₁, Subgroup.mem_map]
  have hmemR₂ : ∀ x, x ∈ R₂ ↔ ∃ p ∈ P', yo2_snd p = x := fun x => by
    rw [hR₂, Subgroup.mem_map]
  have hR₁A : R₁ ≤ A := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := (hmemR₁ x).mp hx
    rw [yo2_fst_apply]
    exact p.1.2
  have hR₂A : R₂ ≤ A' := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := (hmemR₂ x).mp hx
    rw [yo2_snd_apply]
    exact p.2.2
  have hR₁3 : ∀ x ∈ R₁, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (hmemR₁ x).mp hx
    rw [← map_pow, hcube p hp, map_one]
  have hR₂3 : ∀ x ∈ R₂, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (hmemR₂ x).mp hx
    rw [← map_pow, hcube p hp, map_one]
  have hR₁P : IsPGroup 3 R₁ := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hR₁3 g g.2)⟩
  have hR₂P : IsPGroup 3 R₂ := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hR₂3 g g.2)⟩
  have hR₁c : IsCyclic ↥R₁ := hcyc R₁ hR₁A hR₁P
  have hR₂c : IsCyclic ↥R₂ := hcyc' R₂ hR₂A hR₂P
  have hR₁card : Nat.card R₁ ≤ 3 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥R₁)
    rw [← hg]
    exact orderOf_le_of_pow_eq_one (by norm_num) (Subtype.ext (by simpa using hR₁3 g g.2))
  have hR₂card : Nat.card R₂ ≤ 3 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥R₂)
    rw [← hg]
    exact orderOf_le_of_pow_eq_one (by norm_num) (Subtype.ext (by simpa using hR₂3 g g.2))
  let Θ : ↥P' → ↥R₁ × ↥R₂ := fun p =>
    (⟨yo2_fst (p : ↥A × ↥A'), (hmemR₁ _).mpr ⟨(p : ↥A × ↥A'), p.2, rfl⟩⟩,
      ⟨yo2_snd (p : ↥A × ↥A'), (hmemR₂ _).mpr ⟨(p : ↥A × ↥A'), p.2, rfl⟩⟩)
  have hΘinj : Function.Injective Θ := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ h
    have h1 : yo2_fst p = yo2_fst q := congrArg (fun z : ↥R₁ × ↥R₂ => (z.1 : Q)) h
    have h2 : yo2_snd p = yo2_snd q := congrArg (fun z : ↥R₁ × ↥R₂ => (z.2 : Q)) h
    exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
  have hprodcard : Nat.card P' ≤ Nat.card R₁ * Nat.card R₂ := by
    have := Nat.card_le_card_of_injective Θ hΘinj
    rwa [Nat.card_prod] at this
  have hR₁eq : Nat.card R₁ = 3 := by
    by_contra hne
    have hlt : Nat.card R₁ ≤ 2 := by omega
    have : Nat.card R₁ * Nat.card R₂ ≤ 2 * 3 := Nat.mul_le_mul hlt hR₂card
    omega
  have hR₂eq : Nat.card R₂ = 3 := by
    by_contra hne
    have hlt : Nat.card R₂ ≤ 2 := by omega
    have : Nat.card R₁ * Nat.card R₂ ≤ 3 * 2 := Nat.mul_le_mul hR₁card hlt
    omega
  have hΘbij : Function.Bijective Θ :=
    hΘinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hR₁eq, hR₂eq, hP'card] <;> norm_num)
  obtain ⟨g₁, hg₁⟩ := IsCyclic.exists_monoid_generator (α := ↥R₁)
  obtain ⟨g₂, hg₂⟩ := IsCyclic.exists_monoid_generator (α := ↥R₂)
  have hord₁ : orderOf g₁ = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (fun y => mem_powers_iff_mem_zpowers.mp (hg₁ y)),
      hR₁eq]
  have hord₂ : orderOf g₂ = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (fun y => mem_powers_iff_mem_zpowers.mp (hg₂ y)),
      hR₂eq]
  obtain ⟨⟨q₁, hq₁⟩, hq₁Θ⟩ := hΘbij.2 (g₁, 1)
  obtain ⟨⟨q₂, hq₂⟩, hq₂Θ⟩ := hΘbij.2 (1, g₂)
  have e₁ : yo2_fst q₁ = (g₁ : Q) := congrArg (fun z : ↥R₁ × ↥R₂ => (z.1 : Q)) hq₁Θ
  have e₁' : yo2_snd q₁ = 1 := congrArg (fun z : ↥R₁ × ↥R₂ => (z.2 : Q)) hq₁Θ
  have e₂ : yo2_fst q₂ = 1 := congrArg (fun z : ↥R₁ × ↥R₂ => (z.1 : Q)) hq₂Θ
  have e₂' : yo2_snd q₂ = (g₂ : Q) := congrArg (fun z : ↥R₁ × ↥R₂ => (z.2 : Q)) hq₂Θ
  have hx₁P : (g₁ : Q) ∈ P := by
    have h := (hmemP' q₁).mp hq₁
    rwa [yo2_prod_eq, e₁, e₁', mul_one] at h
  have hx₂P : (g₂ : Q) ∈ P := by
    have h := (hmemP' q₂).mp hq₂
    rwa [yo2_prod_eq, e₂, e₂', one_mul] at h
  refine ⟨(g₁ : Q), Subgroup.mem_inf.mpr ⟨hx₁P, hR₁A g₁.2⟩, (g₂ : Q),
    Subgroup.mem_inf.mpr ⟨hx₂P, hR₂A g₂.2⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hord₁]
  · rw [Subgroup.orderOf_coe, hord₂]
  · intro y hy
    have hyr : y ∈ (yo2_prod hc).range := by
      rw [hrange]
      exact hPA hy
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hyr
    have hqP' : q ∈ P' := (hmemP' q).mpr (by rw [hq]; exact hy)
    obtain ⟨i, hi⟩ :=
      (Submonoid.mem_powers_iff _ _).mp (hg₁ ⟨yo2_fst q, (hmemR₁ _).mpr ⟨q, hqP', rfl⟩⟩)
    obtain ⟨j, hj⟩ :=
      (Submonoid.mem_powers_iff _ _).mp (hg₂ ⟨yo2_snd q, (hmemR₂ _).mpr ⟨q, hqP', rfl⟩⟩)
    have ei : (g₁ : Q) ^ i = yo2_fst q := by
      have := congrArg Subtype.val hi
      simpa using this
    have ej : (g₂ : Q) ^ j = yo2_snd q := by
      have := congrArg Subtype.val hj
      simpa using this
    refine ⟨i, j, ?_⟩
    rw [← hq, yo2_prod_eq, ← ei, ← ej]

end CFSG.Quasithin.H13.NF314pt
