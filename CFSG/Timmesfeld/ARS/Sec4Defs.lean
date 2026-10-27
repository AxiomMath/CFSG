module

public import CFSG.Timmesfeld.ARS.BasicBridge

public section

namespace CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G]

@[expose] def conjSet (Δ : Set (Subgroup G)) (g : G) : Set (Subgroup G) :=
  (fun B => conjSub B g) '' Δ

@[expose] def gen (Δ : Set (Subgroup G)) : Subgroup G := ⨆ B ∈ Δ, B

@[expose] def IsWeakTI (R Δ : Set (Subgroup G)) : Prop :=
  Δ ⊆ R ∧ (∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B) ∧ Δ ≠ R ∧
    ∀ d ∈ rootElts R, Δ ∩ conjSet Δ d = ∅ ∨ Δ ∩ conjSet Δ d = Δ

@[expose] def IsTI (R Δ : Set (Subgroup G)) : Prop :=
  Δ ⊆ R ∧ (∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B) ∧ Δ ≠ R ∧
    ∀ g : G, Δ ∩ conjSet Δ g = ∅ ∨ Δ ∩ conjSet Δ g = Δ

section conjSet

variable {Δ Δ' : Set (Subgroup G)} {B : Subgroup G} {g h : G}

theorem conjSub_mem_conjSet (hB : B ∈ Δ) (g : G) : conjSub B g ∈ conjSet Δ g :=
  ⟨B, hB, rfl⟩

theorem mem_conjSet {E : Subgroup G} : E ∈ conjSet Δ g ↔ conjSub E g⁻¹ ∈ Δ := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one]
  · intro h
    refine ⟨_, h, ?_⟩
    change conjSub (conjSub E g⁻¹) g = E
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

@[simp] theorem conjSet_one (Δ : Set (Subgroup G)) : conjSet Δ 1 = Δ := by
  simp [conjSet]

theorem conjSet_mul (Δ : Set (Subgroup G)) (g h : G) :
    conjSet Δ (g * h) = conjSet (conjSet Δ h) g := by
  rw [conjSet, conjSet, conjSet, Set.image_image]
  exact Set.image_congr fun B _ => conjSub_mul B g h

@[simp] theorem conjSet_conjSet_inv (Δ : Set (Subgroup G)) (g : G) :
    conjSet (conjSet Δ g) g⁻¹ = Δ := by
  rw [← conjSet_mul, inv_mul_cancel, conjSet_one]

theorem conjSet_injective (g : G) : Function.Injective fun Δ : Set (Subgroup G) => conjSet Δ g :=
  fun Δ Δ' h => by
    have := congrArg (fun Γ => conjSet Γ g⁻¹) h
    simpa using this

end conjSet

section gen

variable {Δ Δ' : Set (Subgroup G)} {B H : Subgroup G}

theorem le_gen (hB : B ∈ Δ) : B ≤ gen Δ :=
  le_iSup₂ (f := fun (E : Subgroup G) (_ : E ∈ Δ) => E) B hB

theorem gen_le (h : ∀ B ∈ Δ, B ≤ H) : gen Δ ≤ H :=
  iSup₂_le h

theorem gen_le_iff : gen Δ ≤ H ↔ ∀ B ∈ Δ, B ≤ H :=
  ⟨fun h _ hB => (le_gen hB).trans h, gen_le⟩

theorem gen_mono (h : Δ ⊆ Δ') : gen Δ ≤ gen Δ' :=
  gen_le fun _ hB => le_gen (h hB)

theorem conjSub_gen (Δ : Set (Subgroup G)) (g : G) : conjSub (gen Δ) g = gen (conjSet Δ g) := by
  apply le_antisymm
  · rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine gen_le fun E hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_gen (conjSub_mem_conjSet hE g)
  · refine gen_le ?_
    rintro _ ⟨E, hE, rfl⟩
    exact Subgroup.map_mono (le_gen hE)

theorem gen_induction {p : G → Prop} {x : G} (hx : x ∈ gen Δ) (hmem : ∀ B ∈ Δ, ∀ y ∈ B, p y)
    (hone : p 1) (hmul : ∀ y z, p y → p z → p (y * z)) : p x := by
  rw [gen, iSup_subtype'] at hx
  exact Subgroup.iSup_induction (C := p) _ hx (fun B y hy => hmem B B.2 y hy) hone hmul

theorem commuting_gen_of_pairwise (h : ∀ B ∈ Δ, ∀ C ∈ Δ, Commuting B C) :
    Commuting (gen Δ) (gen Δ) := by
  have h1 : ∀ B ∈ Δ, Commuting B (gen Δ) := fun B hB =>
    commuting_iff_le_centralizer.2 (gen_le fun C hC => commuting_iff_le_centralizer.1 (h B hB C hC))
  exact (commuting_iff_le_centralizer.2 (gen_le fun B hB =>
    commuting_iff_le_centralizer.1 (h1 B hB).symm))

end gen

@[expose] def stabSet (Δ : Set (Subgroup G)) : Subgroup G where
  carrier := {g | conjSet Δ g = Δ}
  one_mem' := conjSet_one Δ
  mul_mem' := fun {g h} hg hh => by
    change conjSet Δ (g * h) = Δ
    rw [conjSet_mul, show conjSet Δ h = Δ from hh, show conjSet Δ g = Δ from hg]
  inv_mem' := fun {g} hg => by
    change conjSet Δ g⁻¹ = Δ
    conv_lhs => rw [← show conjSet Δ g = Δ from hg]
    exact conjSet_conjSet_inv Δ g

section stabSet

variable {Δ : Set (Subgroup G)} {g : G}

theorem mem_stabSet : g ∈ stabSet Δ ↔ conjSet Δ g = Δ := Iff.rfl

theorem conjSub_mem_of_mem_stabSet (hg : g ∈ stabSet Δ) {B : Subgroup G} (hB : B ∈ Δ) :
    conjSub B g ∈ Δ := by
  rw [← mem_stabSet.1 hg]
  exact conjSub_mem_conjSet hB g

theorem mem_stabSet_of_mul_self (hgg : g * g = 1) (h : ∀ B ∈ Δ, conjSub B g ∈ Δ) :
    g ∈ stabSet Δ := by
  refine Set.Subset.antisymm (Set.image_subset_iff.2 h) fun B hB => ?_
  refine ⟨conjSub B g, h B hB, ?_⟩
  change conjSub (conjSub B g) g = B
  rw [← conjSub_mul, hgg, conjSub_one]

end stabSet

variable {R Δ : Set (Subgroup G)}

theorem IsTI.isWeakTI (h : IsTI R Δ) : IsWeakTI R Δ :=
  ⟨h.1, h.2.1, h.2.2.1, fun d _ => h.2.2.2 d⟩

theorem isWeakTI_iff (hR : IsRootClass R) : IsWeakTI R Δ ↔
    Δ ⊆ R ∧ (∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B) ∧ Δ ≠ R ∧
      ∀ d ∈ rootElts R, Δ ∩ conjSet Δ d = ∅ ∨ conjSet Δ d = Δ := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun d hd => ?_⟩
    rcases h4 d hd with h | h
    · exact Or.inl h
    · right
      obtain ⟨D, hD, hdD, -⟩ := hd
      have hsub : Δ ⊆ conjSet Δ d := fun x hx => (h.symm ▸ hx : x ∈ Δ ∩ conjSet Δ d).2
      refine Set.Subset.antisymm (fun x hx => ?_) hsub
      have hsub' : conjSet Δ d ⊆ conjSet (conjSet Δ d) d := Set.image_mono hsub
      rw [← conjSet_mul, hR.mul_self D hD d hdD, conjSet_one] at hsub'
      exact hsub' hx
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun d hd => ?_⟩
    rcases h4 d hd with h | h
    · exact Or.inl h
    · right
      rw [h, Set.inter_self]

theorem IsWeakTI.conjSub_mem (hR : IsRootClass R) (hΔ : IsWeakTI R Δ) {D E F : Subgroup G}
    {d : G} (hD : D ∈ R) (hd : d ∈ D) (hE : E ∈ Δ) (hEd : conjSub E d = E) (hF : F ∈ Δ) :
    conjSub F d ∈ Δ := by
  rcases eq_or_ne d 1 with rfl | hd1
  · rwa [conjSub_one]
  have hdd : d * d = 1 := hR.mul_self D hD d hd
  rcases hΔ.2.2.2 d ⟨D, hD, hd, hd1⟩ with h | h
  · have hmem : E ∈ Δ ∩ conjSet Δ d := ⟨hE, hEd ▸ conjSub_mem_conjSet hE d⟩
    rw [h] at hmem
    exact hmem.elim
  · obtain ⟨F', hF', hF'F⟩ := (h.symm ▸ hF : F ∈ Δ ∩ conjSet Δ d).2
    rw [← hF'F]
    change conjSub (conjSub F' d) d ∈ Δ
    rwa [← conjSub_mul, hdd, conjSub_one]

theorem IsWeakTI.mem_stabSet (hR : IsRootClass R) (hΔ : IsWeakTI R Δ) {D : Subgroup G}
    (hD : D ∈ Δ) {d : G} (hd : d ∈ D) : d ∈ stabSet Δ :=
  mem_stabSet_of_mul_self (hR.mul_self D (hΔ.1 hD) d hd) fun _ hF =>
    hΔ.conjSub_mem hR (hΔ.1 hD) hd hD (conjSub_of_mem hd) hF

theorem IsWeakTI.gen_le_stabSet (hR : IsRootClass R) (hΔ : IsWeakTI R Δ) :
    gen Δ ≤ stabSet Δ :=
  gen_le fun _ hD _ hd => hΔ.mem_stabSet hR hD hd

end CFSG.Timmesfeld.ARS
