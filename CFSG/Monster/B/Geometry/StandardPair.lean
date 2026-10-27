module

public import CFSG.Monster.B.Geometry.ChamberModel
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

theorem mem_foundation_two_of_three {p l π : ι} (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π)
    (hι : ∀ i, i = p ∨ i = l ∨ i = π) {x y : C} (hy : y ∈ foundation cs δ 2 x) :
    y ∈ residue cs δ {p, l} x ∨ y ∈ residue cs δ {l, π} x ∨ y ∈ residue cs δ {p, π} x := by
  obtain ⟨J, hJ, hyJ⟩ := mem_foundation_iff.mp hy
  have hsub : ∀ {a b c : ι}, a ≠ b → (∀ i, i = a ∨ i = b ∨ i = c) → c ∉ J → J ⊆ {a, b} :=
    fun {a b c} _ hι' hc i hi => by
      rcases hι' i with rfl | rfl | rfl
      · simp
      · simp
      · exact absurd hi hc
  by_cases hp : p ∈ J
  · by_cases hl : l ∈ J
    · have hπ : π ∉ J := by
        intro hπ
        have h3 : ({p, l, π} : Set ι) ⊆ J := by
          intro i hi
          rcases hi with rfl | rfl | hi
          · exact hp
          · exact hl
          · rw [Set.mem_singleton_iff.mp hi]; exact hπ
        have := (Set.encard_le_encard h3).trans hJ
        rw [Set.encard_insert_of_notMem (by simp [hpl, hpπ]), Set.encard_pair hlπ] at this
        have : (1 : ℕ∞) + 2 ≤ 2 := this
        norm_num at this
      exact Or.inl (residue_mono (hsub hpl hι hπ) x hyJ)
    · exact Or.inr (Or.inr (residue_mono (hsub hpπ (fun i => by
        rcases hι i with h | h | h <;> simp [h]) hl) x hyJ))
  · exact Or.inr (Or.inl (residue_mono (hsub hlπ (fun i => by
      rcases hι i with h | h | h <;> simp [h]) hp) x hyJ))

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem exists_dist (x : C) (w : W) : ∃ y, δ x y = w := by
  obtain ⟨ω, -, rfl⟩ := cs.exists_isReduced w
  induction ω using List.reverseRecOn with
  | nil => exact ⟨x, by rw [cs.wordProd_nil]; exact hδ.eq_one_self x⟩
  | append_singleton ω i ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, -, hz⟩ := hδ.exists_simple x y i
    exact ⟨z, by rw [hz, hy, cs.wordProd_append, cs.wordProd_singleton]⟩

theorem apply_mem_residue_iff {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) {J : Set ι}
    {x y : C} : g y ∈ residue cs δ J (g x) ↔ y ∈ residue cs δ J x := by
  rw [mem_residue_iff_mem_parabolic hδ, mem_residue_iff_mem_parabolic hδ, dist_typeAut hδ hg]

theorem apply_mem_foundation_union_iff {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) {x d y : C} :
    g y ∈ foundation cs δ 2 (g x) ∪ {g d} ↔ y ∈ foundation cs δ 2 x ∪ {d} := by
  rw [Set.mem_union, Set.mem_union, mem_foundation_iff_of_dist_eq hδ hδ (dist_typeAut hδ hg),
    Set.mem_singleton_iff, Set.mem_singleton_iff, g.injective.eq_iff]

theorem IsWeylIsometry.inv_comp {c d : C} {Ψ : C → C}
    (hΨ : IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d}) Ψ)
    {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) (hgc : g c = c) (hgd : g d = d) :
    IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d})
      (fun y => g⁻¹ (Ψ y)) := by
  have hg' := inv_mem hg
  have hgc' : g⁻¹ c = c := by rw [Equiv.Perm.inv_eq_iff_eq, hgc]
  have hgd' : g⁻¹ d = d := by rw [Equiv.Perm.inv_eq_iff_eq, hgd]
  have hmem : ∀ y, g⁻¹ y ∈ foundation cs δ 2 c ∪ {d} ↔ y ∈ foundation cs δ 2 c ∪ {d} := by
    intro y
    have := apply_mem_foundation_union_iff hδ hg' (x := c) (d := d) (y := y)
    rwa [hgc', hgd'] at this
  refine isWeylIsometry_of hδ hδ (fun y hy => (hmem _).mpr (hΨ.1.mapsTo hy)) ?_
    (fun y hy z hz => by rw [dist_typeAut hδ hg', hΨ.2 y hy z hz])
  intro y hy
  have hgy : g y ∈ foundation cs δ 2 c ∪ {d} := by
    rw [← hmem]
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hy
  obtain ⟨z, hz, hzy⟩ := hΨ.1.surjOn hgy
  exact ⟨z, hz, by simp only [hzy, Equiv.Perm.inv_def, Equiv.symm_apply_apply]⟩

variable [Finite W]

theorem apply_oppChamber {g : Equiv.Perm C} (hg : g ∈ typeAut cs δ) {x d : C}
    (hxd : δ x d = longest cs Set.univ) (u : W) :
    g (oppChamber cs δ x d u) = oppChamber cs δ (g x) (g d) u := by
  have h := oppChamber_spec hδ hxd u
  refine eq_oppChamber hδ (by rw [dist_typeAut hδ hg]; exact hxd) ?_ ?_
  · rw [dist_typeAut hδ hg]; exact h.1
  · rw [dist_typeAut hδ hg]; exact h.2

omit [Finite W] in
theorem IsWeylIsometry.isTypeIso_residue {c d : C} {Ψ : C → C}
    (hΨ : IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d}) Ψ)
    (hΨc : Ψ c = c) {J : Set ι} (hJ : J.encard ≤ 2) :
    IsTypeIso cs δ δ (residue cs δ J c) (residue cs δ J c) Ψ := by
  have hsub : residue cs δ J c ⊆ foundation cs δ 2 c ∪ {d} :=
    (residue_subset_foundation hJ c).trans Set.subset_union_left
  have hbij := hΨ.bijOn_residue hδ hδ (Or.inl (self_mem_foundation 2 c)) hΨc hsub hsub
  exact (hΨ.mono hsub hbij).isTypeIso

theorem IsWeylIsometry.fix_oppChamber {c d : C} (hcd : δ c d = longest cs Set.univ)
    {Ψ : C → C}
    (hΨ : IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d}) Ψ)
    (hΨc : Ψ c = c) (hΨd : Ψ d = d) {J : Set ι} (hJ : J.encard ≤ 2) {u : W}
    (hu : u ∈ cs.parabolic J) : Ψ (oppChamber cs δ c d u) = oppChamber cs δ c d u := by
  set q := oppChamber cs δ c d u
  have hq := oppChamber_spec hδ hcd u
  have hqR : q ∈ foundation cs δ 2 c ∪ {d} :=
    Or.inl (residue_subset_foundation hJ c ((mem_residue_iff_mem_parabolic hδ).mpr (hq.1 ▸ hu)))
  have hcX : c ∈ foundation cs δ 2 c ∪ {d} := Or.inl (self_mem_foundation 2 c)
  have hdX : d ∈ foundation cs δ 2 c ∪ {d} := Or.inr rfl
  refine eq_oppChamber hδ hcd ?_ ?_
  · rw [← hΨc, hΨ.2 c hcX q hqR]; exact hq.1
  · rw [← hΨd, hΨ.2 q hqR d hdX]; exact hq.2

theorem eq_oppChamber_of_length_le {c d q : C} (hcd : δ c d = longest cs Set.univ) {J : Set ι}
    (hq : q ∈ residue cs δ J c)
    (hlen : cs.length (δ q d) + cs.length (longest cs J) ≤ cs.length (longest cs Set.univ)) :
    q = oppChamber cs δ c d (longest cs J) := by
  have hp := isProjection_oppChamber_longest hδ hcd J
  have hpd := (oppChamber_spec hδ hcd (longest cs J)).2
  generalize oppChamber cs δ c d (longest cs J) = p at hp hpd ⊢
  obtain ⟨-, hgate⟩ := hp.gate hδ hq
  have hl := length_inv_mul_longest (cs := cs) (longest cs J)
  have h1 : cs.length (δ d p) = cs.length (δ p d) := by rw [dist_inv hδ p d, cs.length_inv]
  have h2 : cs.length (δ d q) = cs.length (δ q d) := by rw [dist_inv hδ q d, cs.length_inv]
  rw [hpd] at h1
  have h0 : cs.length (δ p q) = 0 := by omega
  rw [cs.length_eq_zero_iff, hδ.eq_one_iff] at h0
  exact h0.symm

theorem exists_opposite_oppChamber {J : Set ι} {a b : C} (hab : δ a b = longest cs J) :
    ∃ d, δ a d = longest cs Set.univ ∧ b = oppChamber cs δ a d (longest cs J) := by
  have hJ := isLongest_of_finite (cs := cs) J
  obtain ⟨d, hd⟩ := exists_dist hδ b (longest cs J * longest cs Set.univ)
  have hlen := length_inv_mul_longest (cs := cs) (longest cs J)
  rw [hJ.inv_eq] at hlen
  have hmul : δ a b * δ b d = longest cs Set.univ := by
    rw [hab, hd, ← mul_assoc, hJ.mul_self, one_mul]
  have had : δ a d = longest cs Set.univ := by
    rw [dist_eq_mul_of_length_add hδ (by rw [hmul, hab, hd]; omega), hmul]
  exact ⟨d, had, eq_oppChamber hδ had hab (by rw [hd, hJ.inv_eq])⟩

omit hδ [Finite W] in
theorem transitive_of_standard {c₀ d₀ : C}
    (htrans : ∀ c d, δ c d = longest cs Set.univ → ∃ g ∈ typeAut cs δ, g c₀ = c ∧ g d₀ = d) :
    ∀ c d c₁ d₁ : C, δ c d = longest cs Set.univ → δ c₁ d₁ = longest cs Set.univ →
      ∃ g ∈ typeAut cs δ, g c = c₁ ∧ g d = d₁ := by
  intro c d c₁ d₁ hcd hcd₁
  obtain ⟨g, hg, hgc, hgd⟩ := htrans c d hcd
  obtain ⟨g₁, hg₁, hg₁c, hg₁d⟩ := htrans c₁ d₁ hcd₁
  refine ⟨g₁ * g⁻¹, mul_mem hg₁ (inv_mem hg), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, ← hgc, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hg₁c]
  · rw [Equiv.Perm.mul_apply, ← hgd, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hg₁d]

theorem rig₂_of_transitive {c₀ d₀ : C}
    (htrans : ∀ c d, δ c d = longest cs Set.univ → ∃ g ∈ typeAut cs δ, g c₀ = c ∧ g d₀ = d)
    (hrig : ∀ i j : ι, i ≠ j → ∀ g : C → C,
      IsTypeIso cs δ δ (residue cs δ {i, j} c₀) (residue cs δ {i, j} c₀) g →
      g (oppChamber cs δ c₀ d₀ (longest cs {i, j})) =
        oppChamber cs δ c₀ d₀ (longest cs {i, j}) →
      (∀ x ∈ panel cs δ i c₀ ∪ panel cs δ j c₀, g x = x) →
        ∀ x ∈ residue cs δ {i, j} c₀, g x = x) :
    Rig₂ cs δ := by
  intro i j hij a b hb hab g hg hgb hfix
  obtain ⟨d, had, rfl⟩ := exists_opposite_oppChamber hδ hab
  obtain ⟨h, hh, hhc, hhd⟩ := htrans a d had
  have hh' := inv_mem hh
  have hcd₀ : δ c₀ d₀ = longest cs Set.univ := by rw [← dist_typeAut hδ hh, hhc, hhd, had]
  have hmem : ∀ (K : Set ι) (y : C), h y ∈ residue cs δ K a ↔ y ∈ residue cs δ K c₀ := by
    intro K y
    rw [← hhc]
    exact apply_mem_residue_iff hδ hh
  have hmem' : ∀ (K : Set ι) (y : C), h⁻¹ y ∈ residue cs δ K c₀ ↔ y ∈ residue cs δ K a := by
    intro K y
    rw [← hmem, show h (h⁻¹ y) = y from Equiv.apply_symm_apply h y]
  set g' : C → C := fun y => h⁻¹ (g (h y)) with hg'
  have hg'iso : IsTypeIso cs δ δ (residue cs δ {i, j} c₀) (residue cs δ {i, j} c₀) g' := by
    refine ⟨⟨fun y hy => (hmem' _ _).mpr (hg.1.mapsTo ((hmem _ _).mpr hy)), fun y hy z hz e => ?_,
      fun y hy => ?_⟩, fun y hy z hz k => ?_⟩
    · have e' : g (h y) = g (h z) := h⁻¹.injective e
      exact h.injective (hg.1.injOn ((hmem _ _).mpr hy) ((hmem _ _).mpr hz) e')
    · obtain ⟨z, hz, hzy⟩ := hg.1.surjOn ((hmem _ _).mpr hy)
      refine ⟨h⁻¹ z, (hmem' _ _).mpr hz, ?_⟩
      have e1 : h (h⁻¹ z) = z := Equiv.apply_symm_apply h z
      have e2 : h⁻¹ (h y) = y := Equiv.symm_apply_apply h y
      simp only [hg', e1, hzy, e2]
    · simp only [hg']
      rw [dist_typeAut hδ hh', ← dist_typeAut hδ hh y z]
      exact hg.2 _ ((hmem _ _).mpr hy) _ ((hmem _ _).mpr hz) k
  have hopp : h (oppChamber cs δ c₀ d₀ (longest cs {i, j})) =
      oppChamber cs δ a d (longest cs {i, j}) := by
    rw [apply_oppChamber hδ hh hcd₀, hhc, hhd]
  have hg'b : g' (oppChamber cs δ c₀ d₀ (longest cs {i, j})) =
      oppChamber cs δ c₀ d₀ (longest cs {i, j}) := by
    have e : h⁻¹ (h (oppChamber cs δ c₀ d₀ (longest cs {i, j}))) =
        oppChamber cs δ c₀ d₀ (longest cs {i, j}) := Equiv.symm_apply_apply h _
    simp only [hg', hopp, hgb]
    rw [← hopp, e]
  have hg'fix : ∀ x ∈ panel cs δ i c₀ ∪ panel cs δ j c₀, g' x = x := by
    rintro x (hx | hx)
    · simp only [hg']
      rw [hfix (h x) (Or.inl ((hmem _ _).mpr hx)), Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    · simp only [hg']
      rw [hfix (h x) (Or.inr ((hmem _ _).mpr hx)), Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have key := hrig i j hij g' hg'iso hg'b hg'fix
  intro x hx
  have := key (h⁻¹ x) ((hmem' _ _).mpr hx)
  simp only [hg', Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
  exact h.symm.injective this

omit [Finite W] in
theorem real_of_transitive {c₀ d₀ : C}
    (htrans : ∀ c d, δ c d = longest cs Set.univ → ∃ g ∈ typeAut cs δ, g c₀ = c ∧ g d₀ = d)
    (hreal : ∀ Ψ : C → C, IsWeylIsometry δ δ (foundation cs δ 2 c₀ ∪ {d₀})
        (foundation cs δ 2 c₀ ∪ {d₀}) Ψ → Ψ c₀ = c₀ → Ψ d₀ = d₀ →
      ∃ g ∈ typeAut cs δ, Set.EqOn g Ψ (foundation cs δ 2 c₀ ∪ {d₀})) :
    ∀ c d : C, δ c d = longest cs Set.univ → ∀ Ψ : C → C,
      IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d}) Ψ →
        Ψ c = c → Ψ d = d → ∃ g ∈ typeAut cs δ, Set.EqOn g Ψ (foundation cs δ 2 c ∪ {d}) := by
  intro c d hcd Ψ hΨ hΨc hΨd
  obtain ⟨h, hh, hhc, hhd⟩ := htrans c d hcd
  have hh' := inv_mem hh
  have hmem : ∀ y, h y ∈ foundation cs δ 2 c ∪ {d} ↔ y ∈ foundation cs δ 2 c₀ ∪ {d₀} := by
    intro y
    rw [← hhc, ← hhd]
    exact apply_mem_foundation_union_iff hδ hh
  have hmem' : ∀ y, h⁻¹ y ∈ foundation cs δ 2 c₀ ∪ {d₀} ↔ y ∈ foundation cs δ 2 c ∪ {d} := by
    intro y
    rw [← hmem, show h (h⁻¹ y) = y from Equiv.apply_symm_apply h y]
  set Ψ' : C → C := fun y => h⁻¹ (Ψ (h y)) with hΨ'
  have hΨ'iso : IsWeylIsometry δ δ (foundation cs δ 2 c₀ ∪ {d₀}) (foundation cs δ 2 c₀ ∪ {d₀})
      Ψ' := by
    refine isWeylIsometry_of hδ hδ (fun y hy => (hmem' _).mpr (hΨ.1.mapsTo ((hmem y).mpr hy)))
      (fun y hy => ?_) (fun y hy z hz => ?_)
    · obtain ⟨z, hz, hzy⟩ := hΨ.1.surjOn ((hmem y).mpr hy)
      refine ⟨h⁻¹ z, (hmem' _).mpr hz, ?_⟩
      have e1 : h (h⁻¹ z) = z := Equiv.apply_symm_apply h z
      have e2 : h⁻¹ (h y) = y := Equiv.symm_apply_apply h y
      simp only [hΨ', e1, hzy, e2]
    · simp only [hΨ']
      rw [dist_typeAut hδ hh', hΨ.2 _ ((hmem y).mpr hy) _ ((hmem z).mpr hz), dist_typeAut hδ hh]
  have hΨ'c : Ψ' c₀ = c₀ := by
    simp only [hΨ', hhc, hΨc]
    rw [← hhc, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hΨ'd : Ψ' d₀ = d₀ := by
    simp only [hΨ', hhd, hΨd]
    rw [← hhd, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  obtain ⟨g, hg, hgΨ⟩ := hreal Ψ' hΨ'iso hΨ'c hΨ'd
  refine ⟨h * g * h⁻¹, mul_mem (mul_mem hh hg) hh', fun y hy => ?_⟩
  have := hgΨ ((hmem' y).mpr hy)
  simp only [Equiv.Perm.mul_apply]
  rw [this]
  simp only [hΨ', Equiv.Perm.inv_def, Equiv.apply_symm_apply]

end CFSG.Monster.B.Geometry
