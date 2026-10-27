module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

variable {G : Type} [Group G]

abbrev cent₂ (a y : G) : Subgroup G :=
  Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)

theorem mem_cent₂ {a y g : G} : g ∈ cent₂ a y ↔ g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y := by
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have h : ∀ x : G, g * x = x * g ↔ g * x * g⁻¹ = x := fun x => by
    constructor
    · intro h
      rw [h, mul_inv_cancel_right]
    · intro h
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
  rw [h a, h y]

section Index

theorem relIndex_le_of_labelling {H K : Subgroup G} {T : Type} [Finite T]
    (f : H → T) (hf : ∀ g₁ g₂ : H, f g₁ = f g₂ ↔ g₁⁻¹ * g₂ ∈ K.subgroupOf H) :
    K.relIndex H ≤ Nat.card T := by
  classical
  let F : H ⧸ K.subgroupOf H → T := Quotient.lift f fun a b hab =>
    (hf a b).2 (QuotientGroup.leftRel_apply.mp hab)
  have hF : Function.Injective F := by
    intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn
    induction q₂ using Quotient.inductionOn
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hf _ _).1 h))
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective F hF

end Index

theorem conj_eq_iff {g x x' : G} : g * x * g⁻¹ = x' ↔ x = g⁻¹ * x' * g := by
  constructor
  · rintro rfl; group
  · rintro rfl; group

section Normalizer

theorem conj_mem_centralizer_of_mem_normalizer {S : Set G} {g k : G}
    (hg : g ∈ Subgroup.normalizer S) (hk : k ∈ Subgroup.centralizer S) :
    g * k * g⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ S := (Subgroup.mem_set_normalizer_iff''.1 hg h).1 hh
  have h2 := hk _ h1
  calc h * (g * k * g⁻¹) = g * ((g⁻¹ * h * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * h * g)) * g⁻¹ := by rw [h2]
    _ = g * k * g⁻¹ * h := by group

theorem mem_centralizer_pair {a y g : G} :
    g ∈ Subgroup.centralizer ({a, y} : Set G) ↔ g ∈ cent₂ a y := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨(h a (by simp)).symm, (h y (by simp)).symm⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases hx with rfl | rfl
    · exact h1.symm
    · exact h2.symm

theorem mem_centralizer_triple {a y g : G} :
    g ∈ Subgroup.centralizer ({a, y, a * y} : Set G) ↔ g ∈ cent₂ a y := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨(h a (by simp)).symm, (h y (by simp)).symm⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases hx with rfl | rfl | rfl
    · exact h1.symm
    · exact h2.symm
    · calc (a * y) * g = a * (y * g) := by rw [mul_assoc]
        _ = a * (g * y) := by rw [← h2]
        _ = (a * g) * y := by rw [mul_assoc]
        _ = (g * a) * y := by rw [← h1]
        _ = g * (a * y) := by rw [mul_assoc]

end Normalizer

section Edge

variable {a y : G}

theorem mem_edge_inv {Xe : Subgroup G}
    (hXe : ∀ g, g ∈ Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) {g : G} (hg : g ∈ Xe) :
    (g⁻¹ * a * g = a ∧ g⁻¹ * y * g = y) ∨ (g⁻¹ * a * g = y ∧ g⁻¹ * y * g = a) := by
  have := (hXe g⁻¹).1 (Xe.inv_mem hg)
  simpa using this

theorem edge_le_normalizer {Xe : Subgroup G}
    (hXe : ∀ g, g ∈ Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) :
    (Xe : Set G) ⊆ Subgroup.normalizer ({a, y} : Set G) := by
  intro g hg
  rw [SetLike.mem_coe] at hg
  rw [SetLike.mem_coe, Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · rintro (rfl | rfl)
    · rcases (hXe g).1 hg with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
    · rcases (hXe g).1 hg with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  · intro hh
    have hh' : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rcases hh with hh | hh
    · rw [hh] at hh'
      rcases mem_edge_inv hXe hg with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [hh', h1]
    · rw [hh] at hh'
      rcases mem_edge_inv hXe hg with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [hh', h1]

theorem cent_inf_edge {Xe : Subgroup G} (hne : a ≠ y)
    (hXe : ∀ g, g ∈ Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) :
    Subgroup.centralizer ({a} : Set G) ⊓ Xe = cent₂ a y := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_cent₂, hXe]
  constructor
  · rintro ⟨hga, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨h1, h2⟩
    · exfalso
      have : g * a * g⁻¹ = a := by
        calc g * a * g⁻¹ = a * g * g⁻¹ := by rw [hga]
          _ = a := by group
      exact hne (this.symm.trans h1)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, Or.inl ⟨h1, h2⟩⟩
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h1]

theorem edge_normal {Xe : Subgroup G}
    (hXe : ∀ g, g ∈ Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) :
    ∀ g ∈ Xe, ∀ k ∈ cent₂ a y, g * k * g⁻¹ ∈ cent₂ a y := by
  intro g hg k hk
  rw [← mem_centralizer_pair] at hk ⊢
  exact conj_mem_centralizer_of_mem_normalizer (edge_le_normalizer hXe hg) hk

theorem edge_sq_mem {Xe : Subgroup G}
    (hXe : ∀ g, g ∈ Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) {g : G} (hg : g ∈ Xe) : g ^ 2 ∈ cent₂ a y := by
  rw [mem_cent₂]
  have e : ∀ x : G, g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := fun x => by
    simp only [pow_two, mul_inv_rev]; group
  rcases (hXe g).1 hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [e, h1, h1], by rw [e, h2, h2]⟩
  · exact ⟨by rw [e, h1, h2], by rw [e, h2, h1]⟩

theorem edge_label_iff {u v : G} (hne : a ≠ y)
    (hu : (u * a * u⁻¹ = a ∧ u * y * u⁻¹ = y) ∨ (u * a * u⁻¹ = y ∧ u * y * u⁻¹ = a))
    (hv : (v * a * v⁻¹ = a ∧ v * y * v⁻¹ = y) ∨ (v * a * v⁻¹ = y ∧ v * y * v⁻¹ = a)) :
    ((u * a * u⁻¹ = a) ↔ (v * a * v⁻¹ = a)) ↔ u⁻¹ * v ∈ cent₂ a y := by
  rw [mem_cent₂]
  have key : ∀ x : G, (u⁻¹ * v) * x * (u⁻¹ * v)⁻¹ = u⁻¹ * (v * x * v⁻¹) * u := fun x => by group
  rw [key, key]
  constructor
  · intro h
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv1 : v * a * v⁻¹ = a := h.1 h1
      rcases hv with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h3, h4]
        exact ⟨(conj_eq_iff.1 h1).symm, (conj_eq_iff.1 h2).symm⟩
      · exact absurd (hv1.symm.trans h3) hne
    · have hna : ¬ (u * a * u⁻¹ = a) := fun h' => hne (h'.symm.trans h1)
      have hnv : ¬ (v * a * v⁻¹ = a) := fun h' => hna (h.2 h')
      rcases hv with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact absurd h3 hnv
      · rw [h3, h4]
        exact ⟨(conj_eq_iff.1 h1).symm, (conj_eq_iff.1 h2).symm⟩
  · rintro ⟨h1, h2⟩
    have : v * a * v⁻¹ = u * a * u⁻¹ := by
      calc v * a * v⁻¹ = u * (u⁻¹ * (v * a * v⁻¹) * u) * u⁻¹ := by group
        _ = u * a * u⁻¹ := by rw [h1]
    rw [this]

theorem edge_relIndex_le {Xe : Subgroup G} (hne : a ≠ y)
    (hXe : ∀ g, g ∈ Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) : (cent₂ a y).relIndex Xe ≤ 2 := by
  classical
  have h := relIndex_le_of_labelling (G := G) (H := Xe) (K := cent₂ a y) (T := Bool)
    (fun g => decide ((g : G) * a * (g : G)⁻¹ = a)) ?_
  · simpa using h
  intro g₁ g₂
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, decide_eq_decide]
  exact edge_label_iff hne ((hXe g₁).1 g₁.2) ((hXe g₂).1 g₂.2)

end Edge

section Triangle

variable {a y : G}

theorem mem_normalizer_of_fixes {S : Set G} {g : G} (h : ∀ s ∈ S, g * s * g⁻¹ = s) :
    g ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx]; exact hx
  · intro hx
    have hx' : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have h2 : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
      have := h _ hx
      calc g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * (g * (g * x * g⁻¹) * g⁻¹) * g := by rw [this]
        _ = g * x * g⁻¹ := by group
    rw [← hx', h2]; exact hx

theorem cent₂_le_normalizer_triple :
    cent₂ a y ≤ Subgroup.normalizer ({a, y, a * y} : Set G) := by
  intro g hg
  refine mem_normalizer_of_fixes fun s hs => ?_
  have hg' := mem_centralizer_triple.2 hg
  have := Subgroup.mem_centralizer_iff.1 hg' s hs
  calc g * s * g⁻¹ = s * g * g⁻¹ := by rw [← this]
    _ = s := by group

theorem triple_sq_mem {Xt : Subgroup G} (ha : a * a = 1) (hne : a ≠ y)
    (hXt : Xt = Subgroup.normalizer ({a, y, a * y} : Set G)) {g : G}
    (hga : g * a * g⁻¹ = a) (hg : g ∈ Xt) : g ^ 2 ∈ cent₂ a y := by
  subst hXt
  rw [mem_cent₂]
  have e : ∀ x : G, g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := fun x => by
    simp only [pow_two, mul_inv_rev]; group
  have hy : g * y * g⁻¹ ∈ ({a, y, a * y} : Set G) := (Subgroup.mem_set_normalizer_iff.1 hg y).1
    (by simp)
  rcases hy with h | h | h
  · exfalso
    have : y = g⁻¹ * a * g := conj_eq_iff.1 h
    exact hne ((conj_eq_iff.1 hga).trans this.symm)
  · exact ⟨by rw [e, hga, hga], by rw [e, h, h]⟩
  · refine ⟨by rw [e, hga, hga], ?_⟩
    have h' : g * (a * y) * g⁻¹ = (g * a * g⁻¹) * (g * y * g⁻¹) := by group
    have : g * y * g⁻¹ = a * y := h
    rw [e, this]
    calc g * (a * y) * g⁻¹ = (g * a * g⁻¹) * (g * y * g⁻¹) := h'
      _ = a * (a * y) := by rw [hga, this]
      _ = y := by rw [← mul_assoc, ha, one_mul]

theorem triple_normal : ∀ g ∈ Subgroup.normalizer ({a, y, a * y} : Set G), ∀ k ∈ cent₂ a y,
    g * k * g⁻¹ ∈ cent₂ a y := by
  intro g hg k hk
  rw [← mem_centralizer_triple] at hk ⊢
  exact conj_mem_centralizer_of_mem_normalizer hg hk

theorem cent₂_inf_cent_le_xt1 {z : G} :
    cent₂ a y ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.normalizer ({a, y, a * y * z} : Set G) := by
  intro g hg
  refine ⟨hg.2, mem_normalizer_of_fixes fun s hs => ?_⟩
  obtain ⟨hga, hgy⟩ := mem_cent₂.1 hg.1
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hg.2
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [this]
      _ = z := by group
  rcases hs with rfl | rfl | rfl
  · exact hga
  · exact hgy
  · calc g * (a * y * z) * g⁻¹ = (g * a * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      _ = a * y * z := by rw [hga, hgy, hgz]

end Triangle

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
