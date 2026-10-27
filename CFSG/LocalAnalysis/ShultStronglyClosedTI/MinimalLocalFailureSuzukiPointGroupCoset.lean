module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open scoped Pointwise
open CFSG.ShultStronglyClosedTI

variable {G : Type} [Group G]

theorem exists_coset_translation {Q C : Subgroup G} (hCQ : C ≤ Subgroup.centralizer (Q : Set G))
    (u : G) :
    ∃ τ : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G) →* Q,
      (∀ c, ((τ c : Q) : G) = u⁻¹ * (c * u * (c : G)⁻¹)) ∧
      ∀ c, τ c = 1 ↔ (c : G) ∈ Subgroup.centralizer ({u} : Set G) := by
  have huS : u ∈ u • (Q : Set G) := by rw [mem_leftCoset_iff, inv_mul_cancel]; exact Q.one_mem
  have hmem : ∀ c : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G),
      u⁻¹ * (c * u * (c : G)⁻¹) ∈ Q := fun c => by
    have h := (Subgroup.mem_set_normalizer_iff.mp c.2.2 u).mp huS
    rwa [mem_leftCoset_iff] at h
  let τ : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G) →* Q :=
    { toFun := fun c => ⟨u⁻¹ * (c * u * (c : G)⁻¹), hmem c⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun c d => Subtype.ext (by
        set y := u⁻¹ * ((d : G) * u * (d : G)⁻¹) with hydef
        have hy : (d : G) * u * (d : G)⁻¹ = u * y := by rw [hydef]; group
        have hc : (c : G) * y = y * c :=
          (Subgroup.mem_centralizer_iff.mp (hCQ c.2.1) _ (hmem d)).symm
        have hyc : y * (c : G)⁻¹ = (c : G)⁻¹ * y := by
          rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hc, mul_inv_cancel_right]
        change u⁻¹ * ((c : G) * d * u * ((c : G) * d)⁻¹) = u⁻¹ * (c * u * (c : G)⁻¹) * y
        calc u⁻¹ * ((c : G) * d * u * ((c : G) * d)⁻¹)
            = u⁻¹ * (c * ((d : G) * u * (d : G)⁻¹) * (c : G)⁻¹) := by group
          _ = u⁻¹ * (c * u * (y * (c : G)⁻¹)) := by rw [hy]; group
          _ = u⁻¹ * (c * u * (c : G)⁻¹) * y := by rw [hyc]; group) }
  refine ⟨τ, fun c => rfl, fun c => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h1
    have h2 := congrArg (fun x : Q => (x : G)) h1
    change u⁻¹ * (c * u * (c : G)⁻¹) = 1 at h2
    rw [inv_mul_eq_one, eq_mul_inv_iff_mul_eq] at h2
    exact h2.symm
  · intro h1
    refine Subtype.ext ?_
    change u⁻¹ * (c * u * (c : G)⁻¹) = 1
    rw [h1, mul_inv_cancel_right, inv_mul_cancel]

theorem centralizer_le_coset_normalizer {Q C : Subgroup G}
    (hCQ : C ≤ Subgroup.centralizer (Q : Set G)) (u : G) :
    C ⊓ Subgroup.centralizer ({u} : Set G) ≤
      C ⊓ Subgroup.normalizer (u • (Q : Set G)) := by
  rintro c ⟨hcC, hcu⟩
  refine ⟨hcC, Subgroup.mem_set_normalizer_iff.mpr fun x => ?_⟩
  have hcu' := Subgroup.mem_centralizer_singleton_iff.mp hcu
  have key : ∀ d ∈ C, d * u = u * d → ∀ x, u⁻¹ * x ∈ Q → u⁻¹ * (d * x * d⁻¹) ∈ Q := by
    intro d hd hdu x hx
    have : u⁻¹ * (d * x * d⁻¹) = d * (u⁻¹ * x) * d⁻¹ := by
      rw [show d * x * d⁻¹ = d * u * (u⁻¹ * x) * d⁻¹ by group, hdu]
      group
    rw [this, ← Subgroup.mem_centralizer_iff.mp (hCQ hd) _ hx, mul_inv_cancel_right]
    exact hx
  rw [mem_leftCoset_iff, mem_leftCoset_iff]
  refine ⟨key c hcC hcu' x, fun hx => ?_⟩
  have h := key c⁻¹ (C.inv_mem hcC) (by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcu', mul_inv_cancel_right]) _ hx
  rwa [inv_inv, show c⁻¹ * (c * x * c⁻¹) * c = x by group] at h

theorem card_coset_normalizer {Q C : Subgroup G} (hCQ : C ≤ Subgroup.centralizer (Q : Set G))
    (u : G) (τ : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G) →* Q)
    (hτ : ∀ c, τ c = 1 ↔ (c : G) ∈ Subgroup.centralizer ({u} : Set G)) :
    Nat.card (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G) =
      Nat.card τ.range * Nat.card (C ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
  rw [← Subgroup.card_mul_index τ.ker, Subgroup.index_ker, mul_comm]
  congr 1
  have hle := centralizer_le_coset_normalizer hCQ u
  refine Nat.card_congr ((MulEquiv.subgroupCongr ?_).trans
    (Subgroup.subgroupOfEquivOfLe hle)).toEquiv
  ext c
  rw [MonoidHom.mem_ker, hτ, Subgroup.mem_subgroupOf]
  exact ⟨fun h => ⟨c.2.1, h⟩, fun h => h.2⟩

theorem conj_coset_eq_mul {Q C : Subgroup G} (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hCQ : C ≤ Subgroup.centralizer (Q : Set G)) {u : G}
    (τ : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G) →* Q)
    (hτ : ∀ c, ((τ c : Q) : G) = u⁻¹ * (c * u * (c : G)⁻¹))
    (c : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G)) {σ : G}
    (hσ : σ ∈ u • (Q : Set G)) : (c : G)⁻¹ * σ * c = σ * (τ c⁻¹ : G) := by
  rw [mem_leftCoset_iff] at hσ
  have h1 := hτ c⁻¹
  simp only [Subgroup.coe_inv, inv_inv] at h1
  have hcy : (c : G)⁻¹ * (u⁻¹ * σ) * c = u⁻¹ * σ := by
    rw [mul_assoc, Subgroup.mem_centralizer_iff.mp (hCQ c.2.1) _ hσ, inv_mul_cancel_left]
  calc (c : G)⁻¹ * σ * c = ((c : G)⁻¹ * u * c) * ((c : G)⁻¹ * (u⁻¹ * σ) * c) := by group
    _ = u * (τ c⁻¹ : G) * (u⁻¹ * σ) := by rw [hcy, h1]; group
    _ = σ * (τ c⁻¹ : G) := by
        rw [mul_assoc, hQ _ (τ c⁻¹).2 _ hσ]
        group

theorem translation_range_eq_bot_or_top {Q C X : Subgroup G} {u : G}
    (τ : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G) →* Q)
    (hτ : ∀ c, ((τ c : Q) : G) = u⁻¹ * (c * u * (c : G)⁻¹))
    (hXC : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C)
    (hXQ : ∀ x ∈ X, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hXu : ∀ x ∈ X, x * u = u * x)
    (hXreg : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1}, ∃ x ∈ X, x * a * x⁻¹ = b) :
    τ.range = ⊥ ∨ τ.range = ⊤ := by
  by_cases hbot : τ.range = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  obtain ⟨c, rfl⟩ := hy
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 1
  · rw [hw]
    exact Subgroup.one_mem _
  have hy1' : ((τ c : Q) : G) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have hw1 : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
  obtain ⟨x, hxX, hxw⟩ := hXreg _ ⟨(τ c).2, hy1'⟩ _ ⟨w.2, hw1⟩
  have hxu' : x⁻¹ * u = u * x⁻¹ := (show Commute x u from hXu x hxX).inv_left.eq
  have hxN : x * (c : G) * x⁻¹ ∈ Subgroup.normalizer (u • (Q : Set G)) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun σ => ?_
    have hxS : ∀ g ∈ X, ∀ σ, σ ∈ u • (Q : Set G) → g * σ * g⁻¹ ∈ u • (Q : Set G) := by
      intro g hg σ hσ
      rw [mem_leftCoset_iff] at hσ ⊢
      have h1 := hXQ g hg _ hσ
      rwa [show g * (u⁻¹ * σ) * g⁻¹ = u⁻¹ * (g * σ * g⁻¹) by
        rw [show g * (u⁻¹ * σ) * g⁻¹ = (g * u⁻¹) * σ * g⁻¹ by group]
        rw [(show Commute g u from hXu g hg).inv_right.eq]
        group] at h1
    have hcN := Subgroup.mem_set_normalizer_iff.mp c.2.2
    constructor
    · intro hσ
      have := hxS x hxX _ ((hcN _).mp (by
        have h2 := hxS x⁻¹ (X.inv_mem hxX) σ hσ
        rwa [inv_inv] at h2))
      convert this using 1
      group
    · intro hσ
      have h3 := hxS x⁻¹ (X.inv_mem hxX) _ hσ
      rw [inv_inv, show x⁻¹ * (x * c * x⁻¹ * σ * (x * c * x⁻¹)⁻¹) * x =
        c * (x⁻¹ * σ * x) * (c : G)⁻¹ by group] at h3
      have h4 := hxS x hxX _ ((hcN _).mpr h3)
      rwa [show x * (x⁻¹ * σ * x) * x⁻¹ = σ by group] at h4
  let c' : (C ⊓ Subgroup.normalizer (u • (Q : Set G)) : Subgroup G) :=
    ⟨x * c * x⁻¹, hXC x hxX _ c.2.1, hxN⟩
  refine ⟨c', Subtype.ext ?_⟩
  rw [hτ, ← hxw, hτ]
  change u⁻¹ * (x * c * x⁻¹ * u * (x * c * x⁻¹)⁻¹) = x * (u⁻¹ * (c * u * (c : G)⁻¹)) * x⁻¹
  have hxuinv : x * u⁻¹ = u⁻¹ * x := (show Commute x u from hXu x hxX).inv_right.eq
  have hxux : x⁻¹ * u * x = u := by rw [hxu', inv_mul_cancel_right]
  calc u⁻¹ * (x * c * x⁻¹ * u * (x * c * x⁻¹)⁻¹)
      = u⁻¹ * x * c * (x⁻¹ * u * x) * (c : G)⁻¹ * x⁻¹ := by group
    _ = u⁻¹ * x * c * u * (c : G)⁻¹ * x⁻¹ := by rw [hxux]
    _ = x * u⁻¹ * c * u * (c : G)⁻¹ * x⁻¹ := by rw [← hxuinv]
    _ = x * (u⁻¹ * (c * u * (c : G)⁻¹)) * x⁻¹ := by group

theorem localHull_map_conj (z u g : G) :
    (Subgroup.closure (involutionPointClass z ∩
        (Subgroup.centralizer ({u} : Set G) : Set G))).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure (involutionPointClass z ∩
        (Subgroup.centralizer ({g * u * g⁻¹} : Set G) : Set G)) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_inter_iff, SetLike.mem_coe,
    Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨hyD, hyu⟩, rfl⟩
    refine ⟨by simpa using PairInvolutionFixedField.conj_mem_pointClass hyD g⁻¹, ?_⟩
    calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [hyu]
      _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  · rintro ⟨hxD, hxu⟩
    refine ⟨g⁻¹ * x * g, ⟨PairInvolutionFixedField.conj_mem_pointClass hxD g, ?_⟩, by group⟩
    calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hxu]
      _ = u * (g⁻¹ * x * g) := by group

theorem mem_normalizer_of_mem_centralizer_hull {z u c : G}
    (hc : c ∈ Subgroup.centralizer ({u} : Set G)) :
    c ∈ Subgroup.normalizer (Subgroup.closure (involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G)) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h := localHull_map_conj z u c
  rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right] at h
  exact h

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
