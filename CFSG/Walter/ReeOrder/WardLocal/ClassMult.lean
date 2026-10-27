module

public import CFSG.Walter.ReeOrder.WardLocal.Three

public section

open scoped BigOperators Classical

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G]

@[expose] noncomputable def cls (x : G) : Finset G := Finset.univ.filter fun g => IsConj g x

theorem mem_cls {x g : G} : g ∈ cls x ↔ IsConj g x := by simp [cls]

theorem cls_invariant (x : G) : ∀ g ∈ cls x, ∀ c : G, c * g * c⁻¹ ∈ cls x := by
  intro g hg c
  rw [mem_cls] at hg ⊢
  exact (isConj_iff.mpr ⟨c, rfl⟩).symm.trans hg

theorem sum_cls {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (x : G) :
    ∑ g ∈ cls x, χ g = (Nat.card (ConjClasses.mk x).carrier : ℂ) * χ x := by
  have h := sum_isConj_mul (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)) x
  rw [← h, cls, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

theorem class_mult (x y z : G) :
    (((cls x ×ˢ cls y).filter fun p => p.1 * p.2 = z).card : ℂ) *
        Nat.card (Subgroup.centralizer ({x} : Set G)) *
        Nat.card (Subgroup.centralizer ({y} : Set G)) =
      Nat.card G * ∑ χ ∈ (irreducibles_finite G).toFinset,
        χ x * χ y * starRingEnd ℂ (χ z) / χ 1 := by
  rw [card_mul_eq _ _ (cls_invariant x) (cls_invariant y)]
  have hsum : ∀ χ ∈ (irreducibles_finite G).toFinset,
      (∑ g ∈ cls x, χ g) * (∑ g ∈ cls y, χ g) * starRingEnd ℂ (χ z) / χ 1 =
        (Nat.card (ConjClasses.mk x).carrier : ℂ) * Nat.card (ConjClasses.mk y).carrier *
          (χ x * χ y * starRingEnd ℂ (χ z) / χ 1) := by
    intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    rw [sum_cls hχ, sum_cls hχ]
    ring
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum]
  have hx : (Nat.card (ConjClasses.mk x).carrier : ℂ) *
      Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
    exact_mod_cast card_conjClass_mul_card_centralizer x
  have hy : (Nat.card (ConjClasses.mk y).carrier : ℂ) *
      Nat.card (Subgroup.centralizer ({y} : Set G)) = Nat.card G := by
    exact_mod_cast card_conjClass_mul_card_centralizer y
  have hG0 : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  set Sm := ∑ χ ∈ (irreducibles_finite G).toFinset, χ x * χ y * starRingEnd ℂ (χ z) / χ 1
  calc (Nat.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk x).carrier : ℂ) *
          Nat.card (ConjClasses.mk y).carrier * Sm) *
        Nat.card (Subgroup.centralizer ({x} : Set G)) *
        Nat.card (Subgroup.centralizer ({y} : Set G))
      = (Nat.card G : ℂ)⁻¹ * Sm * ((Nat.card (ConjClasses.mk x).carrier : ℂ) *
          Nat.card (Subgroup.centralizer ({x} : Set G))) *
          ((Nat.card (ConjClasses.mk y).carrier : ℂ) *
          Nat.card (Subgroup.centralizer ({y} : Set G))) := by ring
    _ = Nat.card G * Sm := by rw [hx, hy]; field_simp

theorem sum_normSq_le (x : G) {X : Finset (G → ℂ)} (hX : X ⊆ (irreducibles_finite G).toFinset) :
    ∑ χ ∈ X, Complex.normSq (χ x) ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have h := sum_irr_mul_conj x x
  simp only [IsConj.refl, ↓reduceIte] at h
  have h' : ∑ χ ∈ (irreducibles_finite G).toFinset, Complex.normSq (χ x) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    have := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.natCast_re] at this
    exact this
  rw [← h']
  exact Finset.sum_le_sum_of_subset_of_nonneg hX fun χ _ _ => Complex.normSq_nonneg _

namespace Block

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {S : WardSetup G L q (-1)} {D : S.EtaData}
  {m : ℕ} (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1))
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
include hq hG

omit hq hG in
theorem xi_one : B.ξ₂ 1 = (q : ℂ) ^ 2 - q + 1 ∧ B.ξ₃ 1 = (q : ℂ) ^ 3 ∧
    B.ξ₄ 1 = (q : ℂ) * ((q : ℂ) ^ 2 - q + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← deg_eq B.irr_2, B.deg_2]; push_cast; ring
  · rw [← deg_eq B.irr_3, B.deg_3]; push_cast; ring
  · rw [← deg_eq B.irr_4, B.deg_4]; push_cast; ring

theorem sum_R {x y : G} (hx : Odd (orderOf x)) (hx3 : 3 ∣ orderOf x) (hy : Odd (orderOf y))
    (hy3 : 3 ∣ orderOf y) {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, χ x * χ y * starRingEnd ℂ (χ (S.κ r)) / χ 1 =
      1 + B.ξ₂ x * B.ξ₂ y / ((q : ℂ) ^ 2 - q + 1) +
        B.ξ₄ x * B.ξ₄ y / ((q : ℂ) * ((q : ℂ) ^ 2 - q + 1)) - 2 / ((q : ℂ) ^ 3 + 1) := by
  rw [D.sum_split]
  have hθ : ∀ j : S.W.RFam, starRingEnd ℂ (j.1 r) = j.1 r := fun j => by
    have := congrFun (S.W.conj_R j.1 j.2) r
    simpa using this
  have hsumθ : ∑ j : S.W.RFam, j.1 r = -1 := by
    rw [Finset.sum_coe_sort S.W.RFam (fun θ => θ r), S.W.sum_R_Ro hr hr1]
    simp
  have hη1 : ∀ j, D.η j 1 = (q : ℂ) ^ 3 + 1 := fun j => by
    rw [D.η_one j, B.dη_eq]; push_cast; ring
  have hη1' : ∀ j, D.η' j 1 = (q : ℂ) ^ 3 + 1 := fun j => by
    rw [D.η'_one j, B.dη_eq]; push_cast; ring
  have e1 : ∑ j, D.η j x * D.η j y * starRingEnd ℂ (D.η j (S.κ r)) / D.η j 1 =
      -1 / ((q : ℂ) ^ 3 + 1) := by
    simp only [fun j => (B.eta_eq_one hq hG hx hx3 j).1, fun j => (B.eta_eq_one hq hG hy hy3 j).1,
      fun j => WardSetup.EtaData.τ_η_eq D j hr hr1, B.ε_eq, Int.cast_one, one_mul, hθ, hη1,
      mul_one, ← Finset.sum_div, hsumθ]
  have e2 : ∑ j, D.η' j x * D.η' j y * starRingEnd ℂ (D.η' j (S.κ r)) / D.η' j 1 =
      -1 / ((q : ℂ) ^ 3 + 1) := by
    simp only [fun j => (B.eta_eq_one hq hG hx hx3 j).2.1,
      fun j => (B.eta_eq_one hq hG hy hy3 j).2.1, fun j => WardSetup.EtaData.τ_η'_eq D j hr hr1,
      B.ε_eq, Int.cast_one, one_mul, hθ, hη1', mul_one, ← Finset.sum_div, hsumθ]
  have e3 : ∑ χ ∈ D.NE, χ x * χ y * starRingEnd ℂ (χ (S.κ r)) / χ 1 =
      1 + B.ξ₂ x * B.ξ₂ y / ((q : ℂ) ^ 2 - q + 1) +
        B.ξ₄ x * B.ξ₄ y / ((q : ℂ) * ((q : ℂ) ^ 2 - q + 1)) := by
    have hsub : S.S1 ⊆ D.NE := fun χ hχ => D.S1_NE hχ
    rw [← Finset.sum_subset hsub (fun χ hχ hnot => by
      rw [D.τ_NE hχ hr hr1, D.z_off hχ hnot]; simp), B.sum_S1]
    obtain ⟨h2, h3, h4⟩ := B.xi_one
    simp only [D.τ_NE (D.S1_NE (show (1 : G → ℂ) ∈ S.S1 from S.one_S1)) hr hr1,
      D.τ_NE (D.S1_NE (show B.ξ₂ ∈ S.S1 by rw [B.hS1]; simp)) hr hr1,
      D.τ_NE (D.S1_NE (show B.ξ₃ ∈ S.S1 by rw [B.hS1]; simp)) hr hr1,
      D.τ_NE (D.S1_NE (show B.ξ₄ ∈ S.S1 by rw [B.hS1]; simp)) hr hr1,
      WardSetup.EtaData.z_one (S := S), B.z_2, B.z_3, B.z_4, B.xi3_eq_zero hq hG hx3, h2, h4]
    simp
  rw [e1, e2, e3]
  ring

end Block

end CFSG.Walter.WardLocal
