module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Card

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type*} [Group G]

private lemma s1611e3_exists_notMem {E : Subgroup G} {S : Set G} (hSfin : S.Finite)
    (hS : S.ncard < Nat.card ↥E) : ∃ x ∈ E, x ∉ S := by
  by_contra h
  rw [not_exists] at h
  have hsub : (E : Set G) ⊆ S := by
    intro x hx
    by_contra hxS
    exact h x ⟨hx, hxS⟩
  have hEncard : (E : Set G).ncard = Nat.card ↥E := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  have hle : (E : Set G).ncard ≤ S.ncard := Set.ncard_le_ncard hsub hSfin
  omega

private lemma s1611e3_closure_two_aux {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(Subgroup.closure {x}) = 2 ∧ ∀ z ∈ Subgroup.closure {x}, z = 1 ∨ z = x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  let T : Subgroup G :=
    { carrier := {1, x}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv ⊢
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · rw [hu, hv]; exact Or.inl (one_mul 1)
        · rw [hu, hv]; exact Or.inr (one_mul x)
        · rw [hu, hv]; exact Or.inr (mul_one x)
        · rw [hu, hv]; exact Or.inl hx
      inv_mem' := by
        intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
        rcases hu with hu | hu
        · rw [hu]; exact Or.inl (inv_one)
        · rw [hu]; exact Or.inr hxinv }
  have hTle : T ≤ Subgroup.closure {x} := by
    intro z hz
    have hz' : z = 1 ∨ z = x := by
      change z ∈ ({1, x} : Set G) at hz
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    rcases hz' with hz' | hz'
    · rw [hz']; exact (Subgroup.closure {x}).one_mem
    · rw [hz']; exact Subgroup.subset_closure (by simp)
  have hcle : Subgroup.closure {x} ≤ T := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    rw [hz]
    change (x : G) = 1 ∨ (x : G) = x
    exact Or.inr rfl
  have heq : Subgroup.closure {x} = T := le_antisymm hcle hTle
  have hTcard : Nat.card ↥T = 2 := by
    have h1 : Nat.card ↥T = (T : Set G).ncard := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    have h2 : (T : Set G).ncard = 2 := by
      change ({1, x} : Set G).ncard = 2
      exact Set.ncard_pair hx1.symm
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · rw [heq]; exact hTcard
  · intro z hz
    have hzT : z ∈ T := hcle hz
    change z ∈ ({1, x} : Set G) at hzT
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzT

private lemma s1611e3_closure_four_aux {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card ↥(Subgroup.closure {x, y}) = 4 ∧
      ∀ z ∈ Subgroup.closure {x, y}, z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  let T : Subgroup G :=
    { carrier := {1, x, y, x * y}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv ⊢
        rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv
        · rw [hu, hv]; exact Or.inl (one_mul 1)
        · rw [hu, hv]; exact Or.inr (Or.inl (one_mul x))
        · rw [hu, hv]; exact Or.inr (Or.inr (Or.inl (one_mul y)))
        · rw [hu, hv]; exact Or.inr (Or.inr (Or.inr (one_mul (x * y))))
        · rw [hu, hv]; exact Or.inr (Or.inl (mul_one x))
        · rw [hu, hv]; exact Or.inl hx
        · rw [hu, hv]; exact Or.inr (Or.inr (Or.inr rfl))
        · rw [hu, hv]
          exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hx, one_mul])))
        · rw [hu, hv]; exact Or.inr (Or.inr (Or.inl (mul_one y)))
        · rw [hu, hv]; exact Or.inr (Or.inr (Or.inr hxy.symm))
        · rw [hu, hv]; exact Or.inl hy
        · rw [hu, hv]
          exact Or.inr (Or.inl (by rw [← mul_assoc, hxy.symm, mul_assoc, hy, mul_one]))
        · rw [hu, hv]; exact Or.inr (Or.inr (Or.inr (mul_one (x * y))))
        · rw [hu, hv]
          exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, hxy.symm, ← mul_assoc, hx, one_mul])))
        · rw [hu, hv]
          exact Or.inr (Or.inl (by rw [mul_assoc, hy, mul_one]))
        · rw [hu, hv]
          exact Or.inl (by
            have hself : (x * y)⁻¹ = x * y := by rw [mul_inv_rev, hxinv, hyinv, hxy.symm]
            exact inv_eq_iff_mul_eq_one.mp hself)
      inv_mem' := by
        intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
        rcases hu with hu | hu | hu | hu
        · rw [hu]; exact Or.inl (inv_one)
        · rw [hu]; exact Or.inr (Or.inl hxinv)
        · rw [hu]; exact Or.inr (Or.inr (Or.inl hyinv))
        · rw [hu]; exact Or.inr (Or.inr (Or.inr (by
            rw [mul_inv_rev, hxinv, hyinv, hxy.symm]))) }
  have hTle : T ≤ Subgroup.closure ({x, y} : Set G) := by
    intro z hz
    have hz' : z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
      change z ∈ ({1, x, y, x * y} : Set G) at hz
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    rcases hz' with hz' | hz' | hz' | hz'
    · rw [hz']; exact (Subgroup.closure {x, y}).one_mem
    · rw [hz']; exact Subgroup.subset_closure (by simp)
    · rw [hz']; exact Subgroup.subset_closure (by simp)
    · rw [hz']
      exact (Subgroup.closure {x, y}).mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have hcle : Subgroup.closure ({x, y} : Set G) ≤ T := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      change (x : G) = 1 ∨ (x : G) = x ∨ (x : G) = y ∨ (x : G) = x * y
      exact Or.inr (Or.inl rfl)
    · rw [hz]
      change (y : G) = 1 ∨ (y : G) = x ∨ (y : G) = y ∨ (y : G) = x * y
      exact Or.inr (Or.inr (Or.inl rfl))
  have heq : Subgroup.closure ({x, y} : Set G) = T := le_antisymm hcle hTle
  have hTcard : Nat.card ↥T = 4 := by
    have h1 : Nat.card ↥T = (T : Set G).ncard := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    have h2 : (T : Set G).ncard = 4 := by
      change ({1, x, y, x * y} : Set G).ncard = 4
      rw [Set.ncard_eq_four]
      refine ⟨1, x, y, x * y, hx1.symm, hy1.symm, ?_, hne, ?_, ?_, rfl⟩
      · intro h
        have : x = y := by
          calc x = x * y * y⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
            _ = 1 * y⁻¹ := by rw [h.symm]
            _ = y := by rw [hyinv, one_mul]
        exact hne this
      · intro h
        have : y = 1 := by
          have h3 := congrArg (fun z => x * z) h
          rw [hx, ← mul_assoc, hx, one_mul] at h3
          exact h3.symm
        exact hy1 this
      · intro h
        have : x = 1 := by
          have h3 := congrArg (fun z => z * y⁻¹) h
          rw [mul_assoc, mul_inv_cancel, mul_one] at h3
          exact h3.symm
        exact hx1 this
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · rw [heq]; exact hTcard
  · intro z hz
    have hzT : z ∈ T := hcle hz
    change z ∈ ({1, x, y, x * y} : Set G) at hzT
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzT

private lemma s1611e3_ncard_eight {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (hcP : c ∉ ({1, a, b, a * b} : Set G)) :
    ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G).ncard = 8 := by
  have hcfour := s1611e3_closure_four_aux ha hb hab ha1 hb1 hne
  have hPsub : (Subgroup.closure {a, b} : Set G) = ({1, a, b, a * b} : Set G) := by
    apply Set.Subset.antisymm
    · intro z hz
      have h := hcfour.2 z hz
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz | hz
      · rw [hz]; exact (Subgroup.closure {a, b}).one_mem
      · rw [hz]; exact Subgroup.subset_closure (by simp)
      · rw [hz]; exact Subgroup.subset_closure (by simp)
      · rw [hz]
        exact (Subgroup.closure {a, b}).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  have hcP' : c ∉ (Subgroup.closure {a, b} : Set G) := by rwa [hPsub]
  have hPcard : ({1, a, b, a * b} : Set G).ncard = 4 := by
    rw [Set.ncard_eq_four]
    refine ⟨1, a, b, a * b, ha1.symm, hb1.symm, ?_, hne, ?_, ?_, rfl⟩
    · intro h
      have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
      have : a = b := by
        calc a = a * b * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
          _ = 1 * b⁻¹ := by rw [h.symm]
          _ = b := by rw [hb_inv, one_mul]
      exact hne this
    · intro h
      have : b = 1 := by
        have h3 := congrArg (fun z => a * z) h
        rw [ha, ← mul_assoc, ha, one_mul] at h3
        exact h3.symm
      exact hb1 this
    · intro h
      have : a = 1 := by
        have h3 := congrArg (fun z => z * b⁻¹) h
        rw [mul_assoc, mul_inv_cancel, mul_one] at h3
        exact h3.symm
      exact ha1 this
  have hQcard : ((fun w => c * w) '' ({1, a, b, a * b} : Set G)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (fun u v huv => mul_left_cancel huv), hPcard]
  have hdisj : Disjoint ({1, a, b, a * b} : Set G)
      ((fun w => c * w) '' ({1, a, b, a * b} : Set G)) := by
    rw [Set.disjoint_left]
    intro z hzP hzQ
    obtain ⟨w, hwP, rfl⟩ := hzQ
    have hzP' : c * w ∈ (Subgroup.closure {a, b} : Set G) := by rwa [hPsub]
    have hwP' : w ∈ (Subgroup.closure {a, b} : Set G) := by rwa [hPsub]
    have hc : c ∈ (Subgroup.closure {a, b} : Set G) := by
      have hcw : c = (c * w) * w⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hcw]
      exact (Subgroup.closure {a, b}).mul_mem hzP'
        ((Subgroup.closure {a, b}).inv_mem hwP')
    exact hcP' hc
  have hS : ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G) =
      ({1, a, b, a * b} : Set G) ∪ ((fun w => c * w) '' ({1, a, b, a * b} : Set G)) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_image]
    constructor
    · rintro (hz | hz | hz | hz | hz | hz | hz | hz)
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr (Or.inl hz))
      · exact Or.inl (Or.inr (Or.inr (Or.inl hz)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr hz)))
      · exact Or.inr ⟨1, Or.inl rfl, by rw [hz, mul_one]⟩
      · exact Or.inr ⟨a, Or.inr (Or.inl rfl), by rw [hz, hac.symm]⟩
      · exact Or.inr ⟨b, Or.inr (Or.inr (Or.inl rfl)), by rw [hz, hbc.symm]⟩
      · exact Or.inr ⟨a * b, Or.inr (Or.inr (Or.inr rfl)),
          by rw [hz, ← mul_assoc, ← hac, mul_assoc, ← hbc, ← mul_assoc]⟩
    · rintro (hz | ⟨w, hw, hwz⟩)
      · rcases hz with hz | hz | hz | hz
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr (Or.inl hz))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
      · rcases hw with hw | hw | hw | hw
        · rw [hw] at hwz
          rw [← hwz, mul_one]
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rw [hw] at hwz
          rw [← hwz, hac.symm]
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · rw [hw] at hwz
          rw [← hwz, hbc.symm]
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        · rw [hw] at hwz
          rw [← hwz, ← mul_assoc, ← hac, mul_assoc, ← hbc, ← mul_assoc]
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  rw [hS, Set.ncard_union_eq hdisj, hPcard, hQcard]

theorem sixFin_card_two {E : Subgroup G} (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : Nat.card ↥E = 2) :
    ∃ a ∈ E, a ≠ 1 ∧ ∀ x ∈ E, x = 1 ∨ x = a := by
  have hEfin : (E : Set G).Finite := by
    change Finite ↥(E : Set G)
    rw [SetLike.coe_sort_coe]
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hEncard : (E : Set G).ncard = 2 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]; exact hcard
  obtain ⟨a, haE, ha_notin⟩ : ∃ a ∈ E, a ∉ ({1} : Set G) :=
    s1611e3_exists_notMem (Set.finite_singleton 1)
      (by rw [Set.ncard_singleton, hcard]; omega)
  have ha1 : a ≠ 1 := by simpa using ha_notin
  refine ⟨a, haE, ha1, ?_⟩
  intro x hxE
  have hsub : ({1, a} : Set G) ⊆ (E : Set G) := by
    intro y hy
    rcases hy with hy | hy
    · rw [hy]; exact E.one_mem
    · rw [hy]; exact haE
  have hpair : ({1, a} : Set G).ncard = 2 := Set.ncard_pair ha1.symm
  have heq : ({1, a} : Set G) = (E : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hEfin
    rw [hEncard, hpair]
  have : x ∈ ({1, a} : Set G) := heq ▸ hxE
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this

theorem sixFin_card_four {E : Subgroup G} (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : Nat.card ↥E = 4) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ ∀ x ∈ E, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hEfin : (E : Set G).Finite := by
    change Finite ↥(E : Set G)
    rw [SetLike.coe_sort_coe]
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hEncard : (E : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]; exact hcard
  obtain ⟨a, haE, ha_notin⟩ : ∃ a ∈ E, a ∉ ({1} : Set G) :=
    s1611e3_exists_notMem (Set.finite_singleton 1)
      (by rw [Set.ncard_singleton, hcard]; omega)
  have ha1 : a ≠ 1 := by simpa using ha_notin
  have hfin2 : ({1, a} : Set G).Finite := (Set.finite_singleton a).insert 1
  have h2le : ({1, a} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({a} : Set G)
    simpa using this
  obtain ⟨b, hbE, hb_notin⟩ : ∃ b ∈ E, b ∉ ({1, a} : Set G) :=
    s1611e3_exists_notMem hfin2 (by omega)
  have hb1 : b ≠ 1 := by intro h; exact hb_notin (by simp [h])
  have hba : b ≠ a := by intro h; exact hb_notin (by simp [h])
  refine ⟨a, haE, b, hbE, ha1, hb1, hba.symm, ?_⟩
  have h4 : ({1, a, b, a * b} : Set G).ncard = 4 := by
    rw [Set.ncard_eq_four]
    refine ⟨1, a, b, a * b, ha1.symm, hb1.symm, ?_, hba.symm, ?_, ?_, rfl⟩
    · intro h
      have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hbE)
      have : a = b := by
        calc a = a * b * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
          _ = 1 * b⁻¹ := by rw [h.symm]
          _ = b := by rw [hb_inv, one_mul]
      exact hba this.symm
    · intro h
      have : b = 1 := by
        have h3 := congrArg (fun z => a * z) h
        rw [hsq a haE, ← mul_assoc, hsq a haE, one_mul] at h3
        exact h3.symm
      exact hb1 this
    · intro h
      have : a = 1 := by
        have h3 := congrArg (fun z => z * b⁻¹) h
        rw [mul_assoc, mul_inv_cancel, mul_one] at h3
        exact h3.symm
      exact ha1 this
  have hsub : ({1, a, b, a * b} : Set G) ⊆ (E : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy
    · rw [hy]; exact E.one_mem
    · rw [hy]; exact haE
    · rw [hy]; exact hbE
    · rw [hy]; exact E.mul_mem haE hbE
  have heq : ({1, a, b, a * b} : Set G) = (E : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hEfin
    rw [hEncard, h4]
  intro x hxE
  have : x ∈ ({1, a, b, a * b} : Set G) := heq ▸ hxE
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this

theorem sixFin_card_eight {E : Subgroup G} (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : Nat.card ↥E = 8) :
    ∃ a ∈ E, ∃ b ∈ E, ∃ c ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b ∧
      ∀ x ∈ E, x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = c ∨ x = a * c ∨ x = b * c ∨
        x = a * b * c := by
  have hEfin : (E : Set G).Finite := by
    change Finite ↥(E : Set G)
    rw [SetLike.coe_sort_coe]
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hEncard : (E : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]; exact hcard
  obtain ⟨a, haE, ha_notin⟩ : ∃ a ∈ E, a ∉ ({1} : Set G) :=
    s1611e3_exists_notMem (Set.finite_singleton 1)
      (by rw [Set.ncard_singleton, hcard]; omega)
  have ha1 : a ≠ 1 := by simpa using ha_notin
  have hfin2 : ({1, a} : Set G).Finite := (Set.finite_singleton a).insert 1
  have h2le : ({1, a} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({a} : Set G)
    simpa using this
  obtain ⟨b, hbE, hb_notin⟩ : ∃ b ∈ E, b ∉ ({1, a} : Set G) :=
    s1611e3_exists_notMem hfin2 (by omega)
  have hb1 : b ≠ 1 := by intro h; exact hb_notin (by simp [h])
  have hba : b ≠ a := by intro h; exact hb_notin (by simp [h])
  have hfin4 : ({1, a, b, a * b} : Set G).Finite :=
    (((Set.finite_singleton (a * b)).insert b).insert a).insert 1
  have h4le : ({1, a, b, a * b} : Set G).ncard ≤ 4 := by
    have e1 := Set.ncard_insert_le (b : G) ({a * b} : Set G)
    have e2 := Set.ncard_insert_le (a : G) ({b, a * b} : Set G)
    have e3 := Set.ncard_insert_le (1 : G) ({a, b, a * b} : Set G)
    simp only [Set.ncard_singleton] at e1
    omega
  obtain ⟨c, hcE, hc_notin⟩ : ∃ c ∈ E, c ∉ ({1, a, b, a * b} : Set G) :=
    s1611e3_exists_notMem hfin4 (by omega)
  have hc1 : c ≠ 1 := by intro h; exact hc_notin (by simp [h])
  have hca : c ≠ a := by intro h; exact hc_notin (by simp [h])
  have hcb : c ≠ b := by intro h; exact hc_notin (by simp [h])
  have hcab : c ≠ a * b := by intro h; exact hc_notin (by simp [h])
  refine ⟨a, haE, b, hbE, c, hcE, ha1, hb1, hc1, hba.symm, hca, hcb, hcab, ?_⟩
  have h8 : ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G).ncard = 8 :=
    s1611e3_ncard_eight (hsq a haE) (hsq b hbE) (hsq c hcE) (hcomm a haE b hbE)
      (hcomm a haE c hcE) (hcomm b hbE c hcE) ha1 hb1 hba.symm hc_notin
  have hsub : ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G) ⊆ (E : Set G) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
    · rw [hz]; exact E.one_mem
    · rw [hz]; exact haE
    · rw [hz]; exact hbE
    · rw [hz]; exact E.mul_mem haE hbE
    · rw [hz]; exact hcE
    · rw [hz]; exact E.mul_mem haE hcE
    · rw [hz]; exact E.mul_mem hbE hcE
    · rw [hz]; exact E.mul_mem (E.mul_mem haE hbE) hcE
  have heq : ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G) = (E : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hEfin
    rw [hEncard, h8]
  intro x hxE
  have : x ∈ ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G) := heq ▸ hxE
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this

theorem sixFin_card_gt {E : Subgroup G} (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : 8 < Nat.card ↥E) :
    ∃ a ∈ E, ∃ b ∈ E, ∃ c ∈ E, ∃ d ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ d ≠ 1 ∧ a ≠ b ∧ c ≠ a ∧
      c ≠ b ∧ c ≠ a * b ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ d ≠ a * b ∧ d ≠ a * c ∧ d ≠ b * c ∧
      d ≠ a * b * c := by
  obtain ⟨a, haE, ha_notin⟩ : ∃ a ∈ E, a ∉ ({1} : Set G) :=
    s1611e3_exists_notMem (Set.finite_singleton 1)
      (by rw [Set.ncard_singleton]; omega)
  have ha1 : a ≠ 1 := by simpa using ha_notin
  have hfin2 : ({1, a} : Set G).Finite := (Set.finite_singleton a).insert 1
  have h2le : ({1, a} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({a} : Set G)
    simpa using this
  obtain ⟨b, hbE, hb_notin⟩ : ∃ b ∈ E, b ∉ ({1, a} : Set G) :=
    s1611e3_exists_notMem hfin2 (by omega)
  have hb1 : b ≠ 1 := by intro h; exact hb_notin (by simp [h])
  have hba : b ≠ a := by intro h; exact hb_notin (by simp [h])
  have hfin4 : ({1, a, b, a * b} : Set G).Finite :=
    (((Set.finite_singleton (a * b)).insert b).insert a).insert 1
  have h4le : ({1, a, b, a * b} : Set G).ncard ≤ 4 := by
    have e1 := Set.ncard_insert_le (b : G) ({a * b} : Set G)
    have e2 := Set.ncard_insert_le (a : G) ({b, a * b} : Set G)
    have e3 := Set.ncard_insert_le (1 : G) ({a, b, a * b} : Set G)
    simp only [Set.ncard_singleton] at e1
    omega
  obtain ⟨c, hcE, hc_notin⟩ : ∃ c ∈ E, c ∉ ({1, a, b, a * b} : Set G) :=
    s1611e3_exists_notMem hfin4 (by omega)
  have hc1 : c ≠ 1 := by intro h; exact hc_notin (by simp [h])
  have hca : c ≠ a := by intro h; exact hc_notin (by simp [h])
  have hcb : c ≠ b := by intro h; exact hc_notin (by simp [h])
  have hcab : c ≠ a * b := by intro h; exact hc_notin (by simp [h])
  have hfin8 : ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G).Finite :=
    (((((((Set.finite_singleton (a * b * c)).insert (b * c)).insert (a * c)).insert c).insert
      (a * b)).insert b).insert a).insert 1
  have h8le : ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G).ncard ≤ 8 := by
    have e1 := Set.ncard_insert_le (b * c : G) ({a * b * c} : Set G)
    have e2 := Set.ncard_insert_le (a * c : G) ({b * c, a * b * c} : Set G)
    have e3 := Set.ncard_insert_le (c : G) ({a * c, b * c, a * b * c} : Set G)
    have e4 := Set.ncard_insert_le (a * b : G) ({c, a * c, b * c, a * b * c} : Set G)
    have e5 := Set.ncard_insert_le (b : G) ({a * b, c, a * c, b * c, a * b * c} : Set G)
    have e6 := Set.ncard_insert_le (a : G) ({b, a * b, c, a * c, b * c, a * b * c} : Set G)
    have e7 := Set.ncard_insert_le (1 : G) ({a, b, a * b, c, a * c, b * c, a * b * c} : Set G)
    simp only [Set.ncard_singleton] at e1
    omega
  obtain ⟨d, hdE, hd_notin⟩ : ∃ d ∈ E,
      d ∉ ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Set G) :=
    s1611e3_exists_notMem hfin8 (by omega)
  have hd1 : d ≠ 1 := by intro h; exact hd_notin (by simp [h])
  have hda : d ≠ a := by intro h; exact hd_notin (by simp [h])
  have hdb : d ≠ b := by intro h; exact hd_notin (by simp [h])
  have hdc : d ≠ c := by intro h; exact hd_notin (by simp [h])
  have hdab : d ≠ a * b := by intro h; exact hd_notin (by simp [h])
  have hdac : d ≠ a * c := by intro h; exact hd_notin (by simp [h])
  have hdbc : d ≠ b * c := by intro h; exact hd_notin (by simp [h])
  have hdabc : d ≠ a * b * c := by intro h; exact hd_notin (by simp [h])
  exact ⟨a, haE, b, hbE, c, hcE, d, hdE, ha1, hb1, hc1, hd1, hba.symm, hca, hcb, hcab,
    hda, hdb, hdc, hdab, hdac, hdbc, hdabc⟩

theorem sixFin_closure_two {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(Subgroup.closure {x}) = 2 ∧ ∀ z ∈ Subgroup.closure {x}, z = 1 ∨ z = x :=
  s1611e3_closure_two_aux hx hx1

theorem sixFin_closure_four {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card ↥(Subgroup.closure {x, y}) = 4 ∧
      ∀ z ∈ Subgroup.closure {x, y}, z = 1 ∨ z = x ∨ z = y ∨ z = x * y :=
  s1611e3_closure_four_aux hx hy hxy hx1 hy1 hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
