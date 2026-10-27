module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7G
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_centralizes {E Y : Subgroup G} (hE9 : Nat.card E = 9)
    (hE3 : ∀ y ∈ E, y ^ 3 = 1) (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    (hY8 : Nat.card Y ≤ 8) : ∃ y ∈ E, y ≠ 1 ∧ ∀ v ∈ Y, y * v * y⁻¹ = v := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥E)
      (by rw [hE9]; norm_num)
    exact congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  have : Fintype ↥E := Fintype.ofFinite _
  have hYc : (Set.toFinite (Y : Set G)).toFinset.card = Nat.card Y :=
    (Nat.card_eq_card_finite_toFinset (Set.toFinite (Y : Set G))).symm
  have hcard : ∀ v ∈ Y, Nat.card ↥(stab E v) = 3 ∨ stab E v = E := by
    intro v hv
    have hdvd : Nat.card ↥(stab E v) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hE9]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hk'
      have hinj : Function.Injective (fun y : ↥E => (y : G) * v * (y : G)⁻¹) := by
        intro a b hab
        have h1 : (b : G)⁻¹ * a ∈ stab E v := by
          refine mem_stab.mpr ⟨E.mul_mem (E.inv_mem b.2) a.2, ?_⟩
          have hab' : (a : G) * v * (a : G)⁻¹ = (b : G) * v * (b : G)⁻¹ := hab
          calc (b : G)⁻¹ * a * v * ((b : G)⁻¹ * a)⁻¹
              = (b : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * b := by group
            _ = v := by rw [hab']; group
        rw [hk', Subgroup.mem_bot, inv_mul_eq_one] at h1
        exact Subtype.ext h1.symm
      have h9 : 9 ≤ (Set.toFinite (Y : Set G)).toFinset.card := by
        rw [← hE9, Nat.card_eq_fintype_card, ← Finset.card_univ,
          ← Finset.card_image_of_injective _ hinj]
        refine Finset.card_le_card fun x hx => ?_
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
        rw [Set.Finite.mem_toFinset]
        exact (Subgroup.mem_normalizer_iff.mp (hEY y.2) v).mp hv
      omega
    · left
      rw [hk']
      norm_num
    · right
      exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hE9]; norm_num)
  have hne1 : ∀ v ∈ Y, Nat.card ↥(stab E v) = 3 → v ≠ 1 := by
    rintro v - h3 rfl
    have : stab E 1 = E := inf_eq_left.mpr fun y _ => Subgroup.mem_centralizer_singleton_iff.mpr
      (by group)
    rw [this, hE9] at h3
    omega
  have hexists : ∀ v ∈ Y, Nat.card ↥(stab E v) = 3 → ∃ y ∈ E, y ∉ stab E v := by
    rintro v - h3
    by_contra h
    push Not at h
    have : stab E v = E := le_antisymm inf_le_left h
    rw [this, hE9] at h3
    omega
  by_cases hall : ∀ v ∈ Y, stab E v = E
  · obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (fun h : E = ⊥ => by rw [h, Subgroup.card_bot] at hE9; omega)
    refine ⟨y, y.2, fun h => hy (Subtype.ext h), fun v hv => ?_⟩
    have := (hall v hv).ge y.2
    exact (mem_stab.mp this).2
  push Not at hall
  obtain ⟨v₁, hv₁, hS₁⟩ := hall
  have h3₁ := (hcard v₁ hv₁).resolve_right hS₁
  have hkey : ∀ v ∈ Y, stab E v₁ ≤ stab E v := by
    intro v hv
    by_contra hle
    have h3 : Nat.card ↥(stab E v) = 3 := (hcard v hv).resolve_right fun h => by
      apply hle
      rw [h]
      exact inf_le_left
    have hne : stab E v₁ ≠ stab E v := fun h => hle h.le
    have hinter : ∀ {A B : Subgroup G}, Nat.card A = 3 → ¬ A ≤ B → A ⊓ B = ⊥ := by
      intro A B hA hAB
      have hdvd : Nat.card ↥(A ⊓ B) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        apply hAB
        have := Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ B ≤ A) (by rw [hA, h3'])
        exact this ▸ inf_le_right
    have h12 := hinter h3₁ hle
    have hv₃ : v₁ * v ∈ Y := Y.mul_mem hv₁ hv
    have hle₁ : stab E (v₁ * v) ⊓ stab E v₁ ≤ stab E v := by
      intro e ⟨he3, he1⟩
      obtain ⟨heE, h3e⟩ := mem_stab.mp he3
      obtain ⟨-, h1e⟩ := mem_stab.mp he1
      refine mem_stab.mpr ⟨heE, ?_⟩
      calc e * v * e⁻¹ = (e * v₁ * e⁻¹)⁻¹ * (e * (v₁ * v) * e⁻¹) := by group
        _ = v := by rw [h1e, h3e]; group
    have hle₂ : stab E (v₁ * v) ⊓ stab E v ≤ stab E v₁ := by
      intro e ⟨he3, he2⟩
      obtain ⟨heE, h3e⟩ := mem_stab.mp he3
      obtain ⟨-, h2e⟩ := mem_stab.mp he2
      refine mem_stab.mpr ⟨heE, ?_⟩
      calc e * v₁ * e⁻¹ = (e * (v₁ * v) * e⁻¹) * (e * v * e⁻¹)⁻¹ := by group
        _ = v₁ := by rw [h2e, h3e]; group
    have hb₁ : stab E (v₁ * v) ⊓ stab E v₁ = ⊥ := by
      rw [eq_bot_iff, ← h12, inf_comm (stab E v₁)]
      exact le_inf hle₁ inf_le_right
    have hb₂ : stab E (v₁ * v) ⊓ stab E v = ⊥ := by
      rw [eq_bot_iff, ← h12]
      exact le_inf hle₂ inf_le_right
    have hS1ne : stab E v₁ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at h3₁; omega
    have hS2ne : stab E v ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at h3; omega
    have h33 : Nat.card ↥(stab E (v₁ * v)) = 3 := (hcard _ hv₃).resolve_right fun h => by
      rw [h, inf_eq_right.mpr inf_le_left] at hb₁
      exact hS1ne hb₁
    have hne₁ : stab E (v₁ * v) ≠ stab E v₁ := fun h => by
      rw [h, inf_idem] at hb₁
      exact hS1ne hb₁
    have hne₂ : stab E (v₁ * v) ≠ stab E v := fun h => by
      rw [h, inf_idem] at hb₂
      exact hS2ne hb₂
    obtain ⟨y₁, hy₁, hy₁'⟩ := hexists v₁ hv₁ h3₁
    obtain ⟨y₂, hy₂, hy₂'⟩ := hexists v hv h3
    obtain ⟨y₃, hy₃, hy₃'⟩ := hexists _ hv₃ h33
    have c₁ := three_le_card_orb hE3 hy₁ hy₁'
    have c₂ := three_le_card_orb hE3 hy₂ hy₂'
    have c₃ := three_le_card_orb hE3 hy₃ hy₃'
    have d₁₂ := disjoint_orb hEc hne
    have d₁₃ := disjoint_orb hEc hne₁.symm
    have d₂₃ := disjoint_orb hEc hne₂.symm
    have hU : (orb E v₁ ∪ orb E v ∪ orb E (v₁ * v)).card ≥ 9 := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d₁₃, d₂₃⟩),
        Finset.card_union_of_disjoint d₁₂]
      omega
    have h1U : (1 : G) ∉ orb E v₁ ∪ orb E v ∪ orb E (v₁ * v) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨one_notMem_orb (hne1 v₁ hv₁ h3₁), one_notMem_orb (hne1 v hv h3)⟩,
        one_notMem_orb (hne1 _ hv₃ h33)⟩
    have hsub : insert 1 (orb E v₁ ∪ orb E v ∪ orb E (v₁ * v)) ⊆
        (Set.toFinite (Y : Set G)).toFinset := by
      refine Finset.insert_subset ?_ (Finset.union_subset (Finset.union_subset
        (orb_subset hEY hv₁) (orb_subset hEY hv)) (orb_subset hEY hv₃))
      rw [Set.Finite.mem_toFinset]
      exact Y.one_mem
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem h1U] at this
    omega
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (fun h : stab E v₁ = ⊥ => by rw [h, Subgroup.card_bot] at h3₁; omega)
  refine ⟨y, (inf_le_left : stab E v₁ ≤ E) y.2, fun h => hy (Subtype.ext h), fun v hv => ?_⟩
  exact (mem_stab.mp (hkey v hv y.2)).2

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7
