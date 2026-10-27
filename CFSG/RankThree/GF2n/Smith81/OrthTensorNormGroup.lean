module

public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

variable {Γ : Type*} [Group Γ]

structure ThreeFactors (A : Fin 3 → Subgroup Γ) (E : Subgroup Γ) : Prop where
  le : ∀ i, A i ≤ E
  simple : ∀ i, IsSimpleGroup ↥(A i)
  nonab : ∀ i, ∃ x ∈ A i, ∃ y ∈ A i, x * y ≠ y * x
  comm : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, x * y = y * x
  gen : ∀ e ∈ E, ∃ a₀ ∈ A 0, ∃ a₁ ∈ A 1, ∃ a₂ ∈ A 2, e = a₀ * a₁ * a₂

theorem eq_one_of_mem_of_commute_of_isSimpleGroup {S : Subgroup Γ} (hS : IsSimpleGroup S)
    (hn : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) {a : Γ} (ha : a ∈ S)
    (hc : ∀ y ∈ S, y * a = a * y) : a = 1 := by
  have hz : (⟨a, ha⟩ : S) ∈ Subgroup.center S :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2)
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  · obtain ⟨x, hx, y, hy, hxy⟩ := hn
    refine absurd ?_ hxy
    have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (⟨y, hy⟩ : S)) ⟨x, hx⟩
    exact congrArg Subtype.val this

theorem eq_bot_or_eq_of_isSimpleGroup_of_normalized {A B : Subgroup Γ} (hAB : A ≤ B)
    (hB : IsSimpleGroup B) (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) : A = ⊥ ∨ A = B := by
  have hN : (A.subgroupOf B).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr (by
      simpa using hn g g.2 x (Subgroup.mem_subgroupOf.mp hx))⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (A.subgroupOf B) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact eq_bot_iff.mpr fun a ha =>
      Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h ha (hAB ha))
  · right
    exact le_antisymm hAB (Subgroup.subgroupOf_eq_top.mp h)

namespace ThreeFactors

variable {A : Fin 3 → Subgroup Γ} {E : Subgroup Γ}

theorem ne (h : ThreeFactors A E) {i j : Fin 3} (hij : i ≠ j) : A i ≠ A j := by
  intro hA
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nonab i
  exact hxy (h.comm i j hij x hx y (by rw [← hA]; exact hy))

theorem conj_mem (h : ThreeFactors A E) (i : Fin 3) {e : Γ} (he : e ∈ E) {x : Γ}
    (hx : x ∈ A i) : e * x * e⁻¹ ∈ A i := by
  have step : ∀ k, ∀ a ∈ A k, ∀ x ∈ A i, a * x * a⁻¹ ∈ A i := by
    intro k a ha x hx
    by_cases hk : k = i
    · subst hk
      exact mul_mem (mul_mem ha hx) (inv_mem ha)
    · rw [h.comm k i hk a ha x hx, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
  obtain ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, rfl⟩ := h.gen e he
  have e1 : a₀ * a₁ * a₂ * x * (a₀ * a₁ * a₂)⁻¹ =
      a₀ * (a₁ * (a₂ * x * a₂⁻¹) * a₁⁻¹) * a₀⁻¹ := by group
  rw [e1]
  exact step 0 a₀ ha₀ _ (step 1 a₁ ha₁ _ (step 2 a₂ ha₂ x hx))

theorem conj_iff (h : ThreeFactors A E) (i : Fin 3) {e : Γ} (he : e ∈ E) (x : Γ) :
    x ∈ A i ↔ e * x * e⁻¹ ∈ A i := by
  refine ⟨h.conj_mem i he, fun hx => ?_⟩
  have h1 := h.conj_mem i (inv_mem he) hx
  have e1 : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
  rwa [e1] at h1

theorem eq_one (h : ThreeFactors A E) {z : Γ} (hz : z ∈ E)
    (hc : ∀ i, ∀ s ∈ A i, z * s = s * z) : z = 1 := by
  obtain ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, rfl⟩ := h.gen z hz
  have hz' : ∀ i, a₀ * a₁ * a₂ ∈ Subgroup.centralizer (A i : Set Γ) := fun i =>
    Subgroup.mem_centralizer_iff.mpr fun s hs => (hc i s hs).symm
  have hother : ∀ i j, j ≠ i → ∀ a ∈ A j, a ∈ Subgroup.centralizer (A i : Set Γ) :=
    fun i j hji a ha =>
      Subgroup.mem_centralizer_iff.mpr fun s hs => h.comm i j (Ne.symm hji) s hs a ha
  have key : ∀ i, ∀ a ∈ A i, a ∈ Subgroup.centralizer (A i : Set Γ) → a = 1 :=
    fun i a ha hca => eq_one_of_mem_of_commute_of_isSimpleGroup (h.simple i) (h.nonab i) ha
      fun y hy => Subgroup.mem_centralizer_iff.mp hca y hy
  have h0 : a₀ = 1 := by
    refine key 0 a₀ ha₀ ?_
    have e1 : a₀ = a₀ * a₁ * a₂ * (a₁ * a₂)⁻¹ := by group
    rw [e1]
    exact mul_mem (hz' 0)
      (inv_mem (mul_mem (hother 0 1 (by decide) a₁ ha₁) (hother 0 2 (by decide) a₂ ha₂)))
  have h1 : a₁ = 1 := by
    refine key 1 a₁ ha₁ ?_
    have e1 : a₁ = a₀⁻¹ * (a₀ * a₁ * a₂) * a₂⁻¹ := by group
    rw [e1]
    exact mul_mem (mul_mem (inv_mem (hother 1 0 (by decide) a₀ ha₀)) (hz' 1))
      (inv_mem (hother 1 2 (by decide) a₂ ha₂))
  have h2 : a₂ = 1 := by
    refine key 2 a₂ ha₂ ?_
    have e1 : a₂ = (a₀ * a₁)⁻¹ * (a₀ * a₁ * a₂) := by group
    rw [e1]
    exact mul_mem
      (inv_mem (mul_mem (hother 2 0 (by decide) a₀ ha₀) (hother 2 1 (by decide) a₁ ha₁)))
      (hz' 2)
  rw [h0, h1, h2, one_mul, one_mul]

theorem exists_eq_of_normal (h : ThreeFactors A E) {K : Subgroup Γ} (hKE : K ≤ E)
    (hKn : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ ∈ K) (hK : IsSimpleGroup K) : ∃ j, K = A j := by
  by_contra hne
  push Not at hne
  have hbot : ∀ j, K ⊓ A j = ⊥ := by
    intro j
    rcases eq_bot_or_eq_of_isSimpleGroup_of_normalized (inf_le_right : K ⊓ A j ≤ A j)
        (h.simple j) (fun b hb a ha => Subgroup.mem_inf.mpr
          ⟨hKn b (h.le j hb) a (Subgroup.mem_inf.mp ha).1,
            mul_mem (mul_mem hb (Subgroup.mem_inf.mp ha).2) (inv_mem hb)⟩) with h1 | h1
    · exact h1
    · exfalso
      have hAK : A j ≤ K := inf_eq_right.mp h1
      rcases eq_bot_or_eq_of_isSimpleGroup_of_normalized hAK hK
          (fun b hb a ha => h.conj_mem j (hKE hb) ha) with h2 | h2
      · obtain ⟨x, hx, y, hy, hxy⟩ := h.nonab j
        rw [h2, Subgroup.mem_bot] at hx hy
        exact hxy (by rw [hx, hy])
      · exact hne j h2.symm
  have hcomm : ∀ j, ∀ k ∈ K, ∀ s ∈ A j, k * s = s * k := by
    intro j k hk s hs
    have hmem : k * s * k⁻¹ * s⁻¹ ∈ K ⊓ A j := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : s * k⁻¹ * s⁻¹ ∈ K := hKn s (h.le j hs) k⁻¹ (inv_mem hk)
        have e1 : k * s * k⁻¹ * s⁻¹ = k * (s * k⁻¹ * s⁻¹) := by group
        rw [e1]
        exact mul_mem hk h1
      · exact mul_mem (h.conj_mem j (hKE hk) hs) (inv_mem hs)
    rw [hbot j, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hmem)
  have hK1 : ∀ k ∈ K, k = 1 := fun k hk => h.eq_one (hKE hk) fun j s hs => hcomm j k hk s hs
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne K
  exact hab (Subtype.ext ((hK1 a ha).trans (hK1 b hb).symm))

theorem exists_perm (h : ThreeFactors A E) (T : Γ) (hT : ∀ x ∈ E, T * x * T⁻¹ ∈ E)
    (hT' : ∀ x ∈ E, T⁻¹ * x * T ∈ E) :
    ∃ π : Equiv.Perm (Fin 3), ∀ (i : Fin 3) (x : Γ), x ∈ A i ↔ T * x * T⁻¹ ∈ A (π i) := by
  have hmem : ∀ i x, x ∈ (A i).map (MulAut.conj T).toMonoidHom ↔ T⁻¹ * x * T ∈ A i := by
    intro i x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have key : ∀ i, ∃ j, (A i).map (MulAut.conj T).toMonoidHom = A j := by
    intro i
    refine h.exists_eq_of_normal ?_ ?_ ?_
    · intro x hx
      have h1 := hT _ (h.le i ((hmem i x).mp hx))
      have e1 : T * (T⁻¹ * x * T) * T⁻¹ = x := by group
      rwa [e1] at h1
    · intro e he k hk
      rw [hmem] at hk ⊢
      have h1 := h.conj_mem i (hT' e he) hk
      have e1 : T⁻¹ * (e * k * e⁻¹) * T = (T⁻¹ * e * T) * (T⁻¹ * k * T) * (T⁻¹ * e * T)⁻¹ := by
        group
      rwa [e1]
    · have := h.simple i
      exact ((A i).equivMapOfInjective _ (MulAut.conj T).injective).symm.isSimpleGroup
  choose f hf using key
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    apply h.ne hne
    have h1 : (A i).map (MulAut.conj T).toMonoidHom = (A j).map (MulAut.conj T).toMonoidHom := by
      rw [hf i, hf j, hij]
    exact Subgroup.map_injective (MulAut.conj T).injective h1
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i x => ?_⟩
  rw [Equiv.ofBijective_apply, ← hf i, hmem]
  have e1 : T⁻¹ * (T * x * T⁻¹) * T = x := by group
  rw [e1]

end ThreeFactors

end CFSG.RankThree.GF2n.Smith81.OrthTN
