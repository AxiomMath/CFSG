module

public import CFSG.Timmesfeld.ARS.CaseOADegLevi
public import CFSG.Timmesfeld.ARS.CaseOADegSpAlign
public import CFSG.Timmesfeld.ARS.CaseMSpLevi

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Matrix Transvection CFSG.LieType CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CaseM

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOADeg

section Lagr

variable {n : ℕ} {F : Type} [Field F]

theorem spForm_apply (u v : Fin n ⊕ Fin n → F) :
    spForm u v = ∑ i, (u (Sum.inl i) * v (Sum.inr i) - u (Sum.inr i) * v (Sum.inl i)) := by
  simp [spForm, spGram, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply,
    sub_eq_add_neg, Finset.sum_add_distrib]

theorem spForm_eq_zero_of_inl {u v : Fin n ⊕ Fin n → F} (hu : ∀ i, u (Sum.inl i) = 0)
    (hv : ∀ i, v (Sum.inl i) = 0) : spForm u v = 0 := by
  simp [spForm_apply, hu, hv]

theorem spForm_eq_zero_of_inr {u v : Fin n ⊕ Fin n → F} (hu : ∀ i, u (Sum.inr i) = 0)
    (hv : ∀ i, v (Sum.inr i) = 0) : spForm u v = 0 := by
  simp [spForm_apply, hu, hv]

theorem spForm_single_inr (v : Fin n ⊕ Fin n → F) (i : Fin n) :
    spForm v (Pi.single (Sum.inr i) 1) = v (Sum.inl i) := by
  simp [spForm_apply, Pi.single_apply]

theorem spForm_single_inl (v : Fin n ⊕ Fin n → F) (i : Fin n) :
    spForm v (Pi.single (Sum.inl i) 1) = -v (Sum.inr i) := by
  simp [spForm_apply, Pi.single_apply]

theorem mulVec_spElt_apply [CharP F 2] {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (hba : b ≠ a)
    (c : F) (v : Fin n ⊕ Fin n → F) (x : Fin n ⊕ Fin n) :
    (Symplectic.SpExtras.mat n F (spElt a b c) *ᵥ v) x =
      v x + c * ((if x = a then v (Sum.swap b) else 0) +
        (if x = b then v (Sum.swap a) else 0)) := by
  rw [mat_spElt hab]
  simp only [hba, ↓reduceIte, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul,
    Function.update_apply, Pi.zero_apply]

theorem inl_eq_zero_of_commuting {v : Fin 2 ⊕ Fin 2 → F} {X : Subgroup (StatedSp 2 F)}
    (hX : IsTransGroup v X) (hv : v ≠ 0) (i : Fin 2)
    (hc : Commuting X (Symplectic.rootGroup 2 F (-longC2 i))) : v (Sum.inl i) = 0 := by
  rcases hX.spForm_eq_zero (isTransGroup_neg₂ i) hv hc with h | ⟨l, hl⟩
  · rwa [spForm_single_inr] at h
  · have h1 := congrFun hl (Sum.inr i)
    have h2 := congrFun hl (Sum.inl i)
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul, reduceCtorEq, ite_false,
      ite_true] at h1 h2
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at h1
    exact (mul_eq_zero.1 h2.symm).resolve_left hl0

theorem inr_eq_zero_of_commuting {v : Fin 2 ⊕ Fin 2 → F} {X : Subgroup (StatedSp 2 F)}
    (hX : IsTransGroup v X) (hv : v ≠ 0) (i : Fin 2)
    (hc : Commuting X (Symplectic.rootGroup 2 F (longC2 i))) : v (Sum.inr i) = 0 := by
  rcases hX.spForm_eq_zero (isTransGroup_pos₂ i) hv hc with h | ⟨l, hl⟩
  · rw [spForm_single_inl, neg_eq_zero] at h
    exact h
  · have h1 := congrFun hl (Sum.inl i)
    have h2 := congrFun hl (Sum.inr i)
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul, reduceCtorEq, ite_false,
      ite_true] at h1 h2
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at h1
    exact (mul_eq_zero.1 h2.symm).resolve_left hl0

end Lagr

theorem exists_isTransGroup {F : Type} [Field F] {Φ : StatedSp 2 F →* G}
    {Δ₁ : Set (Subgroup G)}
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 2 F (Pi.single 1 1)) g).map Φ)
    {X : Subgroup G} (hX : X ∈ Δ₁) :
    ∃ v : Fin 2 ⊕ Fin 2 → F, ∃ X' : Subgroup (StatedSp 2 F), IsTransGroup v X' ∧ v ≠ 0 ∧
      X = X'.map Φ := by
  obtain ⟨g, rfl⟩ := (hΔ X).1 hX
  have he0 : (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) ≠ 0 := fun h0 => by
    have := congrFun h0 (Sum.inl 1)
    simp at this
  have hT := isTransGroup_pos₂ (F := F) 1
  rw [longC2_one] at hT
  exact ⟨_, _, hT.conjSub g, mat_mulVec_ne_zero' g he0, rfl⟩

namespace DegOA

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)} (hD : DegOA R A A₀ Δ₁ Δ₂)
include hD

theorem conjSub_mem_deltaSet {F : Type} [Field F] {Φ : StatedSp 2 F →* G}
    (hΦ : Function.Injective Φ) (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 2 F (Pi.single 1 1)) g).map Φ)
    {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (L : (Fin 2 ⊕ Fin 2 → F) → Prop)
    (hL : ∀ (v : Fin 2 ⊕ Fin 2 → F) (X' : Subgroup (StatedSp 2 F)), IsTransGroup v X' → v ≠ 0 →
      X'.map Φ ∈ deltaSet R A A₀ B → L v)
    (hLL : ∀ v w, L v → L w → spForm v w = 0) {z₀ : StatedSp 2 F}
    (hz₀ : ∀ v, L v → L (Symplectic.SpExtras.mat 2 F z₀ *ᵥ v)) :
    ∀ X ∈ deltaSet R A A₀ B, conjSub X (Φ z₀) ∈ deltaSet R A A₀ B := by
  have hR := hD.hyp.root
  have hzV : Φ z₀ ∈ gen Δ₁ := hrange ▸ ⟨z₀, rfl⟩
  have hzl : Φ z₀ ∈ levi R A A₀ := hD.gen₁_le_levi hzV
  have hz₂ : ∀ {Y : Subgroup G}, Y ∈ Δ₂ → ∀ y ∈ Y, Commute (Φ z₀) y := fun hY y hy =>
    hD.commuting_gen _ hzV y (le_gen hY hy)
  intro X hX
  rcases hD.mem_or_mem hX.1 with hX₁ | hX₂
  · obtain ⟨v, X', hX'T, hv, rfl⟩ := exists_isTransGroup hΔ hX₁
    have hLv := hL v X' hX'T hv hX
    have hconj : conjSub (X'.map Φ) (Φ z₀) = (conjSub X' z₀).map Φ :=
      ModelRank.conjSub_map Φ X' z₀
    have hmem : conjSub (X'.map Φ) (Φ z₀) ∈ leviSet R A A₀ :=
      Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hzl
    refine hD.sec12.mem_deltaSet_of_forall_commuting hB hmem fun Y hY => ?_
    rcases hD.mem_or_mem hY.1 with hY₁ | hY₂
    · obtain ⟨w, Y', hY'T, hw, rfl⟩ := exists_isTransGroup hΔ hY₁
      rw [hconj]
      exact (CaseM.commuting_map_iff hΦ).2 ((hX'T.conjSub z₀).commuting hY'T
        (hLL _ _ (hz₀ v hLv) (hL w Y' hY'T hw hY)))
    · have hle : conjSub (X'.map Φ) (Φ z₀) ≤ gen Δ₁ := by
        rw [hconj, ← hrange]
        exact Subgroup.map_le_range Φ _
      exact hD.commuting_gen.mono hle (le_gen hY₂)
  · rw [conjSub_of_forall_commute (hz₂ hX₂)]
    exact hX

theorem commute_of_preserves {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : Sec12.IsSubframe R A A₀ E C P Q) (h0 : P 0 ∈ Δ₂ ∧ Q 0 ∈ Δ₂) {F : Type} [Field F]
    {Φ : StatedSp 2 F →* G} (hΦ : Function.Injective Φ) (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 2 F (Pi.single 1 1)) g).map Φ)
    (LE LC : (Fin 2 ⊕ Fin 2 → F) → Prop)
    (hLE : ∀ (v : Fin 2 ⊕ Fin 2 → F) (X' : Subgroup (StatedSp 2 F)), IsTransGroup v X' → v ≠ 0 →
      X'.map Φ ∈ deltaSet R A A₀ E → LE v)
    (hLC : ∀ (v : Fin 2 ⊕ Fin 2 → F) (X' : Subgroup (StatedSp 2 F)), IsTransGroup v X' → v ≠ 0 →
      X'.map Φ ∈ deltaSet R A A₀ C → LC v)
    (hLLE : ∀ v w, LE v → LE w → spForm v w = 0) (hLLC : ∀ v w, LC v → LC w → spForm v w = 0)
    {z₀ : StatedSp 2 F} (hz₀E : ∀ v, LE v → LE (Symplectic.SpExtras.mat 2 F z₀ *ᵥ v))
    (hz₀C : ∀ v, LC v → LC (Symplectic.SpExtras.mat 2 F z₀ *ᵥ v)) (hz2 : z₀ * z₀ = 1) :
    (∀ e ∈ E, Commute (Φ z₀) e) ∧ ∀ c ∈ C, Commute (Φ z₀) c := by
  have hzV : Φ z₀ ∈ gen Δ₁ := hrange ▸ ⟨z₀, rfl⟩
  have hzl : Φ z₀ ∈ levi R A A₀ := hD.gen₁_le_levi hzV
  have hz2' : Φ z₀ * Φ z₀ = 1 := by rw [← map_mul, hz2, map_one]
  have hz₂ : ∀ {Y : Subgroup G}, Y ∈ Δ₂ → ∀ y ∈ Y, Commute (Φ z₀) y := fun hY y hy =>
    hD.commuting_gen _ hzV y (le_gen hY hy)
  have hEz := hD.sec12.conjSub_eq_of_deltaSet_subset hfr.memE hzl hz2'
    (hD.conjSub_mem_deltaSet hΦ hrange hΔ hfr.memE LE hLE hLLE hz₀E)
  have hCz := hD.sec12.conjSub_eq_of_deltaSet_subset hfr.memC hzl hz2'
    (hD.conjSub_mem_deltaSet hΦ hrange hΔ hfr.memC LC hLC hLLC hz₀C)
  exact ⟨hD.sec12.commute_of_conjSub_eq_of_pair hfr.memE (hfr.memP 0).1 (hfr.memQ 0).1
      (hfr.opposite 0) (hfr.memQ 0).2.1.2.2.symm hEz (hz₂ h0.1) (hz₂ h0.2) hz2',
    hD.sec12.commute_of_conjSub_eq_of_pair hfr.memC (hfr.memQ 0).1 (hfr.memP 0).1
      (hfr.opposite 0).symm (hfr.memP 0).2.1.2.2.symm hCz (hz₂ h0.2) (hz₂ h0.1) hz2'⟩

theorem commute_short {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : Sec12.IsSubframe R A A₀ E C P Q) (h0 : P 0 ∈ Δ₂ ∧ Q 0 ∈ Δ₂) {F : Type} [Field F]
    [CharP F 2] {Φ : StatedSp 2 F →* G} (hΦ : Function.Injective Φ) (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 2 F (Pi.single 1 1)) g).map Φ)
    (hP : ∀ i, (Symplectic.rootGroup 2 F (longC2 i)).map Φ = ![P 2, P 1] i)
    (hQ : ∀ i, (Symplectic.rootGroup 2 F (-longC2 i)).map Φ = ![Q 2, Q 1] i)
    {a b : Fin 2 ⊕ Fin 2} (hab : (a = Sum.inl 0 ∧ b = Sum.inr 1) ∨ (a = Sum.inl 1 ∧ b = Sum.inr 0))
    (c : F) : (∀ e ∈ E, Commute (Φ (spElt a b c)) e) ∧ ∀ x ∈ C, Commute (Φ (spElt a b c)) x := by
  have hR := hD.hyp.root
  have hQE : ∀ i, (Symplectic.rootGroup 2 F (-longC2 i)).map Φ ∈ deltaSet R A A₀ E := fun i => by
    rw [hQ i]; fin_cases i; exacts [hfr.memQ 2, hfr.memQ 1]
  have hPC : ∀ i, (Symplectic.rootGroup 2 F (longC2 i)).map Φ ∈ deltaSet R A A₀ C := fun i => by
    rw [hP i]; fin_cases i; exacts [hfr.memP 2, hfr.memP 1]
  have hLE : ∀ (v : Fin 2 ⊕ Fin 2 → F) (X' : Subgroup (StatedSp 2 F)), IsTransGroup v X' →
      v ≠ 0 → X'.map Φ ∈ deltaSet R A A₀ E → ∀ i, v (Sum.inl i) = 0 := fun v X' hT hv hX i =>
    inl_eq_zero_of_commuting hT hv i ((CaseM.commuting_map_iff hΦ).1
      (hD.sec12.commuting_of_mem_deltaSet' hfr.memE hX (hQE i)))
  have hLC : ∀ (v : Fin 2 ⊕ Fin 2 → F) (X' : Subgroup (StatedSp 2 F)), IsTransGroup v X' →
      v ≠ 0 → X'.map Φ ∈ deltaSet R A A₀ C → ∀ i, v (Sum.inr i) = 0 := fun v X' hT hv hX i =>
    inr_eq_zero_of_commuting hT hv i ((CaseM.commuting_map_iff hΦ).1
      (hD.sec12.commuting_of_mem_deltaSet' hfr.memC hX (hPC i)))
  have hab' : b ≠ Sum.swap a := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hba : b ≠ a := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hpres : ∀ v : Fin 2 ⊕ Fin 2 → F, ((∀ i, v (Sum.inl i) = 0) →
      ∀ i, (Symplectic.SpExtras.mat 2 F (spElt a b c) *ᵥ v) (Sum.inl i) = 0) ∧
      ((∀ i, v (Sum.inr i) = 0) →
        ∀ i, (Symplectic.SpExtras.mat 2 F (spElt a b c) *ᵥ v) (Sum.inr i) = 0) := by
    intro v
    refine ⟨fun hv i => ?_, fun hv i => ?_⟩ <;> rw [mulVec_spElt_apply hab' hba] <;>
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases i <;> simp [hv]
  have hz2 : spElt a b c * spElt a b c = 1 := by
    rw [← spElt_add, CharTwo.add_self_eq_zero, spElt_zero]
  exact hD.commute_of_preserves hfr h0 hΦ hrange hΔ _ _ hLE hLC
    (fun v w hv hw => spForm_eq_zero_of_inl hv hw) (fun v w hv hw => spForm_eq_zero_of_inr hv hw)
    (fun v hv => (hpres v).1 hv) (fun v hv => (hpres v).2 hv) hz2

end DegOA

end CaseOADeg

end CFSG.Timmesfeld.ARS
