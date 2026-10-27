module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRC_absIrred_of_connected {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (hp2 : p ≠ 2) {ι : Type}
    (g : ι → (V ≃ₗ[ZMod p] V)) (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
    (hg : ∀ i w, g i w = w - α i w • h i) (hα : ∀ i, α i (h i) = 2)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤)
    (hker : ∀ w, (∀ i, α i w = 0) → w = 0)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hA : A = Subgroup.closure (Set.range g)) :
    ZS.AbsIrred p A := by
  have hp : p.Prime := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hzero' : ((2 : ℕ) : ZMod p) = 0 := by simpa using hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero'
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)
  have hmem : ∀ i, g i ∈ A := by
    intro i
    rw [hA]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hhne : ∀ i, h i ≠ 0 := by
    intro i hi
    have hz : α i (h i) = 0 := by rw [hi, map_zero]
    rw [hα i] at hz
    exact h2ne hz
  have hsub : ∀ i w, g i w - w = -(α i w) • h i := by
    intro i w
    rw [hg i w, sub_sub_cancel_left, neg_smul]
  constructor
  ·
    intro W hW
    by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    · right
      obtain ⟨w, hwW, hwne⟩ := (Submodule.ne_bot_iff W).mp hWbot
      have hex : ∃ i, α i w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact hwne (hker w hcon)
      obtain ⟨i, hi⟩ := hex
      have hgiw : g i w ∈ W := hW (g i) (hmem i) w hwW
      have hhi : h i ∈ W := by
        have h1 : g i w - w ∈ W := W.sub_mem hgiw hwW
        rw [hsub i w] at h1
        have h2 : (α i w) • h i ∈ W := by simpa using W.neg_mem h1
        have hunit : (α i w)⁻¹ * (α i w) = 1 := inv_mul_cancel₀ hi
        have h3 := W.smul_mem ((α i w)⁻¹) h2
        simpa [smul_smul, hunit] using h3
      have hstep : ∀ a b, (α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) → h a ∈ W → h b ∈ W := by
        intro a b hab hha
        have hga : g b (h a) ∈ W := hW (g b) (hmem b) (h a) hha
        have h1 : g b (h a) - h a ∈ W := W.sub_mem hga hha
        rw [hsub b (h a)] at h1
        have h2 : (α b (h a)) • h b ∈ W := by simpa using W.neg_mem h1
        have hunit : (α b (h a))⁻¹ * (α b (h a)) = 1 := inv_mul_cancel₀ hab.2
        have h3 := W.smul_mem ((α b (h a))⁻¹) h2
        simpa [smul_smul, hunit] using h3
      have hall : ∀ j, h j ∈ W := by
        intro j
        induction hconn i j with
        | refl => exact hhi
        | tail _ hbc ih => exact hstep _ _ hbc ih
      have hle : Submodule.span (ZMod p) (Set.range h) ≤ W := by
        rw [Submodule.span_le]
        rintro x ⟨j, rfl⟩
        exact hall j
      rw [hspan] at hle
      exact top_le_iff.mp hle
  ·
    intro f hf
    have hstar : ∀ i w, α i w • f (h i) = α i (f w) • h i := by
      intro i w
      have h1 : f (g i w) = g i (f w) := by
        have hc := LinearMap.congr_fun (hf (g i) (hmem i)) w
        simpa [LinearMap.comp_apply] using hc
      have hA1 : f (g i w) = f w - α i w • f (h i) := by
        rw [hg i w, map_sub, map_smul]
      have hB1 : f (g i w) = f w - α i (f w) • h i := by
        rw [h1, hg i (f w)]
      have h4 : f w - α i w • f (h i) = f w - α i (f w) • h i := by
        rw [← hA1, hB1]
      have hAB : f w + α i (f w) • h i = f w + α i w • f (h i) :=
        sub_eq_sub_iff_add_eq_add.mp h4
      exact (add_left_cancel hAB).symm
    let c : ι → ZMod p := fun i => (2 : ZMod p)⁻¹ * α i (f (h i))
    have hc : ∀ i, f (h i) = c i • h i := by
      intro i
      have hs := hstar i (h i)
      rw [hα i] at hs
      have h2inv : (2 : ZMod p)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2ne
      have hcon := congrArg (fun x => (2 : ZMod p)⁻¹ • x) hs
      simp only [smul_smul, h2inv, one_smul] at hcon
      simpa [c] using hcon
    have hedge : ∀ a b, (α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) → c a = c b := by
      intro a b hab
      have hs1 : (α a (h b) * c a) • h a = (c b * α a (h b)) • h a := by
        have hs' := hstar a (h b)
        rw [hc a, hc b] at hs'
        rw [map_smul] at hs'
        rw [smul_eq_mul] at hs'
        rw [smul_smul] at hs'
        exact hs'
      have h2 : (α a (h b) * c a) * α a (h a) = (c b * α a (h b)) * α a (h a) := by
        have hcon := congrArg (α a) hs1
        simpa only [map_smul, smul_eq_mul] using hcon
      rw [hα a] at h2
      have h3 : α a (h b) * c a = c b * α a (h b) := mul_right_cancel₀ h2ne h2
      have h4 : α a (h b) * c a = α a (h b) * c b := by
        rw [h3, mul_comm (c b) (α a (h b))]
      exact mul_left_cancel₀ hab.1 h4
    by_cases hempty : Nonempty ι
    · obtain ⟨i₀⟩ := hempty
      have hcst : ∀ j, c j = c i₀ := by
        intro j
        induction hconn i₀ j with
        | refl => rfl
        | tail _ hbc ih => exact (hedge _ _ hbc).symm.trans ih
      refine ⟨c i₀, ?_⟩
      apply LinearMap.ext_on_range hspan
      intro i
      rw [hc i, LinearMap.smul_apply, LinearMap.id_apply, hcst i]
    ·
      haveI : IsEmpty ι := not_nonempty_iff.mp hempty
      refine ⟨0, ?_⟩
      apply LinearMap.ext
      intro x
      have htop : (⊤ : Submodule (ZMod p) V) = ⊥ := by
        rw [← hspan, Set.range_eq_empty h, Submodule.span_empty]
      have hx : x = 0 := by
        have hxbot : x ∈ (⊥ : Submodule (ZMod p) V) := htop ▸ Submodule.mem_top
        simpa using hxbot
      simp [hx]

end CFSG.StandardType
