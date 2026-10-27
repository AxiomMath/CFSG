module

public import CFSG.Quasithin.Background.P4InspOrthBasic
public import CFSG.Quasithin.Background.G9StmtsModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

section Perm

variable {n : ℕ}

theorem p4insporth_permAct_mem (σ : Equiv.Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ permCore n) : permAct σ x ∈ permCore n := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

@[expose] def p4insporth_permLin (σ : Equiv.Perm (Fin n)) :
    ↥(permCore n) ≃ₗ[ZMod 2] ↥(permCore n) where
  toFun x := ⟨permAct σ x, p4insporth_permAct_mem σ x.2⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    rfl
  map_smul' c x := by
    apply Subtype.ext
    funext i
    rfl
  invFun x := ⟨permAct σ⁻¹ x, p4insporth_permAct_mem σ⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp [permAct]
  right_inv x := by
    apply Subtype.ext
    funext i
    simp [permAct]

theorem p4insporth_permLin_apply (σ : Equiv.Perm (Fin n)) (x : ↥(permCore n)) :
    ((p4insporth_permLin σ x : ↥(permCore n)) : Fin n → ZMod 2) = permAct σ x := rfl

@[expose] def p4insporth_permHom (n : ℕ) : Equiv.Perm (Fin n) →* GLV ↥(permCore n) where
  toFun := p4insporth_permLin
  map_one' := by
    ext x i
    simp [p4insporth_permLin_apply, permAct]
  map_mul' σ τ := by
    ext x i
    simp [p4insporth_permLin_apply, permAct, _root_.mul_inv_rev]

theorem p4insporth_permHom_apply (σ : Equiv.Perm (Fin n)) (x : ↥(permCore n)) :
    ((p4insporth_permHom n σ x : ↥(permCore n)) : Fin n → ZMod 2) = permAct σ x := rfl

@[expose] def p4insporth_pairVec (i j : Fin n) : Fin n → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem p4insporth_pairVec_mem (i j : Fin n) : p4insporth_pairVec i j ∈ permCore n := by
  show ∑ m, p4insporth_pairVec i j m = 0
  simp only [p4insporth_pairVec, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
    Finset.mem_univ, ite_true]
  decide

theorem p4insporth_permAct_single (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permAct σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) 1 := by
  funext m
  simp only [permAct, Pi.single_apply]
  by_cases h : m = σ i
  · subst h
    simp
  · have h' : ¬ σ.symm m = i := fun h' => h (by rw [← h']; simp)
    simp [h, h']

theorem p4insporth_permAct_pairVec (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permAct σ (p4insporth_pairVec i j) = p4insporth_pairVec (σ i) (σ j) := by
  simp only [p4insporth_pairVec, ← p4insporth_permAct_single]
  rfl

theorem p4insporth_eq_of_fix_pair {σ : Equiv.Perm (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (h : permAct σ (p4insporth_pairVec i j) = p4insporth_pairVec i j) : σ i = i ∨ σ i = j := by
  have h1 : p4insporth_pairVec (σ i) (σ j) = p4insporth_pairVec i j := by
    rw [← p4insporth_permAct_pairVec]
    exact h
  have h2 := congrFun h1 (σ i)
  simp only [p4insporth_pairVec, Pi.add_apply, Pi.single_apply] at h2
  have hσ : σ i ≠ σ j := fun h' => hij (σ.injective h')
  by_cases hi : σ i = i
  · exact Or.inl hi
  · by_cases hj : σ i = j
    · exact Or.inr hj
    · exfalso
      simp [hi, hj, hσ] at h2

theorem p4insporth_eq_one_of_fix (hn : 3 ≤ n) {σ : Equiv.Perm (Fin n)}
    (h : ∀ i j, i ≠ j → permAct σ (p4insporth_pairVec i j) = p4insporth_pairVec i j) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    by_cases h0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, fun h' => by simp [Fin.ext_iff, h0] at h',
        fun h' => by simp [Fin.ext_iff, h0] at h', by simp [Fin.ext_iff]⟩
    · by_cases h1 : i.val = 1
      · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, fun h' => by simp [Fin.ext_iff, h1] at h',
          fun h' => by simp [Fin.ext_iff, h1] at h', by simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega,
          fun h' => by simp [Fin.ext_iff] at h'; omega, by simp [Fin.ext_iff]⟩
  rcases p4insporth_eq_of_fix_pair hij (h i j hij) with h1 | h1
  · exact h1
  · rcases p4insporth_eq_of_fix_pair hik (h i k hik) with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hjk

theorem p4insporth_permHom_injective (hn : 3 ≤ n) : Function.Injective (p4insporth_permHom n) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine p4insporth_eq_one_of_fix hn fun i j _ => ?_
  have := congrArg (fun g : GLV ↥(permCore n) =>
    ((g ⟨p4insporth_pairVec i j, p4insporth_pairVec_mem i j⟩ : ↥(permCore n)) :
      Fin n → ZMod 2)) hσ
  exact this

@[expose] def p4insporth_wt (x : Fin n → ZMod 2) : ℕ := ∑ i, (x i).val

@[expose] def p4insporth_qP (x : Fin n → ZMod 2) : ZMod 2 := ((p4insporth_wt x / 2 : ℕ) : ZMod 2)

theorem p4insporth_wt_permAct (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) :
    p4insporth_wt (permAct σ x) = p4insporth_wt x := by
  unfold p4insporth_wt permAct
  exact Equiv.sum_comp σ⁻¹ (fun i => (x i).val)

theorem p4insporth_wt_cast (x : Fin n → ZMod 2) : ((p4insporth_wt x : ℕ) : ZMod 2) = ∑ i, x i := by
  simp [p4insporth_wt]

theorem p4insporth_two_dvd_wt {x : Fin n → ZMod 2} (hx : x ∈ permCore n) : 2 ∣ p4insporth_wt x := by
  have h : ∑ i, x i = 0 := hx
  rw [← p4insporth_wt_cast] at h
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

theorem p4insporth_wt_add_inter (x y : Fin n → ZMod 2) :
    p4insporth_wt (x + y) + 2 * ∑ i, (x i * y i).val = p4insporth_wt x + p4insporth_wt y := by
  unfold p4insporth_wt
  have h : ∀ a b : ZMod 2, (a + b).val + 2 * (a * b).val = a.val + b.val := by decide
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => h (x i) (y i)

theorem p4insporth_inter_cast (x y : Fin n → ZMod 2) :
    ((∑ i, (x i * y i).val : ℕ) : ZMod 2) = x ⬝ᵥ y := by
  simp [dotProduct]

theorem p4insporth_qP_add {x y : Fin n → ZMod 2} (hx : x ∈ permCore n) (hy : y ∈ permCore n) :
    p4insporth_qP (x + y) = p4insporth_qP x + p4insporth_qP y + x ⬝ᵥ y := by
  have hxy : x + y ∈ permCore n := (permCore n).add_mem hx hy
  obtain ⟨a, ha⟩ := p4insporth_two_dvd_wt hx
  obtain ⟨b, hb⟩ := p4insporth_two_dvd_wt hy
  obtain ⟨c, hc⟩ := p4insporth_two_dvd_wt hxy
  have h := p4insporth_wt_add_inter x y
  rw [ha, hb, hc] at h
  have hnat : c + ∑ i, (x i * y i).val = a + b := by omega
  have hcast : (c : ZMod 2) + ((∑ i, (x i * y i).val : ℕ) : ZMod 2) = a + b := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 2) hnat
  rw [p4insporth_inter_cast] at hcast
  have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
  have e : ∀ m : ℕ, 2 * m / 2 = m := fun m => by omega
  unfold p4insporth_qP
  rw [hc, ha, hb, e, e, e]
  calc (c : ZMod 2) = (c + x ⬝ᵥ y) + x ⬝ᵥ y := by rw [add_assoc, h2, add_zero]
    _ = a + b + x ⬝ᵥ y := by rw [hcast]

theorem p4insporth_qP_permAct (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) :
    p4insporth_qP (permAct σ x) = p4insporth_qP x := by
  unfold p4insporth_qP
  rw [p4insporth_wt_permAct]

end Perm

section Trans

variable {U V : Type} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]

theorem p4insporth_isPermCore_of_map {n : ℕ} {G₀ : Subgroup (Equiv.Perm (Fin n))}
    (ι : U ≃ₗ[ZMod 2] V) {H : Subgroup (GLV U)} {H₀ : Subgroup (GLV V)}
    (hH : H.map (p4insporth_cg ι).toMonoidHom = H₀) (h : IsPermCoreModule H₀ G₀) :
    IsPermCoreModule H G₀ := by
  obtain ⟨φ, β, hs, hk, he⟩ := h
  let e : ↥H ≃* ↥H₀ :=
    (Subgroup.equivMapOfInjective H (p4insporth_cg ι).toMonoidHom
      (p4insporth_cg ι).injective).trans (MulEquiv.subgroupCongr hH)
  have he' : ∀ γ : ↥H, ((e γ : ↥H₀) : GLV V) = p4insporth_cg ι (γ : GLV U) := fun γ => rfl
  refine ⟨e.trans φ, ι.symm.toLinearMap.comp β, ι.symm.surjective.comp hs, fun u => ?_,
    fun γ u u' hu' => ?_⟩
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
    exact hk u
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h1 := he (e γ) u u' hu'
    rw [h1, he' γ, p4insporth_cg_apply]
    simp

end Trans

end P4InspOrth

end G11

end CFSG.Quasithin
