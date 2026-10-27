module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Defs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits
open scoped commutatorElement

section Coordinates

theorem toStd_five_zero (v : Fin 2 → ℤ) : toStd 5 v 0 = v 0 := by
  simp [toStd, show ¬ Even 5 by decide]

theorem toStd_five_one (v : Fin 2 → ℤ) : toStd 5 v 1 = v 1 - v 0 := by
  simp [toStd, show ¬ Even 5 by decide]

theorem mem_roots_coords5 {γ : Fin 2 → ℤ}
    (h : γ ∈ roots (isFiniteType_cartan 5) (divisible 5)) :
    (γ 0 = 1 ∧ γ 1 = 0) ∨ (γ 0 = -1 ∧ γ 1 = 0) ∨ (γ 0 = 1 ∧ γ 1 = 1) ∨ (γ 0 = -1 ∧ γ 1 = -1) ∨
    (γ 0 = 1 ∧ γ 1 = 2) ∨ (γ 0 = -1 ∧ γ 1 = -2) ∨ (γ 0 = 0 ∧ γ 1 = 1) ∨ (γ 0 = 0 ∧ γ 1 = -1) ∨
    (γ 0 = 2 ∧ γ 1 = 2) ∨ (γ 0 = -2 ∧ γ 1 = -2) ∨ (γ 0 = 0 ∧ γ 1 = 2) ∨
      (γ 0 = 0 ∧ γ 1 = -2) := by
  rw [roots_eq] at h
  rcases h with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [toStd_five_zero] at h0
    rw [toStd_five_one] at h1
    fin_cases i <;> fin_cases j <;> simp [weight, Fin.rev] at hij hi hj hji h0 h1 <;> omega
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [toStd_five_zero] at h0
    rw [toStd_five_one] at h1
    fin_cases i <;> simp [weight, Fin.rev] at hi h0 h1 <;> omega
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [toStd_five_zero] at h0
    rw [toStd_five_one] at h1
    fin_cases i <;> simp [weight, Fin.rev] at hi h0 h1 <;> omega

theorem octRootB_one : octRootB 1 = ![1, 0] := by simp [octRootB]
theorem octRootB_two : octRootB 2 = ![1, 1] := by simp [octRootB]
theorem octRootB_three : octRootB 3 = ![1, 2] := by simp [octRootB]
theorem octRootB_four : octRootB 4 = ![0, 1] := by simp [octRootB]
theorem octRootB_neg_one : octRootB (-1) = ![-1, 0] := by simp [octRootB]
theorem octRootB_neg_two : octRootB (-2) = ![-1, -1] := by simp [octRootB]
theorem octRootB_neg_three : octRootB (-3) = ![-1, -2] := by simp [octRootB]
theorem octRootB_neg_four : octRootB (-4) = ![0, -1] := by simp [octRootB]

theorem octRootB_mem_roots' {i : ℤ} (hi : IsRoot 4 i) :
    octRootB i ∈ roots (isFiniteType_cartan 5) (divisible 5) := by
  rw [roots_eq]
  rcases isRoot_four_iff.1 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inl ⟨0, 1, by decide, by decide, by decide, by decide, ?_⟩
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_one]
  · refine Or.inr (Or.inr ⟨by decide, 0, by decide, ?_⟩)
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_two]
  · refine Or.inl ⟨0, 3, by decide, by decide, by decide, by decide, ?_⟩
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_three]
  · refine Or.inr (Or.inr ⟨by decide, 1, by decide, ?_⟩)
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_four]
  · refine Or.inl ⟨1, 0, by decide, by decide, by decide, by decide, ?_⟩
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_neg_one]
  · refine Or.inr (Or.inr ⟨by decide, 4, by decide, ?_⟩)
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_neg_two]
  · refine Or.inl ⟨4, 1, by decide, by decide, by decide, by decide, ?_⟩
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_neg_three]
  · refine Or.inr (Or.inr ⟨by decide, 3, by decide, ?_⟩)
    funext k; fin_cases k <;> simp [weight, toStd_five_zero, toStd_five_one, octRootB_neg_four]

theorem octRootB_ht_pos {i : ℤ} (h1 : 1 ≤ i) (h4 : i ≤ 4) : 0 < ht (octRootB i) := by
  rw [ht_fin_two]
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;>
    simp [octRootB]

theorem octRootB_ht_neg {i : ℤ} (h1 : 1 ≤ i) (h4 : i ≤ 4) : ht (octRootB (-i)) < 0 := by
  rw [ht_fin_two]
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;>
    simp [octRootB]

theorem pos_root_cases5 {γ : Fin 2 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartan 5) (divisible 5))
    (hp : 0 < ht γ) : γ = octRootB 1 ∨ γ = octRootB 2 ∨ γ = octRootB 3 ∨ γ = octRootB 4 ∨
      (γ 0 = 2 ∧ γ 1 = 2) ∨ (γ 0 = 0 ∧ γ 1 = 2) := by
  have h := mem_roots_coords5 hγ
  rw [ht_fin_two] at hp
  have h' : (γ 0 = 1 ∧ γ 1 = 0) ∨ (γ 0 = 1 ∧ γ 1 = 1) ∨ (γ 0 = 1 ∧ γ 1 = 2) ∨
      (γ 0 = 0 ∧ γ 1 = 1) ∨ (γ 0 = 2 ∧ γ 1 = 2) ∨ (γ 0 = 0 ∧ γ 1 = 2) := by omega
  rcases h' with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | h | h
  · exact Or.inl (ext_fin_two (by simp [octRootB_one, h0]) (by simp [octRootB_one, h1]))
  · exact Or.inr (Or.inl (ext_fin_two (by simp [octRootB_two, h0]) (by simp [octRootB_two, h1])))
  · exact Or.inr (Or.inr (Or.inl (ext_fin_two (by simp [octRootB_three, h0])
      (by simp [octRootB_three, h1]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ext_fin_two (by simp [octRootB_four, h0])
      (by simp [octRootB_four, h1])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem eq_two_smul_two {γ : Fin 2 → ℤ} (h : γ 0 = 2 ∧ γ 1 = 2) : γ = 2 • octRootB 2 :=
  ext_fin_two (by simp [octRootB_two, h.1]) (by simp [octRootB_two, h.2])

theorem eq_two_smul_four {γ : Fin 2 → ℤ} (h : γ 0 = 0 ∧ γ 1 = 2) : γ = 2 • octRootB 4 :=
  ext_fin_two (by simp [octRootB_four, h.1]) (by simp [octRootB_four, h.2])

theorem octRootB_ne_two_smul {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) (δ : Fin 2 → ℤ) :
    octRootB k ≠ 2 • δ := by
  intro h
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl <;>
    simp [octRootB] at h0 h1' <;> omega

end Coordinates

section Commutators

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem octRootB_mem_roots_un {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    octRootB k ∈ (rootDatum hF 5).roots :=
  octRootB_mem_roots' (isRoot_four_of h1 h4)

theorem rootGroup_two_le_un {γ : Fin 2 → ℤ} (hγ : γ ∈ (rootDatum hF 5).roots)
    (h2 : 2 • γ ∈ (rootDatum hF 5).roots) :
    (rootDatum hF 5).rootGroup (2 • γ) ≤ (rootDatum hF 5).rootGroup γ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  exact (steinbergExtras hF 5 (by norm_num) ζ hζ).two_smul_le γ hγ h2

theorem octComm_aux_un5 {a b : ℤ} (ha : 1 ≤ a) (ha4 : a ≤ 4) (hb : 1 ≤ b) (hb4 : b ≤ 4)
    (hind : LinIndepPair (octRootB a) (octRootB b)) {S : Subgroup (SU (unitaryInvolution F p f) 5)}
    (hS : ∀ ε : Fin 2 → ℤ, ε ∈ openCone (rootDatum hF 5).roots (octRootB a) (octRootB b) →
      (rootDatum hF 5).rootGroup ε ≤ S) :
    ∀ x ∈ un5Oct hF a, ∀ y ∈ un5Oct hF b, ⁅x, y⁆ ∈ S := fun x hx y hy => by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF 5 (by norm_num) ζ hζ
  exact (iSup₂_le hS : (⨆ ε ∈ openCone (rootDatum hF 5).roots (octRootB a) (octRootB b),
      (rootDatum hF 5).rootGroup ε) ≤ S)
    (hext.commutator_mem (octRootB a) (octRootB_mem_roots_un hF ha ha4)
      (octRootB b) (octRootB_mem_roots_un hF hb hb4) hind x hx y hy)

end Commutators

end CFSG.Quasithin.H13.F431.Un
