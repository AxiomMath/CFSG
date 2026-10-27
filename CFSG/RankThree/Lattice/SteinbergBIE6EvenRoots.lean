module

public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.RankThree.Lattice.SteinbergBIE6QplusFold

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.Chevalley.C2E6Std

theorem e6Root_sub_single_table : ∀ k : Fin 72, 2 ≤ height (e6Root k) →
    ∃ j : Fin Tag.E6.rank, ∃ k' : Fin 72, e6Root k' = e6Root k - Pi.single j 1 := by
  decide +kernel

theorem e6Root_height_one_table : ∀ k : Fin 72, height (e6Root k) = 1 →
    ∃ j : Fin Tag.E6.rank, e6Root k = Pi.single j 1 := by
  decide +kernel

theorem exists_root_sub_single {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h2 : 2 ≤ height α) : ∃ j : Fin Tag.E6.rank, IsRoot Tag.E6 (α - Pi.single j 1) := by
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
  obtain ⟨j, k', hk'⟩ := e6Root_sub_single_table k h2
  exact ⟨j, hk' ▸ isRoot_e6Root k'⟩

theorem eq_single_of_height_eq_one {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h1 : height α = 1) : ∃ j : Fin Tag.E6.rank, α = Pi.single j 1 := by
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
  exact e6Root_height_one_table k h1

theorem iform_self_E6 {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  have hd : Tag.E6.symmetrizer j j = 1 := by fin_cases j <;> rfl
  rw [hj, hd, mul_one]

theorem iform_single_right_E6 (x : Fin Tag.E6.rank → ℤ) (j : Fin Tag.E6.rank) :
    iform x (Pi.single j 1) = ∑ i, Tag.E6.cartan j i * x i := by
  have hd : Tag.E6.symmetrizer j j = 1 := by fin_cases j <;> rfl
  rw [iform_single_right, hd, one_mul]

theorem support_split_pos (n : ℕ) : ∀ {α : Fin Tag.E6.rank → ℤ}, IsRoot Tag.E6 α →
    height α = n → 0 < n → ∀ {C C' : Set (Fin Tag.E6.rank)},
      (∀ a ∈ C, ∀ b ∈ C', Tag.E6.cartan a b = 0) → (∀ i, α i ≠ 0 → i ∈ C ∨ i ∈ C') →
        (∀ i, α i ≠ 0 → i ∈ C) ∨ (∀ i, α i ≠ 0 → i ∈ C') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α hα hn hpos C C' hsep hsupp
    by_cases h1 : n = 1
    · obtain ⟨j, rfl⟩ := eq_single_of_height_eq_one hα (hn.trans (by rw [h1]; norm_num))
      have hj : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) j ≠ 0 := by simp
      have hzero : ∀ i, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) i ≠ 0 → i = j := fun i hi => by
        by_contra hij
        exact hi (by simp [hij])
      rcases hsupp j hj with hC | hC
      · exact Or.inl fun i hi => hzero i hi ▸ hC
      · exact Or.inr fun i hi => hzero i hi ▸ hC
    · obtain ⟨j, hβ⟩ := exists_root_sub_single hα (by omega)
      set β := α - Pi.single j 1 with hβdef
      have hαβ : α = β + Pi.single j 1 := by rw [hβdef, sub_add_cancel]
      have hβn : height β = ((n - 1 : ℕ) : ℤ) := by
        rw [hβdef, height_sub, hn, height_single, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have hβpos : 0 < n - 1 := by omega
      have hβsupp : ∀ i, β i ≠ 0 → i ∈ C ∨ i ∈ C' := fun i hi => by
        by_cases hij : i = j
        · exact hsupp i (by
            subst hij
            intro h0
            have hβi : β i = -1 := by
              have e : α i = β i + 1 := by rw [hαβ]; simp
              omega
            have hβr : IsRoot Tag.E6 β := hβ
            have hnn := (IsRoot.height_pos_iff hβr).1 (by omega) i
            omega)
        · exact hsupp i (by
            have e : α i = β i := by rw [hαβ]; simp [hij]
            rw [e]
            exact hi)
      have hβj : iform β (Pi.single j 1) = -1 := by
        have e := iform_self_E6 hα
        rw [hαβ, iform_add_left, iform_add_right, iform_add_right, iform_self_E6 hβ,
          iform_comm (Pi.single j 1) β, show iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ)
            (Pi.single j 1) = 2 from iform_self_E6 (isRoot_single Tag.E6 j)] at e
        omega
      have hjα : α j ≠ 0 := by
        have e : α j = β j + 1 := by rw [hαβ]; simp
        have hnn := (IsRoot.height_pos_iff hβ).1 (by omega) j
        omega
      have key : ∀ (S S' : Set (Fin Tag.E6.rank)), (∀ a ∈ S, ∀ b ∈ S', Tag.E6.cartan a b = 0) →
          (∀ i, β i ≠ 0 → i ∈ S) → j ∈ S' → False := by
        intro S S' hsep' hβS hjS'
        have h0 : iform β (Pi.single j 1) = 0 := by
          rw [iform_single_right_E6]
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : β i = 0
          · rw [hi, mul_zero]
          · have := hsep' i (hβS i hi) j hjS'
            rw [cartan_symm_E6, this, zero_mul]
        omega
      rcases ih (n - 1) (by omega) hβ hβn hβpos hsep hβsupp with hC | hC
      · rcases hsupp j hjα with hjC | hjC
        · refine Or.inl fun i hi => ?_
          by_cases hij : i = j
          · exact hij ▸ hjC
          · exact hC i (by
              have e : α i = β i := by rw [hαβ]; simp [hij]
              rw [← e]
              exact hi)
        · exact (key C C' hsep hC hjC).elim
      · rcases hsupp j hjα with hjC | hjC
        · exact (key C' C (fun a ha b hb => by rw [cartan_symm_E6]; exact hsep b hb a ha) hC
            hjC).elim
        · refine Or.inr fun i hi => ?_
          by_cases hij : i = j
          · exact hij ▸ hjC
          · exact hC i (by
              have e : α i = β i := by rw [hαβ]; simp [hij]
              rw [← e]
              exact hi)

theorem support_split {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    {C C' : Set (Fin Tag.E6.rank)} (hsep : ∀ a ∈ C, ∀ b ∈ C', Tag.E6.cartan a b = 0)
    (hsupp : ∀ i, α i ≠ 0 → i ∈ C ∨ i ∈ C') :
    (∀ i, α i ≠ 0 → i ∈ C) ∨ (∀ i, α i ≠ 0 → i ∈ C') := by
  rcases IsRoot.height_pos_or_neg hα with hpos | hneg
  · exact support_split_pos (height α).toNat hα (Int.toNat_of_nonneg hpos.le).symm (by omega)
      hsep hsupp
  · have hpos : 0 < height (-α) := by rw [height_neg]; omega
    have h := support_split_pos (height (-α)).toNat (IsRoot.neg hα)
      (Int.toNat_of_nonneg hpos.le).symm (by omega) hsep
      (fun i hi => hsupp i (by simpa using hi))
    simpa using h

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

@[expose] def qpIndex : Fin 15 :=
  ((gammaStable_iff_mem_e6QpSupport D.J).1 ⟨D.J_ne_univ, D.J_stable⟩).choose

theorem J_eq : D.J = e6QpSupport D.qpIndex :=
  ((gammaStable_iff_mem_e6QpSupport D.J).1 ⟨D.J_ne_univ, D.J_stable⟩).choose_spec

theorem i₀_mem' : D.i₀ ∈ e6QpSupport D.qpIndex := D.J_eq ▸ D.i₀_mem

theorem Ξ_eq : D.Ξ = e6Xi (e6QpSupport D.qpIndex) D.i₀ := by
  rw [Ξ, D.J_eq]

theorem δ_eq : D.δ = e6Delta (e6QpSupport D.qpIndex) := by
  rw [δ, D.J_eq]

@[expose] def support : Set (Fin Tag.E6.rank) := {j | Pi.single j 1 ∈ D.Ξ}

theorem orth : e6XiOrth (e6QpSupport D.qpIndex) D.i₀ := by
  intro α hα k hk
  rw [← D.Ξ_eq] at hα
  rw [← D.δ_eq] at hk ⊢
  exact D.orthogonal α hα k hk

theorem Ξ_eq_parabolicRoots : D.Ξ = parabolicRoots Tag.E6 D.support := by
  set m := D.qpIndex
  have hi₀ := D.i₀_mem'
  set C := e6JComponent (e6QpSupport m) D.i₀ with hC
  set C' := e6JComponent (e6QpSupport m) (e6QpPerm m D.i₀) with hC'
  have hΞ : D.Ξ = parabolicRoots Tag.E6 C ∪ parabolicRoots Tag.E6 C' := by
    rw [D.Ξ_eq]
    exact e6Xi_eq m hi₀
  have hsupp : ∀ j, j ∈ D.support ↔ j ∈ C ∨ j ∈ C' := fun j => by
    change Pi.single j 1 ∈ D.Ξ ↔ _
    rw [hΞ, Set.mem_union, single_mem_parabolicRoots_iff, single_mem_parabolicRoots_iff]
  ext α
  constructor
  · intro hα
    rw [hΞ] at hα
    rcases hα with h | h
    · exact ⟨h.1, fun i hi => h.2 i fun hc => hi ((hsupp i).2 (Or.inl hc))⟩
    · exact ⟨h.1, fun i hi => h.2 i fun hc => hi ((hsupp i).2 (Or.inr hc))⟩
  · intro hα
    rw [hΞ]
    have hπ := (e6QpPerm_mem_iff m D.i₀).1 hi₀
    by_cases hCC : C = C'
    · left
      refine ⟨hα.1, fun i hi => hα.2 i fun hs => ?_⟩
      rcases (hsupp i).1 hs with h | h
      · exact hi h
      · exact hi (hCC ▸ h)
    · have hsep : ∀ a ∈ C, ∀ b ∈ C', Tag.E6.cartan a b = 0 := by
        intro a ha b hb
        by_contra hne
        exact hCC (e6JComponent_eq_of_adj m hi₀ hπ ha hb (Or.inr hne))
      have hs : ∀ i, α i ≠ 0 → i ∈ C ∨ i ∈ C' := fun i hi => by
        by_contra h
        exact hi (hα.2 i fun hs => h ((hsupp i).1 hs))
      rcases support_split hα.1 hsep hs with h | h
      · exact Or.inl ⟨hα.1, fun i hi => by by_contra h'; exact hi (h i h')⟩
      · exact Or.inr ⟨hα.1, fun i hi => by by_contra h'; exact hi (h i h')⟩

theorem isRoot_of_mem_Ξ {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) : IsRoot Tag.E6 α := by
  rw [D.Ξ_eq_parabolicRoots] at hα
  exact hα.1

theorem neg_mem_Ξ {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) : -α ∈ D.Ξ := by
  rw [D.Ξ_eq] at hα ⊢
  exact neg_mem_e6Xi D.qpIndex D.i₀_mem' hα

theorem δ_mem_Ξ {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) : D.δ α ∈ D.Ξ := by
  rw [D.Ξ_eq] at hα ⊢
  rw [D.δ_eq]
  exact e6Delta_mem_e6Xi D.qpIndex D.i₀_mem' hα

theorem δ_δ (x : Fin Tag.E6.rank → ℤ) : D.δ (D.δ x) = x := by
  rw [D.δ_eq]
  exact e6Delta_qp_involutive D.qpIndex x

theorem height_δ {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) : height (D.δ α) = height α := by
  rw [D.Ξ_eq] at hα
  rw [D.δ_eq]
  exact height_e6Delta_of_mem_e6Xi D.qpIndex D.i₀_mem' hα

theorem δ_add (x y : Fin Tag.E6.rank → ℤ) : D.δ (x + y) = D.δ x + D.δ y := by
  rw [D.δ_eq]
  exact e6Delta_qp_add D.qpIndex x y

theorem δ_neg (x : Fin Tag.E6.rank → ℤ) : D.δ (-x) = -D.δ x := by
  rw [D.δ_eq]
  exact e6Delta_qp_neg D.qpIndex x

theorem iform_δ (x y : Fin Tag.E6.rank → ℤ) : iform (D.δ x) (D.δ y) = iform x y :=
  iform_e6Delta D.J x y

theorem mem_support_iff {j : Fin Tag.E6.rank} : j ∈ D.support ↔ Pi.single j 1 ∈ D.Ξ := Iff.rfl

theorem support_subset {j : Fin Tag.E6.rank} (hj : j ∈ D.support) : j ∈ e6QpSupport D.qpIndex := by
  have h : Pi.single j 1 ∈ D.Ξ := hj
  rw [D.Ξ_eq] at h
  exact mem_e6QpSupport_of_single_mem_e6Xi D.qpIndex D.i₀_mem' h

theorem δ_single {j : Fin Tag.E6.rank} (hj : j ∈ D.support) :
    D.δ (Pi.single j 1) = Pi.single (e6QpPerm D.qpIndex j) 1 := by
  rw [D.δ_eq]
  exact e6Delta_qp_single D.qpIndex (D.support_subset hj)

theorem perm_mem_support {j : Fin Tag.E6.rank} (hj : j ∈ D.support) :
    e6QpPerm D.qpIndex j ∈ D.support := by
  change Pi.single _ 1 ∈ D.Ξ
  rw [← D.δ_single hj]
  exact D.δ_mem_Ξ hj

theorem iform_δ_eq_zero {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) (hne : D.δ α ≠ α) :
    iform α (D.δ α) = 0 := by
  have h := D.orthogonal α hα 1 (by rw [Function.iterate_one]; exact hne)
  rwa [Function.iterate_one] at h

theorem height_δ_pos {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) (hpos : 0 < height α) :
    0 < height (D.δ α) := by
  rw [D.height_δ hα]
  exact hpos

end E6EvenFixedRootDatum

end CFSG.RankThree.Lattice
