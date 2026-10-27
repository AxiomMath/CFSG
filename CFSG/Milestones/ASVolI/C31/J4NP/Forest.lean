module

public import CFSG.Milestones.ASVolI.C31.J4NP.Orbit

public section

namespace CFSG.ASVolI

variable {G : Type*} [Group G]

theorem burnsideJ4NP_centralizer_sup_zpowers (A : Subgroup G) (y : G) :
    Subgroup.centralizer ((A ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer {y} := by
  refine le_antisymm (le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))))) fun x hx => ?_
  obtain ⟨hA, hy⟩ := Subgroup.mem_inf.mp hx
  have hle : A ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer {x} :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hA a ha))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hy).symm))
  exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hz)

theorem burnsideJ4NP_sup_zpowers_eq_of_inv_mul_mem {A : Subgroup G} {c x : G}
    (hx : c⁻¹ * x ∈ A) : A ⊔ Subgroup.zpowers x = A ⊔ Subgroup.zpowers c := by
  apply le_antisymm
  · refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
    simpa using (A ⊔ Subgroup.zpowers c).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) (Subgroup.mem_sup_left hx)
  · refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
    simpa using (A ⊔ Subgroup.zpowers x).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) (Subgroup.mem_sup_left (A.inv_mem hx))

theorem burnsideJ4NP_sup_zpowers_eq_map_conj {A : Subgroup G} {n p x : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) (hx : (n * p * n⁻¹)⁻¹ * x ∈ A) :
    A ⊔ Subgroup.zpowers x = (A ⊔ Subgroup.zpowers p).map (MulAut.conj n).toMonoidHom := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, burnsideJ4NP_map_conj_eq_iff.mpr hn]
  exact burnsideJ4NP_sup_zpowers_eq_of_inv_mul_mem hx

theorem burnsideJ4NP_forest {A N : Subgroup G} {roots : Set G} {F : ℕ → G} {par : ℕ → ℕ}
    {lab : ℕ → G} {m : ℕ}
    (hF : ∀ i < m, F i ∈ roots ∨ (par i < i ∧ lab i ∈ N ∧
      A ⊔ Subgroup.zpowers (F i) =
        (A ⊔ Subgroup.zpowers (F (par i))).map (MulAut.conj (lab i)).toMonoidHom)) :
    ∀ i < m, ∃ r ∈ roots, ∃ n ∈ N,
      A ⊔ Subgroup.zpowers (F i) = (A ⊔ Subgroup.zpowers r).map (MulAut.conj n).toMonoidHom := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hF i hi with hr | ⟨hp, hl, he⟩
    · exact ⟨F i, hr, 1, N.one_mem, (burnsideJ4NP_map_conj_eq_iff.mpr (Subgroup.one_mem _)).symm⟩
    · obtain ⟨r, hr, n, hn, hpe⟩ := ih (par i) hp (hp.trans hi)
      exact ⟨r, hr, lab i * n, N.mul_mem hl hn, by rw [he, hpe, burnsideJ4NP_map_conj_map_conj]⟩

theorem burnsideJ4NP_forest_cosets {A N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (A : Set G)) {roots : Set G} {F : ℕ → G} {par : ℕ → ℕ}
    {lab : ℕ → G} {m : ℕ}
    (hF : ∀ i < m, F i ∈ roots ∨
      (par i < i ∧ lab i ∈ N ∧ (lab i * F (par i) * (lab i)⁻¹)⁻¹ * F i ∈ A))
    {X : Set G} (hX : ∀ x ∈ X, ∃ i < m, (F i)⁻¹ * x ∈ A) :
    ∀ x ∈ X, ∃ r ∈ roots, ∃ n ∈ N,
      A ⊔ Subgroup.zpowers x = (A ⊔ Subgroup.zpowers r).map (MulAut.conj n).toMonoidHom := by
  have hforest := burnsideJ4NP_forest (A := A) (N := N) (roots := roots) (F := F) (par := par)
    (lab := lab) (m := m) fun i hi => (hF i hi).imp_right fun ⟨hp, hl, hc⟩ =>
      ⟨hp, hl, burnsideJ4NP_sup_zpowers_eq_map_conj (hN hl) hc⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := hX x hx
  obtain ⟨r, hr, n, hn, he⟩ := hforest i hi
  exact ⟨r, hr, n, hn, (burnsideJ4NP_sup_zpowers_eq_of_inv_mul_mem hxi).trans he⟩

end CFSG.ASVolI
