module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawInternal

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6}

theorem mem_of_occurs_of_vanish_cent {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)}
    (hc : occurs m U c) {j : Root m} (hj : Vanish m (cent m c) j) : j ∈ c := by
  by_contra hjc
  have hU : U ≤ cent m c := fun u hu => by
    simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
    exact fun i hi => hc.2.1 i hi u hu
  have h2 := root_coroot m j
  rw [hj _ (coroot_mem_cent_of_not_mem hc (fun u hu => hj u (hU hu)) hjc)] at h2
  exact absurd h2 (by decide)

theorem list_prod_reflection_mem_weyl {c : Finset (Root m)} {w : List (Root m)}
    (hw : ∀ j ∈ w, j ∈ c) : (w.map (reflection m)).prod ∈ weyl m c := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨j, hw j hj, rfl⟩

theorem mem_weyl_of_word {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)}
    (hc : occurs m U c) {g : V m ≃ₗ[ZMod 3] V m} (hfix : ∀ v ∈ cent m c, g v = v)
    {w : List (Root m)} (hg : g = (w.map (reflection m)).prod)
    (hw : ∀ j ∈ w, ∀ v, g v = v → root m j v = 0) : g ∈ weyl m c := by
  rw [hg]
  exact list_prod_reflection_mem_weyl fun j hj =>
    mem_of_occurs_of_vanish_cent hc fun v hv => hw j hj v (hfix v hv)

@[expose] def SplitAt (m : Fin 6) (g : V m ≃ₗ[ZMod 3] V m) (u : V m) : Prop :=
  ∃ c₁ : Finset (Root m), (∀ i ∈ c₁, ∀ j, root m j u = 0 → Adj m i j → j ∈ c₁) ∧
    (∃ x, (∀ i ∈ c₁, root m i x = 0) ∧ g x ≠ x) ∧
    ∃ x, (∀ i, root m i u = 0 → i ∉ c₁ → root m i x = 0) ∧ g x ≠ x

theorem mem_cent_iff {c : Finset (Root m)} {x : V m} :
    x ∈ cent m c ↔ ∀ i ∈ c, root m i x = 0 := by
  simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]

theorem not_splitAt_of_mem_cent {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)}
    (hc : occurs m U c) {g : V m ≃ₗ[ZMod 3] V m} (hfix : ∀ v ∈ cent m c, g v = v) {u : V m}
    (hu : u ∈ cent m c) : ¬ SplitAt m g u := by
  rintro ⟨c₁, hcl, ⟨x₁, hx₁, hgx₁⟩, x₂, hx₂, hgx₂⟩
  have hcu := mem_cent_iff.1 hu
  by_cases hT : (c.filter (· ∈ c₁)).Nonempty
  · have hT' := hc.2.2.2 (c.filter (· ∈ c₁)) (Finset.filter_subset _ _) hT fun i hi j hj hij => by
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hj, hcl i hi.2 j (hcu j hj) hij⟩
    refine hgx₁ (hfix x₁ (mem_cent_iff.2 fun i hi => hx₁ i ?_))
    have hi' : i ∈ c.filter (· ∈ c₁) := by rwa [hT']
    exact (Finset.mem_filter.1 hi').2
  · exact hgx₂ (hfix x₂ (mem_cent_iff.2 fun i hi =>
      hx₂ i (hcu i hi) fun hi₁ => hT ⟨i, Finset.mem_filter.2 ⟨hi, hi₁⟩⟩))

theorem mem_weyl_of_splitAt {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)}
    (hc : occurs m U c) {g : V m ≃ₗ[ZMod 3] V m} (hg : g ∈ ambientNormalizer m)
    (hfix : ∀ v ∈ cent m c, g v = v) (hsplit : ∀ u, g u = u → u ≠ 0 → SplitAt m g u) :
    g ∈ weyl m c := by
  have hbot : ∀ u ∈ cent m c, u = 0 := fun u hu => by
    by_contra hu0
    exact not_splitAt_of_mem_cent hc hfix hu (hsplit u (hfix u hu) hu0)
  have huniv : c = Finset.univ := Finset.eq_univ_of_forall fun j =>
    mem_of_occurs_of_vanish_cent hc fun u hu => by rw [hbot u hu, map_zero]
  subst huniv
  rw [weyl, Finset.coe_univ, Set.image_univ]
  exact hg

@[expose] def FixWeylCert (m : Fin 6) (g : V m ≃ₗ[ZMod 3] V m) : Prop :=
  (∃ w : List (Root m), g = (w.map (reflection m)).prod ∧
    ∀ j ∈ w, ∀ v, g v = v → root m j v = 0) ∨ ∀ u, g u = u → u ≠ 0 → SplitAt m g u

theorem mem_weyl_of_fixWeylCert {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)}
    (hc : occurs m U c) {g : V m ≃ₗ[ZMod 3] V m} (hg : g ∈ ambientNormalizer m)
    (hcert : FixWeylCert m g) (hfix : ∀ v ∈ cent m c, g v = v) : g ∈ weyl m c := by
  rcases hcert with ⟨w, hw, hwv⟩ | hsplit
  · exact mem_weyl_of_word hc hfix hw hwv
  · exact mem_weyl_of_splitAt hc hg hfix hsplit

end CFSG.StandardType.GGQ2Frame.ExcRaw
