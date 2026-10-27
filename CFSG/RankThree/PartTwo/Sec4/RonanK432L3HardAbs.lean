module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Invariant

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

namespace L3Hard

theorem commute_notMem_of_hom_conj {G : Type*} {Q : Type} [Group G] [Group Q] (φ : G →* Q)
    {a b k g t : G} (hk : k * a * k⁻¹ = b) (hc : φ b * φ a = φ a * φ b)
    (hn : φ b ∉ Subgroup.zpowers (φ a)) (ht : φ t = φ (g * k * g⁻¹)) :
    (φ t * φ (g * a * g⁻¹) * (φ t)⁻¹) * φ (g * a * g⁻¹) =
        φ (g * a * g⁻¹) * (φ t * φ (g * a * g⁻¹) * (φ t)⁻¹) ∧
      φ t * φ (g * a * g⁻¹) * (φ t)⁻¹ ∉ Subgroup.zpowers (φ (g * a * g⁻¹)) := by
  have h1 : φ t * φ (g * a * g⁻¹) * (φ t)⁻¹ = φ g * φ b * (φ g)⁻¹ := by
    rw [ht, ← hk]
    simp only [map_mul, map_inv]
    group
  have h2 : φ g * φ a * (φ g)⁻¹ = φ (g * a * g⁻¹) := by simp only [map_mul, map_inv]
  rw [h1]
  exact commute_notMem_of_conj (φ g) hc.symm hn (a' := φ (g * a * g⁻¹)) (Or.inl h2)

theorem hom_commute_of_conj_eq {G : Type*} {Q : Type} [Group G] [Group Q] (φ : G →* Q)
    {c d s : G} (h : c * d * c⁻¹ = s * d) (hs : φ s = 1) : φ c * φ d = φ d * φ c := by
  have h' : φ c * φ d * (φ c)⁻¹ = φ d := by
    have := congrArg φ h
    simpa [hs] using this
  calc φ c * φ d = (φ c * φ d * (φ c)⁻¹) * φ c := by group
    _ = φ d * φ c := by rw [h']

theorem not_weaklyClosed_of_mem_subgroup {Q : Type} [Group Q] (S : Subgroup Q) (z g : S)
    (hc : ((g : Q) * z * (g : Q)⁻¹) * z = z * ((g : Q) * z * (g : Q)⁻¹))
    (hn : (g : Q) * z * (g : Q)⁻¹ ∉ Subgroup.zpowers (z : Q)) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  refine not_weaklyClosed_of_commute_conj (g := g) ?_ ?_
  · apply Subtype.ext
    exact hc
  · intro hmem
    apply hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg (fun w : S => (w : Q)) hk
    simpa using this

theorem listRow_map_of_witness {G Q : Type} [Group G] [Group Q] (φ : G →* Q) (L : Subgroup G)
    [Finite (L.map φ)]
    (h : ∀ x ∈ L, orderOf (φ x) = 3 → ∃ t ∈ L,
      (φ t * φ x * (φ t)⁻¹) * φ x = φ x * (φ t * φ x * (φ t)⁻¹) ∧
        φ t * φ x * (φ t)⁻¹ ∉ Subgroup.zpowers (φ x)) :
    ListRow (L.map φ) := by
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  obtain ⟨x, hxL, hx⟩ := Subgroup.mem_map.mp z.2
  have hzo : orderOf (φ x) = 3 := by
    rw [hx, Subgroup.orderOf_coe]
    exact hz
  obtain ⟨t, htL, hc, hn⟩ := h x hxL hzo
  refine not_weaklyClosed_of_mem_subgroup (L.map φ) z ⟨φ t, Subgroup.mem_map_of_mem φ htL⟩ ?_ ?_
  · show (φ t * (z : Q) * (φ t)⁻¹) * (z : Q) = (z : Q) * (φ t * (z : Q) * (φ t)⁻¹)
    rw [← hx]
    exact hc
  · show φ t * (z : Q) * (φ t)⁻¹ ∉ Subgroup.zpowers (z : Q)
    rw [← hx]
    exact hn

end L3Hard

end CFSG.RankThree.PartTwo.Sec4.RonanK432
