module

public import CFSG.RankThree.GF2n.Stroth80.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem StrothHyp.sup_inf_centralizer_eq (H : StrothHyp M Q Z) {N : Subgroup G} (hNQ : N ≤ Q)
    (hNM : M ≤ Subgroup.normalizer (N : Set G)) :
    (N ⊔ Z) ⊓ Subgroup.centralizer (N : Set G) = Z := by
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hZcent : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z := by
    intro z hz y hy
    rw [← H.centralizer_Q] at hz
    exact (Subgroup.mem_centralizer_iff.mp hz y hy).symm
  have hNZQ : N ⊔ Z ≤ Q := sup_le hNQ hZQ
  set U := (N ⊔ Z) ⊓ Subgroup.centralizer (N : Set G)
  have hZU : Z ≤ U := fun z hz =>
    ⟨Subgroup.mem_sup_right hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hZcent z hz y (hNQ hy)).symm⟩
  have hUQ : U ≤ Q := inf_le_left.trans hNZQ
  have hcomm : IsMulCommutative U := by
    refine ⟨⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => Subtype.ext ?_⟩⟩
    have hvC : N ⊔ Z ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun z hz => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          exact (Subgroup.mem_centralizer_iff.mp hv.2 y hy).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          exact (hZcent z hz v (hUQ hv)).symm
    have := Subgroup.mem_centralizer_iff.mp (hvC hu.1) v rfl
    exact this.symm
  have hMU : M ≤ Subgroup.normalizer (U : Set G) := by
    intro m hm
    have hN := hNM hm
    have hZn := H.Z_normal.2 hm
    rw [Subgroup.mem_normalizer_iff] at hN hZn ⊢
    have key : ∀ g : G, (∀ x, x ∈ N ↔ g * x * g⁻¹ ∈ N) → (∀ x, x ∈ Z ↔ g * x * g⁻¹ ∈ Z) →
        ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
      intro g hgN hgZ u hu
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      · have hle : N ⊔ Z ≤ (N ⊔ Z).comap (MulAut.conj g).toMonoidHom :=
          sup_le (fun x hx => Subgroup.mem_sup_left ((hgN x).mp hx))
            (fun x hx => Subgroup.mem_sup_right ((hgZ x).mp hx))
        exact hle hu.1
      · have hy' : g⁻¹ * y * g ∈ N := by
          exact (hgN _).mpr (by simpa [mul_assoc] using hy)
        have hc := Subgroup.mem_centralizer_iff.mp hu.2 _ hy'
        calc y * (g * u * g⁻¹) = g * ((g⁻¹ * y * g) * u) * g⁻¹ := by group
          _ = g * (u * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
          _ = g * u * g⁻¹ * y := by group
    refine fun u => ⟨fun hu => key m hN hZn u hu, fun hu => ?_⟩
    have hN' : ∀ x, x ∈ N ↔ m⁻¹ * x * m⁻¹⁻¹ ∈ N := fun x => by
      constructor
      · intro hx; exact (hN _).mpr (by simpa [mul_assoc] using hx)
      · intro hx; simpa [mul_assoc] using (hN _).mp hx
    have hZ' : ∀ x, x ∈ Z ↔ m⁻¹ * x * m⁻¹⁻¹ ∈ Z := fun x => by
      constructor
      · intro hx; exact (hZn _).mpr (by simpa [mul_assoc] using hx)
      · intro hx; simpa [mul_assoc] using (hZn _).mp hx
    simpa [mul_assoc] using key m⁻¹ hN' hZ' _ hu
  exact (H.maxAb.eq_of_le ⟨hUQ.trans H.Q_normal.1, hMU, hcomm⟩ hZU).symm


end CFSG.RankThree.GF2n.Stroth80
