module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNormAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_natSum3_normalizer_two (hW : ∀ w : W, w ^ 2 = 1) {L Z : Subgroup (MulAut W)}
    {J : Subgroup W} (hL : IsPSL 3 2 1 ↥L) (hJ : NatSum3 L J) (hZ : Nat.card ↥Z = 7)
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z) (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w) {x : MulAut W} {k : ℕ} (hx : x ^ (2 ^ k) = 1)
    (hxZ : Z.map (MulAut.conj x).toMonoidHom = Z) (hxL : L.map (MulAut.conj x).toMonoidHom = L)
    (hxJ : J.map x.toMonoidHom = J) :
    (∃ l ∈ L, ∀ w ∈ J, x w = l w) ∧ ∀ z ∈ Z, x * z = z * x := by
  obtain ⟨V, -, hVirr, hVc, hxV⟩ :=
    s16c167_norm_exists_stable_irr hW hL hJ hZ hZL hZJ hZf hx hxL hxJ
  have hσL : ∀ y ∈ L, x * y * x⁻¹ ∈ L := by
    intro y hy
    have h : (MulAut.conj x).toMonoidHom y ∈ L.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rw [hxL] at h
    simpa [MulAut.conj_apply] using h
  obtain ⟨l₀, hl₀, hcent⟩ := inner_of_stable_card_eight hW hL
    (fun y hy v hv => hVirr.1 ⟨y, hy⟩ v hv) hVc (s16c167_norm_irr_nontrivial hVirr hVc) hσL
    (StabLat.mem_stabSub_of_map_eq hxV)
  have hxl := s16c167_norm_natSum3_two_element_inner hW hL hJ hZ hZL hZJ hZf hx hxZ hxJ hl₀ hcent
  exact ⟨⟨l₀, hl₀, hxl⟩, s16c167_norm_commute_of_agree hZL hZJ hZf hxZ hxJ hl₀ hxl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
