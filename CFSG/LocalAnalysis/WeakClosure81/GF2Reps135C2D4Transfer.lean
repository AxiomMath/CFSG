module

public import CFSG.Quasithin.Background.SmithB45TorLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Tor

theorem exists_finset_closure_top {G : Type*} [Group G] (C : Subgroup G) (T : Finset G)
    (hT : ∀ y ∈ T, y ∈ C) (hC : C ≤ Subgroup.closure (T : Set G)) :
    ∃ T' : Finset C, T'.card ≤ T.card ∧ (∀ y ∈ T', (y : G) ∈ T) ∧
      Subgroup.closure (T' : Set C) = ⊤ := by
  classical
  refine ⟨T.subtype (· ∈ C), ?_, ?_, ?_⟩
  · refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
    · intro y hy
      simpa using (Finset.mem_subtype.1 hy)
    · intro a _ b _ h
      exact Subtype.ext h
  · intro y hy
    exact Finset.mem_subtype.1 hy
  · set N : Subgroup C := Subgroup.closure (T.subtype (· ∈ C) : Set C) with hN
    have himg : C.subtype '' (T.subtype (· ∈ C) : Set C) = (T : Set G) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact Finset.mem_subtype.1 hz
      · intro hy
        exact ⟨⟨y, hT y hy⟩, Finset.mem_subtype.2 hy, rfl⟩
    have hmap : N.map C.subtype = Subgroup.closure (T : Set G) := by
      rw [hN, MonoidHom.map_closure, himg]
    have hCN : C ≤ N.map C.subtype := by
      rw [hmap]
      exact hC
    refine le_antisymm le_top ?_
    intro z _
    have hz : (z : G) ∈ N.map C.subtype := hCN z.2
    rcases Subgroup.mem_map.1 hz with ⟨w, hw, hwz⟩
    have hwz' : w = z := Subtype.ext hwz
    simpa [hwz'] using hw

theorem exists_conj_gen_of_modelProj {W : Type} [CommGroup W] (L : Subgroup (MulAut W))
    (hZL : Subgroup.center ↥L = ⊥) {M : Type*} [Group M]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* M) {x : ↥L} {ξ : M}
    (hx : ∃ g : M, g * modelProj L e x * g⁻¹ = ξ) {T : Finset M}
    (hT : ∀ y ∈ T, ∃ g : M, y = g * ξ * g⁻¹) (hgen : Subgroup.closure (T : Set M) = ⊤) :
    ∃ T' : Finset (MulAut W), T'.card ≤ T.card ∧
      (∀ y ∈ T', ∃ g ∈ L, y = g * (x : MulAut W) * g⁻¹) ∧
      L ≤ Subgroup.closure (T' : Set (MulAut W)) := by
  classical
  obtain ⟨ψ, _, hψ⟩ := exists_modelLift L hZL e
  refine ⟨T.image ψ, Finset.card_image_le, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.1 hy with ⟨t, ht, rfl⟩
    obtain ⟨g, hg⟩ := hT t ht
    obtain ⟨g₁, hg₁⟩ := hx
    have ht' : t = (g * g₁) * modelProj L e x * (g * g₁)⁻¹ := by
      rw [hg, ← hg₁]
      group
    obtain ⟨l, hl⟩ := modelProj_surjective L e (g * g₁)
    refine ⟨(l : MulAut W), l.2, ?_⟩
    rw [ht', ← hl]
    simp only [map_mul, map_inv, hψ]
  · intro l hl
    have hmem : modelProj L e ⟨l, hl⟩ ∈ Subgroup.closure (T : Set M) := by
      rw [hgen]
      trivial
    have hmap := MonoidHom.map_closure ψ (T : Set M)
    have hthis : ψ (modelProj L e ⟨l, hl⟩) ∈
        Subgroup.closure (↑(T.image ψ) : Set (MulAut W)) := by
      rw [Finset.coe_image, ← hmap]
      exact Subgroup.mem_map_of_mem ψ hmem
    rwa [hψ ⟨l, hl⟩] at hthis

end CFSG.LocalAnalysis.WeakClosure81
