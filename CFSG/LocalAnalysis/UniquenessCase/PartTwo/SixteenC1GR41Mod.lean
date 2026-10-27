module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Act
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitStruct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code
open CFSG.RankThree.OrthogonalInvolutions

theorem s16c1G_qModel_map {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true) (x : V₀) :
    qModel true (g x) = qModel true x :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (omegaGroup_le (qModel true) (qModel_nondegenerate true) hg) x

theorem s16c1G_polar_map {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true) (x y : V₀) :
    polar (qModel true) (g x) (g y) = polar (qModel true) x y := by
  rw [polar, polar, ← map_add, s16c1G_qModel_map hg, s16c1G_qModel_map hg, s16c1G_qModel_map hg]

theorem s16c1G_mapsTo_add {g : V₀ ≃ₗ[ZMod 2] V₀} {z x y : V₀}
    (hx : g x = x ∨ g x = x + z) (hy : g y = y ∨ g y = y + z) :
    g (x + y) = x + y ∨ g (x + y) = x + y + z := by
  rw [map_add]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left; rw [hx, hy]
  · right; rw [hx, hy]; abel
  · right; rw [hx, hy]; abel
  · left
    rw [hx, hy]
    calc x + z + (y + z) = x + y + (z + z) := by abel
      _ = x + y := by rw [s16c1G_add_self, add_zero]

theorem s16c1G_all_of_basis {g : V₀ ≃ₗ[ZMod 2] V₀} {z : V₀} (S : Finset (Fin 6))
    (h : ∀ i ∈ S, g (Pi.single i 1) = Pi.single i 1 ∨ g (Pi.single i 1) = Pi.single i 1 + z)
    (x : V₀) (hx : ∀ i, i ∉ S → x i = 0) : g x = x ∨ g x = x + z := by
  have hx' : x = ∑ i, x i • (Pi.single i 1 : V₀) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx']
  refine Finset.sum_induction _ (fun v : V₀ => g v = v ∨ g v = v + z)
    (fun a b ha hb => s16c1G_mapsTo_add ha hb) (Or.inl (by simp)) fun i _ => ?_
  by_cases hi : i ∈ S
  · rcases zmod2_eq_zero_or_eq_one (x i) with h0 | h1
    · rw [h0, zero_smul]
      exact Or.inl (by simp)
    · rw [h1, one_smul]
      exact h i hi
  · rw [hx i hi, zero_smul]
    exact Or.inl (by simp)

private theorem s16c1G_finrank_V₀ : finrank (ZMod 2) V₀ = 6 := by
  show finrank (ZMod 2) (Fin 6 → ZMod 2) = 6
  exact Module.finrank_fin_fun (ZMod 2)

theorem s16c1G_ncard_singular : {v : V₀ | v ≠ 0 ∧ qModel true v = 0}.ncard = 27 := by
  rcases ncard_singular_nonsingular (V := V₀) (Q := qModel true) s16c1G_finrank_V₀
      (qModel_nondegenerate true) with h | h
  · exfalso
    have h2 := h.2
    rw [qModel_true, ncard_qMinus] at h2
    omega
  · exact h.1

theorem s16c1G_orbit_singular {z : V₀} (hz : z ≠ 0) (hq : qModel true z = 0) :
    MulAction.orbit (Ω₀ true) z = {v : V₀ | v ≠ 0 ∧ qModel true v = 0} := by
  have h5 : 5 ≤ finrank (ZMod 2) V₀ := by rw [s16c1G_finrank_V₀]; norm_num
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hz ((LinearEquiv.map_eq_zero_iff (x : V₀ ≃ₗ[ZMod 2] V₀)).mp h)
    · exact (s16c1G_qModel_map x.2 z).trans hq
  · rintro ⟨hv0, hv⟩
    obtain ⟨x, hx, hxz⟩ := exists_mem_omegaGroup_apply_eq (V := V₀) (Q := qModel true)
      (qModel_nondegenerate true) h5 hz hv0 (by rw [hq, hv])
    exact ⟨⟨x, hx⟩, hxz⟩

theorem s16c1G_card_stab_sing {z : V₀} (hz : z ≠ 0) (hq : qModel true z = 0) :
    Nat.card (MulAction.stabilizer (Ω₀ true) z) = 960 := by
  classical
  have key : Nat.card (MulAction.orbit (Ω₀ true) z) *
      Nat.card (MulAction.stabilizer (Ω₀ true) z) = Nat.card ↥(Ω₀ true) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Ω₀ true) z)
  have horbcard : Nat.card (MulAction.orbit (Ω₀ true) z) = 27 := by
    rw [s16c1G_orbit_singular hz hq, Nat.card_coe_set_eq]
    exact s16c1G_ncard_singular
  rw [horbcard, s16c1_card_omega0] at key
  omega

theorem s16c1G_card_stab_nonsing {z : V₀} (hz : qModel true z = 1) :
    Nat.card (MulAction.stabilizer (Ω₀ true) z) = 720 := by
  have h := s16c1_omega0_card_stab_nonsing hz
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_).symm
  rw [MulAction.mem_stabilizer_iff]
  rfl

@[expose] noncomputable def s16c1G_stabEquiv {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true)
    {z₀ z : V₀} (h : g z₀ = z) :
    ↥(MulAction.stabilizer (Ω₀ true) z₀) ≃* ↥(MulAction.stabilizer (Ω₀ true) z) :=
  MulAction.stabilizerEquivStabilizer (g := (⟨g, hg⟩ : ↥(Ω₀ true))) h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
