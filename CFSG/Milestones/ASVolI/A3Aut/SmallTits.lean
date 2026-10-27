module

public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.SmallBase

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6.TitsLat
open scoped Pointwise

theorem burnsideAut_a315_tits :
    ∀ (G : Type) [Group G] (L T B : Subgroup G), CFSG.Quasithin.A315Hyp L T B →
      CFSG.Quasithin.IsTits ↥L → CFSG.Quasithin.A315Case7 L T B := by
  intro G _ L T B h hL
  haveI : Finite G := h.sqtk.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut : ∀ α : MulAut ↥L, Odd (orderOf α) → ∃ l : ↥L, α = MulAut.conj l := by
    intro α hα
    obtain ⟨l, hl⟩ := burnsideA26_tits hL α hα
    exact ⟨l, hl.symm⟩
  obtain ⟨hBL, hc⟩ := burnsideA315x_config_of_hyp h hOut
  obtain ⟨e⟩ := titsModelEquiv ↥L 2 1 hL
  haveI := h.simple
  haveI : IsSimpleGroup ↥titsD := e.symm.isSimpleGroup
  have hnab : ∃ a b : ↥titsD, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
    rw [map_mul, map_mul, h']
  have hc' := hc.map e
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hc'.sylow
  obtain ⟨h3, h4⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index isSylowTwoOf_flagStab
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥titsD (h1.toSylow h2) (h3.toSylow h4)
  have hc'' := hc'.map (MulAut.conj g)
  have hS2 : (((T ⊓ L).subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      titsFlagStab := by
    have hsm : ((g • (h1.toSylow h2) : Sylow 2 ↥titsD) : Subgroup ↥titsD) =
        (((T ⊓ L).subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      ext x
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [← hsm, hg]
    rfl
  set B₂ := ((B.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom with hB₂
  have hcardB : Nat.card ↥B₂ = Nat.card ↥B := by
    rw [hB₂, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv]
  have hne := burnsideAut_Config_sup_ne_top hc'' hnab
  obtain ⟨-, hcard⟩ := hc''.sup_card
  rw [hS2] at hne hcard
  rw [card_titsFlagStab, hcardB] at hcard
  have h3B : ∀ k : ℕ, Nat.card ↥B = 3 ^ k → False := fun k hk =>
    hc''.false_of_pow_three (k := k) (by rw [hcardB]; exact hk)
  refine ⟨hL, ?_⟩
  rcases tits_overgroups (B₂ ⊔ titsFlagStab) le_sup_right with h5 | h5 | h5 | h5
  · rw [h5, card_titsFlagStab] at hcard
    exact (h3B 0 (by omega)).elim
  · rw [h5, card_titsPointStab] at hcard
    omega
  · rw [h5, card_titsLineStab] at hcard
    exact (h3B 1 (by omega)).elim
  · exact (hne h5).elim

end CFSG.ASVolI
