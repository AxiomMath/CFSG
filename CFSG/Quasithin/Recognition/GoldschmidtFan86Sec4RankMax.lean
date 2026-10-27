module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4RankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem map_conj_stabilizer_inf (h : G) (u v : V) :
    (MulAction.stabilizer G u ⊓ MulAction.stabilizer G v).map (MulAut.conj h).toMonoidHom =
      MulAction.stabilizer G (h • u) ⊓ MulAction.stabilizer G (h • v) := by
  ext g
  constructor
  · rintro ⟨x, ⟨hxu, hxv⟩, rfl⟩
    refine ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
    · show (h * x * h⁻¹) • h • u = h • u
      rw [mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.1 hxu]
    · show (h * x * h⁻¹) • h • v = h • v
      rw [mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.1 hxv]
  · rintro ⟨hgu, hgv⟩
    refine ⟨h⁻¹ * g * h, ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩, ?_⟩
    · rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hgu, inv_smul_smul]
    · rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hgv, inv_smul_smul]
    · show h * (h⁻¹ * g * h) * h⁻¹ = g
      group

theorem card_edge_stabilizer_conj (h : G) (u v : V) :
    Nat.card ↥(MulAction.stabilizer G (h • u) ⊓ MulAction.stabilizer G (h • v)) =
      Nat.card ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G v) := by
  rw [← map_conj_stabilizer_inf]
  exact (Nat.card_congr ((MulAut.conj h).subgroupMap _).toEquiv).symm

theorem FanTree.exists_card_edge_bound (F : FanTree Γ G) :
    ∃ B : ℕ, ∀ u v : V, Γ.Adj u v →
      Nat.card ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G v) ≤ B := by
  obtain ⟨α₀⟩ := F.isTree.connected.nonempty
  obtain ⟨β₀, hβ₀⟩ := F.exists_adj α₀
  refine ⟨Nat.card ↥(MulAction.stabilizer G α₀ ⊓ MulAction.stabilizer G β₀), fun u v huv => ?_⟩
  obtain ⟨h, -, hh | hh⟩ := F.edgeTransitive u v α₀ β₀ huv hβ₀
  · rw [← card_edge_stabilizer_conj h u v, hh.1, hh.2]
  · rw [← card_edge_stabilizer_conj h u v, hh.1, hh.2, inf_comm]

theorem Track.omega1_fixer_le_edge (T : Track Γ G) :
    omega1 T.fixer ≤ MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert 1) := fun _ hg =>
  ⟨MulAction.mem_stabilizer_iff.2 ((T.mem_fixer).1 (omega1_le _ hg) 0),
    MulAction.mem_stabilizer_iff.2 ((T.mem_fixer).1 (omega1_le _ hg) 1)⟩

theorem exists_maxRank (F : FanTree Γ G) (T₀ : Track Γ G) (h : T₀.fixer ≠ ⊥) :
    ∃ T : Track Γ G, PushReach T₀ T ∧ T.fixer ≠ ⊥ ∧
      (∀ T', PushReach T T' → omega1 T'.fixer = omega1 T.fixer) ∧
      (∀ T', PushReach T T' → T'.HasReflections → T.HasReflections) := by
  classical
  obtain ⟨B, hB⟩ := F.exists_card_edge_bound
  have hfin : ∀ T' : Track Γ G, Finite ↥(omega1 T'.fixer) := fun T' =>
    haveI := F.finite_stabilizer_inf (T'.line.vert 0) (T'.line.vert 1)
    Finite.of_injective (Subgroup.inclusion T'.omega1_fixer_le_edge)
      (Subgroup.inclusion_injective _)
  have hbd : ∀ T' : Track Γ G, Nat.card ↥(omega1 T'.fixer) ≤ B := fun T' =>
    haveI := F.finite_stabilizer_inf (T'.line.vert 0) (T'.line.vert 1)
    (Subgroup.card_le_of_le T'.omega1_fixer_le_edge).trans (hB _ _ (T'.line.adj 0))
  let S : Set ℕ := {n | ∃ T', PushReach T₀ T' ∧ Nat.card ↥(omega1 T'.fixer) = n}
  have hSne : S.Nonempty := ⟨_, T₀, PushReach.refl _, rfl⟩
  have hSbdd : BddAbove S := ⟨B, by rintro n ⟨T', -, rfl⟩; exact hbd T'⟩
  obtain ⟨T₁, hT₁, hn⟩ := Nat.sSup_mem hSne hSbdd
  have hchosen : ∃ T : Track Γ G, PushReach T₀ T ∧ Nat.card ↥(omega1 T.fixer) = sSup S ∧
      ((∃ T', PushReach T₀ T' ∧ Nat.card ↥(omega1 T'.fixer) = sSup S ∧ T'.HasReflections) →
        T.HasReflections) := by
    by_cases hex : ∃ T', PushReach T₀ T' ∧ Nat.card ↥(omega1 T'.fixer) = sSup S ∧
        T'.HasReflections
    · obtain ⟨T, hT, hc, hr⟩ := hex
      exact ⟨T, hT, hc, fun _ => hr⟩
    · exact ⟨T₁, hT₁, hn, fun h' => absurd h' hex⟩
  obtain ⟨T, hT, hcard, hrefl⟩ := hchosen
  have hlower : omega1 T₀.fixer ≤ omega1 T.fixer := hT.omega1_le
  have hY0 : omega1 T₀.fixer ≠ ⊥ := by
    obtain ⟨x, hx, hx1, hx2⟩ := T₀.exists_involution_of_fixer_ne_bot F h
    intro hbot
    have : x ∈ omega1 T₀.fixer := Subgroup.subset_closure ⟨hx, hx2⟩
    rw [hbot] at this
    exact hx1 (Subgroup.mem_bot.1 this)
  have heq : ∀ T', PushReach T T' → omega1 T'.fixer = omega1 T.fixer := by
    intro T' hTT'
    have hT' : PushReach T₀ T' := hT.trans hTT'
    have hle : omega1 T.fixer ≤ omega1 T'.fixer := hTT'.omega1_le
    have hcard' : Nat.card ↥(omega1 T'.fixer) ≤ sSup S :=
      le_csSup hSbdd ⟨T', hT', rfl⟩
    have := hfin T'
    exact (Subgroup.eq_of_le_of_card_ge hle (hcard ▸ hcard')).symm
  refine ⟨T, hT, ?_, heq, ?_⟩
  · intro hbot
    apply hY0
    rw [eq_bot_iff]
    exact hlower.trans ((omega1_le _).trans (le_of_eq hbot))
  · intro T' hTT' hr'
    refine hrefl ⟨T', hT.trans hTT', ?_, hr'⟩
    rw [heq T' hTT', hcard]

end CFSG.Quasithin.Fan86
