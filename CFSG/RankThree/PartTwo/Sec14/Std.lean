module

public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

structure Sec14Std (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop extends Sec13Data G A c L where
  hypS_or_hypT : HypS A ∨ HypT A
  chosen136 : Chosen136 A

variable {G : Type} [Group G] [Finite G]

@[expose] def IsLBConfig (A B : Subgroup G) (b d : G) (L : Subgroup G) : Prop :=
  B = Subgroup.closure {b, d} ∧ Subgroup.zpowers b ∈ omegaA A ∧ lA A b = {L} ∧
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    ∃ hd : d ∈ L, ∃ S : Sylow 3 ↥L, (⟨d, hd⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hd⟩ : ↥L)}

@[expose] noncomputable def lB (A B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (d : G) (L : Subgroup G) (_ : IsLBConfig A B b d L),
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})

theorem lB_eq_bot {A B : Subgroup G} (h : ∀ b d L, ¬ IsLBConfig A B b d L) : lB A B = ⊥ := by
  refine le_bot_iff.mp (iSup_le fun b => iSup_le fun d => iSup_le fun L => iSup_le fun hc => ?_)
  exact absurd hc (h b d L)

theorem lB_eq_of_unique {A B L : Subgroup G} {b d : G} (hc : IsLBConfig A B b d L)
    (huniq : ∀ b' d' L', IsLBConfig A B b' d' L' →
      inSubgroup perfectResidual (L' ⊓ Subgroup.centralizer {d'}) =
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) :
    lB A B = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) := by
  refine le_antisymm (iSup_le fun b' => iSup_le fun d' => iSup_le fun L' => iSup_le fun hc' =>
    (huniq b' d' L' hc').le) ?_
  exact le_iSup_of_le b (le_iSup_of_le d (le_iSup_of_le L (le_iSup_of_le hc le_rfl)))

omit [Finite G] in
theorem le_centralizer_of_mem_thetaComponentsAt {b : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 b) : L ≤ Subgroup.centralizer {b} := by
  obtain ⟨L', -, rfl⟩ := hL
  exact Subgroup.map_subtype_le L'

theorem lB_le_centralizer (A B : Subgroup G) : lB A B ≤ Subgroup.centralizer (B : Set G) := by
  refine iSup_le fun b => iSup_le fun d => iSup_le fun L => iSup_le fun hc => ?_
  obtain ⟨hB, -, hLb, -, -⟩ := hc
  have hL : L ∈ lA A b := hLb ▸ Set.mem_singleton L
  have hLC : L ≤ Subgroup.centralizer {b} := le_centralizer_of_mem_thetaComponentsAt hL.1
  refine (Subgroup.map_subtype_le _).trans ?_
  rw [hB, Subgroup.centralizer_closure]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro h (rfl | rfl)
  · exact Subgroup.mem_centralizer_iff.mp (hLC (Subgroup.mem_inf.mp hx).1) h (Set.mem_singleton h)
  · exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 h (Set.mem_singleton h)

end CFSG.RankThree.PartTwo.Sec14
