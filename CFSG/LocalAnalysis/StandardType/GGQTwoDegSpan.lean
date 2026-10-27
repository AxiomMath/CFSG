module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDegFrame

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qTwoDegSpan_sup_eq {H : Type*} [Group H] {A : Subgroup H} {N : ℕ} (hN : 2 ≤ N)
    (ρ : Equiv.Perm (Fin N) ≃* ↥A) (ω : Fin N) {W : Subgroup H} (hW : W ≤ A)
    (hnot : ¬ W ≤ Subgroup.map (A.subtype.comp ρ.toMonoidHom)
      (MulAction.stabilizer (Equiv.Perm (Fin N)) ω)) :
    Subgroup.map (A.subtype.comp ρ.toMonoidHom)
      (MulAction.stabilizer (Equiv.Perm (Fin N)) ω) ⊔ W = A := by
  classical
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN
  set E : Equiv.Perm (Fin N) →* H := A.subtype.comp ρ.toMonoidHom with hE
  set P : Subgroup (Equiv.Perm (Fin N)) :=
    MulAction.stabilizer (Equiv.Perm (Fin N)) ω with hP
  have htop : ρ.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ ρ.surjective
  have hE_range : E.range = A := by
    rw [hE, MonoidHom.range_comp, htop, Subgroup.map_top, Subgroup.subtype_range]
  have hPcoat : IsCoatom P := by
    rw [hP]
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      (Equiv.Perm (Fin N)) ω
  have hle : Subgroup.map E P ⊔ W ≤ A := by
    rw [← hE_range]
    exact sup_le (Subgroup.map_le_range E P) (hW.trans (le_of_eq hE_range.symm))
  refine le_antisymm hle ?_
  by_contra hAle
  set Q : Subgroup (Equiv.Perm (Fin N)) := (Subgroup.map E P ⊔ W).comap E with hQ
  have hPQ : P ≤ Q := by
    rw [hQ]
    exact (Subgroup.le_comap_map E P).trans (Subgroup.comap_mono le_sup_left)
  have hQne : Q ≠ ⊤ := by
    intro hQtop
    apply hAle
    intro a ha
    have harange : a ∈ E.range := by rw [hE_range]; exact ha
    obtain ⟨q, rfl⟩ := harange
    have hqQ : q ∈ Q := by rw [hQtop]; trivial
    rw [hQ] at hqQ
    exact Subgroup.mem_comap.mp hqQ
  have hQeqP : Q = P := by
    rcases (hPcoat.le_iff (x := Q)).1 hPQ with h | h
    · exact absurd h hQne
    · exact h
  have hWle : W ≤ Subgroup.map E P := by
    intro w hw
    have hwrange : w ∈ E.range := by rw [hE_range]; exact hW hw
    obtain ⟨q, hq⟩ := hwrange
    have hqP : q ∈ P := by
      have hqQ : q ∈ Q := by
        rw [hQ]
        exact Subgroup.mem_comap.2
          (by rw [hq]; exact Subgroup.mem_sup_right hw)
      rw [hQeqP] at hqQ
      exact hqQ
    rw [← hq]
    exact Subgroup.mem_map_of_mem E hqP
  exact hnot hWle

theorem qTwoDegSpan_exists_not_le {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)} {m N : ℕ}
    (hm : 1 ≤ m) (hNm : N = m + 1)
    (hA : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = N.factorial)
    (hL : Nat.card ↥(ggAutomizer L Bs) = m.factorial) :
    ∃ K ∈ 𝒦, ¬ ggAutomizer K Bs ≤ ggAutomizer L Bs := by
  classical
  by_contra h
  have hle : ∀ K ∈ 𝒦, ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    intro K hK
    by_contra hKnot
    exact h ⟨K, hK, hKnot⟩
  have hJoin_le : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs := by
    unfold ggAutomizerJoin
    exact sup_le le_rfl (iSup_le fun K => iSup_le fun hK => hle K hK)
  have hJoin_eq : ggAutomizerJoin L Bs 𝒦 = ggAutomizer L Bs := by
    apply le_antisymm hJoin_le
    unfold ggAutomizerJoin
    exact le_sup_left
  have hcard_eq : N.factorial = m.factorial := by
    rw [← hA, ← hL, hJoin_eq]
  have hlt : m.factorial < N.factorial :=
    (Nat.factorial_lt (n := m) (m := N) (by omega : 0 < m)).2 (by omega)
  exact absurd hcard_eq hlt.ne'

theorem qTwoDeg_exists_spanning_neighbour
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {m d c : ℕ} (hrow : QTwoRowData k m d c Bs L x) (hm : 5 ≤ m)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e')
    (hNm : N = m + 1) :
    ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  obtain ⟨ρ, hρ, -⟩ := qTwoDegFrame_perm_equiv hP.2 (by omega) hM
  have hALA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  obtain ⟨ω, hω⟩ := qTwoDegFrame_stabilizer hrow.elemAb ρ hρ hALA (by omega) hrow.weyl hNm
  have hcardA : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = N.factorial := by
    rw [← Nat.card_congr ρ.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hcardL := qTwoDegFrame_card_weyl (by omega) hrow.weyl
  obtain ⟨K, hK𝒦, hKL⟩ := qTwoDegSpan_exists_not_le (by omega) hNm hcardA hcardL
  have hKA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    le_sup_of_le_right (le_iSup₂_of_le K hK𝒦 le_rfl)
  have hsup := qTwoDegSpan_sup_eq (by omega) ρ ω hKA (fun h => hKL (by rw [hω]; exact h))
  obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 K hK𝒦
  exact ⟨y, K, hy, by rw [hω]; exact hsup⟩

end CFSG.StandardType.QTwo

end
