module

public import CFSG.Timmesfeld.ARS.QDBasic
public import CFSG.Timmesfeld.ARS.Sec4Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

open QD

theorem eq_of_mem_isolatedSet_of_forall_commuting [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) (hnd : IsNondegenerate R)
    (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {D E : Subgroup G}
    (hD : D ∈ R) (hE : E ∈ isolatedSet R D) (hcomm : ∀ F ∈ isolatedSet R D, Commuting E F) :
    E = D := by
  by_contra hED
  have hER : E ∈ R := hE.1.1
  have hDE : Commuting D E := hE.1.2
  have hΛ : ∀ B ∈ lambdaSet R D, Commuting E B := fun B hB =>
    hcomm B (lambdaSet_subset_isolatedSet hR hD hB)
  have h1 : ∀ B ∈ R, Opposite E B → Opposite D B := by
    intro B hB hEB
    have hne : D ≠ B := fun e => hEB.not_commuting (hR.ne_bot E hER) (e ▸ hDE.symm)
    rcases hR.rel D hD B hB hne with hc | ho | hs
    · exact absurd hEB (hE.2 B ⟨hB, hc⟩)
    · exact ho
    · exfalso
      obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
      exact not_commuting_conjSub_of_opposite hR hiso hER hB hEB ⟨hD, hs.symm⟩ hDE.symm hb hb1
        (hΛ _ (conjSub_mem_lambdaSet_of_special hR hiso hB hD hs.symm hb hb1))
  have h2 : D ∈ isolatedSet R E := by
    refine ⟨⟨hD, hDE.symm⟩, fun C hC hDC => ?_⟩
    have hle : gen (lambdaSet R D) ⊔ C ≤ Subgroup.centralizer (E : Set G) :=
      sup_le (gen_le fun B hB => commuting_iff_le_centralizer.1 (hΛ B hB))
        (commuting_iff_le_centralizer.1 hC.2)
    rw [gen_lambdaSet_sup_eq_top_of hR hiso hnd hD ⟨hC.1, hDC⟩] at hle
    obtain ⟨B, -, hEB⟩ := hiso E hER
    exact hEB.not_commuting (hR.ne_bot E hER) (commuting_iff_le_centralizer.2 (le_top.trans hle))
  obtain ⟨B, hB, hDB, hEB⟩ : ∃ B ∈ R, Opposite D B ∧ ¬ Opposite E B := by
    by_contra! h
    exact hED (hΩ D hD E hER (Set.ext fun B =>
      ⟨fun hB => ⟨hB.1, h1 B hB.1 hB.2⟩, fun hB => ⟨hB.1, h B hB.1 hB.2⟩⟩))
  have hs : Special R E B := by
    have hne : E ≠ B := fun e => hDB.not_commuting (hR.ne_bot D hD) (e ▸ hDE)
    rcases hR.rel E hER B hB hne with h | h | h
    · exact absurd hDB (h2.2 B ⟨hB, h⟩)
    · exact absurd h hEB
    · exact h
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  have hFl := conjSub_mem_lambdaSet_of_special hR hiso hB hER hs.symm hb hb1
  have hnc := not_commuting_conjSub_of_opposite hR hiso hD hB hDB ⟨hER, hs.symm⟩ hDE hb hb1
  have hFI := lambdaSet_subset_isolatedSet hR hER hFl
  have hsp := (special_of_mem_isolatedSet hR h2 hFI hnc).1
  obtain ⟨B', hB'l, hFB'⟩ := exists_mem_lambdaSet_opposite hR hiso hD (hR.conjSub_mem hER b) hsp
  exact hFI.2 B' ⟨hB'l.1.1, hΛ B' hB'l⟩ hFB'

end CFSG.Timmesfeld.ARS
