module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Ag
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Inv3

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem xY_mem_T : xY ∈ T := by
  rw [mem_T_iff]
  have h := chkT_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 h
  refine ⟨i, by have := chkT_spec.1; omega, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, hie]
  exact repL_x

theorem tpTab_mem (j : Fin 45) : tpTab.contains (tpL j) = true := by
  rw [List.contains_iff_mem, ← tpTab_getD j j.2]
  have : j.val < tpTab.length := by rw [tpTab_length]; exact j.2
  rw [List.getD_eq_getElem _ _ this]
  exact List.getElem_mem _

theorem ag_of_centric {D : Subgroup Y}
    (hDT : D ≤ T) (hcen : ∀ t ∈ T, (∀ d ∈ D, t * d = d * t) → t ∈ D) :
    Subgroup.normalizer (D : Set Y) ≤ P1 ∨ Subgroup.normalizer (D : Set Y) ≤ P2 := by
  have hx : xY ∈ D := by
    refine hcen xY xY_mem_T fun d hd => ?_
    have h1 : d ∈ P1 := B0_le_P1 (T_le_B0 (hDT hd))
    rw [← centralizer_x, Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1.symm
  by_cases hP : ∀ p : Fin 45, p ≠ 0 → ∃ d ∈ D, (d : P45) p ≠ p
  · exact Or.inl (normalizer_le_P1_of_unique_point hDT hP)
  by_cases hL : ∀ k < 27, k ≠ 0 → ∃ d ∈ D, (d : P45) '' lnS k ≠ lnS k
  · exact Or.inr (normalizer_le_P2_of_unique_line hDT hL)
  obtain ⟨p, hp0, hpfix⟩ : ∃ p : Fin 45, p ≠ 0 ∧ ∀ d ∈ D, (d : P45) p = p := by
    by_contra hcon
    apply hP
    intro p hp0
    by_contra h
    apply hcon
    exact ⟨p, hp0, fun d hd => by_contra fun hne => h ⟨d, hd, hne⟩⟩
  obtain ⟨k, hk, hk0, hkfix⟩ : ∃ k, k < 27 ∧ k ≠ 0 ∧ ∀ d ∈ D, (d : P45) '' lnS k = lnS k := by
    by_contra hcon
    apply hL
    intro k hk hk0
    by_contra h
    apply hcon
    exact ⟨k, hk, hk0, fun d hd => by_contra fun hne => h ⟨d, hd, hne⟩⟩
  have hok := agOK_spec p.2 (fun h => hp0 (Fin.ext h)) hk hk0
  have hmemH : ∀ d ∈ D, ∃ j, j ∈ agH p.val k ∧ RepL (Tl.getD j []) (d : P45) := by
    intro d hd
    obtain ⟨j, hj, hrep⟩ := (mem_T_iff d).1 (hDT hd)
    refine ⟨j, (mem_agH_iff p.2 hk).2 ⟨hj, ?_, ?_⟩, hrep⟩
    · have := hrep.2 p
      rw [hpfix d hd] at this
      exact this
    · have h1 := image_lineSet hrep (lnTab_lt hk)
      have h2 : lineSet (imgSet (Tl.getD j []) (lnTab.getD k [])) = lineSet (lnTab.getD k []) := by
        rw [← h1]
        exact hkfix d hd
      exact sameSet_of_lineSet_eq h2
  rcases agOK_cases hok with ⟨i, hi, hiH, hcomm⟩ | hz
  · exfalso
    obtain ⟨t, htT, hti⟩ := exists_Tel hi
    have htD : t ∈ D := by
      refine hcen t htT fun d hd => ?_
      obtain ⟨j, hjH, hjrep⟩ := hmemH d hd
      have hj64 := ((mem_agH_iff p.2 hk).1 hjH).1
      have hc := commTab_eq hi hj64 (hcomm j hjH)
      apply Subtype.ext
      refine eq_of_repL (l := comp (Tl.getD i []) (Tl.getD j [])) (repL_mul hti hjrep) ?_
      rw [hc]
      exact repL_mul hjrep hti
    obtain ⟨j, hjH, hjrep⟩ := hmemH t htD
    have hl : Tl.getD i [] = Tl.getD j [] := repL_unique hti hjrep
    rcases chkT_spec.2.2.2.2.2.1 i hi j ((mem_agH_iff p.2 hk).1 hjH).1 with h | h
    · exact hiH (h ▸ hjH)
    · exact h hl
  · left
    intro n hn
    rw [← centralizer_x, Subgroup.mem_centralizer_singleton_iff]
    have hw : n * xY * n⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hn xY).1 hx
    obtain ⟨j, hjH, hjrep⟩ := hmemH _ hw
    have hwe : n * xY * n⁻¹ = sY ((n : P45) 0) := by
      rw [← sY_zero]
      exact sY_conj n 0
    have hrs : RepL (tpL ((n : P45) 0)) (((n * xY * n⁻¹ : Y)) : P45) := by
      rw [hwe]
      exact repL_sT _
    have hl : Tl.getD j [] = tpL ((n : P45) 0) := repL_unique hjrep hrs
    have hcont : tpTab.contains (Tl.getD j []) = true := by rw [hl]; exact tpTab_mem _
    have hzj := zclT_true ((mem_agH_iff p.2 hk).1 hjH).1 hcont
    rcases hz j hjH with h | h
    · rw [hzj] at h
      exact absurd h (by decide)
    · have : n * xY * n⁻¹ = xY :=
        Subtype.ext (eq_of_repL hjrep (by rw [h]; exact repL_x))
      have h2 : n * xY = xY * n := by
        calc n * xY = n * xY * n⁻¹ * n := by simp
          _ = xY * n := by rw [this]
      exact h2

end CFSG.Quasithin.H13.F431.U42
