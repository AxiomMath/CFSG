module

public import CFSG.Quasithin.EmptyFaithful.S152WBase
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.M23

public section

namespace CFSG.Quasithin.S152W

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.GH74.Generic.S45

theorem m12_class_card :
    ∀ u ∈ NativeSporadic.M12, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M12 u) = 192 ∨
      Nat.card (centralizerIn NativeSporadic.M12 u) = 240 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, hsz, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  rw [m12InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m12Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := LAlt.card_centralizerIn_of_reps hn m12Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m12Rep1, m12CentQ1.originalSubgroup), (m12Rep2, m12CentQ2.originalSubgroup)] (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 1000 hok (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_⟩
        rw [hsz.1, hKc1, m12Certificate_originalSubgroup, m12_card]
      · refine ⟨hK2, ?_⟩
        rw [hsz.2, hKc2, m12Certificate_originalSubgroup, m12_card]) u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (hcard.trans hKc1)
  · exact Or.inr (hcard.trans hKc2)

theorem atlasClauses_M11 :
    AtlasClauses ↥NativeSporadic.M11 := by
  refine atlasClauses_of_data
    (card_outer_le_two_of_card_aut m11_center_eq_bot' ?_) [48] ?_ (hbad_of_not_dvd _ (by decide))
  · exact m11_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  · intro t ht
    rw [card_centralizer_subtype]
    have := LAlt.m11_class_card (t : Equiv.Perm (Fin 11)) t.2
      (by rw [Subgroup.orderOf_coe]; exact ht)
    simp only [List.mem_singleton]
    exact this

theorem atlasClauses_M12 :
    AtlasClauses ↥NativeSporadic.M12 := by
  refine atlasClauses_of_data
    (card_outer_le_two_of_card_aut m12_center_eq_bot' m12_mulAut_card) [192, 240] ?_
    (hbad_of_not_dvd _ (by decide))
  intro t ht
  rw [card_centralizer_subtype]
  have := m12_class_card (t : Equiv.Perm (Fin 12)) t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact this

theorem atlasClauses_M22 :
    AtlasClauses ↥NativeSporadic.M22 := by
  refine atlasClauses_of_data
    (card_outer_le_two_of_card_aut m22_center_eq_bot' m22_mulAut_card) [384] ?_
    (hbad_of_not_dvd _ (by decide))
  intro t ht
  rw [card_centralizer_subtype]
  have := LSporB.m22_inner_centralizer_card (t : Equiv.Perm (Fin 22)) t.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  simp only [List.mem_singleton]
  exact this

theorem atlasClauses_M23 :
    AtlasClauses ↥NativeSporadic.M23 := by
  refine atlasClauses_of_data at_m23_schreier.1 [2688] ?_ (hbad_of_not_dvd _ (by decide))
  intro t ht
  rw [card_centralizer_subtype]
  have := LAlt.m23_class_card (t : Equiv.Perm (Fin 23)) t.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  simp only [List.mem_singleton]
  exact this

theorem atlasClauses_M24 :
    AtlasClauses ↥NativeSporadic.M24 := by
  refine atlasClauses_of_data
    (card_outer_le_two_of_card_aut m24_center_eq_bot'
      (m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num)))) [21504, 7680] ?_
    (hbad_of_not_dvd _ (by decide))
  intro t ht
  rw [card_centralizer_subtype]
  have := LAlt.m24_class_card (t : Equiv.Perm (Fin 24)) t.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact this

end CFSG.Quasithin.S152W
