module

public import CFSG.Sporadic.Recognition.HNMultiplierExact

public section

namespace CFSG.Sporadic.Recognition.HNMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.Sporadic.Recognition.CoverBootstrap Subgroup

theorem rel_center_of_eval {r : List (Fin 7 × Bool)} {z : PC} (hr : r ∈ hnRels)
    (hv : FreeGroup.lift hx (FreeGroup.mk r) = z) : z ∈ center PC :=
  hv ▸ lift_coverGen_rel_center hr

theorem hP_central :
    hx 5 * hx 0 * (hx 5)⁻¹ * (hx 0)⁻¹ ∈ center PC ∧
      hx 5 * hx 4 * (hx 5)⁻¹ * (hx 4)⁻¹⁻¹ ∈ center PC ∧
      hx 5 * hx 2 * (hx 5)⁻¹ * (hx 3)⁻¹ ∈ center PC ∧
      hx 5 * hx 3 * (hx 5)⁻¹ * (hx 2)⁻¹ ∈ center PC ∧
      hx 5 * hx 1 * (hx 5)⁻¹ * (hx 3 * hx 0 * (hx 3)⁻¹)⁻¹ ∈ center PC := by
  have c0 : hx 5 * hx 5 ∈ center PC :=
    rel_center_of_eval (r := [((5 : Fin 7), true), (5, true)]) (by decide)
      (by simp [FreeGroup.lift_mk])
  have c1 : hx 4 * hx 5 * hx 4 * hx 5 ∈ center PC :=
    rel_center_of_eval (r := [((4 : Fin 7), true), (5, true), (4, true), (5, true)]) (by decide)
      (by simp [FreeGroup.lift_mk, mul_assoc])
  have c2 : (hx 0)⁻¹ * (hx 5)⁻¹ * hx 0 * hx 5 ∈ center PC :=
    rel_center_of_eval (r := [((0 : Fin 7), false), (5, false), (0, true), (5, true)])
      (by decide) (by simp [FreeGroup.lift_mk, mul_assoc])
  have c3 : (hx 3)⁻¹ * hx 5 * hx 2 * hx 5 ∈ center PC :=
    rel_center_of_eval (r := hnEDef) (by decide)
      (by simp [show hnEDef = [((3 : Fin 7), false), (5, true), (2, true), (5, true)] from
        by decide, FreeGroup.lift_mk, mul_assoc])
  have c4 : (hx 1)⁻¹ * hx 2 * hx 0 * (hx 2)⁻¹ ∈ center PC :=
    rel_center_of_eval (r := hnGDef) (by decide)
      (by simp [show hnGDef = [((1 : Fin 7), false), (2, true), (0, true), (2, false)] from
        by decide, FreeGroup.lift_mk, mul_assoc])
  exact conj_identities (center PC) c0 c1 c2 c3 c4

section Conj

variable {X : Type} [Group X] {g : Fin 7 → X} (H : HNGens g)

include H

theorem hX_ids :
    g 5 * g 0 * (g 5)⁻¹ = g 0 ∧ g 5 * g 4 * (g 5)⁻¹ = (g 4)⁻¹ ∧ g 5 * g 2 * (g 5)⁻¹ = g 3 ∧
      g 5 * g 3 * (g 5)⁻¹ = g 2 ∧ g 5 * g 1 * (g 5)⁻¹ = g 3 * g 0 * (g 3)⁻¹ := by
  have h0 : g 5 * g 5 ∈ (⊥ : Subgroup X) := by
    rw [Subgroup.mem_bot]
    simpa [FreeGroup.lift_mk] using H.rels [((5 : Fin 7), true), (5, true)] (by decide)
  have h1 : g 4 * g 5 * g 4 * g 5 ∈ (⊥ : Subgroup X) := by
    rw [Subgroup.mem_bot]
    simpa [FreeGroup.lift_mk, mul_assoc] using
      H.rels [((4 : Fin 7), true), (5, true), (4, true), (5, true)] (by decide)
  have h2 : (g 0)⁻¹ * (g 5)⁻¹ * g 0 * g 5 ∈ (⊥ : Subgroup X) := by
    rw [Subgroup.mem_bot]
    simpa [FreeGroup.lift_mk, mul_assoc] using
      H.rels [((0 : Fin 7), false), (5, false), (0, true), (5, true)] (by decide)
  have h3 : (g 3)⁻¹ * g 5 * g 2 * g 5 ∈ (⊥ : Subgroup X) := by
    rw [Subgroup.mem_bot]
    have := H.rels hnEDef (by decide)
    simpa [show hnEDef = [((3 : Fin 7), false), (5, true), (2, true), (5, true)] from by decide,
      FreeGroup.lift_mk, mul_assoc] using this
  have h4 : (g 1)⁻¹ * g 2 * g 0 * (g 2)⁻¹ ∈ (⊥ : Subgroup X) := by
    rw [Subgroup.mem_bot]
    have := H.rels hnGDef (by decide)
    simpa [show hnGDef = [((1 : Fin 7), false), (2, true), (0, true), (2, false)] from by decide,
      FreeGroup.lift_mk, mul_assoc] using this
  obtain ⟨e1, e2, e3, e4, e5⟩ := conj_identities (⊥ : Subgroup X) h0 h1 h2 h3 h4
  simp only [Subgroup.mem_bot] at e1 e2 e3 e4 e5
  refine ⟨mul_inv_eq_one.1 e1, ?_, mul_inv_eq_one.1 e3, mul_inv_eq_one.1 e4,
    mul_inv_eq_one.1 e5⟩
  have e2' : g 5 * g 4 * (g 5)⁻¹ * g 4 = 1 := by simpa using e2
  exact eq_inv_of_mul_eq_one_left e2'

end Conj

section Conj2

variable {X : Type} [Group X] {g : Fin 7 → X} (H : HNGens g)

include H

theorem hnConj_eqs (hinj : Function.Injective (hnPsi H)) :
    hx 5 * hx 0 * (hx 5)⁻¹ = hx 0 ∧ hx 5 * hx 4 * (hx 5)⁻¹ = (hx 4)⁻¹ ∧
      hx 5 * hx 2 * (hx 5)⁻¹ = hx 3 ∧ hx 5 * hx 3 * (hx 5)⁻¹ = hx 2 ∧
      hx 5 * hx 1 * (hx 5)⁻¹ = hx 3 * hx 0 * (hx 3)⁻¹ := by
  obtain ⟨E0, E4, E2, E3, E1⟩ := hX_ids H
  obtain ⟨C0, C4, C2, C3, C1⟩ := hP_central
  have hmem : ∀ i : Fin 7, i.val < 5 → hx i ∈ hnH := hx_mem_hnH
  have key : ∀ i : Fin 7, i.val < 5 → ∃ u ∈ hnH,
      hnPi H u = hnPi H (hx 5) * hnPi H (hx i) * (hnPi H (hx 5))⁻¹ ∧
        hx 5 * hx i * (hx 5)⁻¹ * u⁻¹ ∈ center PC := by
    intro i hi
    fin_cases i
    · exact ⟨hx 0, hmem 0 (by decide), by simp only [hnPi_hx]; exact E0.symm, C0⟩
    · exact ⟨hx 3 * hx 0 * (hx 3)⁻¹, mul_mem (mul_mem (hmem 3 (by decide)) (hmem 0 (by decide)))
        (inv_mem (hmem 3 (by decide))), by simp [hnPi_hx, E1], C1⟩
    · exact ⟨hx 3, hmem 3 (by decide), by simp only [hnPi_hx]; exact E2.symm, C2⟩
    · exact ⟨hx 2, hmem 2 (by decide), by simp only [hnPi_hx]; exact E3.symm, C3⟩
    · exact ⟨(hx 4)⁻¹, inv_mem (hmem 4 (by decide)), by simp [hnPi_hx, E4], C4⟩
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
  have hconj := conj_eq_of_perfect (hnPi H) hnH commutator_hnH (hnH_inj H hinj)
    (Set.range fun j => hx (hnSigma j)) rfl (hx 5) (by
      rintro s ⟨j, rfl⟩
      exact key (hnSigma j) (by rw [hnSigma_val]; have := j.2; have h5 := hnS1L_length; omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hconj (hx 0) (hmem 0 (by decide)) (hx 0) (hmem 0 (by decide))
      (by simp only [hnPi_hx, E0])
  · exact hconj (hx 4) (hmem 4 (by decide)) (hx 4)⁻¹ (inv_mem (hmem 4 (by decide)))
      (by simp [hnPi_hx, E4])
  · exact hconj (hx 2) (hmem 2 (by decide)) (hx 3) (hmem 3 (by decide))
      (by simp only [hnPi_hx, E2])
  · exact hconj (hx 3) (hmem 3 (by decide)) (hx 2) (hmem 2 (by decide))
      (by simp only [hnPi_hx, E3])
  · exact hconj (hx 1) (hmem 1 (by decide)) (hx 3 * hx 0 * (hx 3)⁻¹)
      (mul_mem (mul_mem (hmem 3 (by decide)) (hmem 0 (by decide))) (inv_mem (hmem 3 (by decide))))
      (by simp [hnPi_hx, E1])

end Conj2

section D2

variable {X : Type} [Group X] {g : Fin 7 → X} (H : HNGens g)

include H

theorem hnd_sq (hinj : Function.Injective (hnPsi H)) : hx 5 * hx 5 = 1 := by
  have hr : hnRc ∈ hnRels := by simp [hnRels]
  have hval : FreeGroup.lift hx (FreeGroup.mk hnRc) =
      FreeGroup.lift hx (FreeGroup.mk hnConj) * hx 5 *
        (FreeGroup.lift hx (FreeGroup.mk hnConj))⁻¹ * (hx 4 * hx 4)⁻¹ := by
    unfold hnRc
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul, map_mul,
      ← FreeGroup.inv_mk, map_inv]
    simp [FreeGroup.lift_mk]
  have hc := rel_center_of_eval hr hval
  have hc2 := hval ▸ lift_coverGen_rel_sq (R := hnRels) (cw := hnCommWord) hr
  have ha4 : hx 4 * hx 4 * (hx 4 * hx 4) = 1 := by
    have := hnPlain1_eval H hinj [((4 : Fin 7), true), (4, true), (4, true), (4, true)]
      (by decide)
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  exact sq_eq_one_of_conj hc hc2 ha4

theorem hnNwords_eval (hinj : Function.Injective (hnPsi H)) :
    ∀ w ∈ hnNwords, FreeGroup.lift hx (FreeGroup.mk w) = 1 := by
  obtain ⟨N0, N4, N2, N3, N1⟩ := hnConj_eqs H hinj
  have hdd := hnd_sq H hinj
  have e0 : ofCodes [10, 0, 11, 1] = [((5 : Fin 7), true), (0, true), (5, false), (0, false)] := by
    decide
  have e1 : ofCodes [10, 8, 11, 8] = [((5 : Fin 7), true), (4, true), (5, false), (4, true)] := by
    decide
  have e2 : ofCodes [10, 4, 11, 7] = [((5 : Fin 7), true), (2, true), (5, false), (3, false)] := by
    decide
  have e3 : ofCodes [10, 6, 11, 5] = [((5 : Fin 7), true), (3, true), (5, false), (2, false)] := by
    decide
  have e4 : ofCodes [10, 2, 11, 6, 1, 7] = [((5 : Fin 7), true), (1, true), (5, false), (3, true),
      (0, false), (3, false)] := by
    decide
  have e5 : ofCodes [10, 10] = [((5 : Fin 7), true), (5, true)] := by decide
  intro w hw
  simp only [hnNwords, hnNCodes, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
    or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : hx 5 * hx 0 * (hx 5)⁻¹ * (hx 0)⁻¹ = 1 := by rw [N0, mul_inv_cancel]
    rw [e0]
    simpa [FreeGroup.lift_mk, mul_assoc] using h
  · have h : hx 5 * hx 4 * (hx 5)⁻¹ * hx 4 = 1 := by rw [N4, inv_mul_cancel]
    rw [e1]
    simpa [FreeGroup.lift_mk, mul_assoc] using h
  · have h : hx 5 * hx 2 * (hx 5)⁻¹ * (hx 3)⁻¹ = 1 := by rw [N2, mul_inv_cancel]
    rw [e2]
    simpa [FreeGroup.lift_mk, mul_assoc] using h
  · have h : hx 5 * hx 3 * (hx 5)⁻¹ * (hx 2)⁻¹ = 1 := by rw [N3, mul_inv_cancel]
    rw [e3]
    simpa [FreeGroup.lift_mk, mul_assoc] using h
  · have h : hx 5 * hx 1 * (hx 5)⁻¹ * hx 3 * (hx 0)⁻¹ * (hx 3)⁻¹ = 1 := by rw [N1]; group
    rw [e4]
    simpa [FreeGroup.lift_mk, mul_assoc] using h
  · rw [e5]
    simpa [FreeGroup.lift_mk] using hdd

end D2

section Final

variable {X : Type} [Group X] {g : Fin 7 → X} (H : HNGens g)

theorem mem_of_all_contains {l ws : List (List (Fin 7 × Bool))}
    (h : l.all (fun w => ws.contains w) = true) : ∀ w ∈ l, w ∈ ws := fun w hw =>
  List.contains_iff_mem.1 (List.all_eq_true.1 h w hw)

theorem hnL3_mem_plus :
    ∀ w ∈ hnL3, w ∈ restrictWords hnTL hnCoverPlus :=
  fun _ hw => mem_restrictWords_of_subset (fun w' hw' => by simp [hnCoverPlus, hw']) hw

theorem hnL2_mem_plus :
    ∀ w ∈ hnL2, w ∈ restrictWords hnS1L (restrictWords hnTL hnCoverPlus) :=
  fun w hw => mem_restrictWords_of_subset (fun _ hw' => mem_restrictWords_of_subset
    (fun _ hw'' => List.mem_append_left _ hw'') hw') (hnL2_mem w hw)

theorem hnL1_mem_plus :
    ∀ w ∈ hnL1, w ∈ restrictWords hnS2L (restrictWords hnS1L (restrictWords hnTL hnCoverPlus)) :=
  fun w hw => mem_restrictWords_of_subset (fun _ hw' => mem_restrictWords_of_subset
    (fun _ hw'' => mem_restrictWords_of_subset (fun _ hw3 => List.mem_append_left _ hw3) hw'')
    hw') (hnL1_mem w hw)

include H

end Final

end CFSG.Sporadic.Recognition.HNMultiplier
