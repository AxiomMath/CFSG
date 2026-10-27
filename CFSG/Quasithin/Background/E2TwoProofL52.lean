module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherExtremalParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace E2P

namespace L52

variable {F : Type} [Field F]

abbrev P (F : Type) [Field F] (d : ℕ) : Subgroup (projectiveSL 5 F) :=
  projStabilizer (flagSpace 5 F d)

noncomputable abbrev r (F : Type) [Field F] (d : ℕ) (hd : 1 ≤ d) (hd5 : d < 5) :
    projectiveSL 5 F :=
  proj 5 F (reflection 5 F d hd hd5)

theorem U_le (d : ℕ) : projUnitriangular 5 F ≤ P F d :=
  (Subgroup.map_mono (unitriangular_le_upperTriangular 5 F)).trans
    (projUpperTriangular_le_projStabilizer d)

theorem r_mem {i d : ℕ} (hi : 1 ≤ i) (hi5 : i < 5) (hid : d ≠ i) : r F i hi hi5 ∈ P F d := by
  rw [← Subgroup.mem_comap, comap_projStabilizer]
  exact reflection_mem_stabilizer_of_ne hi hi5 hid

theorem r_not_mem {d : ℕ} (hd : 1 ≤ d) (hd5 : d < 5) : r F d hd hd5 ∉ P F d := by
  rw [← Subgroup.mem_comap, comap_projStabilizer]
  exact reflection_notMem_stabilizer hd hd5

theorem P_ne_top {d : ℕ} (hd : 1 ≤ d) (hd5 : d < 5) : P F d ≠ ⊤ := fun h =>
  r_not_mem (F := F) hd hd5 (h ▸ Subgroup.mem_top _)

theorem eq_P_of_isCoatom [Finite F] (hF : Nat.card F = 2) {Y : Subgroup (projectiveSL 5 F)}
    (hY : IsCoatom Y) (hUY : projUnitriangular 5 F ≤ Y) : ∃ d, 1 ≤ d ∧ d < 5 ∧ Y = P F d :=
  eq_projStabilizer_of_isCoatom hY
    ((Subgroup.map_mono (Vol2Native.A312L.upperTriangular_le_unitriangular hF)).trans hUY)

theorem index_P [Finite F] (hF : Nat.card F = 2) {d : ℕ} (hd5 : d < 5) :
    ((P F d).index : ℚ) = gaussianCoeff 5 d 2 := by
  rw [index_projStabilizer, finrank_flagSpace (by omega), hF]

theorem gauss_one : gaussianCoeff 5 1 2 = 31 := by
  norm_num [gaussianCoeff, Finset.prod_range_succ]

theorem gauss_two : gaussianCoeff 5 2 2 = 155 := by
  norm_num [gaussianCoeff, Finset.prod_range_succ]

theorem gauss_three : gaussianCoeff 5 3 2 = 155 := by
  norm_num [gaussianCoeff, Finset.prod_range_succ]

theorem gauss_four : gaussianCoeff 5 4 2 = 31 := by
  norm_num [gaussianCoeff, Finset.prod_range_succ]

theorem P1_ne_P4 : P F 1 ≠ P F 4 := fun h =>
  r_not_mem (F := F) (d := 1) le_rfl (by norm_num)
    (by rw [h]; exact r_mem (i := 1) (d := 4) le_rfl (by norm_num) (by norm_num))

theorem P2_ne_P3 : P F 2 ≠ P F 3 := fun h =>
  r_not_mem (F := F) (d := 2) (by norm_num) (by norm_num)
    (by rw [h]; exact r_mem (i := 2) (d := 3) (by norm_num) (by norm_num) (by norm_num))

theorem map_P [Finite F] (hF : Nat.card F = 2) (α : MulAut (projectiveSL 5 F))
    (hα : (projUnitriangular 5 F).map α.toMonoidHom = projUnitriangular 5 F) {d : ℕ}
    (hd : 1 ≤ d) (hd5 : d < 5) :
    ∃ d', 1 ≤ d' ∧ d' < 5 ∧ (P F d).map α.toMonoidHom = P F d' ∧
      gaussianCoeff 5 d' 2 = gaussianCoeff 5 d 2 := by
  have hc : IsCoatom ((P F d).map α.toMonoidHom) :=
    ((MulEquiv.mapSubgroup α).isCoatom_iff _).mpr (isCoatom_projStabilizer_flagSpace hd hd5)
  obtain ⟨d', hd', hd'5, hd'eq⟩ := eq_P_of_isCoatom hF hc (hα ▸ Subgroup.map_mono (U_le d))
  refine ⟨d', hd', hd'5, hd'eq, ?_⟩
  rw [← index_P hF hd'5, ← index_P hF hd5, ← hd'eq]
  have := Subgroup.index_map_equiv (P F d) α
  exact_mod_cast this

theorem inv14 [Finite F] (hF : Nat.card F = 2) (α : MulAut (projectiveSL 5 F))
    (hα : (projUnitriangular 5 F).map α.toMonoidHom = projUnitriangular 5 F) :
    (P F 1 ⊓ P F 4).map α.toMonoidHom = P F 1 ⊓ P F 4 := by
  rw [Subgroup.map_inf _ _ _ α.injective]
  obtain ⟨a, ha, ha5, hae, hag⟩ := map_P hF α hα (d := 1) le_rfl (by norm_num)
  obtain ⟨b, hb, hb5, hbe, hbg⟩ := map_P hF α hα (d := 4) (by norm_num) (by norm_num)
  have hne : (P F 1).map α.toMonoidHom ≠ (P F 4).map α.toMonoidHom := fun h =>
    P1_ne_P4 (Subgroup.map_injective α.injective h)
  rw [hae, hbe] at hne ⊢
  rw [gauss_one] at hag
  rw [gauss_four] at hbg
  interval_cases a <;> interval_cases b <;> simp_all [gauss_one, gauss_two, gauss_three,
    gauss_four, inf_comm]

theorem inv23 [Finite F] (hF : Nat.card F = 2) (α : MulAut (projectiveSL 5 F))
    (hα : (projUnitriangular 5 F).map α.toMonoidHom = projUnitriangular 5 F) :
    (P F 2 ⊓ P F 3).map α.toMonoidHom = P F 2 ⊓ P F 3 := by
  rw [Subgroup.map_inf _ _ _ α.injective]
  obtain ⟨a, ha, ha5, hae, hag⟩ := map_P hF α hα (d := 2) (by norm_num) (by norm_num)
  obtain ⟨b, hb, hb5, hbe, hbg⟩ := map_P hF α hα (d := 3) (by norm_num) (by norm_num)
  have hne : (P F 2).map α.toMonoidHom ≠ (P F 3).map α.toMonoidHom := fun h =>
    P2_ne_P3 (Subgroup.map_injective α.injective h)
  rw [hae, hbe] at hne ⊢
  rw [gauss_two] at hag
  rw [gauss_three] at hbg
  interval_cases a <;> interval_cases b <;> simp_all [gauss_one, gauss_two, gauss_three,
    gauss_four, inf_comm]

theorem sup_eq_top [Finite F] (hF : Nat.card F = 2) :
    (P F 1 ⊓ P F 4) ⊔ (P F 2 ⊓ P F 3) = ⊤ := by
  by_contra hne
  obtain ⟨Z, hYZ, hZ⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.mpr hne)
  have hUZ : projUnitriangular 5 F ≤ Z :=
    (le_inf (U_le 1) (U_le 4)).trans (le_sup_left.trans hYZ)
  obtain ⟨d, hd, hd5, rfl⟩ := eq_P_of_isCoatom hF hZ.isCoatom hUZ
  have h14 : P F 1 ⊓ P F 4 ≤ P F d := le_sup_left.trans hYZ
  have h23 : P F 2 ⊓ P F 3 ≤ P F d := le_sup_right.trans hYZ
  interval_cases d
  · exact r_not_mem (F := F) (d := 1) le_rfl (by norm_num)
      (h23 ⟨r_mem (by norm_num) (by norm_num) (by norm_num),
        r_mem (by norm_num) (by norm_num) (by norm_num)⟩)
  · exact r_not_mem (F := F) (d := 2) (by norm_num) (by norm_num)
      (h14 ⟨r_mem (by norm_num) (by norm_num) (by norm_num),
        r_mem (by norm_num) (by norm_num) (by norm_num)⟩)
  · exact r_not_mem (F := F) (d := 3) (by norm_num) (by norm_num)
      (h14 ⟨r_mem (by norm_num) (by norm_num) (by norm_num),
        r_mem (by norm_num) (by norm_num) (by norm_num)⟩)
  · exact r_not_mem (F := F) (d := 4) (by norm_num) (by norm_num)
      (h23 ⟨r_mem (by norm_num) (by norm_num) (by norm_num),
        r_mem (by norm_num) (by norm_num) (by norm_num)⟩)

end L52

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem ASHyp.not_l52 (hX : ASHyp K T M) (h : IsPSL 5 2 1 ↥K) : False := by
  obtain ⟨⟨-, hf, -⟩, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have hCh : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  let e' : ↥K ≃* projectiveSL 5 F := e.trans (Setup.X7a.statedSLEquivProjectiveSL 5 F)
  obtain ⟨P0, hP0⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 5) (by norm_num)
  have hU : IsSylowTwoOf (projUnitriangular 5 F) ⊤ := hP0 ▸ isSylowTwoOf_top_of_sylow P0
  exact hX.false_of_invPair e' hU (le_inf (L52.U_le 1) (L52.U_le 4))
    (le_inf (L52.U_le 2) (L52.U_le 3))
    (fun h => L52.P_ne_top (F := F) (d := 1) le_rfl (by norm_num) (top_le_iff.mp (h ▸ inf_le_left)))
    (fun h => L52.P_ne_top (F := F) (d := 2) (by norm_num) (by norm_num)
      (top_le_iff.mp (h ▸ inf_le_left)))
    (L52.sup_eq_top hF2) fun α hα => ⟨L52.inv14 hF2 α hα, L52.inv23 hF2 α hα⟩

end E2P

end CFSG.Quasithin
