module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsA8Data

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix

namespace CFSG.Quasithin.H13.A6.GR

namespace Row8

theorem hgcs8 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (fr : Frame V L ↥(alternatingGroup (Fin 8)) 6) (hfr : ∀ γ, fr.mat γ = mat8 γ.1) :
    ∀ p ∈ gcs8, fr.mat p.1 = matOfCols 6 p.2 := by
  intro p hp
  simp only [gcs8, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hfr]; exact mat_g1
  · rw [hfr]; exact mat_g1inv
  · rw [hfr]; exact mat_g2
  · rw [hfr]; exact mat_g2inv
  · rw [hfr]; exact mat_g3
  · rw [hfr]; exact mat_g3inv

theorem hinv8 : ∀ p ∈ gcs8, ∃ q ∈ gcs8, q.1 = p.1⁻¹ := by
  intro p hp
  simp only [gcs8, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(x1⁻¹, [9, 2, 34, 8, 19, 4]), by simp [gcs8], rfl⟩
  · exact ⟨(x1, [9, 2, 32, 8, 27, 6]), by simp [gcs8], by simp⟩
  · exact ⟨(x2⁻¹, [1, 2, 5, 10, 50, 43]), by simp [gcs8], rfl⟩
  · exact ⟨(x2, [1, 2, 5, 10, 59, 41]), by simp [gcs8], by simp⟩
  · exact ⟨(x3⁻¹, [9, 2, 32, 10, 31, 6]), by simp [gcs8], rfl⟩
  · exact ⟨(x3, [11, 2, 34, 10, 49, 4]), by simp [gcs8], by simp⟩

theorem gcols8_len : ∀ p ∈ gcols8, p.length = 6 := by decide

theorem slist8_cl' : ∀ c ∈ slist8, ∀ p ∈ gcs8, ∃ c' ∈ slist8,
    normC 6 c' = normC 6 (mulC 6 p.2 c) := by
  intro c hc p hp
  have h2 := List.all_eq_true.mp slist8_cl_fast c hc
  have hp' : p.2 ∈ gcols8 := by
    rw [← gcols8_eq]
    exact List.mem_map_of_mem hp
  have h3 := List.any_eq_true.mp (List.all_eq_true.mp h2 p.2 hp')
  obtain ⟨c', hc', h4⟩ := h3
  refine ⟨c', hc', ?_⟩
  have h5 : c' = mulL p.2 c := beq_iff_eq.mp h4
  rw [h5, mulL_eq6 c (gcols8_len p.2 hp')]

theorem slist8_pow' : ∀ c ∈ slist8, isOne 6 (sqIter 6 c 3) = true := by
  intro c hc
  have hl : c.length = 6 := beq_iff_eq.mp (List.all_eq_true.mp slist8_len c hc)
  have hp : isOneL (sqIterL c 3) = true := List.all_eq_true.mp slist8_pow_fast c hc
  rw [← sqIterL_eq 6 3 c hl, isOne_eq (by rw [length_sqIterL, hl])]
  exact hp

@[expose] noncomputable def modelHyp8 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (fr : Frame V L ↥(alternatingGroup (Fin 8)) 6) (hfr : ∀ γ, fr.mat γ = mat8 γ.1) :
    ModelHyp 6 ↥(alternatingGroup (Fin 8)) fr.mat where
  S0 := Subgroup.closure {x | x ∈ gcs8.map Prod.fst}
  p2 := isPGroup_closure laws6 fr.mat fr.mat_mul fr.mat_one (fun γ h => fr.eq_one_of_mat h) gcs8
    (hgcs8 fr hfr) hinv8 slist8 3 slist8_one slist8_cl' slist8_pow'
  gens := [x1, x2, x3]
  gens_mem := by
    intro g hg
    refine Subgroup.subset_closure ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp [gcs8]
  cyc := cycOf 6 gm8 u8 words8 binv8
  cyc_gm := by
    have h1 : fr.mat x1 = matOfCols 6 [9, 2, 32, 8, 27, 6] := by rw [hfr]; exact mat_g1
    have h2 : fr.mat x2 = matOfCols 6 [1, 2, 5, 10, 59, 41] := by rw [hfr]; exact mat_g2
    have h3 : fr.mat x3 = matOfCols 6 [11, 2, 34, 10, 49, 4] := by rw [hfr]; exact mat_g3
    simp only [cycOf, gm8, List.map_cons, List.map_nil]
    rw [h1, h2, h3]
  hB := hB_of laws6 gm8 u8 words8 binv8 hw8 hB8c
  Mem := MemQ
  hMem := fun γ => by rw [hfr]; exact memQ_mat8 γ.1
  a := 7
  hd := by norm_num
  leaf := by
    have h1 : fr.mat x1 = matOfCols 6 [9, 2, 32, 8, 27, 6] := by rw [hfr]; exact mat_g1
    have h2 : fr.mat x2 = matOfCols 6 [1, 2, 5, 10, 59, 41] := by rw [hfr]; exact mat_g2
    have h3 : fr.mat x3 = matOfCols 6 [11, 2, 34, 10, 49, 4] := by rw [hfr]; exact mat_g3
    have h1i : fr.mat x1⁻¹ = matOfCols 6 [9, 2, 34, 8, 19, 4] := by rw [hfr]; exact mat_g1inv
    have h2i : fr.mat x2⁻¹ = matOfCols 6 [1, 2, 5, 10, 50, 43] := by rw [hfr]; exact mat_g2inv
    have h3i : fr.mat x3⁻¹ = matOfCols 6 [9, 2, 32, 10, 31, 6] := by rw [hfr]; exact mat_g3inv
    have hgp : [x1, x2, x3].map (fun s => (fr.mat s, fr.mat s⁻¹)) =
        gp8.map fun p => (matOfCols 6 p.1, matOfCols 6 p.2) := by
      simp only [gp8, List.map_cons, List.map_nil]
      rw [h1, h2, h3, h1i, h2i, h3i]
    rw [hgp]
    exact leaf_of_search laws6 gm8 gp8 u8 words8 binv8 hw8 okQ8 fullQ8 7 MemQ hok8 hfull8
      hsearch8

end Row8

end CFSG.Quasithin.H13.A6.GR

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank in
theorem factCommA8 : FactCommA8 := by
  intro V _ _ hV G L A hB4 hrow v hcond hrk S X hS hSv hXL hXv hSX hXO hX1
  obtain ⟨fr, hfr⟩ := GR.Row8.exists_frame8 hrow
  exact GR.comm_core fr (GR.Row8.modelHyp8 fr hfr) hcond.sq hrk hS hSv hXL hXv hSX hXO hX1

end CFSG.Quasithin.H13.A6
