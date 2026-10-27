module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsG2Mem
public import CFSG.Quasithin.H13.GoldschmidtA6RowsG2Data

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix

namespace CFSG.Quasithin.H13.A6.GR

namespace G2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.H13.VolI

@[expose] def s1 : ↥subG2 := gensK 1 * gensK 0 * gensK 0 * gensK 1 * gensK 0

@[expose] def s2 : ↥subG2 :=
  gensK 1 * gensK 0 * gensK 1 * gensK 0 * gensK 0 * gensK 1 * gensK 0 * gensK 1 * gensK 0 *
    gensK 0

theorem matG2_s1 :
    matG2 s1 = matOfCols 6 [1, 14, 16, 12, 5, 39] := by
  simp only [s1, matG2_mul, matG2_gensK0, matG2_gensK1, colsA, colsB]
  decide +kernel

theorem matG2_s2 :
    matG2 s2 = matOfCols 6 [1, 6, 4, 25, 17, 35] := by
  simp only [s2, matG2_mul, matG2_gensK0, matG2_gensK1, colsA, colsB]
  decide +kernel

theorem matG2_inv_of (g : ↥subG2) {cols icols : List ℕ} (h : matG2 g = matOfCols 6 cols)
    (h1 : matOfCols 6 cols * matOfCols 6 icols = 1) : matG2 g⁻¹ = matOfCols 6 icols := by
  have h2 : matG2 g⁻¹ * matOfCols 6 cols = 1 := by
    rw [← h, ← matG2_mul, inv_mul_cancel, matG2_one]
  exact left_inv_eq_right_inv h2 h1

theorem matG2_s1inv :
    matG2 s1⁻¹ = matOfCols 6 [1, 10, 17, 25, 4, 58] :=
  matG2_inv_of s1 matG2_s1 (by decide +kernel)

theorem matG2_s2inv :
    matG2 s2⁻¹ = matOfCols 6 [1, 6, 4, 24, 17, 39] :=
  matG2_inv_of s2 matG2_s2 (by decide +kernel)

@[expose] def gcsG2 : List (↥subG2 × List ℕ) :=
  [(s1, [1, 14, 16, 12, 5, 39]), (s1⁻¹, [1, 10, 17, 25, 4, 58]),
    (s2, [1, 6, 4, 25, 17, 35]), (s2⁻¹, [1, 6, 4, 24, 17, 39])]

theorem gcsG2_eq : gcsG2.map Prod.snd = gcolsG2 := rfl

theorem hgcsG2
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (fr : Frame V L ↥subG2 6) (hfr : ∀ γ, fr.mat γ = matG2 γ) :
    ∀ p ∈ gcsG2, fr.mat p.1 = matOfCols 6 p.2 := by
  intro p hp
  simp only [gcsG2, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [hfr]; exact matG2_s1
  · rw [hfr]; exact matG2_s1inv
  · rw [hfr]; exact matG2_s2
  · rw [hfr]; exact matG2_s2inv

theorem hinvG2 : ∀ p ∈ gcsG2, ∃ q ∈ gcsG2, q.1 = p.1⁻¹ := by
  intro p hp
  simp only [gcsG2, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨(s1⁻¹, [1, 10, 17, 25, 4, 58]), by simp [gcsG2], rfl⟩
  · exact ⟨(s1, [1, 14, 16, 12, 5, 39]), by simp [gcsG2], by simp⟩
  · exact ⟨(s2⁻¹, [1, 6, 4, 24, 17, 39]), by simp [gcsG2], rfl⟩
  · exact ⟨(s2, [1, 6, 4, 25, 17, 35]), by simp [gcsG2], by simp⟩

theorem slistG2_cl' : ∀ c ∈ slistG2, ∀ p ∈ gcsG2, ∃ c' ∈ slistG2,
    normC 6 c' = normC 6 (mulC 6 p.2 c) := by
  intro c hc p hp
  have h2 := List.all_eq_true.mp slistG2_cl_fast c hc
  have hp' : p.2 ∈ gcolsG2 := by
    rw [← gcsG2_eq]
    exact List.mem_map_of_mem hp
  have h3 := List.any_eq_true.mp (List.all_eq_true.mp h2 p.2 hp')
  obtain ⟨c', hc', h4⟩ := h3
  refine ⟨c', hc', ?_⟩
  have h5 : c' = mulL p.2 c := beq_iff_eq.mp h4
  rw [h5, mulL_eq6 c (gcolsG2_len p.2 hp')]

theorem slistG2_pow' : ∀ c ∈ slistG2, isOne 6 (sqIter 6 c 3) = true := by
  intro c hc
  have hl : c.length = 6 := beq_iff_eq.mp (List.all_eq_true.mp slistG2_len c hc)
  have hp : isOneL (sqIterL c 3) = true := List.all_eq_true.mp slistG2_pow_fast c hc
  rw [← sqIterL_eq 6 3 c hl, isOne_eq (by rw [length_sqIterL, hl])]
  exact hp

theorem leafG2 : ∀ w : Fin 6 → ZMod 2,
    (cycOf 6 gmG2 uG2 wordsG2 binvG2).Pmat w * (cycOf 6 gmG2 uG2 wordsG2 binvG2).Pmat w = 1 →
    (∀ A ∈ (cycOf 6 gmG2 uG2 wordsG2 binvG2).gm,
      (cycOf 6 gmG2 uG2 wordsG2 binvG2).Pmat w * A = A * (cycOf 6 gmG2 uG2 wordsG2 binvG2).Pmat w) →
    fixCard ((cycOf 6 gmG2 uG2 wordsG2 binvG2).Pmat w) = 2 ^ (6 - 2) →
    ∀ K, MemG2 K → K * (cycOf 6 gmG2 uG2 wordsG2 binvG2).Pmat w =
        (cycOf 6 gmG2 uG2 wordsG2 binvG2).Pmat w * K →
      K ^ (3 * 2 ^ 6) = 1 ∧ (K ^ 3 = 1 → K ≠ 1 → Span [K]) := by
  intro w h1 h2 h3 K hK hKP
  have := leaf_of_search laws6 gmG2 [] uG2 wordsG2 binvG2 hwG2 okG2 fullG2 6 MemG2 hokG2 hfullG2
    hsearchG2 w h1 h2 h3 K hK hKP
  exact this

@[expose] def modelHypG2
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (fr : Frame V L ↥subG2 6) (hfr : ∀ γ, fr.mat γ = matG2 γ) :
    ModelHyp 6 ↥subG2 fr.mat where
  S0 := Subgroup.closure {x | x ∈ gcsG2.map Prod.fst}
  p2 := isPGroup_closure laws6 fr.mat fr.mat_mul fr.mat_one (fun γ h => fr.eq_one_of_mat h) gcsG2
    (hgcsG2 fr hfr) hinvG2 slistG2 3 slistG2_one slistG2_cl' slistG2_pow'
  gens := [s1, s2]
  gens_mem := by
    intro g hg
    refine Subgroup.subset_closure ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp [gcsG2]
  cyc := cycOf 6 gmG2 uG2 wordsG2 binvG2
  cyc_gm := by
    have h1 : fr.mat s1 = matOfCols 6 [1, 14, 16, 12, 5, 39] := by rw [hfr]; exact matG2_s1
    have h2 : fr.mat s2 = matOfCols 6 [1, 6, 4, 25, 17, 35] := by rw [hfr]; exact matG2_s2
    simp only [cycOf, gmG2, List.map_cons, List.map_nil]
    rw [h1, h2]
  hB := hB_of laws6 gmG2 uG2 wordsG2 binvG2 hwG2 hBG2
  Mem := MemG2
  hMem := fun γ => by rw [hfr]; exact memG2_matG2 γ
  a := 6
  hd := by norm_num
  leaf := by
    intro w h1 h2 h3 K hK hKP
    obtain ⟨hpow, hsp⟩ := leafG2 w h1 h2 h3 K hK hKP
    refine ⟨hpow, fun h3K h1K => ?_⟩
    have hs := hsp h3K h1K
    intro c hc
    obtain ⟨q, hq, y, hy⟩ := hs c hc
    refine ⟨q, ?_, y, hy⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact List.mem_cons_self

end G2

end CFSG.Quasithin.H13.A6.GR

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank in
theorem factCommG2 :
    FactCommG2 := by
  intro V _ _ hV G L hB4 hrow v hcond hrk S X hS hSv hXL hXv hSX hXO hX1
  obtain ⟨fr, hfr⟩ := GR.G2.exists_frame_g2 hB4 hrow
  exact GR.comm_core fr (GR.G2.modelHypG2 fr hfr) hcond.sq hrk hS hSv hXL hXv hSX hXO hX1

end CFSG.Quasithin.H13.A6
