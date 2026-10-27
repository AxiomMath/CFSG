module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Heis
public import CFSG.RankThree.ThinCatalog.SporadicJ1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankMat
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix

public section

namespace CFSG.Quasithin.SBd19F

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique CFSG.RankThree.ThinCatalog
open CFSG.SectionRank CFSG.QuasithinUnique.Lin2.OddRank.Mat
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

theorem hasElemAb_nine_of_perm_pair {n : ℕ} {H : Subgroup (Perm (Fin n))} {x y : Perm (Fin n)}
    (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hc : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) (hyx2 : y ≠ x ^ 2) :
    Id2519.HasElemAb 3 9 ↥H := by
  refine hasElemAb_nine_of_perm_data (x := (⟨x, hxH⟩ : ↥H)) (y := (⟨y, hyH⟩ : ↥H))
    (Subtype.ext (by simpa using hx)) (Subtype.ext (by simpa using hy))
    (Subtype.ext (by simpa using hc)) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h)) (fun h => hyx (congrArg Subtype.val h))
    (fun h => hyx2 (by simpa using congrArg Subtype.val h))

@[expose] def x11 : Perm (Fin 11) :=
  m11gA * m11gB⁻¹ * m11gA * m11gB * m11gA * m11gB * m11gB

@[expose] def y11 : Perm (Fin 11) :=
  m11gB * m11gA * m11gB⁻¹ * m11gA * m11gB * m11gA * m11gB

theorem x11_pow_three : x11 ^ 3 = 1 := by decide +kernel

theorem y11_pow_three : y11 ^ 3 = 1 := by decide +kernel

theorem x11_comm_y11 : x11 * y11 = y11 * x11 := by decide +kernel

theorem x11_ne_one : x11 ≠ 1 := by decide +kernel

theorem y11_ne_one : y11 ≠ 1 := by decide +kernel

theorem y11_ne_x11 : y11 ≠ x11 := by decide +kernel

theorem y11_ne_x11_sq : y11 ≠ x11 ^ 2 := by decide +kernel

theorem hasElemAb_nine_M11 : Id2519.HasElemAb 3 9 (NativeSporadic.Carrier .M11) :=
  hasElemAb_nine_of_perm_pair
    (m11a * m11b⁻¹ * m11a * m11b * m11a * m11b * m11b : NativeSporadic.M11).2
    (m11b * m11a * m11b⁻¹ * m11a * m11b * m11a * m11b : NativeSporadic.M11).2
    x11_pow_three y11_pow_three x11_comm_y11 x11_ne_one y11_ne_one y11_ne_x11 y11_ne_x11_sq

theorem outThreeOrElemNine_of_alt {S : Type} [Group S] {n : ℕ} (h5 : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) : OutThreeOrElemNine S := by
  rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | h6
  · exact Or.inl (outThreeBound_of_card_outer_dvd_two
      (outer_card_dvd_two_of_equiv_outside_six (Or.inl rfl) e))
  · exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm
      ⟨sylowThreeAlt h6, isElemAbelian_sylowThreeAlt h6, by rw [card_sylowThreeAlt h6]; norm_num⟩)

theorem hasElemAb_nine_of_two_le_pRank {G : Type} [Group G] [Finite G]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : Id2519.HasElemAb 3 9 G := by
  obtain ⟨E, -, hE, hEc⟩ := CFSG.RankThree.PartTwo.Sec5.exists_elemAbelian_le_of_le_pRank
    Nat.prime_three (show 2 ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup G) from h)
  exact ⟨E, hE, by rw [hEc]; norm_num⟩

section Sporadic


theorem outThreeOrElemNine_of_sporadic {S : Type} [Group S] [Finite S]
    (h : ∃ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
        s = .HS ∨ s = .He ∨ s = .Ru) ∧ Nonempty (S ≃* NativeSporadic.Carrier s)) :
    OutThreeOrElemNine S := by
  have h3p : Nat.Prime 3 := Nat.prime_three
  obtain ⟨s, hs, ⟨e⟩⟩ := h
  have hfinC : Finite (NativeSporadic.Carrier s) := Finite.of_equiv S e.toEquiv
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm hasElemAb_nine_M11)
  · have : Finite NativeSporadic.M12 := hfinC
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := M12_sylow3_cubic_witness
    exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_of_two_le_pRank
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)))
  · exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm hasElemAb_nine_M22)
  · exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm hasElemAb_nine_M23)
  · have : Finite NativeSporadic.M24 := hfinC
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := M24_sylow3_cubic_witness
    exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_of_two_le_pRank
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)))
  · have hcard := (CFSG.Sporadic.Schreier.at_j1_schreier).1
    exact Or.inl ((outThreeBound_of_card_outer_dvd_two (by rw [hcard]; exact one_dvd 2)).of_mulEquiv
      (show S ≃* NativeSporadic.J1 from e))
  · have : Finite NativeSporadic.J2 := hfinC
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := J2_sylow3_cubic_witness
    exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_of_two_le_pRank
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)))
  · have : Finite NativeSporadic.J4 := hfinC
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := J4_sylow3_cubic_witness
    exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_of_two_le_pRank
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)))
  · have : Finite NativeSporadic.HS := hfinC
    obtain ⟨x, y, -, hx, hy, hxy, hQ, -⟩ := HS_sylow3_square_witness
    exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_of_two_le_pRank
      (two_le_pRank_of_square_witness h3p hx hy hxy hQ)))
  · have : Finite NativeSporadic.He := hfinC
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := He_sylow3_cubic_witness
    exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_of_two_le_pRank
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)))
  · have : Finite NativeSporadic.Ru := hfinC
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := Ru_sylow3_cubic_witness
    exact Or.inr (Id2519.HasElemAb.of_mulEquiv e.symm (hasElemAb_nine_of_two_le_pRank
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)))

end Sporadic

end CFSG.Quasithin.SBd19F
