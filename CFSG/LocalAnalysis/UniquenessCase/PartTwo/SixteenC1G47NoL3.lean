module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Abs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47StarCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c1_G47_noL3_abs {Hs : Type} [Group Hs] [Finite Hs] {Xs Ys Vs B : Subgroup Hs}
    (hO2 : CFSG.pCore 2 Hs = ⊥) (hY : Ys.Normal) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5)
    (hL3 : IsL3Five ↥Ys) (hHs : ∀ h : Hs, ∃ y ∈ Ys, ∃ b ∈ B, h = y * b)
    (hVB : ∀ b ∈ B, ∀ v ∈ Vs, b * v * b⁻¹ ∈ Vs) (hV2 : IsPGroup 2 Vs)
    (hV2' : ∀ v ∈ Vs, v * v = 1) (hXV : ∀ x ∈ Xs, ∀ v ∈ Vs, x * v * x⁻¹ ∈ Vs)
    (hcard : Nat.card ↥Vs = 2)
    (htr : ∀ v ∈ Vs, v ≠ 1 → ∀ a b : Hs,
      orderOf (a * v * a⁻¹ * (b * v * b⁻¹)) ∈ ({1, 2, 3, 5, 17} : Set ℕ)) : False := by
  classical
  have hVX := s16c1_G47_comm_of_card_le_four hX hXV (by omega)
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((Subgroup.one_lt_card_iff_ne_bot Vs).1 (by omega))
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvY : ¬ ∀ y ∈ Ys, v * y = y * v := fun hc =>
    hv1' (s16c1_G47_cent_trivial hO2 hY hHs hVB hV2 v hv hc)
  obtain ⟨a, -, b, -, hord⟩ := s16c1_G47_L3five_transposition hY hL3 hXY hX (hV2' v hv)
    (hVX v hv) hvY
  have h := htr v hv hv1' a b
  rw [hord] at h
  simp at h

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_noL3 {D : Data G} {L V : Subgroup G} {z : G}
    (hSt : G47Star D (centralizer ({z} : Set G)) L V z) (h46 : Concl1646 L z)
    (h47 : Concl1647 V z) :
    ¬ IsL3Five ↥(starImg (centralizer ({z} : Set G)) (yGen L z)) := fun hL3 =>
  s16c1_G47_noL3_abs hSt.pCore_bot hSt.normal_Y hSt.le_XY h46.2.2.1 hL3 hSt.split hSt.conj_B
    hSt.pgroup hSt.sq hSt.conj_X h47.1 h47.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
