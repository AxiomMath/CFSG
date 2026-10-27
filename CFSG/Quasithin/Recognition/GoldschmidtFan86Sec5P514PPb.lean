module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514PP

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem even_sub_of_val5 (F : FanTree Γ G) (ℓ : Line Γ) {i j : ℤ}
    (hi : valence Γ (ℓ.vert i) = 5) (hj : valence Γ (ℓ.vert j) = 5) : Even (j - i) := by
  by_contra hodd
  obtain ⟨n, hn⟩ : ∃ n : ℤ, j = i + 2 * n + 1 := ⟨(j - i - 1) / 2, by
    rw [Int.not_even_iff_odd] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega⟩
  have h1 := valence_vert_add_two_mul F ℓ (i + 1) n
  have h2 : valence Γ (ℓ.vert (i + 1)) ≠ valence Γ (ℓ.vert i) :=
    fun h => F.alternating _ _ (ℓ.adj i) h.symm
  rw [show i + 1 + 2 * n = j by omega] at h1
  rw [hj] at h1
  exact h2 (h1.symm.trans hi.symm)

theorem pp_even (F : FanTree Γ G) (h40 : Fan40 F) (h53c : Fan53c F) (h54 : Fan54 F)
    (h55b : Fan55b F) (T : Track Γ G) (hT : T.fixer = ⊥) {w w' : G}
    {a b tL tR a' b' tL' tR' : ℤ} (hw : w ∈ T.line.Zc) (hw' : w' ∈ T.line.Zc)
    (hwc : T.line.IsCoreCFix w a b tL tR) (hwc' : T.line.IsCoreCFix w' a' b' tL' tR')
    (hv5 : valence Γ (T.line.vert b) = 5) (hv5' : valence Γ (T.line.vert a') = 5)
    (hrl : tR - b = a' - tL') (hev : Even (tR - b)) : tR - b ≤ 2 := by
  have hpar := even_sub_of_val5 F T.line hv5 hv5'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, tR - a' = 2 * m := by
    obtain ⟨k, hk⟩ := hev
    obtain ⟨l, hl⟩ := hpar
    exact ⟨k - l, by omega⟩
  have hv : valence Γ (T.line.vert (a' + 2 * m)) = 5 := by
    rw [valence_vert_add_two_mul F T.line, hv5']
  refine pp_perfect F h40 h53c h54 h55b T hT hw (lab_mem_Zc F T hw' m)
    (a' := a' + 2 * m) (b' := b' + 2 * m) (tL' := tL' + 2 * m) (tR' := tR' + 2 * m)
    ⟨hwc, isCoreCFix_lab F T m hwc', by omega, by omega⟩ hv5 hv

end P514

end CFSG.Quasithin.Fan86
