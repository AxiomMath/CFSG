module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Pos

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P55

variable {ℓ : Line Γ} {z : G} {a b : ℤ}

theorem fixIdx_of_cen {i : ℤ} (h : z ∈ Cen (ℓ.edgeCirc (G := G) i)) : i ∈ ℓ.fixIdx z :=
  (ℓ.edgeCirc_fix h.1).1

theorem coreC_cen (h : ℓ.IsCoreC z a b) {i : ℤ} (h1 : a ≤ i) (h2 : i < b) :
    z ∈ Cen (ℓ.edgeCirc (G := G) i) := h.2.2.1 i h1 h2

theorem coreC_not_left (h : ℓ.IsCoreC z a b) : z ∉ Cen (ℓ.edgeCirc (G := G) (a - 1)) :=
  fun hc => h.2.2.2.1 ⟨fixIdx_of_cen hc, hc⟩

theorem coreC_not_right (h : ℓ.IsCoreC z a b) : z ∉ Cen (ℓ.edgeCirc (G := G) b) :=
  fun hc => h.2.2.2.2 ⟨fixIdx_of_cen hc, hc⟩

theorem coreC_eq_or_gap {a' b' : ℤ} (h₁ : ℓ.IsCoreC z a b) (h₂ : ℓ.IsCoreC z a' b') :
    (a = a' ∧ b = b') ∨ b < a' ∨ b' < a := by
  have l1 := h₁.1
  have l2 := h₂.1
  rcases lt_trichotomy a a' with h | h | h
  · by_cases hb : a' < b
    · exact absurd (coreC_cen h₁ (i := a' - 1) (by omega) (by omega)) (coreC_not_left h₂)
    · by_cases hbe : b = a'
      · have := coreC_cen h₂ (i := a') le_rfl l2
        rw [← hbe] at this
        exact absurd this (coreC_not_right h₁)
      · right; left; omega
  · subst h
    rcases lt_trichotomy b b' with hb | hb | hb
    · exact absurd (coreC_cen h₂ (i := b) l1.le hb) (coreC_not_right h₁)
    · left; exact ⟨rfl, hb⟩
    · exact absurd (coreC_cen h₁ (i := b') l2.le hb) (coreC_not_right h₂)
  · by_cases hb : a < b'
    · exact absurd (coreC_cen h₂ (i := a - 1) (by omega) (by omega)) (coreC_not_left h₁)
    · by_cases hbe : b' = a
      · have := coreC_cen h₁ (i := a) le_rfl l1
        rw [← hbe] at this
        exact absurd this (coreC_not_right h₂)
      · right; right; omega

theorem zz_le_zc (hz : z ∈ ℓ.ZZ) : z ∈ ℓ.Zc := by
  obtain ⟨hz2, i, hi⟩ := hz
  have hs : z ∈ ℓ.edgeStab (G := G) i := hi.1
  have h0 : z • ℓ.vert i = ℓ.vert i := MulAction.mem_stabilizer_iff.1 hs.1
  have h1 : z • ℓ.vert (i + 1) = ℓ.vert (i + 1) := MulAction.mem_stabilizer_iff.1 hs.2
  refine ⟨hz2, i, mem_edgeCirc_of_fix hz2 h0 h1, fun h hh => ?_⟩
  have hfix := ℓ.edgeCirc_fix hh
  exact hi.2 h ⟨MulAction.mem_stabilizer_iff.2 hfix.1, MulAction.mem_stabilizer_iff.2 hfix.2⟩

end P55

theorem fan55b (F : FanTree Γ G) (h54 : Fan54 F) : Fan55b F := by
  intro h40 T z a b tL tR a' b' hz hd hc
  have hd2 : T.line.IsCoreCFix z a' b' tL tR := ⟨hd.fix, hc⟩
  have c11 := fan55c F h54 h40 T z z a b tL tR a b tL tR hz hz hd hd
  have c12 := fan55c F h54 h40 T z z a b tL tR a' b' tL tR hz hz hd hd2
  have c21 := fan55c F h54 h40 T z z a' b' tL tR a b tL tR hz hz hd2 hd
  have c22 := fan55c F h54 h40 T z z a' b' tL tR a' b' tL tR hz hz hd2 hd2
  rw [abs_le] at c11 c12 c21 c22
  have l1 := P55.cfix_a_lt hd
  have l2 := P55.cfix_a_lt hd2
  rcases P55.coreC_eq_or_gap hd.core hc with ⟨h1, h2⟩ | h | h
  · exact ⟨h1.symm, h2.symm⟩
  · omega
  · omega

end CFSG.Quasithin.Fan86
