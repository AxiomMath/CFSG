module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Set
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513bAux
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Seven
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Rev

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_5_18_core (F : FanTree Γ G)
    (hb2 : ∀ (L : ZLab Γ G) (T : Track Γ G) (a : ℤ), P518.B2Set F L T a →
      P518.zA L T a 0 • P518.zA L T a 5 • P518.xv T a 1 ≠ P518.zA L T a 5 • P518.xv T a 1)
    (h33 : Fan33 F) (h36 : Fan36 F)
    (h481 : Fan40 F → ∀ T₀ : Track Γ G, T₀.fixer ≠ ⊥ → ∃ T' : Track Γ G, InPiStar T')
    (h510 : Fan510 F) (h511 : Fan511 F) (h512cen : Fan512cen F) (h512b : Fan512b F)
    (h512c : Fan512c F) (h515a : Fan515a F) (h516 : Fan516 F) (h517a : Fan517a F)
    (h517c : Fan517c F) (hD : LemmaD F) : Fan518 F := by
  intro h40 T z a tL tR hXi hz hz1 hc hval
  by_contra hlt
  push Not at hlt
  have hv5 : valence Γ (T.line.vert (a + 1)) = 5 := by
    rcases F.valence (T.line.vert (a + 1)) with h | h
    · exact absurd h hval
    · exact h
  obtain ⟨i, hi⟩ := hXi
  have hi1 : i ≠ 1 := fun h => by
    subst h
    have := ((h510 h40 T hi z hz hz1).2 a (a + 2) tL tR hc).2.2
    omega
  have hXi1 : ∀ T' : Track Γ G, ¬ Xi 1 T' := by
    intro T' hT'
    rcases Nat.lt_or_ge 1 i with h | h
    · exact hi.2 1 le_rfl h ⟨T', hT'⟩
    · have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · exact hi.1.elim
      · exact hi1 rfl
  have hrl : tR - (a + 2) = a - tL := ((h511 h40 i T hi1 hi z hz hz1).2 a (a + 2) tL tR hc).2
  have hodd : Odd (tR - (a + 2)) := by
    rcases Int.even_or_odd (tR - (a + 2)) with he | ho
    · have := h512c h40 T ⟨i, hi⟩ z hz hz1 a (a + 2) tL tR hc he
      omega
    · exact ho
  have hle5 := h516 h40 T z a tL tR ⟨i, hi⟩ hz hz1 hc hval
  have hr5 : tR - (a + 2) = 5 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hT : ∀ T' : Track Γ G, T'.fixer = ⊥ := fun T' => by
    by_contra h
    obtain ⟨T'', hT''⟩ := h481 h40 T' h
    exact hXi1 T'' hT''
  have hcinv := h512cen h40 T z a ⟨i, hi⟩ hz hz1 hc.core
  obtain ⟨L, hLz, hLH⟩ := P62.exists_labHyp F h40 h512b h517a hD h517c T ⟨i, hi⟩ a hz hz1 hc.core
    hv5 hcinv
  have hLz' : L.z (P518.xv T a 0) = z := by simpa [P518.xv] using hLz
  have C : P518.Ctx L T a := ⟨by simpa [P518.xv] using hv5, fun j => by
    rw [hLz']
    exact (hc.fix (a + 1 + j)).trans (by omega)⟩
  have h2 : L.z (P518.xv T a 2) ∈ ballStab Γ G 2 (P518.xv T a 0) := by
    have h1 := (h515a h40 T z a tL tR ⟨i, hi⟩ hz hz1 hc hval (by omega) 0 1 (by norm_num)
      (by omega)).1
    have e : L.z (P518.xv T a 2) = T.τ ^ (0 + 1 : ℤ) * z * T.τ ^ (-(0 + 1 : ℤ)) := by
      have := P518.zA_eq C 1
      rw [hLz'] at this
      simpa [P518.zA] using this
    rw [e]
    simpa [P518.xv] using h1
  have hlab : P518.Lab18 L := ⟨hLH, P518.z4_transport F h40 L (by simpa using C.val_even F 1)
    (P518.xv_dist_two' F T a 0) h2⟩
  have hn4 : ¬ LineSingLe Γ G T.line 4 :=
    Sec3Seven.not_lineSingLe_four F h40 h36 T (hasLenTwoReflection_of_inXi ⟨i, hi⟩)
  have hn4' : ¬ LineSingLe Γ G T.rev.line 4 := fun h => hn4 (lineSingLe_of_rev h)
  have S : P518.B2Set F L T a := ⟨h40, h33, hn4, hlab, C⟩
  have S' : P518.B2Set F L T.rev (-a - 12) := ⟨h40, h33, hn4', hlab, C.rev F⟩
  have hb2a := hb2 L T a S
  have hb2' : P518.zA L T a 5 • P518.zA L T a 0 • P518.xv T a 9 ≠
      P518.zA L T a 0 • P518.xv T a 9 := by
    simpa [P518.zA_rev, P518.xv_rev] using hb2 L T.rev (-a - 12) S'
  exact P518.endgame F (fun L T a E => P518.b3 F h40 E) hlab C (hT T) hb2a hb2'

end CFSG.Quasithin.Fan86
