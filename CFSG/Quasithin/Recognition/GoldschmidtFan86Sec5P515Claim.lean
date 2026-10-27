module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem claim (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) (m t : ℤ)
    (ht : t = 1 ∨ t = 2) {k : G}
    (hk0 : k • T.line.vert (a + 1 + 2 * m) = T.line.vert (a + 1 + 2 * m))
    (hk2 : k • T.line.vert (a + 1 + 2 * (m + 1)) = T.line.vert (a + 1 + 2 * (m + 1))) {l : V}
    (hl : ∃ g : G, g • T.line.vert (a + 1) = l)
    (hzl : Lb z (T.line.vert (a + 1)) l • T.line.vert (a + 1 + 2 * m) =
      T.line.vert (a + 1 + 2 * m))
    (hxi : Lb z (T.line.vert (a + 1)) (k • T.line.vert (a + 1 + 2 * (m + t))) • l = l) :
    Lb z (T.line.vert (a + 1)) l • T.line.vert (a + 1 + 2 * (m + 1)) =
      T.line.vert (a + 1 + 2 * (m + 1)) := by
  set α := T.line.vert (a + 1) with hα
  set u := T.line.vert (a + 1 + 2 * (m + t)) with hu
  have hu1 : ∃ g : G, g • α = u := ⟨T.τ ^ (m + t), T.zpow_smul_vert (m + t) (a + 1)⟩
  set zl := Lb z α l with hzl_def
  have hzlc : zl ∈ Cinv G l := Lb_cinv C.cinv hl
  have hzu : Lb z α u ∈ Cinv G u := Lb_cinv C.cinv hu1
  have hconj : Lb z α (k • u) = k * Lb z α u * k⁻¹ := (Lb_conj C.cinv hu1 k).symm
  have hcomm : Lb z α (k • u) * zl = zl * Lb z α (k • u) :=
    hzlc.2.2.2 _ (MulAction.mem_stabilizer_iff.2 hxi)
  set x' := k⁻¹ * zl * k with hx'
  have hk0' : k⁻¹ • T.line.vert (a + 1 + 2 * m) = T.line.vert (a + 1 + 2 * m) := by
    rw [inv_smul_eq_iff]
    exact hk0.symm
  have hk2' : k⁻¹ • T.line.vert (a + 1 + 2 * (m + 1)) = T.line.vert (a + 1 + 2 * (m + 1)) := by
    rw [inv_smul_eq_iff]
    exact hk2.symm
  have hx'e : x' • T.line.vert (a + 1 + 2 * m) = T.line.vert (a + 1 + 2 * m) := by
    simp only [hx', mul_smul, hk0, hzl, hk0']
  have hx'c : x' * Lb z α u = Lb z α u * x' := by
    have h1 : Lb z α u = k⁻¹ * Lb z α (k • u) * k := by rw [hconj]; group
    rw [h1]
    calc k⁻¹ * zl * k * (k⁻¹ * Lb z α (k • u) * k)
        = k⁻¹ * (zl * Lb z α (k • u)) * k := by group
      _ = k⁻¹ * (Lb z α (k • u) * zl) * k := by rw [hcomm]
      _ = k⁻¹ * Lb z α (k • u) * k * (k⁻¹ * zl * k) := by group
  have hxu : x' • u = u := by
    by_contra hne
    have hb := C.b513 (a + 1 + 2 * (m + t)) (-(2 * t)) (by omega) x' ?_ ?_ (Lb z α u) hzu
    · exact hb hx'c
    · rw [MulAction.mem_stabilizer_iff, show a + 1 + 2 * (m + t) + -(2 * t) = a + 1 + 2 * m by
        ring]
      exact hx'e
    · exact fun h => hne (MulAction.mem_stabilizer_iff.1 h)
  have hx'2 : x' • T.line.vert (a + 1 + 2 * (m + 1)) = T.line.vert (a + 1 + 2 * (m + 1)) :=
    Line.fixes_between F.isTree F.adj_smul T.line (by omega) (by omega) hx'e hxu
  have : zl • T.line.vert (a + 1 + 2 * (m + 1)) = T.line.vert (a + 1 + 2 * (m + 1)) := by
    have h3 : zl = k * x' * k⁻¹ := by simp only [hx']; group
    rw [h3, mul_smul, mul_smul, hk2', hx'2, hk2]
  exact this

theorem exists_swapper (F : FanTree Γ G) (h40 : Fan40 F) (ℓ : Line Γ) (c : ℤ) {ξ : V}
    (hv3 : valence Γ (ℓ.vert (c + 3)) = 3) (hξ : Γ.Adj (ℓ.vert (c + 3)) ξ)
    (h2 : ξ ≠ ℓ.vert (c + 2)) (h4 : ξ ≠ ℓ.vert (c + 4)) :
    ∃ h : G, h • ℓ.vert c = ℓ.vert c ∧ h • ℓ.vert (c + 2) = ℓ.vert (c + 2) ∧
      h • ℓ.vert (c + 3) = ℓ.vert (c + 3) ∧ h • ℓ.vert (c + 4) = ξ := by
  have hns : ¬ RightSingular Γ G (ℓ.arc c 3).vert 0 3 := fun h =>
    h40 3 (by norm_num) (by norm_num) ⟨ℓ.arc c 3, h⟩
  obtain ⟨X, hX, hX4⟩ := ℓ.exists_fixer_right' c 3 0 3 (by norm_num) hns
  have f0 : X • ℓ.vert c = ℓ.vert c := by simpa using hX c (by norm_num) (by norm_num)
  have f2 : X • ℓ.vert (c + 2) = ℓ.vert (c + 2) := hX _ (by norm_num) (by norm_num)
  have f3 : X • ℓ.vert (c + 3) = ℓ.vert (c + 3) := hX _ (by norm_num) (by norm_num)
  have hX4' : X • ℓ.vert (c + 4) ≠ ℓ.vert (c + 4) := by
    simpa [show c + 3 + 1 = c + 4 by ring] using hX4
  have a34 : Γ.Adj (ℓ.vert (c + 3)) (ℓ.vert (c + 4)) := by
    have := ℓ.adj (c + 3)
    rwa [show c + 3 + 1 = c + 4 by ring] at this
  have a32 : Γ.Adj (ℓ.vert (c + 3)) (ℓ.vert (c + 2)) := by
    have := (ℓ.adj (c + 2)).symm
    rwa [show c + 2 + 1 = c + 3 by ring] at this
  have n24 : ℓ.vert (c + 2) ≠ ℓ.vert (c + 4) := by
    have := ℓ.nb (c + 2)
    rwa [show c + 2 + 2 = c + 4 by ring] at this
  have hadj : Γ.Adj (ℓ.vert (c + 3)) (X • ℓ.vert (c + 4)) := by
    have := (F.adj_smul X _ _).2 a34
    rwa [f3] at this
  rcases P58.eq_of_three hv3 a32 a34 hξ n24 (Ne.symm h2) (Ne.symm h4) hadj with e | e | e
  · exact absurd (MulAction.injective X (show X • ℓ.vert (c + 4) = X • ℓ.vert (c + 2) by
      rw [e, f2])) (fun h => n24 h.symm)
  · exact absurd e hX4'
  · exact ⟨X, f0, f2, f3, e⟩

end P515

end CFSG.Quasithin.Fan86
