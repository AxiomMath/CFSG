module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TF
public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem Q_le_conj_LB (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) :
    Q ≤ conjSubgroup h (LB M Q B) :=
  calc Q = conjSubgroup h Q := (hc.conj_Q_eq hh).symm
    _ ≤ conjSubgroup h (LB M Q B) := Subgroup.map_mono sec39_Q_le_LB

omit [Finite G] in
theorem le_normalizer_of_forall {T D : Subgroup G} (h : ∀ l ∈ T, ∀ k ∈ D, l * k * l⁻¹ ∈ D) :
    T ≤ Subgroup.normalizer (D : Set G) := fun l hl => by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h l hl k, fun hk => ?_⟩
  have := h l⁻¹ (T.inv_mem hl) _ hk
  rwa [show l⁻¹ * (l * k * l⁻¹) * l⁻¹⁻¹ = k by group] at this

theorem Xhat_le_normalizer_inf (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) :
    Xhat M Q B h ≤
      Subgroup.normalizer ((LB M Q B ⊓ conjSubgroup h (LB M Q B) : Subgroup G) : Set G) := by
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hQH : Q ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) :=
    le_inf sec39_Q_le_LB (Q_le_conj_LB hc hh)
  have hcommL' : ⁅conjSubgroup h (LB M Q B), conjSubgroup h (LB M Q B)⁆ ≤ Q := by
    have := hc'.commutator_LB_le_Q
    rwa [hLconj] at this
  refine sup_le (le_normalizer_of_forall fun l hl k hk => ?_)
    (le_normalizer_of_forall fun l hl k hk => ?_)
  · have e : l * k * l⁻¹ = ⁅l, k⁆ * k := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _
      (hQH (hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hl hk.1))) hk
  · have e : l * k * l⁻¹ = ⁅l, k⁆ * k := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _
      (hQH (hcommL' (Subgroup.commutator_mem_commutator hl hk.2))) hk

theorem conj_mem_inf_of_mem_Xhat (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) {g : G}
    (hg : g ∈ Xhat M Q B h) {k : G} (hk : k ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) :
    g * k * g⁻¹ ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B) :=
  (Subgroup.mem_normalizer_iff.mp (Xhat_le_normalizer_inf hc hh hg) k).mp hk

theorem conjSubgroup_inf_eq_of_mem_Xhat (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) {g : G}
    (hg : g ∈ Xhat M Q B h) :
    conjSubgroup g (LB M Q B ⊓ conjSubgroup h (LB M Q B)) =
      LB M Q B ⊓ conjSubgroup h (LB M Q B) :=
  conjSubgroup_eq_self_iff.mpr (Xhat_le_normalizer_inf hc hh hg)

theorem not_conj_le_normalizer (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M)
    (hne : LB M Q B ≠ conjSubgroup h (LB M Q B)) :
    ¬ conjSubgroup h (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) := by
  intro hle
  have := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).1 h hh fun x hx => hle hx
  exact hne this.symm

theorem exists_swap_of_line (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M)
    (hne : LB M Q B ≠ conjSubgroup h (LB M Q B)) (hline : LineGeom M Q Z B h) :
    ∃ w ∈ Xhat M Q B h, conjSubgroup w (LB M Q B) = conjSubgroup h (LB M Q B) := by
  obtain ⟨g, hgL', hgN⟩ := SetLike.not_le_iff_exists.mp (not_conj_le_normalizer h34 hs hh hne)
  have hgL : conjSubgroup g (LB M Q B) ≠ LB M Q B := fun e =>
    hgN (conjSubgroup_eq_self_iff.mp e)
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hgX : g ∈ LB M Q B ⊔ LB M Q (conjSubgroup h B) := by
    rw [hLconj]
    exact (le_sup_right : conjSubgroup h (LB M Q B) ≤ LB M Q B ⊔ conjSubgroup h (LB M Q B)) hgL'
  rcases line_orbit_of_geom hc hh hline g hgX with h1 | ⟨ε, hε, h2⟩
  · exact absurd h1 hgL
  · rw [hLconj] at h2
    refine ⟨ε⁻¹ * g, ?_, ?_⟩
    · have hεX : ε ∈ Xhat M Q B h := (le_sup_left : LB M Q B ≤ Xhat M Q B h) hε
      have hgX' : g ∈ Xhat M Q B h := by
        rw [hLconj] at hgX
        exact hgX
      exact (Xhat M Q B h).mul_mem ((Xhat M Q B h).inv_mem hεX) hgX'
    · rw [conjSubgroup_mul, h2, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem inf_conj_LB_eq_H (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) {ε : G}
    (hε : ε ∈ LB M Q B) :
    LB M Q B ⊓ conjSubgroup ε (conjSubgroup h (LB M Q B)) =
      LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
  have hεX : ε ∈ Xhat M Q B h := (le_sup_left : LB M Q B ≤ Xhat M Q B h) hε
  have hLε : conjSubgroup ε (LB M Q B) = LB M Q B := conjSubgroup_eq_self_iff.mpr
    (Subgroup.le_normalizer hε)
  calc LB M Q B ⊓ conjSubgroup ε (conjSubgroup h (LB M Q B))
      = conjSubgroup ε (LB M Q B) ⊓ conjSubgroup ε (conjSubgroup h (LB M Q B)) := by rw [hLε]
    _ = conjSubgroup ε (LB M Q B ⊓ conjSubgroup h (LB M Q B)) := (conjSubgroup_inf _ _ _).symm
    _ = LB M Q B ⊓ conjSubgroup h (LB M Q B) := conjSubgroup_inf_eq_of_mem_Xhat hc hh hεX

theorem inf_conj_inf_eq_H (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M)
    (hne : LB M Q B ≠ conjSubgroup h (LB M Q B)) (hline : LineGeom M Q Z B h) {ε : G}
    (hε : ε ∈ Xhat M Q B h) (hεL : conjSubgroup ε (conjSubgroup h (LB M Q B)) ≠
      conjSubgroup h (LB M Q B)) :
    conjSubgroup h (LB M Q B) ⊓ conjSubgroup ε (conjSubgroup h (LB M Q B)) =
      LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
  obtain ⟨w, hwX, hw⟩ := exists_swap_of_line h34 hs hh hne hline
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  set g : G := w⁻¹ * ε * w with hg
  have hgX : g ∈ Xhat M Q B h :=
    (Xhat M Q B h).mul_mem ((Xhat M Q B h).mul_mem ((Xhat M Q B h).inv_mem hwX) hε) hwX
  have hgX' : g ∈ LB M Q B ⊔ LB M Q (conjSubgroup h B) := by
    rw [hLconj]
    exact hgX
  have hwg : w * g = ε * w := by simp [hg, mul_assoc]
  have hLg : conjSubgroup g (LB M Q B) ≠ LB M Q B := by
    intro e
    apply hεL
    have h1 : conjSubgroup (w * g) (LB M Q B) = conjSubgroup w (LB M Q B) := by
      rw [conjSubgroup_mul, e]
    rw [hwg, conjSubgroup_mul, hw] at h1
    exact h1
  rcases line_orbit_of_geom hc hh hline g hgX' with h1 | ⟨ε', hε', h2⟩
  · exact absurd h1 hLg
  · rw [hLconj] at h2
    have hinf : LB M Q B ⊓ conjSubgroup g (LB M Q B) =
        LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
      rw [h2]
      exact inf_conj_LB_eq_H hc hh hε'
    have hconj1 : conjSubgroup w (LB M Q B ⊓ conjSubgroup g (LB M Q B)) =
        conjSubgroup h (LB M Q B) ⊓ conjSubgroup ε (conjSubgroup h (LB M Q B)) := by
      rw [conjSubgroup_inf, hw, ← conjSubgroup_mul, hwg, conjSubgroup_mul, hw]
    rw [← hconj1, hinf]
    exact conjSubgroup_inf_eq_of_mem_Xhat hc hh hwX

end HS9

end CFSG.RankThree.GF2n.Stroth80
