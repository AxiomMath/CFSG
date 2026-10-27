module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Lab
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Ctx (F : FanTree Γ G) (T : Track Γ G) (z : G) (a r : ℤ) : Prop where
  val : valence Γ (T.line.vert (a + 1)) = 5
  cinv : z ∈ Cinv G (T.line.vert (a + 1))
  ball : z ∈ ballStab Γ G 2 (T.line.vert (a + 1))
  f2 : F2At Γ z (T.line.vert (a + 1))
  fix : ∀ m i : ℤ, i ∈ T.line.fixIdx (lab T z m) ↔ a - r + 2 * m ≤ i ∧ i ≤ a + 2 + r + 2 * m
  b513 : ∀ (a' d : ℤ), d.natAbs ≤ 4 → ∀ x ∈ MulAction.stabilizer G (T.line.vert (a' + d)),
    x ∉ MulAction.stabilizer G (T.line.vert a') → ∀ w ∈ Cinv G (T.line.vert a'), x * w ≠ w * x

theorem mkCtx (F : FanTree Γ G) (h513b : Fan513b F) (h510 : Fan510 F)
    (h511 : Fan511 F) (h512cen : Fan512cen F) (h512b : Fan512b F) (h40 : Fan40 F)
    (T : Track Γ G) (z : G) (a tL tR : ℤ) (hXi : InXi T) (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1)
    (hc : T.line.IsCoreFix z a (a + 2) tL tR) (hval : valence Γ (T.line.vert (a + 1)) ≠ 3)
    (hr : 5 ≤ tR - (a + 2)) :
    (∀ T' : Track Γ G, ¬ Xi 1 T') ∧ tL = a - (tR - (a + 2)) ∧
      Ctx F T z a (tR - (a + 2)) := by
  obtain ⟨i, hi⟩ := hXi
  have hi1 : i ≠ 1 := by
    rintro rfl
    have := ((h510 h40 T hi z hz hz1).2 a (a + 2) tL tR hc).2.2
    omega
  have hXi1 : ∀ T' : Track Γ G, ¬ Xi 1 T' := by
    intro T' hT'
    have hi2 : 2 ≤ i := by
      rcases i with _ | _ | n
      · exact hi.1.elim
      · exact absurd rfl hi1
      · omega
    exact hi.2 1 le_rfl (by omega) ⟨T', hT'⟩
  have hrl : tR - (a + 2) = a - tL :=
    ((h511 h40 i T hi1 hi z hz hz1).2 a (a + 2) tL tR hc).2
  have hv5 : valence Γ (T.line.vert (a + 1)) = 5 := by
    have h := F.valence (T.line.vert (a + 1))
    have h' : Nat.card (Γ.neighborSet (T.line.vert (a + 1))) ≠ 3 := hval
    rcases h with h | h
    · exact absurd h h'
    · exact h
  have hcinv := h512cen h40 T z a ⟨i, hi⟩ hz hz1 hc.core
  have hb := h512b h40 T z a ⟨i, hi⟩ hz hz1 hc.core
  refine ⟨hXi1, by omega, ?_⟩
  exact
    { val := hv5
      cinv := hcinv
      ball := hb.1
      f2 := hb.2
      fix := fun m j => by
        rw [mem_fixIdx_lab, hc.fix]
        omega
      b513 := fun a' d hd x hx hxa w hw =>
        h513b h40 hXi1 T ⟨i, hi⟩ a' d hd x hx hxa w hw }

theorem lab_eq_Lb {F : FanTree Γ G} {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r)
    (m : ℤ) : lab T z m = Lb z (T.line.vert (a + 1)) (T.line.vert (a + 1 + 2 * m)) := by
  rw [Lb_eq C.cinv (g := T.τ ^ m) (T.zpow_smul_vert m (a + 1))]
  simp [lab, zpow_neg]

theorem Lb_mem_ballStab (F : FanTree Γ G) {z : G} {α u : V} (hz : z ∈ Cinv G α)
    (hb : z ∈ ballStab Γ G 2 α) (hu : ∃ g : G, g • α = u) :
    Lb z α u ∈ ballStab Γ G 2 u := by
  obtain ⟨g, rfl⟩ := hu
  rw [Lb_eq hz rfl]
  refine mem_ballStab.2 fun w hw => ?_
  have hd : Γ.dist α (g⁻¹ • w) ≤ 2 := by
    have := Fan86.dist_smul F g⁻¹ (g • α) w
    rw [inv_smul_smul] at this
    omega
  have h1 := mem_ballStab.1 hb _ hd
  simp only [mul_smul, h1, smul_inv_smul]

end P515

end CFSG.Quasithin.Fan86
