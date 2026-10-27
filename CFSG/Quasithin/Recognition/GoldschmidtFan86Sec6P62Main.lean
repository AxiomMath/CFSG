module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem r_ne_two (F : FanTree Γ G) (h40 : Fan40 F) (h512b : Fan512b F) (h517a : Fan517a F)
    (hD : LemmaD F) (h517c : Fan517c F) (T : Track Γ G) (hT : InXi T) {z : G}
    (hZ : z ∈ T.line.ZZ) (hz1 : z ≠ 1) {a tL tR : ℤ}
    (hfix : T.line.IsCoreFix z a (a + 2) tL tR)
    (hα : valence Γ (T.line.vert (a + 1)) = 5) (hz : z ∈ Cinv G (T.line.vert (a + 1)))
    (hl : a - tL = 2) : False := by
  obtain ⟨L, hLz, H⟩ := exists_labHyp F h40 h512b h517a hD h517c T hT a hZ hz1 hfix.core hα hz
  set ℓ := T.line with hℓ
  have hd1 : Γ.dist (ℓ.vert (a + 1)) (ℓ.vert (a - 1)) = 2 := by
    rw [dist_comm, Line.dist_eq F.isTree ℓ (by omega)]
    omega
  have hd2 : Γ.dist (ℓ.vert (a + 1)) (ℓ.vert (a + 1 + 2)) = 2 := by
    rw [Line.dist_eq F.isTree ℓ (by omega)]
    omega
  have hbr : Br Γ (ℓ.vert (a + 1)) (ℓ.vert a) (ℓ.vert (a - 1)) := by
    refine ⟨(ℓ.adj a).symm, ℓ.adj_pred a, fun e => ?_⟩
    have := ℓ.nb (a - 1)
    rw [show a - 1 + 2 = a + 1 by omega] at this
    exact this e
  have hτα : T.τ • ℓ.vert (a + 1) = ℓ.vert (a + 1 + 2) := T.trans (a + 1)
  have hl₂ : L.z (ℓ.vert (a + 1 + 2)) = T.τ * z * T.τ⁻¹ := by
    rw [← hτα, L.equivariant T.τ _ hα, hLz]
  have hmove : L.z (ℓ.vert (a + 1 + 2)) • ℓ.vert (a - 1) ≠ ℓ.vert (a - 1) := by
    rw [hl₂, mul_smul, mul_smul]
    have h3 : T.τ⁻¹ • ℓ.vert (a - 1) = ℓ.vert (a - 3) := by
      rw [inv_smul_eq_iff, T.trans, show a - 3 + 2 = a - 1 by omega]
    rw [h3]
    intro e
    have hne : z • ℓ.vert (a - 3) ≠ ℓ.vert (a - 3) := by
      intro hf
      have := (hfix.fix (a - 3)).1 hf
      omega
    apply hne
    have e' : T.τ • (z • ℓ.vert (a - 3)) = T.τ • ℓ.vert (a - 3) := by
      rw [e, T.trans, show a - 3 + 2 = a - 1 by omega]
    exact MulAction.injective T.τ e'
  have hnc : NC L (ℓ.vert (a - 1)) (ℓ.vert (a + 1 + 2)) :=
    (nc_iff F H hα hbr hd2).2 hmove
  exact noncomm_false F H h40 hα ⟨_, _, hd1, hd2, hnc⟩

end P62

theorem fan_6_2 (F : FanTree Γ G) (h519 : Fan519 F) (h53a : Fan53a F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) (h61 : Fan61 F) (hD : LemmaD F)
    (h517a : Fan517a F) (h517c : Fan517c F) : Fan62 F := by
  intro h40' T hT z hz hz1
  obtain ⟨hex, hall⟩ := h519 h40' T hT z hz hz1
  refine And.intro hex fun a b tL tR hfix => ?_
  obtain ⟨hba, hrl, hr3⟩ := hall a b tL tR hfix
  obtain ⟨hr1, -, h5r, -⟩ := h53a h40' T.line z a b tL tR hz hfix
  have hb : b = a + 2 := by omega
  subst hb
  have hcin : z ∈ Cinv G (T.line.vert (a + 1)) := h512cen h40' T z a hT hz hz1 hfix.core
  have hv5 : valence Γ (T.line.vert (a + 1)) = 5 := by
    have h1 := h61 h40' _ z hcin
    have h2 := F.valence (T.line.vert (a + 1))
    change ¬ Nat.card _ = 3 at h1
    change valence Γ _ = 5
    unfold valence
    omega
  have hr2 : 2 ≤ tR - (a + 2) := by
    by_contra hlt
    have htR : tR = a + 1 + 2 := by omega
    have h1 := T.line.valence_add_two F (a + 1)
    rw [← htR, hv5] at h1
    have := h5r (by rw [h1]; omega)
    omega
  have hne : tR - (a + 2) ≠ 2 := fun h =>
    P62.r_ne_two F h40' h512b h517a hD h517c T hT hz hz1 hfix hv5 hcin (by omega)
  omega

end CFSG.Quasithin.Fan86
