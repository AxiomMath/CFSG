module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E4
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem E_data (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (h53c : Fan53c F)
    (T : Track Γ G) (hT : T.fixer = ⊥) {z : G} {a r : ℤ} (hr0 : 0 ≤ r)
    (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2))) {w : G} {p q : V}
    (hp : Γ.Adj (T.line.vert (a + 2)) p) (hq : Γ.Adj (T.line.vert (a + 2)) q) (hpq : p ≠ q)
    (hform : w = Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q) (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hcen : w ∈ Cen (T.line.edgeCirc (G := G) (a + 2)))
    (hfixw : ∀ i, a + 2 - r ≤ i → i ≤ a + 2 + r → w • T.line.vert i = T.line.vert i) :
    w ∈ T.line.Zc ∧ ∃ tL tR b : ℤ, (∀ i, i ∈ T.line.fixIdx w ↔ tL ≤ i ∧ i ≤ tR) ∧
      tL ≤ a + 2 - r ∧ a + 2 + r ≤ tR ∧ T.line.IsCoreC w (a + 2) b ∧ (b = a + 3 ∨ b = a + 4) := by
  have hwZ : w ∈ T.line.Zc := ⟨hw2, a + 2, hcen⟩
  have hfx0 : w • T.line.vert (a + 2) = T.line.vert (a + 2) := hfixw (a + 2) (by omega) (by omega)
  obtain ⟨tL, tR, hfix⟩ := exists_fixIdx_interval F T hT hw1 (i₀ := a + 2) hfx0
  have hl : tL ≤ a + 2 - r := ((hfix _).1 (hfixw (a + 2 - r) le_rfl (by omega))).1
  have hr : a + 2 + r ≤ tR := ((hfix _).1 (hfixw (a + 2 + r) (by omega) le_rfl)).2
  obtain ⟨a', b', ha', hb', hcoreW⟩ := exists_isCoreWith T.line
    (P := fun k => w ∈ Cen (T.line.edgeCirc (G := G) k)) hfix
    (fun k hk => ⟨(T.line.edgeCirc_fix hk.1).1, (T.line.edgeCirc_fix hk.1).2⟩) hcen
  have hlen := h53c h40 T.line w a' b' hwZ hcoreW
  have hbl : a' = a + 2 := by
    by_contra hne
    have hcen1 : w ∈ Cen (T.line.edgeCirc (G := G) (a + 1)) :=
      hcoreW.2.2.1 (a + 1) (by omega) (by omega)
    exact not_cen_pred F h40 h51a T C hp hq hpq (by rw [← hform]; exact hcen1)
      (by rw [← hform]; exact hcen)
  subst hbl
  exact ⟨hwZ, tL, tR, b', hfix, hl, hr, hcoreW, by omega⟩

end P514

end CFSG.Quasithin.Fan86
