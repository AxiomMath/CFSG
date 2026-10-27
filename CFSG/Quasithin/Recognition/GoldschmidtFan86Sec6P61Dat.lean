module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Cls
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E4

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem E_data1 (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (h53c : Fan53c F)
    (T : Track Γ G) (hZ : ZcFin F) {z : G} {a r : ℤ} (hr0 : 0 ≤ r)
    (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2))) {w : G} {p q : V}
    (hp : Γ.Adj (T.line.vert (a + 2)) p) (hq : Γ.Adj (T.line.vert (a + 2)) q) (hpq : p ≠ q)
    (hform : w = Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q) (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hcen : w ∈ Cen (T.line.edgeCirc (G := G) (a + 2)))
    (hfixw : ∀ i, a + 2 - r ≤ i → i ≤ a + 2 + r → w • T.line.vert i = T.line.vert i) :
    w ∈ T.line.Zc ∧ ∃ tL tR b : ℤ, (∀ i, i ∈ T.line.fixIdx w ↔ tL ≤ i ∧ i ≤ tR) ∧
      tL ≤ a + 2 - r ∧ a + 2 + r ≤ tR ∧ T.line.IsCoreC w (a + 2) b ∧ (b = a + 3 ∨ b = a + 4) := by
  have hwZ : w ∈ T.line.Zc := ⟨hw2, a + 2, hcen⟩
  have hfx0 : w • T.line.vert (a + 2) = T.line.vert (a + 2) := hfixw (a + 2) (by omega) (by omega)
  obtain ⟨tL, tR, hfix⟩ := hZ T w hwZ hw1
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

theorem cls_int1 (r o : ℤ) (_hr : 1 ≤ r) (hodd : r % 2 = 1)
    (tL₁ tR₁ a₁ b₁ tL₂ tR₂ a₂ b₂ : ℤ)
    (hf₁ : tL₁ ≤ o - r ∧ o + r ≤ tR₁) (hf₂ : tL₂ ≤ o - r ∧ o + r ≤ tR₂)
    (hc₁ : (a₁ = o ∧ b₁ = o + 1) ∨ (a₁ = o ∧ b₁ = o + 2))
    (hc₂ : (a₂ = o ∧ b₂ = o + 1) ∨ (a₂ = o ∧ b₂ = o + 2))
    (hc3₁ : -1 ≤ (tR₁ - b₁) - r ∧ (tR₁ - b₁) - r ≤ 1 ∧ -1 ≤ (a₁ - tL₁) - r ∧
      (a₁ - tL₁) - r ≤ 1 ∧ -1 ≤ (tR₁ - b₁) - (a₁ - tL₁) ∧ (tR₁ - b₁) - (a₁ - tL₁) ≤ 1)
    (hc3₂ : -1 ≤ (tR₂ - b₂) - r ∧ (tR₂ - b₂) - r ≤ 1 ∧ -1 ≤ (a₂ - tL₂) - r ∧
      (a₂ - tL₂) - r ≤ 1 ∧ -1 ≤ (tR₂ - b₂) - (a₂ - tL₂) ∧ (tR₂ - b₂) - (a₂ - tL₂) ≤ 1)
    (m₁ i₁ j₁ : ℤ) (hp₁ : (i₁ = 0 ∨ i₁ = 1) ∧ (j₁ = 0 ∨ j₁ = 1) ∧ tR₁ = a₁ + 2 * m₁ - i₁ ∧
      tL₁ + 2 * m₁ = b₁ + j₁)
    (m₂ i₂ j₂ : ℤ) (hp₂ : (i₂ = 0 ∨ i₂ = 1) ∧ (j₂ = 0 ∨ j₂ = 1) ∧ tR₂ = a₂ + 2 * m₂ - i₂ ∧
      tL₂ + 2 * m₂ = b₂ + j₂)
    (hR : (tR₁ < tR₂ → tR₁ = o + r + 2) ∧ (tR₂ < tR₁ → tR₂ = o + r + 2) ∧
      (tR₁ = tR₂ → tR₁ + 1 ≤ o + r + 2))
    (hL : (tL₂ < tL₁ → tL₁ = o - r) ∧ (tL₁ < tL₂ → tL₂ = o - r) ∧
      (tL₁ = tL₂ → o - r ≤ tL₁ - 1)) :
    ((tR₁ = o + r + 3 ∧ b₁ = o + 2) ∨ (tR₂ = o + r + 3 ∧ b₂ = o + 2)) ∧
    ((tL₁ = o - r - 1 ∧ a₁ = o) ∨ (tL₂ = o - r - 1 ∧ a₂ = o)) := by
  obtain ⟨hf₁l, hf₁r⟩ := hf₁
  obtain ⟨hf₂l, hf₂r⟩ := hf₂
  obtain ⟨hi₁, hj₁, hp₁a, hp₁b⟩ := hp₁
  obtain ⟨hi₂, hj₂, hp₂a, hp₂b⟩ := hp₂
  obtain ⟨hR1, hR2, hR3⟩ := hR
  obtain ⟨hL1, hL2, hL3⟩ := hL
  rcases hc₁ with ⟨ha₁, hb₁⟩ | ⟨ha₁, hb₁⟩ <;> rcases hc₂ with ⟨ha₂, hb₂⟩ | ⟨ha₂, hb₂⟩ <;>
    rcases hi₁ with rfl | rfl <;> rcases hj₁ with rfl | rfl <;>
    rcases hi₂ with rfl | rfl <;> rcases hj₂ with rfl | rfl <;> omega

end P61

end CFSG.Quasithin.Fan86
