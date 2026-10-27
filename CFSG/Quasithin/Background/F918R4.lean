module

public import CFSG.Quasithin.Background.F918N0
public import CFSG.Quasithin.Background.F918R0
public import CFSG.Quasithin.Background.F918R2
public import CFSG.Quasithin.Background.F918R3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem d35InspTwo_of_B51 (hB51 : AsB51) : D35InspTwo := by
  intro Y _ _ hY J K K' hhyp hcK hq' hcomm hcK' hcover
  obtain ⟨-, hcases⟩ := (hB51 Y hY J K hhyp).1
  rcases hcases with h1 | h2 | ⟨n, h3⟩ | h4
  · exact d35Two_caseI hY (hcK ▸ h1.1) hcK hq' hcomm
  · obtain ⟨-, n, F, hF, hFin, hFc, I, π, hind, hsup, hreal, -, -⟩ := h2
    have hsup' : ⨆ i, I i = ⊤ := by rw [hsup, hcK]
    have hind' : ∀ i, I i ⊓ ⨆ (j : Fin 2) (_ : j ≠ i), I j = ⊥ := fun i => (hind i).eq_bot
    have hle := d35Two_card_le (by norm_num : 3 ≤ 3) π hcomm I hsup' hind'
      (fun i => Or.inl (hreal i))
    have hinj := pi_injective_of_realizes (by norm_num : 2 ≤ 3) π (Or.inl (hreal 0))
    have hge := d35Two_card_ge (by norm_num : 3 ≤ 3) π (hreal 0).1 hinj hq' hcover
    have hgt := card_stated_gt (d := 3) (m := 4) (F := F) (Or.inl ⟨rfl, rfl⟩)
    simp only [Fintype.card_fin] at hle
    have h1 : Nat.card ↥(StatedSL 3 F) ≤ 3 * Nat.card F ^ 4 :=
      hge.trans (Nat.mul_le_mul_left 3 hle)
    exact absurd hgt (not_lt.mpr h1)
  · obtain ⟨-, hn, π, U₁, U₂, hdir, hr₁, hr₂⟩ := h3
    have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    let I : Fin 2 → Subgroup Y := ![U₁, U₂]
    have hind : iSupIndep I :=
      (iSupIndep_pair (by decide : (0 : Fin 2) ≠ 1) (by decide)).mpr (disjoint_iff.mpr hdir.2)
    have hsup' : ⨆ i, I i = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← hcK, ← hdir.1]
      exact sup_le (le_iSup I 0) (le_iSup I 1)
    have hreal : ∀ i, (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia K (I i) ⊥ π ∨
        (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia K (I i) ⊥ π := by
      intro i
      fin_cases i
      · exact Or.inl hr₁
      · exact Or.inr hr₂
    have hind' : ∀ i, I i ⊓ ⨆ (j : Fin 2) (_ : j ≠ i), I j = ⊥ := fun i => (hind i).eq_bot
    have hle := d35Two_card_le hn3 π hcomm I hsup' hind' hreal
    have hinj := pi_injective_of_realizes (by omega : 2 ≤ n) π (hreal 0)
    have hge := d35Two_card_ge hn3 π hr₁.1 hinj hq' hcover
    have hgt := card_stated_gt (d := n) (m := 4) (F := ZMod 2)
      (Or.inr ⟨by simp, hn, 2, by norm_num, by omega, by norm_num⟩)
    simp only [Fintype.card_fin, Nat.card_zmod] at hle hgt
    have h1 : Nat.card ↥(StatedSL n (ZMod 2)) ≤ n * 2 ^ 4 :=
      hge.trans (Nat.mul_le_mul_left n hle)
    exact absurd hgt (not_lt.mpr h1)
  · obtain ⟨-, n, hn, k, hk1, hkn, I, π, -, hind, hsup, hreal⟩ := h4
    have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    rw [bot_sup_eq, hcK] at hsup
    have hind' : ∀ i, I i ⊓ ⨆ (j : Fin k) (_ : j ≠ i), I j = ⊥ := fun i => by
      simpa only [bot_sup_eq] using hind i
    have hle := d35Two_card_le hn3 π hcomm I hsup hind' (fun i => Or.inl (hreal i))
    have hk0 : 0 < k := hk1
    have hinj := pi_injective_of_realizes (by omega : 2 ≤ n) π (Or.inl (hreal ⟨0, hk0⟩))
    have hge := d35Two_card_ge hn3 π (hreal ⟨0, hk0⟩).1 hinj hq' hcover
    have hgt := card_stated_gt (d := n) (m := k * k) (F := ZMod 2)
      (Or.inr ⟨by simp, hn, k, hk1, hkn, rfl⟩)
    simp only [Fintype.card_fin, Nat.card_zmod] at hle hgt
    have h1 : Nat.card ↥(StatedSL n (ZMod 2)) ≤ n * 2 ^ (k * k) :=
      hge.trans (Nat.mul_le_mul_left n hle)
    exact absurd hgt (not_lt.mpr h1)

end CFSG.Quasithin
