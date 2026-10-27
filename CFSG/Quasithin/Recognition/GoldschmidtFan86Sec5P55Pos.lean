module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55H

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P55

theorem isShift_zpow (T : Track Γ G) (m : ℤ) : IsShift T.line (T.τ ^ m) (2 * m) :=
  fun i => T.zpow_smul_vert m i

theorem translate_data (F : FanTree Γ G) (T : Track Γ G) (m : ℤ) {z' : G} {a' b' tL' tR' : ℤ}
    (hz' : z' ∈ T.line.Zc) (hd' : T.line.IsCoreCFix z' a' b' tL' tR') :
    T.τ ^ m * z' * T.τ ^ (-m) ∈ T.line.Zc ∧
      T.line.IsCoreCFix (T.τ ^ m * z' * T.τ ^ (-m)) (a' + 2 * m) (b' + 2 * m) (tL' + 2 * m)
        (tR' + 2 * m) := by
  rw [zpow_neg]
  exact ⟨IsShift.zc F (isShift_zpow T m) hz', IsShift.isCoreCFix F (isShift_zpow T m) hd'⟩

theorem obs (F : FanTree Γ G) (h54 : Fan54 F) (h40 : Fan40 F) (T : Track Γ G) {z z' : G}
    {a b tL tR a' b' tL' tR' : ℤ} (hz : z ∈ T.line.Zc) (hz' : z' ∈ T.line.Zc)
    (hd : T.line.IsCoreCFix z a b tL tR) (hd' : T.line.IsCoreCFix z' a' b' tL' tR') :
    (a' = tR ∨ a' = tR + 1) ↔ (tL' = b ∨ tL' = b + 1) := by
  have h1 := P55.cfix_tL_le hd
  have h2 := P55.cfix_le_tR hd
  have h3 := P55.cfix_tL_le hd'
  have h4 := P55.cfix_a_lt hd'
  constructor
  · intro h
    have hb := fan55h1 F h54 h40 T.line z z' a b tL tR a' b' tL' tR' hz hz' hd hd' h
    by_contra hn
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, k ≤ -1 ∧ (tL' + 2 * k = b ∨ tL' + 2 * k = b + 1) :=
      ⟨-((tL' - b) / 2), by omega, by omega⟩
    obtain ⟨hzk, hdk⟩ := translate_data F T k hz' hd'
    have := fan55h2 F h54 h40 T.line z _ a b tL tR _ _ _ _ hz hzk hd hdk hk2
    omega
  · intro h
    have hb := fan55h2 F h54 h40 T.line z z' a b tL tR a' b' tL' tR' hz hz' hd hd' h
    by_contra hn
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, k ≤ -1 ∧ (a' + 2 * k = tR ∨ a' + 2 * k = tR + 1) :=
      ⟨-((a' - tR) / 2), by omega, by omega⟩
    obtain ⟨hzk, hdk⟩ := translate_data F T k hz' hd'
    have := fan55h1 F h54 h40 T.line z _ a b tL tR _ _ _ _ hz hzk hd hdk hk2
    omega

end P55

theorem fan55a (F : FanTree Γ G) (h54 : Fan54 F) : Fan55a F := by
  intro h40 T z z' a b tL tR a' b' tL' tR' hz hz' hd hd'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, a' + 2 * m = tR ∨ a' + 2 * m = tR + 1 :=
    ⟨-((a' - tR) / 2), by omega⟩
  obtain ⟨hzm, hdm⟩ := P55.translate_data F T m hz' hd'
  have hobs := (P55.obs F h54 h40 T hz hzm hd hdm).1 hm
  exact ⟨m, hd, hdm, a' + 2 * m - tR, tL' + 2 * m - b, by omega, by omega, by omega, by omega⟩

theorem fan55c (F : FanTree Γ G) (h54 : Fan54 F) : Fan55c F := by
  intro h40 T z z' a b tL tR a' b' tL' tR' hz hz' hd hd'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, tL' + 2 * m = b ∨ tL' + 2 * m = b + 1 :=
    ⟨-((tL' - b) / 2), by omega⟩
  obtain ⟨hzm, hdm⟩ := P55.translate_data F T m hz' hd'
  have hobs := (P55.obs F h54 h40 T hz hzm hd hdm).2 hm
  rw [abs_le]
  constructor <;> omega

end CFSG.Quasithin.Fan86
