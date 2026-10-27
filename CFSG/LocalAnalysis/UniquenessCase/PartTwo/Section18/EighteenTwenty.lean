module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.GammaTwoBarHyp18
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem calABar_eq_empty_of_lt_aBar {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {k : ℕ}
    (hk : 0 < k) (h : aBar M V₀ V hV < k) : calABar k M V₀ V hV = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  have hle : k ≤ aBar M V₀ V hV := by
    simpa [aBar, calABar] using CFSG.Quasithin.E3.le_aParam_of_mem_aSet (W := Vtil V₀ V hV) hk hA
  omega

@[expose] def Gap_18_20_aBar (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∀ s : ℕ, P18_13_2 D V₀ V p L h s → s = 2 →
    aBar D.M V₀ V h.hyp125.isElemAbelian ≤ 2 * S17.nOf L

theorem eighteen_twenty_false (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h) {s : ℕ} (hs : P18_13_2 D V₀ V p L h s) (hs2 : s = 2)
    (haBar : aBar D.M V₀ V h.hyp125.isElemAbelian ≤ 2 * S17.nOf L)
    (hcong : ∀ (f : ℕ),
      IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f →
        S17.nOf L = f ∧ 1 < f) : False := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hn2 : 2 ≤ S17.nOf L := by
    obtain ⟨-, -, f, hΩ, -⟩ := hs
    obtain ⟨hN, h1⟩ := hcong f hΩ
    omega
  have hr : ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := h16 s hs
  have hδ : ((4 * S17.nOf L : ℕ) : ℕ∞) ≤ deltaInf D.M V := by
    have hδ' : ((2 * S17.nOf L * s : ℕ) : ℕ∞) ≤ deltaInf D.M V := h17 s hs
    have hnum : 2 * S17.nOf L * s = 4 * S17.nOf L := by rw [hs2]; ring
    rwa [hnum] at hδ'
  have hsmall : mSub V₀ ≤ 1 := h.small
  have hrm : ((4 * S17.nOf L - 1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : 4 * S17.nOf L - 1 + mSub V₀ <
      4 * S17.nOf L + 1)) hr
  have hMne : D.M ≠ ⊤ := uc22p20a_M_ne_top D
  have hrMVle : rMV D.M V ≤ (mSub V : ℕ∞) := by
    have hCbot : ¬ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ≤ D.M := by
      rw [show Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ by simp]
      exact fun hle => hMne (top_le_iff.mp hle)
    calc rMV D.M V ≤ (E3.mQuot V ⊥ : ℕ∞) :=
          CFSG.LocalAnalysis.WeakClosure81.rMV_le_mQuot D.M V ⊥ bot_le hCbot
      _ = (mSub V : ℕ∞) := by rw [E3.mQuot_bot_eq_rk]; rfl
  have h4n1_lt : 4 * S17.nOf L - 1 < mSub V := by
    have h1 : ((4 * S17.nOf L - 1 : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast (by omega :
        4 * S17.nOf L - 1 ≤ 4 * S17.nOf L - 1 + mSub V₀)) hrm
    exact_mod_cast lt_of_lt_of_le h1 hrMVle
  have hjle : 4 * S17.nOf L ≤ mSub V := by omega
  have hj3 : 3 ≤ 4 * S17.nOf L := by omega
  obtain ⟨A, hA, hAbar⟩ :=
    exists_gammaTwo_barSub_ne_bot_of_hyp18 D V₀ V p L h hx h61 h126 h66 h127 h1114 h111 h183 h1669
  have hAgam : A ∈ F12.Gam 2 D.M V := ⟨hA.1.trans D.sylowM.le, hA.2⟩
  obtain ⟨-, U, g, hUV, hcard, hAeq⟩ := hA
  obtain ⟨B, hB⟩ := eighteen_twenty_exists_gamma hV hUV hcard hAeq hj3 hjle
  have hmem := (h18 2 A hAgam hAbar (4 * S17.nOf L) hδ hrm B hB).1
  have hk0 : 0 < 4 * S17.nOf L - 2 := by omega
  have hle : 4 * S17.nOf L - 2 ≤ aBar D.M V₀ V hV := by
    have h' := CFSG.Quasithin.E3.le_aParam_of_mem_aSet (W := Vtil V₀ V hV) hk0 hmem
    simpa [aBar, calABar] using h'
  have hlt : aBar D.M V₀ V hV < 4 * S17.nOf L - 2 := by omega
  rw [calABar_eq_empty_of_lt_aBar hV hk0 hlt] at hmem
  exact absurd hmem (by simp)

theorem eighteen_twenty (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h)
    (hgapA : Gap_18_20_aBar D V₀ V p L h)
    (hcong : ∀ (f : ℕ),
      IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f →
        S17.nOf L = f ∧ 1 < f) :
    R18_20At D V₀ V p L h := by
  intro s hs
  by_contra hsne
  have hs2 : s = 2 := by
    obtain ⟨h1, h2, -⟩ := hs
    omega
  exact eighteen_twenty_false D V₀ V p L h hx h61 h126 h66 h127 h1114 h111 h183 h1669
    h16 h17 h18 hs hs2 (hgapA s hs hs2) hcong

theorem eighteen_twentytwo (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h13 : R18_13At D V₀ V p L h)
    (h19 : R18_19At D V₀ V p L h) (h20 : R18_20At D V₀ V p L h)
    (h21 : R18_21At D V₀ V p L h) :
    R18_22At D V₀ V p L h := by
  unfold R18_22At at *
  rcases h13 with h1 | ⟨s, hs⟩ | h3
  · exact absurd h1 h21
  · have h1 : s = 1 := h20 s hs
    rwa [h1] at hs
  · exact absurd h3 h19

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
