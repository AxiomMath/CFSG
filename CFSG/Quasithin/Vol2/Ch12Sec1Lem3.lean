module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem7
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Conj

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

namespace Sec1213

variable {G : Type} [Group G] [Finite G]

open Sec121Tr in
theorem false_of_card_comm (hComm : LemH9Comm) {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp121 G T L V V₁ V₂ n) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hV : IsElemAbelian 2 V)
    (hNV : Subgroup.normalizer (V : Set G) = Subgroup.normalizer (L : Set G)) {h : G}
    (hVh : V ≤ Subgroup.normalizer (conjSubgroup V h : Set G)) {Y : Subgroup G} (hYV : Y ≤ V)
    (hc : Nat.card (⁅Y, conjSubgroup V h⁆ : Subgroup G) ≤ 2 ^ 2)
    (hi : 2 ^ 2 * Nat.card ↥(Y ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) ≤ Nat.card Y) :
    False := by
  have hH9 := h9Hyp_of_hyp121 hyp hTL hV
  have hXN : conjSubgroup Y h⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    have h1 := conjSubgroup_mono_left h⁻¹ (hYV.trans hVh)
    rwa [conjSubgroup_normalizer, conjSubgroup_conj_inv] at h1
  have hXM : conjSubgroup Y h⁻¹ ≤ Subgroup.normalizer (L : Set G) := hXN.trans hNV.le
  have hXe : IsElemAbelian 2 (conjSubgroup Y h⁻¹) :=
    isElemAbelian_conjSubgroup (B2F.isElemAbelian_mono hYV hV) h⁻¹
  have hcomm : Nat.card (commV (autI hV (conjSubgroup Y h⁻¹))) ≤ 2 ^ 2 := by
    rw [card_commV_autI hV hXN, ← E3.card_conjSubgroup _ h, conjSubgroup_commutator,
      conjSubgroup_inv_conj]
    exact hc
  have h2 := hComm _ _ _ _ _ _ _ hH9 _ (autI_mono hV hXM) (isElemAbelian2_autI hV hXe hXN) hcomm
  have h3 := card_autI_mul_card_inf hV hXN
  have h4 : Nat.card ↥(conjSubgroup Y h⁻¹ ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(Y ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) := by
    have h5 := Sec1217.card_conj_inf_centralizer Y (conjSubgroup V h) h⁻¹
    rwa [conjSubgroup_conj_inv] at h5
  have hpos : 0 < Nat.card ↥(Y ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) :=
    Nat.card_pos
  rw [h4, E3.card_conjSubgroup Y h⁻¹] at h3
  nlinarith

end Sec1213

open Sec1213 Sec1217 Sec121H9 Sec121Tr H9Conj in
theorem lem1213_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211) (hH91 : LemH91)
    (hH92 : LemH92Use) (hFF5 : LemH9FF5) (hComm : LemH9Comm) : Lem1213 := by
  intro G _ _ T L V V₁ V₂ n hyp hn
  subst hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hW
  obtain ⟨hTL, hNV⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hV := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hcV : IsMulCommutative ↥V := hV.1
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNV.ge
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hH9 := h9Hyp_of_hyp121 hyp hTL hV
  obtain ⟨hcard₁, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 hyp
  obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ 5 hyp hTL).2
  have hβ' := isDualH9_of_isDualPairing121 hV hV₁V hV₂V hβ
  have h92 := hH92 _ _ _ _ _ _ _ hH9 hβ'
  have hr : ((5 : ℕ) : ℕ∞) ≤ rParam V :=
    (((lem1212_of h1001 h331 h1211) G T L V V₁ V₂ 5 β hyp hβ).2 hV).1
  have hw0 : wParam T V = ((0 : ℕ) : ℕ∞) := le_antisymm (iInf₂_le 0 hW) (by simp)
  have hLnorm : ∀ {Y : Subgroup G}, Y ≤ V → autI hV L ≤ stabV (subI hV Y) →
      ∀ {b : G} (hbN : b ∈ Subgroup.normalizer (V : Set G)),
        convI hV ⟨b, hbN⟩ ∈ autI hV L → b ∈ Subgroup.normalizer (Y : Set G) := by
    intro Y hYV hinv b hbN hbL
    refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := hinv hbL (IntMod.mk hV ⟨a, hYV ha⟩)
    rw [mem_subI, mem_subI, convI_apply_val] at h1
    exact h1.mp ha
  have hmain : ∀ h : G, conjSubgroup V h ≤ Subgroup.normalizer (L : Set G) →
      2 ^ 5 ≤ Nat.card (autI hV (conjSubgroup V h)) → False := by
    intro h hBM hB5
    have hBN : conjSubgroup V h ≤ Subgroup.normalizer (V : Set G) := hBM.trans hMV
    have hBe : IsElemAbelian 2 (conjSubgroup V h) := isElemAbelian_conjSubgroup hV h
    have hBbe := isElemAbelian2_autI hV hBe hBN
    have hBbM := autI_mono hV hBM
    have hBb1 : autI hV (conjSubgroup V h) ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hB5
      norm_num at hB5
    have hcomm : ⁅V, conjSubgroup V h⁆ ≠ ⊥ := by
      intro h0
      apply hBb1
      rw [autI_eq_bot_iff hV hBN, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.commutator_comm]
      exact h0
    have hoff : IsWOffenderAt T V h := by
      refine ⟨hcomm, ?_⟩
      rw [inf_eq_left.mpr hBN, mQuot_self, hw0]
    have hk : ((4 : ℕ) : ℕ∞) + wParam T V + 1 ≤ rParam V := by
      rw [hw0]
      refine le_trans ?_ hr
      norm_num
    have h332 := e3_32 hV hoff hk
    rw [inf_eq_left.mpr hBN] at h332
    obtain ⟨hBbL, htop, hC5⟩ := h92 _ hBbM hBbe hB5
    have hVB : V ≤ Subgroup.normalizer (conjSubgroup V h : Set G) := by
      intro v hv
      have h1 : IntMod.mk hV ⟨v, hv⟩ ∈ gammaCheck 4 (autI hV (conjSubgroup V h)) := by
        refine H9Conj.gammaCheck_mono (k := 3) (by norm_num) _ ?_
        rw [htop]
        exact Subgroup.mem_top _
      exact (h332 (Subgroup.mem_map_of_mem (valHom hV) h1)).2
    have hfix : ∀ {Y : Subgroup G}, Y ≤ V → autI hV L ≤ stabV (subI hV Y) →
        Nat.card Y = 2 ^ 5 →
        Nat.card ↥(fixV (autI hV (conjSubgroup V h)) ⊓ subI hV Y) ≤ 2 ^ 2 → False := by
      intro Y hYV hinv hYcard hle
      rw [card_fixV_autI_inf_subI hV hBN hYV] at hle
      have hYB : ⁅Y, conjSubgroup V h⁆ ≤ Y ⊓ Subgroup.centralizer (conjSubgroup V h : Set G) := by
        rw [Subgroup.commutator_le]
        intro y hy b hb
        have hbY : b ∈ Subgroup.normalizer (Y : Set G) :=
          hLnorm hYV hinv (hBN hb) (hBbL ((mem_autI hV).2 ⟨⟨b, hBN hb⟩, hb, rfl⟩))
        have h1 : ⁅y, b⁆ ∈ conjSubgroup V h := by
          rw [commutatorElement_def]
          exact (conjSubgroup V h).mul_mem
            ((Subgroup.mem_normalizer_iff.mp (hVB (hYV hy)) b).mp hb)
            ((conjSubgroup V h).inv_mem hb)
        refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun c hc => B2F.isElemAbelian_comm hBe hc h1⟩
        rw [commutatorElement_def]
        have h2 : b * y⁻¹ * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hbY y⁻¹).mp (Y.inv_mem hy)
        have e : y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
        rw [e]
        exact Y.mul_mem hy h2
      refine false_of_card_comm hComm hyp hTL hV hNV hVB hYV
        ((Subgroup.card_le_of_le hYB).trans hle) ?_
      rw [hYcard]
      omega
    rcases hC5 with h1 | h1
    · exact hfix hV₁V hH9.inv₁ hcard₁ h1
    · exact hfix hV₂V hH9.inv₂ hcard₂ h1
  have hff : ∀ h : G, conjSubgroup V h ≤ Subgroup.normalizer (L : Set G) →
      V ≤ Subgroup.normalizer (conjSubgroup V h : Set G) → autI hV (conjSubgroup V h) ≠ ⊥ →
      Nat.card (autI hV (conjSubgroup V h)) ≤ 2 ^ 4 →
      Nat.card V ≤ Nat.card (autI hV (conjSubgroup V h)) *
        Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) → False := by
    intro h hBM hVB hBb1 hB4 hFFc
    have hBN : conjSubgroup V h ≤ Subgroup.normalizer (V : Set G) := hBM.trans hMV
    have hBbe := isElemAbelian2_autI hV (isElemAbelian_conjSubgroup hV h) hBN
    obtain ⟨h1, h2⟩ := hFF5 _ _ _ _ _ _ hH9 _ (autI_mono hV hBM) hBbe hBb1 hB4
      (by rw [card_fixV_autI hV hBN]; exact hFFc)
    rw [card_closure_comm hV hBN hV₁V] at h1
    refine false_of_card_comm hComm hyp hTL hV hNV hVB hV₁V
      (by rw [Subgroup.commutator_comm]; exact h1) ?_
    have h3 := Subgroup.relIndex_mul_card (fixV (autI hV (conjSubgroup V h)) ⊓ subI hV V₁)
      (subI hV V₁)
    rw [inf_eq_left.mpr (inf_le_right : fixV (autI hV (conjSubgroup V h)) ⊓ subI hV V₁ ≤
      subI hV V₁), card_fixV_autI_inf_subI hV hBN hV₁V, card_subI hV hV₁V] at h3
    rw [← h3]
    exact Nat.mul_le_mul_right _ h2
  have hboth : ∀ h : G, conjSubgroup V h ≤ Subgroup.normalizer (L : Set G) →
      V ≤ Subgroup.normalizer (conjSubgroup V h : Set G) → autI hV (conjSubgroup V h) ≠ ⊥ →
      Nat.card V ≤ Nat.card (autI hV (conjSubgroup V h)) *
        Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) → False := by
    intro h hBM hVB hBb1 hFFc
    by_cases h4 : Nat.card (autI hV (conjSubgroup V h)) ≤ 2 ^ 4
    · exact hff h hBM hVB hBb1 h4 hFFc
    · refine hmain h hBM ?_
      have hp := isPGroup_of_isElemAbelian2
        (isElemAbelian2_autI hV (isElemAbelian_conjSubgroup hV h) (hBM.trans hMV))
      rw [card_eq_two_pow_of_isPGroup hp] at h4 ⊢
      have h5 : 5 ≤ rk ↥(autI hV (conjSubgroup V h)) := by
        by_contra hlt
        exact h4 (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Nat.pow_le_pow_right (by norm_num) h5
  obtain ⟨g, hgT, hgC⟩ := exists_conj_of_not_wClos_le hV2 hW
  have hAM : conjSubgroup V g ≤ Subgroup.normalizer (L : Set G) := hgT.trans hTL
  have hAN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hA1 : autI hV (conjSubgroup V g) ≠ ⊥ := fun h => hgC ((autI_eq_bot_iff hV hAN).mp h)
  by_cases hVA : V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)
  ·
    have hVA' : conjSubgroup (conjSubgroup V g) g⁻¹ = V := conjSubgroup_conj_inv V g
    have hA'N : conjSubgroup V g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
      have h1 := conjSubgroup_mono_left g⁻¹ hVA
      rwa [conjSubgroup_normalizer, hVA'] at h1
    have hVA'' : V ≤ Subgroup.normalizer (conjSubgroup V g⁻¹ : Set G) := by
      have h1 := conjSubgroup_mono_left g⁻¹ hAN
      rwa [conjSubgroup_normalizer, hVA'] at h1
    have hA'M : conjSubgroup V g⁻¹ ≤ Subgroup.normalizer (L : Set G) := hA'N.trans hNV.le
    have hcardA : Nat.card (conjSubgroup V g) = Nat.card V := E3.card_conjSubgroup V g
    have hcardA' : Nat.card (conjSubgroup V g⁻¹) = Nat.card V := E3.card_conjSubgroup V g⁻¹
    have h1 := card_autI_mul_card_inf hV hAN
    have h2 := card_autI_mul_card_inf hV hA'N
    have hb : Nat.card ↥(conjSubgroup V g⁻¹ ⊓ Subgroup.centralizer (V : Set G)) =
        Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) := by
      have h3 := card_conj_inf_centralizer V (conjSubgroup V g) g⁻¹
      rwa [hVA'] at h3
    have ha : Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g⁻¹ : Set G)) =
        Nat.card ↥(conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) := by
      have h3 := card_conj_inf_centralizer (conjSubgroup V g) V g⁻¹
      rwa [hVA'] at h3
    have hA'1 : autI hV (conjSubgroup V g⁻¹) ≠ ⊥ := by
      intro h0
      rw [autI_eq_bot_iff hV hA'N] at h0
      apply hA1
      rw [autI_eq_bot_iff hV hAN]
      have h3 : Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) = Nat.card V := by
        rw [← hb, inf_eq_left.mpr h0, hcardA']
      have h4 : V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left h3.ge
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h5 : v ∈ V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) := by rw [h4]; exact hv
      exact ((Subgroup.mem_centralizer_iff.mp h5.2) x hx).symm
    rcases le_total (Nat.card ↥(conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)))
        (Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G))) with hle | hle
    · refine hboth g hAM hVA hA1 ?_
      rw [← hcardA, ← h1]
      exact Nat.mul_le_mul_left _ hle
    · refine hboth g⁻¹ hA'M hVA'' hA'1 ?_
      rw [← hcardA', ← h2, hb, ha]
      exact Nat.mul_le_mul_left _ hle
  ·
    refine hmain g hAM ?_
    have hrA := e3_4_two hVA
    rw [card_autI_eq hV hAN, relIndex_eq_two_pow (isPGroup_conjSubgroup hV2 g)]
    exact Nat.pow_le_pow_right (by norm_num) (by exact_mod_cast hr.trans hrA)

end CFSG.Quasithin.H13
