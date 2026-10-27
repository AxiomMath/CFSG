module

public import CFSG.Timmesfeld.ARS.ExclNSDefs
public import CFSG.Blueprint.Catalog
import CFSG.Timmesfeld.ARS.NSLFrameModels
import CFSG.Timmesfeld.ARS.CaseOANSLAssembleMinus
import CFSG.Timmesfeld.ARS.CaseHFinal
import CFSG.Timmesfeld.ARS.CaseHU33
public import CFSG.Timmesfeld.ARS.Sec5Count
public import CFSG.Timmesfeld.ARS.Sec5Maximal
import CFSG.Timmesfeld.ARS.CaseHConnected

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint
open CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem NSLFrameData.injOn_rootGroup (F : NSLFrameData G R) :
    Set.InjOn F.Ψ (F.D.rootGroup (Pi.single F.i₀ 1) : Set F.K) := by
  intro x hx y hy hxy
  have hk : x * y⁻¹ ∈ F.Ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have h1 := F.hext.eq_one_of_mem_normalizer F.i₀ _ (mul_mem hx (inv_mem hy))
    (Subgroup.center_le_normalizer _ (F.ker hk))
  exact mul_inv_eq_one.1 h1

theorem NSLFrameData.card_map_rootGroup (F : NSLFrameData G R) :
    Nat.card ((F.D.rootGroup (Pi.single F.i₀ 1)).map F.Ψ) =
      Nat.card (F.D.rootGroup (Pi.single F.i₀ 1)) := by
  have h := Nat.card_image_of_injOn F.injOn_rootGroup
  rw [← Subgroup.coe_map] at h
  exact h

theorem NSLFrameData.exists_card (h : Hyp G R) (F : NSLFrameData G R) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card (F.D.rootGroup (Pi.single F.i₀ 1)) = 2 ^ f ∧
      ∀ E ∈ R, Nat.card E = 2 ^ f := by
  have := h.finite
  obtain ⟨f, hf, hM, -⟩ := F.opp.exists_mulEquiv_SL2' h.root F.mem
  exact ⟨f, hf, F.card_map_rootGroup.symm.trans hM,
    fun E hE => (h.root.card_eq hE F.mem).trans hM⟩

theorem NSLFrameData.lieModel_of (h : Hyp G R) (F : NSLFrameData G R)
    (hK : CFSG.IsQuasisimple F.K) {t : StatedLieTag} {n p f : ℕ}
    (hm : LieModel (F.K ⧸ Subgroup.center F.K) t n p f) : LieModel G t n p f := by
  obtain ⟨x, hx, hx1⟩ := h.root.exists_ne_one F.mem
  obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hx
  exact lieModel_of_center_eq_bot h.center
    (lieModel_quotient_of_surjective hK hm F.surj ⟨k, hx1⟩)

theorem NSLType.three_le_of_cartanC {n : ℕ} {i₀ : Fin n}
    (h : NSLType n (Symplectic.cartanC n) i₀) : 3 ≤ n := by
  rcases ExclNS.NSLType.elim h with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨rfl, -, hC⟩ | ⟨rfl, -, hC⟩
  · exact h3
  · exact h3
  · have hG : ∀ i j : Fin (Tag.rank .G2), Tag.cartan .G2 i j = ExclNS.g2e i.val j.val := by
      intro i j; fin_cases i <;> fin_cases j <;> rfl
    exact absurd (Matrix.ext fun i j => (hG i j).trans (hC i j).symm) cartan_G2_ne_cartanC
  · have hF : ∀ i j : Fin (Tag.rank .F4), Tag.cartan .F4 i j = ExclNS.f4e i.val j.val := by
      intro i j; fin_cases i <;> fin_cases j <;> rfl
    exact absurd (Matrix.ext fun i j => (hF i j).trans (hC i j).symm) cartan_F4_ne_cartanC

theorem NSLType.bounds_of_cartanB {m : ℕ} {i₀ : Fin m} (h : NSLType m (Spin.cartanB m) i₀) :
    3 ≤ m ∧ i₀.val + 1 < m := by
  rcases ExclNS.NSLType.elim h with ⟨h3, hi, -⟩ | ⟨h3, hi, -⟩ | ⟨rfl, -, hC⟩ | ⟨rfl, -, hC⟩
  · exact ⟨h3, hi⟩
  · exact ⟨h3, hi⟩
  · have hG : ∀ i j : Fin (Tag.rank .G2), Tag.cartan .G2 i j = ExclNS.g2e i.val j.val := by
      intro i j; fin_cases i <;> fin_cases j <;> rfl
    exact absurd (Matrix.ext fun i j => (hG i j).trans (hC i j).symm)
      CaseOANSL.cartan_G2_ne_cartanB
  · have hF : ∀ i j : Fin (Tag.rank .F4), Tag.cartan .F4 i j = ExclNS.f4e i.val j.val := by
      intro i j; fin_cases i <;> fin_cases j <;> rfl
    exact absurd (Matrix.ext fun i j => (hF i j).trans (hC i j).symm)
      CaseOANSL.cartan_F4_ne_cartanB

theorem NSLType.val_eq_zero_of_rank_two {r : ℕ} {C : Matrix (Fin r) (Fin r) ℤ} {i₀ : Fin r}
    (h : NSLType r C i₀) (hr : r = 2) : i₀.val = 0 := by
  rcases ExclNS.NSLType.elim h with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, hi, -⟩ | ⟨h4, -⟩ <;> omega

theorem NSLType.val_lt_two_of_cartan_F4 {i₀ : Fin (Tag.rank .F4)}
    (h : NSLType (Tag.rank .F4) (Tag.cartan .F4) i₀) : i₀.val < 2 := by
  rcases ExclNS.NSLType.elim h with ⟨-, -, hC⟩ | ⟨-, -, hC⟩ | ⟨h2, -⟩ | ⟨-, hi, -⟩
  · exact absurd hC cartan_F4_ne_cartanC
  · exact absurd hC CaseOANSL.cartan_F4_ne_cartanB
  · exact absurd h2 (by decide)
  · exact hi

@[expose] def NSLOrderOutcome (G : Type) [Group G] (R : Set (Subgroup G)) : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
    ((∃ n, 3 ≤ n ∧ LieModel G .PSp n 2 f) ∨ (∃ n, 4 ≤ n ∧ LieModel G .POmegaMinus n 2 f) ∨
      (2 ≤ f ∧ LieModel G .G2 0 2 f) ∨ LieModel G .trialityD4 0 2 f ∨ LieModel G .F4 0 2 f ∨
      LieModel G .twistedE6 0 2 f)) ∨
  LieModel G .PSU 3 3 1

theorem NSLFrameData.nslOrderOutcome (h : Hyp G R) (F : NSLFrameData G R) :
    NSLOrderOutcome G R := by
  have := h.finite
  have hperf : Group.IsPerfect G := CaseH.isPerfect h
  obtain ⟨f, hf, hX, hE⟩ := F.exists_card h
  have hL : ∀ (_ : CFSG.IsQuasisimple F.K) {t : StatedLieTag} {n p f' : ℕ},
      LieModel (F.K ⧸ Subgroup.center F.K) t n p f' → LieModel G t n p f' :=
    fun hK _ _ _ _ hm => F.lieModel_of h hK hm
  cases F with
  | mk K D nw T hct hext hdiv i₀ htype hpg Ψ hsurj hker hmem hopp hcomm hconc =>
  dsimp only at hX hL
  cases hconc with
  | symplectic n F₀ =>
    have hn := NSLType.three_le_of_cartanC htype
    obtain ⟨hK, hm⟩ := quasisimple_lieModel_symplecticDatum hn i₀ hf hX
    exact Or.inl ⟨f, hf, hE, Or.inl ⟨n, hn, hL hK hm⟩⟩
  | @minus n K' _ b c hirr =>
    obtain ⟨h3, hi⟩ := NSLType.bounds_of_cartanB htype
    have h3' : 3 ≤ n - 1 := h3
    have hi' : i₀.val + 1 < n - 1 := hi
    obtain ⟨hK, hm⟩ := quasisimple_lieModel_minusDatum hirr (by omega) i₀ (by omega) hf hX
    exact Or.inl ⟨f, hf, hE, Or.inr (Or.inl ⟨n, by omega, hL hK hm⟩)⟩
  | g2 K₀ =>
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      have hK₀ : Nat.card K₀ = 2 := (card_adjDatum_rootGroup (τ := .G2) i₀).symm.trans hX
      exact Or.inr (lieModel_PSU_of_g2Datum_two hK₀ Ψ hsurj hker)
    · obtain ⟨hK, hm⟩ := quasisimple_lieModel_g2Datum i₀ hf2 hX
      exact Or.inl ⟨f, hf, hE, Or.inr (Or.inr (Or.inl ⟨hf2, hL hK hm⟩))⟩
  | twistedD4 e =>
    obtain ⟨rfl, hK, hm⟩ := quasisimple_lieModel_twistedD4Datum e i₀
      (NSLType.val_eq_zero_of_rank_two htype rfl) hX
    exact Or.inl ⟨f, hf, hE, Or.inr (Or.inr (Or.inr (Or.inl (hL hK hm))))⟩
  | f4 K₀ =>
    obtain ⟨hK, hm⟩ := quasisimple_lieModel_f4Datum i₀ hf hX
    exact Or.inl ⟨f, hf, hE, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL hK hm)))))⟩
  | twistedE6 e =>
    obtain ⟨rfl, hK, hm⟩ := quasisimple_lieModel_twistedE6Datum e i₀
      (NSLType.val_lt_two_of_cartan_F4 htype) hX
    exact Or.inl ⟨f, hf, hE, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hL hK hm)))))⟩

theorem orderOutcome_of_sigmaEqLambda (h : Hyp G R) (hH : SigmaEqLambda R) :
    (∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ ∃ n, 3 ≤ n ∧ LieModel G .PSL n 2 f) ∨
      NSLOrderOutcome G R := by
  have := h.finite
  have hR := h.root
  obtain ⟨A, hA, -⟩ := h.nondeg
  have hEA : ∀ E ∈ R, Nat.card E = Nat.card A := fun E hE => hR.card_eq hE hA
  by_cases hmax : IsCoatom (Subgroup.normalizer (A : Set G))
  · have h3 := CaseH.three_le_ncard_linesThrough h hH hA hmax
    by_cases h23 : Nat.card A = 2 ∧ (linesThrough R A).ncard = 3
    · exact Or.inr (Or.inr (lieModel_PSU_of_caseH h hH hA h23.1 h23.2))
    · have hT := CaseH.mTransitive_of_not_two_three h hH hA h3 h23
      rcases caseHFrameInput G R h hH hT A hA h3 h23 with ⟨f, hf, hc, hG⟩ | ⟨f, hf, hc, hG⟩
      · obtain ⟨F, _, _, hF, φ, hcc, hgen, hnt⟩ := hG
        have hq : 3 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
        obtain ⟨-, -, -, -, hmodel⟩ := exists_lieModel_of_coneCompatible_G2 Nat.prime_two
          (by omega) hq hF h.center hcc hgen hnt
        exact Or.inr (Or.inl ⟨f, by omega, fun E hE => (hEA E hE).trans hc,
          Or.inr (Or.inr (Or.inl ⟨hf, hmodel⟩))⟩)
      · obtain ⟨F, _, _, hF, σ, hσ, φ, hcc, hgen, hnt⟩ := hG
        obtain ⟨-, -, -, -, hmodel⟩ := exists_lieModel_of_coneCompatible_twistedD4 Nat.prime_two
          hf hF σ hσ h.center hcc hgen hnt
        exact Or.inr (Or.inl ⟨f, hf, fun E hE => (hEA E hE).trans hc,
          Or.inr (Or.inr (Or.inr (Or.inl hmodel)))⟩)
  · obtain ⟨Δ, hΔ, hAΔ⟩ := (exists_isTI_iff h hA).1 hmax
    have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
      fun _ hA _ hB e => eq_of_omegaSet_eq h hA hB e
    obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow h.root h.noIsolated h.nondeg hΩ hΔ.isWeakTI hAΔ
    obtain ⟨hm2, X, hX⟩ := Linear.exists_isRootFrame h.root h.noIsolated h.nondeg hΩ hΔ hAΔ hm
    have hcfg := hX.isConfig
    have hgen := hX.iSup_adj_eq_top
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨f, hf, hE, hL⟩ := hcfg.lieModel_A_two hR h.noIsolated h.center hgen
      exact Or.inl ⟨f, hf, hE, 3, le_rfl, hL⟩
    · obtain ⟨f, hf, hE, hL⟩ := hcfg.lieModel_A hR h.noIsolated h.center hm3 hgen
      exact Or.inl ⟨f, hf, hE, m + 1, by omega, hL⟩

end CFSG.Timmesfeld.ARS
