module

public import CFSG.Quasithin.H13.GoldschmidtC137L32Baum
public import CFSG.Quasithin.H13.GoldschmidtC137Data

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {G : Type} [Group G]

namespace L32Ctx

variable [Finite G] {X T L P W : Subgroup G} {u : G} (h : L32Ctx X T L P W u)
include h

theorem hC (φ : IntMod W h.hWe ≃* Multiplicative L3.Vec) :
    ∀ B, ¬ IsStrongFFStarOffender (autI h.hWe (pCoreOf 2 P)) B := by
  intro B hB
  by_cases hRne : autI h.hWe (pCoreOf 2 P) = ⊥
  · exact hB.1.2.1 (le_bot_iff.1 (hRne ▸ hB.1.1))
  · rw [h.autI_R_eq_v4M φ hRne] at hB
    exact not_strong_of_le_v4M φ (uM_ne_one h) hB.1 hB.2

theorem hDE (φ : IntMod W h.hWe ≃* Multiplicative L3.Vec) {A₀ : Subgroup G}
    (hA₀ : IsMaxElemAbelian (pCoreOf 2 P) A₀) (hc : Nat.card (autI h.hWe A₀) = 2) :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod W h.hWe))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI h.hWe L, B1.conjAut g (Y i) ≤ autI h.hWe (pCoreOf 2 P)) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn h.hWe (L ⊔ pCoreOf 2 P) (Y i))) ∧
      (∀ i, Y i = autI h.hWe (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 (pCoreOf 2 P)) ∧
      autI h.hWe L ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI h.hWe L)) ∧
      ∀ A, IsFFStarOffender (autI h.hWe (pCoreOf 2 P)) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod W h.hWe))), A = ⨆ k, Ai k ∧
          ∀ k, IsFFStarOffender (autI h.hWe (pCoreOf 2 P)) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI h.hWe L, Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI h.hWe (pCoreOf 2 P) := by
  set R := pCoreOf 2 P with hR
  set Y₀ := autI h.hWe A₀ with hY₀
  have hRne : autI h.hWe R ≠ ⊥ := by
    intro hb
    have : Y₀ ≤ ⊥ := hb ▸ autI_mono h.hWe hA₀.1
    rw [le_bot_iff] at this
    rw [this, Subgroup.card_bot] at hc
    omega
  have hRv := h.autI_R_eq_v4M φ hRne
  have hY₀le : Y₀ ≤ v4M φ (uM h) (uM_ne_one h) := hRv ▸ autI_mono h.hWe hA₀.1
  obtain ⟨t₀, ht₀v, ht₀1, hY₀t⟩ : ∃ t ∈ v4M φ (uM h) (uM_ne_one h), t ≠ 1 ∧
      Y₀ = Subgroup.zpowers t := by
    rcases subgroup_le_v4M_cases φ (uM_ne_one h) hY₀le with h0 | h1 | h4
    · rw [h0, Subgroup.card_bot] at hc
      omega
    · exact h1
    · rw [h4, card_v4M φ (uM_ne_one h)] at hc
      omega
  have ht₀2 := v4M_sq φ ht₀v
  obtain ⟨g₂, g₃, hgen⟩ := exists_gen_conj φ ht₀2 ht₀1
  set c : Fin 3 → MulAut (IntMod W h.hWe) := ![1, g₂, g₃] with hcdef
  have hex : ∀ i, ∃ l : G, ∃ hl : l ∈ normalizer (W : Set G), l ∈ L ∧
      convI h.hWe ⟨l, hl⟩ = c i := by
    intro i
    have hi : c i ∈ autI h.hWe L := by rw [h.autI_L_top]; trivial
    obtain ⟨l, hlL, hlc⟩ := (mem_autI h.hWe).1 hi
    exact ⟨l, l.2, hlL, hlc⟩
  choose ℓ hℓN hℓL hℓc using hex
  have hR2 : IsPGroup 2 R := isPGroup_pCoreOf_two_gc P
  have hRX : R ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le
  have hpieces := fun i => exists_Dpiece h.hWe h.hXN h.hLX hRX hR2 h.hA2 hA₀ (hℓL i)
  have hYi : ∀ i, B1.conjAut (c i) Y₀ = Subgroup.zpowers (c i * t₀ * (c i)⁻¹) := by
    intro i
    rw [hY₀t, conjAut_zpowers]
  refine ⟨3, fun i => B1.conjAut (c i) Y₀, fun i => cjSub (ℓ i) (starPreIn h.hWe R Y₀),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : (c i)⁻¹ ∈ autI h.hWe L := Subgroup.inv_mem _ (by rw [h.autI_L_top]; trivial)
    refine ⟨(c i)⁻¹, hi, ?_⟩
    rw [B1.conjAut_inv_conjAut]
    exact autI_mono h.hWe hA₀.1
  · intro i
    obtain ⟨hX, hS, -, -⟩ := hpieces i
    refine ⟨hX, ?_⟩
    rwa [hℓc i] at hS
  · intro i
    obtain ⟨-, -, hJ, -⟩ := hpieces i
    rwa [hℓc i] at hJ
  · intro i
    exact (hpieces i).2.2.2
  · rw [h.autI_L_top, ← hgen]
    refine (Subgroup.closure_le (⨆ i, B1.conjAut (c i) Y₀)).2 ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact (le_iSup (fun i => B1.conjAut (c i) Y₀) 0)
        (by rw [hYi 0]; simp [hcdef])
    · exact (le_iSup (fun i => B1.conjAut (c i) Y₀) 1)
        (by rw [hYi 1]; simp [hcdef])
    · exact (le_iSup (fun i => B1.conjAut (c i) Y₀) 2)
        (by rw [hYi 2]; simp [hcdef])
  · have hone : ∀ i, rkIdx (fixV (B1.conjAut (c i) Y₀)) = 1 := by
      intro i
      have hs2 : (c i * t₀ * (c i)⁻¹) ^ 2 = 1 := by rw [conj_pow, ht₀2]; group
      have hs1 : c i * t₀ * (c i)⁻¹ ≠ 1 := fun h1 => ht₀1 (conj_eq_one_iff.1 h1)
      rw [hYi i, rkIdx_of_card φ (k := 2)
        (by rw [card_fixV_zpowers_invol φ hs2 hs1]; norm_num) (by norm_num)]
    rw [Fin.sum_univ_three, hone, hone, hone, h.autI_L_top, fixV_top φ,
      rkIdx_of_card φ (k := 0) (by simp) (by norm_num)]
  · intro A hA
    rw [hRv] at hA ⊢
    obtain ⟨r, Ai, hAeq, hAi⟩ := offender_cover φ (uM_ne_one h) hA
    refine ⟨r, Ai, hAeq, fun k => ?_⟩
    obtain ⟨t, htv, ht1, hAk⟩ := (hAi k).2
    obtain ⟨g, hg, hgt⟩ := v4M_conj_trans φ ht₀v ht₀1 htv ht1
    have hgL : g ∈ autI h.hWe L := by rw [h.autI_L_top]; trivial
    have e : B1.conjAut g (B1.conjAut (c 0) Y₀) = Ai k := by
      rw [hYi 0, conjAut_zpowers, hAk]
      simp [hcdef, hgt]
    refine ⟨(hAi k).1, 0, g, hgL, ?_, ?_⟩
    · exact e.symm.le
    · rw [e, hAk]
      exact Subgroup.zpowers_le.2 htv

end L32Ctx

end CFSG.Quasithin.H13.U3.GC137
