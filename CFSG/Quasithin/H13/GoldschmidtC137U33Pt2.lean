module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Pt1
public import CFSG.Quasithin.H13.GoldschmidtC137DE

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
  (E : Entry33 X T V L (pCoreOf 2 P) h.hVe)
  {A : Subgroup (MulAut (IntMod V h.hVe))} (hA : PtA (autI h.hVe X) (autI h.hVe P) A)
  {c : MulAut (IntMod V h.hVe)} (hc : c ∈ autI h.hVe L)
  (hLc : autI h.hVe L ≤ A ⊔ B1.conjAut c A)
  (hrk : rkIdx (fixV (autI h.hVe L)) = 6)
include h E hA hc hLc hrk

theorem hDE_u33 :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V h.hVe))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI h.hVe L, B1.conjAut g (Y i) ≤ autI h.hVe (pCoreOf 2 P)) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn h.hVe (L ⊔ pCoreOf 2 P) (Y i))) ∧
      (∀ i, Y i = autI h.hVe (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 (pCoreOf 2 P)) ∧
      autI h.hVe L ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI h.hVe L)) ∧
      ∀ B, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) B →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V h.hVe))),
          B = ⨆ k, Ai k ∧ ∀ k, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI h.hVe L, Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI h.hVe (pCoreOf 2 P) := by
  have hR2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hA₂ := h.toBaum.hA2
  obtain ⟨A₀, hA₀, hA₀C⟩ := h.exists_A0 E
  have hAA₀ : autI h.hVe A₀ = A := autI_A0 h E hA hA₀ hA₀C
  let cc : Fin 2 → MulAut (IntMod V h.hVe) := ![1, c]
  have hcc : ∀ i, cc i ∈ autI h.hVe L := by
    intro i
    fin_cases i
    · exact (autI h.hVe L).one_mem
    · exact hc
  have hex : ∀ i, ∃ l : G, ∃ hl : l ∈ normalizer (V : Set G), l ∈ L ∧
      convI h.hVe ⟨l, hl⟩ = cc i := by
    intro i
    obtain ⟨l, hlL, hlc⟩ := (mem_autI h.hVe).1 (hcc i)
    exact ⟨l, l.2, hlL, hlc⟩
  choose ℓ hℓN hℓL hℓc using hex
  have hpieces := fun i => exists_Dpiece h.hVe h.hXN h.hLX h.hRX hR2 hA₂ hA₀ (hℓL i)
  refine ⟨2, fun i => B1.conjAut (cc i) (autI h.hVe A₀),
    fun i => cjSub (ℓ i) (starPreIn h.hVe (pCoreOf 2 P) (autI h.hVe A₀)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(cc i)⁻¹, Subgroup.inv_mem _ (hcc i), ?_⟩
    rw [B1.conjAut_inv_conjAut]
    exact autI_mono h.hVe hA₀.1
  · intro i
    obtain ⟨hX, hS, -, -⟩ := hpieces i
    refine ⟨hX, ?_⟩
    rwa [hℓc i] at hS
  · intro i
    obtain ⟨-, -, hJ, -⟩ := hpieces i
    rwa [hℓc i] at hJ
  · intro i
    exact (hpieces i).2.2.2
  · simp only [hAA₀]
    refine hLc.trans (sup_le ?_ ?_)
    · have h0 := le_iSup (fun i : Fin 2 => B1.conjAut (cc i) A) 0
      simpa [cc, conjAut_one_gc] using h0
    · have h1 := le_iSup (fun i : Fin 2 => B1.conjAut (cc i) A) 1
      simpa [cc] using h1
  · rw [Fin.sum_univ_two]
    simp only [rkIdx_fixV_conjAut, hAA₀, hA.rk]
    omega
  · intro B hB
    have hle : B ≤ pCoreOf 2 (autI h.hVe P) := h.autI_R ▸ hB.1
    have hX : IsFFStarOffender (autI h.hVe X) B :=
      ⟨hB.1.trans (autI_mono h.hVe h.hRX), hB.2.1, hB.2.2.1, hB.2.2.2⟩
    have hBA := hA.uniq B hle hX
    subst hBA
    refine ⟨1, fun _ => B, (iSup_const).symm, fun _ => ⟨hB, 0, 1, (autI h.hVe L).one_mem, ?_, ?_⟩⟩
    · simp [cc, conjAut_one_gc, hAA₀]
    · simp [cc, conjAut_one_gc, hAA₀]
      exact hB.1

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
