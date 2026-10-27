module

public import CFSG.Quasithin.H13.L32A771b
public import CFSG.Quasithin.H13.L32A771c
public import CFSG.Quasithin.H13.L32A773o

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_ctx72_of (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h69 : Lemma14_7_69) (h70 : Lemma14_7_70) :
    ∃ l₀ : G, Ctx72 G T L V l₀ ∧
      (pCoreOf 2 (hz T V)).relIndex (conjSub l₀ (fsuU T V) ⊔ pCoreOf 2 (hz T V)) = 2 ∧
      conjSub l₀ (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨hcard, γ, γ', g, k, V₂, hN, -, -, hcap, hrel, -, hb3, l₀, hl₀, hUα⟩ := h70 G T L V h
  have hU := fsuU_eq_conjClosure_hz hMod h
  have h2 := h69 G T L V h γ γ' g k hN
  have hR := hN.uα_le hF
  rw [hUα] at h2 hR hcap hrel
  have h1b := commutator_le_fsuU_of h h63 hF h1222 h1332 h1334 hl₀ hR h2 hcap
  have hne : conjSub l₀ (fsuU T V) ≠ fsuU T V := by
    rw [← hUα, hU]
    exact hN.uα_ne hF
  have hnorm : fsuU T V ≤ Subgroup.normalizer (conjSub l₀ (fsuU T V) : Set G) := by
    rw [← hUα, hU]
    exact hN.le_normalizer hF
  exact ⟨l₀,
    { hyp := h, h1222 := h1222, h1332 := h1332, h1334 := h1334, h63 := h63, hF := hF,
      card_u0 := hcard, mem := hl₀, ne := hne, norm := hnorm, cap := hcap, rel := hrel,
      b3 := hb3, h71 := h1b }, h2, hR⟩

namespace Ctx72

variable {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem isL24Section_QH (hu0 : u0 T V = fsuV1 T V) (h13314 : A6.Stmt13_3_14) :
    IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have hU := fsuU_eq_conjClosure_hz C.hMod C.hyp
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hL24 : IsL24Section (kz T V) (fsuU T V) (fsuV1 T V) := by
    rw [← hu0]
    exact isL24Section_u0 C.hyp C.hMod C.h63
  have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
  have hQH : pCoreOf 2 (hz T V) ≤ hz T V := pCoreOf_le 2 _
  have hHU : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
    rw [hU]
    exact le_normalizer_conjClosure V _
  set D := fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) with hD
  have hV1D : fsuV1 T V ≤ D := le_inf hV1U fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (hQH hq) z hz).symm
  have hKD : kz T V ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    have hxH : x ∈ hz T V := oTwoUpper_le _ hx
    rw [← conjSub_eq_self_iff, hD, conjSub_inf, conjSub_eq_self_iff.mpr (hHU hxH),
      ← conjSub_centralizer, conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hxH)]
  have hDV1 : D = fsuV1 T V := by
    rcases hL24.eq_or_eq hV1D inf_le_left hKD with hD1 | hDU
    · exact hD1
    · exfalso
      have h4 := lemma14_7_4_one C.hyp C.h13322 C.hMod h13314 hV2
      have hg1 : A6.g1 T V = hz T V := normalizer_eq_centralizer_of_card_two hV1
      rw [hg1] at h4
      have hbot : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro v hv
        have hvD : v ∈ D := by
          rw [hDU]
          exact le_conjClosure V _ (hV2.2.1 hv)
        exact (Subgroup.mem_inf.mp hvD).2
      rw [hbot] at h4
      have h0 : Nat.card ↥(⊥ : Subgroup G) = 2 := by rw [h4]; exact hV1
      rw [Subgroup.card_bot] at h0
      exact absurd h0 (by norm_num)
  have hrel16 : (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)).relIndex
      (pCoreOf 2 (hz T V)) = 16 := by
    have h1 := C.hF.F97_relIndex C.hF.F911_2
    rw [← hU] at h1
    rw [h1]
    change D.relIndex (fsuU T V) = 16
    rw [hDV1, ← hu0]
    exact relIndex_u0 C.hyp C.hMod C.h63
  refine isL24Section_dual hL24 (fun a ha b hb => F7.isElemAbelian_comm hUe ha hb) hV1 hV1U
    (pCoreOf_le 2 _) (oTwoUpper_le _) ((oTwoUpper_le _).trans (le_normalizer_pCoreOf 2 _))
    (fun q hq u hu => ?_) hrel16
  rw [hU] at hu
  exact C.hF.commutator_mem_V₁ hq hu

end Ctx72

end CFSG.Quasithin.H13.L32A
