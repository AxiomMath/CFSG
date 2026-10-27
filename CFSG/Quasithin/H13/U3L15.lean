module

public import CFSG.Quasithin.H13.U3L15U
public import CFSG.Quasithin.H13.U3L15L
public import CFSG.Quasithin.H13.U3L15A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative commutatorElement

theorem not_isHatA6_of_center_eq_bot {G : Type} [Group G] {L : Subgroup G}
    (h : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) : ¬ IsHatA6 L := by
  rintro ⟨-, hc, -⟩
  rw [h, card_bot] at hc
  norm_num at hc

theorem stmt13_3_15_of
    (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14)
    (hhatP : U3HatL2Plus) : A6.Stmt13_3_15 := by
  intro G _ _ T L V V₂ X I₂ hH hV hzv hV2 hA5 hXhat hXn hI₂
  obtain ⟨-, -, ⟨-, hVall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hcomm, hmod⟩ := hVall V hV
  rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, hnat, -⟩ | ⟨hu, -, -⟩
  · exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
    exact hA5.false e
  · obtain ⟨S⟩ := setting4_of_case_b h1332 hH hV hzv h6
    exact u3Stmt13_3_15_of_A6 h1332 h13314 hhatP S hV2 hXhat hXn hI₂
  · exfalso
    rw [hzv, card_bot] at hc2
    norm_num at hc2
  · have hnh : ¬ IsHatA6 L := by
      obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hl
      have hsSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
        HSType.isSimpleGroup_SL_three_two
      have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e).2 hsSL
      have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
        have hna0 : ∃ a b : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), a * b ≠ b * a := by
          decide
        obtain ⟨a, b, hab⟩ := hna0
        exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
      exact not_isHatA6_of_center_eq_bot (center_eq_bot_of_isSimpleGroup hna)
    exact u3Stmt13_3_15_of_L32 h1332 h13314 hH hl hnat hV hzv hV2 (hXn hnh) hI₂
  · exact u3Stmt13_3_15_of_U3 h1332 h13314 hH hu hV hV2 (hXn (not_isHatA6_of_U3 hu)) hI₂

variable {G : Type} [Group G] [Finite G]

theorem u3V3Centralizer_of_13314
    (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) :
    U3V3Centralizer := by
  intro G _ _ T L V z hH hU3 hF V₂ V₃ h12 h23 h3V hT2 hT3 hc2 hc3
  have hirr := u3_isIrrPlusIn h1332 hH hU3 hF
  have hV2 : IsV2 T V V₂ := ⟨by rw [fsuV1_eq hF]; exact h12, h23.trans h3V, hT2, hc2⟩
  exact (u3Stmt13_3_15_of_U3 h1332 h13314 hH hU3 hirr hV2 rfl rfl).2.2.2.2.2.2.2.2 V₃ h23 h3V hT3
    hc3 |>.1

theorem u3_abelian_centralizer_hull_of_13314
    (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14)
    (h12_4 : U3Stmt13_3_12_4) (hcod : U3CodimThreeCentralizerControl) :
    U3AbelianCentralizerHull := by
  intro G _ _ T L V z hH hU3 hF
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  let S : HullSetting G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  have hB := u3V3Centralizer_of_13314 h1332 h13314
  have hsup : (⨆ h ∈ centralizer ({z} : Set G), CFSG.conjugate V h) = conjClosure V S.H := by
    rw [S.H_eq]
    apply le_antisymm
    · refine iSup₂_le fun h hh x hx => ?_
      rw [mem_conjugate_iff'] at hx
      have := mem_conjClosure (Z := V) (inv_mem hh) hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
    · refine conjClosure_le fun k hk v hv => ?_
      have hmem : k * v * k⁻¹ ∈ CFSG.conjugate V k⁻¹ := by
        rw [mem_conjugate_iff', inv_inv]
        simpa [mul_assoc] using hv
      exact (le_iSup₂ (f := fun h (_ : h ∈ centralizer ({z} : Set G)) =>
        CFSG.conjugate V h) k⁻¹ (inv_mem hk)) hmem
  rw [hsup]
  have hVea := isElemAbelian_of_isElementaryAbelian' V
  by_cases hHM : S.H ≤ normalizer (L : Set G)
  · obtain ⟨-, -, hTI, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
    have hle : conjClosure V S.H ≤ V := by
      refine conjClosure_le fun k hk v hv => ?_
      have hkM := hHM (inv_mem hk)
      rcases hTI _ hkM with h | h
      · have : k * v * k⁻¹ ∈ CFSG.conjugate V k⁻¹ := by
          rw [mem_conjugate_iff', inv_inv]
          simpa [mul_assoc] using hv
        rwa [h] at this
      · exfalso
        have hz : z ∈ V ⊓ CFSG.conjugate V k⁻¹ := mem_inf.2 ⟨S.hzV, by
          rw [mem_conjugate_iff', S.conj_V₁_of_H (inv_mem hk) S.z_mem_V₁]
          exact S.hzV⟩
        rw [h] at hz
        exact S.hz1 hz
    exact (F7.isElemAbelian_mono hVea hle).1
  · have hcod' : ∀ F : Subgroup G, F ≤ V → F.relIndex V ≤ 8 →
        centralizer (F : Set G) ≤ normalizer (V : Set G) :=
      fun F hFV hidx => hcod G T L V z hH hU3 hF F hFV hidx
    have hirr := u3_isIrrPlusIn h1332 hH hU3 hF
    have h14 : ¬ pCoreOf 2 S.H ≤ centralizer (S.V₂ : Set G) := by
      have := h13314 G T L V S.V₂ hH hirr (inf_centralizer_L_eq_bot hF) S.isV2
        (not_iso_a5_of_U3 hU3 hF)
      rwa [S.g1_eq_H] at this
    have h15 : pCoreOf 2 S.H ⊓ centralizer (S.V₂ : Set G) ≤
        pCoreOf 2 (normalizer (S.V₂ : Set G)) := by
      have h := u3Stmt13_3_15_of_U3 h1332 h13314 (I₂ := conjClosure (pCoreOf 2 (A6.g1 T V))
        (normalizer (S.V₂ : Set G))) hH hU3 hirr S.isV2 rfl rfl
      rw [S.g1_eq_H] at h
      exact h.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1
    exact (S.hullHyp (S.centralizer_V₃_le hB) (S.comm_eq_bot h12_4 hB) hHM h14 h15
      hcod').isElemAbelian.1

end CFSG.Quasithin.H13.U3
