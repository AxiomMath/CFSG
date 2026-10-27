module

public import CFSG.Quasithin.H13.GoldschmidtC137Pt3Aux
public import CFSG.Quasithin.H13.GoldschmidtC137U33Img
public import CFSG.Quasithin.H13.GoldschmidtC137U33Facts

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem autI_baum_le_u33 [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V) (hVR : V ≤ R)
    (hRN : R ≤ normalizer (V : Set G)) :
    autI hV (baum R) ≤ autI hV R ⊓ centSub (fixV (autI hV (thompsonJ R))) :=
  CFSG.Quasithin.H13.U3.GC137.autI_baum_le hV hVR hRN

structure PtA {W : Type} [CommGroup W] [Finite W] (X₀ P₀ A : Subgroup (MulAut W)) : Prop where
  le : A ≤ pCoreOf 2 P₀
  off : IsFFStarOffender X₀ A
  uniq : ∀ B : Subgroup (MulAut W), B ≤ pCoreOf 2 P₀ → IsFFStarOffender X₀ B → B = A
  cent : pCoreOf 2 P₀ ⊓ centSub (fixV A) ≤ A
  card : Nat.card ↥A = 8
  rk : rkIdx (fixV A) = 3

theorem G2Point.exists_PtA {W : Type} [CommGroup W] [Finite W] {X₀ L₀ P₀ : Subgroup (MulAut W)}
    (hp : G2Point X₀ L₀ P₀) :
    ∃ A, PtA X₀ P₀ A ∧ ∃ c ∈ L₀, L₀ ≤ A ⊔ B1.conjAut c A := by
  obtain ⟨A, h1, h2, h3, h4, h5, h6, c, hc, hL⟩ := hp
  exact ⟨A, ⟨h1, h2, h3, h4, h5, h6⟩, c, hc, hL⟩

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
include h

theorem hRX : pCoreOf 2 P ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le

theorem hVR : V ≤ pCoreOf 2 P := h.toBaum.hVR

theorem hRN : pCoreOf 2 P ≤ normalizer (V : Set G) := h.hRX.trans h.hXN

section Entry

variable (E : Entry33 X T V L (pCoreOf 2 P) h.hVe)
include E

theorem exists_A0 : ∃ A₀ : Subgroup G, IsMaxElemAbelian (pCoreOf 2 P) A₀ ∧
    ¬ A₀ ≤ centralizer (V : Set G) := by
  by_contra hcon
  push Not at hcon
  exact E.hJ (iSup₂_le fun A hA => hcon A hA)

variable {A : Subgroup (MulAut (IntMod V h.hVe))}
  (hA : PtA (autI h.hVe X) (autI h.hVe P) A)
include hA

theorem autI_A0 {A₀ : Subgroup G} (hA₀ : IsMaxElemAbelian (pCoreOf 2 P) A₀)
    (hA₀C : ¬ A₀ ≤ centralizer (V : Set G)) : autI h.hVe A₀ = A := by
  have hB : autI h.hVe A₀ ∈ offenderImages h.hVe (pCoreOf 2 P) := ⟨A₀, ⟨hA₀, hA₀C⟩, rfl⟩
  have hB' := offenderImages_sub_conjIn h.hVe h.hXN h.hRX hB
  have hle : autI h.hVe A₀ ≤ pCoreOf 2 (autI h.hVe P) :=
    h.autI_R ▸ autI_mono h.hVe hA₀.1
  exact hA.uniq _ hle (E.stab.2.1 _ hB')

theorem autI_J : autI h.hVe (thompsonJ (pCoreOf 2 P)) = A := by
  obtain ⟨A₀, hA₀, hA₀C⟩ := h.exists_A0 E
  have hAA₀ := autI_A0 h E hA hA₀ hA₀C
  rw [← ffJP_conjIn_eq h.hVe h.hXN h.hRX h.C_le_R]
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => iSup_le fun hBR => ?_
    have hle : B ≤ pCoreOf 2 (autI h.hVe P) := h.autI_R ▸ hBR
    exact (hA.uniq B hle (E.stab.2.1 B hB)).le
  · have hmem : A ∈ C124.offenderImagesConjIn h.hVe X (pCoreOf 2 P) := by
      rw [← hAA₀]
      exact offenderImages_sub_conjIn h.hVe h.hXN h.hRX ⟨A₀, ⟨hA₀, hA₀C⟩, rfl⟩
    have hAR : A ≤ autI h.hVe (pCoreOf 2 P) := h.autI_R ▸ hA.le
    exact le_iSup₂_of_le A hmem (le_iSup (fun _ : A ≤ autI h.hVe (pCoreOf 2 P) => A) hAR)

theorem autI_baum : autI h.hVe (baum (pCoreOf 2 P)) = A := by
  apply le_antisymm
  · have h1 := autI_baum_le_u33 h.hVe h.hVR h.hRN
    rw [autI_J h E hA, h.autI_R] at h1
    exact h1.trans hA.cent
  · rw [← autI_J h E hA]
    exact autI_mono h.hVe (B2F.thompsonJ_le_baum _)

theorem no_strong : ∀ B, ¬ IsStrongFFStarOffender (autI h.hVe (pCoreOf 2 P)) B := by
  rintro B ⟨hB, hr⟩
  have hle : B ≤ pCoreOf 2 (autI h.hVe P) := h.autI_R ▸ hB.1
  have hX : IsFFStarOffender (autI h.hVe X) B :=
    ⟨hB.1.trans (autI_mono h.hVe h.hRX), hB.2.1, hB.2.2.1, hB.2.2.2⟩
  have hBA := hA.uniq B hle hX
  subst hBA
  unfold rAV at hr
  have h8 : rk ↥B = 3 := by
    unfold rk
    rw [hA.card]
    exact padicValNat.prime_pow (p := 2) 3
  rw [hA.rk, h8] at hr
  norm_num at hr

end Entry

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
