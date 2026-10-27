module

public import CFSG.Quasithin.H13.GoldschmidtC137Data
public import CFSG.Quasithin.Background.C124Offender

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem ffJP_le_gc {W : Type*} [CommGroup W] (P : Set (Subgroup (MulAut W)))
    (Y : Subgroup (MulAut W)) : ffJP P Y ≤ Y :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun h => h

section Offenders

variable {X V R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem le_of_autI_le (hXN : X ≤ normalizer (V : Set G)) (hRX : R ≤ X)
    (hCR : X ⊓ centralizer (V : Set G) ≤ R) {A : Subgroup G} (hAX : A ≤ X)
    (hA : autI hV A ≤ autI hV R) : A ≤ R := by
  intro a ha
  have haN := hXN (hAX ha)
  obtain ⟨r, hrR, hr⟩ := (mem_autI hV).1 (hA (convI_mem_autI hV ha haN))
  have hc : convI hV (r⁻¹ * ⟨a, haN⟩) = 1 := by
    rw [map_mul, map_inv, hr, inv_mul_cancel]
  have hcen := (convI_eq_one_iff hV _).1 hc
  have h1 : (r : G)⁻¹ * a ∈ R := hCR ⟨X.mul_mem (X.inv_mem (hRX hrR)) (hAX ha), hcen⟩
  have : a = (r : G) * ((r : G)⁻¹ * a) := by group
  rw [this]
  exact R.mul_mem hrR h1

theorem mem_offenderImages_of_le (hXN : X ≤ normalizer (V : Set G)) (hRX : R ≤ X)
    (hCR : X ⊓ centralizer (V : Set G) ≤ R) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : B ∈ C124.offenderImagesConjIn hV X R) (hBR : B ≤ autI hV R) :
    B ∈ offenderImages hV R := by
  obtain ⟨hB0, A, rfl, g, hg, hgA⟩ := hB
  have hAeq : cjSub g (cjSub g⁻¹ A) = A := cjSub_cjSub_inv g A
  have hAX : A ≤ X := by
    rw [← hAeq]
    exact cjSub_le (Subgroup.le_normalizer hg) (hgA.1.trans hRX)
  have hAR : A ≤ R := le_of_autI_le hV hXN hRX hCR hAX hBR
  have hAe : IsElemAbelian 2 A := by
    have := isElemAbelian_cjSub (g := g) hgA.2.1
    rwa [hAeq] at this
  refine ⟨A, ⟨⟨hAR, hAe, fun B' hB'R hB'e => ?_⟩, fun hAC => hB0 ?_⟩, rfl⟩
  · exact (hgA.2.2 B' hB'R hB'e).trans_eq (card_cjSub g⁻¹ A)
  · exact autI_eq_bot_of_le_centralizer hV hAC

theorem offenderImages_sub_conjIn (hXN : X ≤ normalizer (V : Set G)) (hRX : R ≤ X)
    {B : Subgroup (MulAut (IntMod V hV))} (hB : B ∈ offenderImages hV R) :
    B ∈ C124.offenderImagesConjIn hV X R := by
  obtain ⟨A, ⟨hA, hAC⟩, rfl⟩ := hB
  refine ⟨fun h0 => hAC ?_, A, rfl, 1, X.one_mem, ?_⟩
  · exact (autI_eq_bot_iff hV (hA.1.trans (hRX.trans hXN))).1 h0
  · have : cjSub (1 : G)⁻¹ A = A := by
      ext x
      simp [mem_cjSub]
    rw [this]
    exact hA

theorem ffJP_conjIn_eq (hXN : X ≤ normalizer (V : Set G)) (hRX : R ≤ X)
    (hCR : X ⊓ centralizer (V : Set G) ≤ R) :
    ffJP (C124.offenderImagesConjIn hV X R) (autI hV R) = autI hV (thompsonJ R) := by
  have hRN : R ≤ normalizer (V : Set G) := hRX.trans hXN
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => iSup_le fun hBR => ?_
    obtain ⟨A, ⟨hAmax, hAC⟩, rfl⟩ := mem_offenderImages_of_le hV hXN hRX hCR hB hBR
    exact autI_mono hV (le_iSup₂_of_le A hAmax le_rfl)
  · set J₁ := ffJP (C124.offenderImagesConjIn hV X R) (autI hV R) with hJ₁
    have hJ₁R : J₁ ≤ autI hV R := ffJP_le_gc _ _
    have hle : thompsonJ R ≤ starPreIn hV R J₁ := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      refine mem_starPreIn.2 ⟨hA.1 ha, hRN (hA.1 ha), ?_⟩
      by_cases hAC : A ≤ centralizer (V : Set G)
      · have : convI hV ⟨a, hRN (hA.1 ha)⟩ = 1 := (convI_eq_one_iff hV _).2 (hAC ha)
        rw [this]
        exact J₁.one_mem
      · have hAB : autI hV A ∈ offenderImages hV R := ⟨A, ⟨hA, hAC⟩, rfl⟩
        have hAB' := offenderImages_sub_conjIn hV hXN hRX hAB
        have hAR : autI hV A ≤ autI hV R := autI_mono hV hA.1
        have hAJ : autI hV A ≤ J₁ :=
          le_iSup₂_of_le (autI hV A) hAB' (le_iSup (fun _ : autI hV A ≤ autI hV R => autI hV A) hAR)
        exact hAJ (convI_mem_autI hV ha _)
    calc autI hV (thompsonJ R) ≤ autI hV (starPreIn hV R J₁) := autI_mono hV hle
      _ = J₁ := autI_starPreIn hV hRN hJ₁R

end Offenders

end CFSG.Quasithin.H13.U3.GC137
