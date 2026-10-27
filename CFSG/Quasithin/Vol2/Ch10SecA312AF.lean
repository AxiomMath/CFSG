module

public import CFSG.Quasithin.Vol2.Ch10SecA312AE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.Quasithin.Vol2.Ch10SecA312AD
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

theorem autFixInner_of_top (h : AutFixInner ↥(⊤ : Subgroup X)) : AutFixInner X :=
  autFixInner_of_mulEquiv Subgroup.topEquiv.symm h

theorem autFixInner_of_case (hE : Ch1.EvenLieAutInner) (hS : Ch1.SporadicAutInner)
    (hq : CFSG.IsQuasisimple X) {B : Subgroup X}
    (hcase : A312C2 B ⊤ ∨ A312C3 B ⊤ ∨ A312C4 B ⊤ ∨ A312C5 B ⊤ ∨ A312C12 B ⊤ ∨ A312C13 B ⊤ ∨
      A312C14 B ⊤ ∨ A312C17 B ⊤ ∨ A312C18 B ⊤ ∨ A312C20 B ⊤) : AutFixInner X := by
  apply autFixInner_of_top
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  have hp : commutator ↥(⊤ : Subgroup X) = ⊤ := Group.isPerfect_def.mp hq'.1
  have lie : Ch1.SQTKCharTwoLie ↥(⊤ : Subgroup X) → AutFixInner ↥(⊤ : Subgroup X) :=
    autFixInner_of_lie hE
  rcases hcase with ⟨-, hrk, -⟩ | ⟨f, hSz, hF4, -⟩ | ⟨-, hL45, -⟩ | ⟨-, hL5, -⟩ |
      (⟨-, hM22⟩ | ⟨-, hHat⟩) | ⟨-, hM23⟩ | ⟨-, hM24⟩ | ⟨hJ4, -⟩ | ⟨-, hHS⟩ | ⟨-, -, hRu⟩
  · rcases hrk with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hfo, hf3, h⟩⟩ | h
    · exact lie (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, h⟩)⟩))
    · exact autFixInner_of_quotient hp (autFixInner_of_lie hE (sqtkCharTwoLie_of_isSL3 hf h))
    · exact lie (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, h⟩)))⟩))
    · exact lie (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, h⟩))))⟩))
    · exact lie (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hf, h⟩)))))⟩))
    · exact lie (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hfo, hf3, h⟩))))))⟩))
    · exact lie (Or.inl (Or.inr h))
  · obtain ⟨-, a, ha, K, _, _, hfa, -⟩ := hSz
    exact lie (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨⟨a, hfa⟩, by omega, hF4⟩))))))⟩))
  · rcases hL45 with h | h
    · exact lie (Or.inr ⟨4, Or.inl rfl, h⟩)
    · exact lie (Or.inr ⟨5, Or.inr rfl, h⟩)
  · exact lie (Or.inr ⟨5, Or.inr rfl, hL5⟩)
  · exact autFixInner_of_sporadic hS (s := .M22) (by simp [Ch1.IsSQTKSporadicName]) (by decide)
      hM22
  · exact autFixInner_of_quotient (Group.isPerfect_def.mp hHat.1.1)
      (autFixInner_of_sporadic hS (s := .M22) (by simp [Ch1.IsSQTKSporadicName]) (by decide)
        hHat.2.2)
  · exact autFixInner_of_sporadic hS (s := .M23) (by simp [Ch1.IsSQTKSporadicName]) (by decide)
      hM23
  · exact autFixInner_of_sporadic hS (s := .M24) (by simp [Ch1.IsSQTKSporadicName]) (by decide)
      hM24
  · exact autFixInner_of_sporadic hS (s := .J4) (by simp [Ch1.IsSQTKSporadicName]) (by decide)
      hJ4
  · exact autFixInner_of_sporadic hS (s := .HS) (by simp [Ch1.IsSQTKSporadicName]) (by decide)
      hHS
  · exact autFixInner_of_sporadic hS (s := .Ru) (by simp [Ch1.IsSQTKSporadicName]) (by decide)
      hRu

theorem a312AutCent_of (hList : Vol2Native.A312ListFactsCat) (hE : Ch1.EvenLieAutInner)
    (hS : Ch1.SporadicAutInner) (hZ : A312ZCentFacts) : A312AutCent := by
  intro X _ _ hq hsq hO T hT B hB hBX hTB htypes V hVB hV hBV hcomm hV1 hc hlift
  have hcase := hList X hq hsq hO T hT B hB hBX
  by_cases hsp : A312Sp4 B
  · exact Or.inr hsp
  refine Or.inl fun α hαB hαT hα2 => ?_
  by_contra hα1
  obtain ⟨β, hβ1, hβ2, hβB, hβT⟩ := exists_involution_fix hO hT hTB hαB hαT hα2 hα1
  have hconf : AutFixInner X → ZCentConf X T B := fun hinner => by
    obtain ⟨g, rfl⟩ := hinner T hT β hβ2 hβT
    obtain ⟨z, hzT, hzc, hzg⟩ := exists_center_of_conj hT hβ2 hβT
    have hz1 : z ≠ 1 := fun h => hβ1 (by rw [← hzg, h, map_one])
    have hzB : ∀ b ∈ B, z * b = b * z := fun b hb => by
      have h := hβB b hb
      rw [← hzg, MulAut.conj_apply] at h
      calc z * b = z * b * z⁻¹ * z := by group
        _ = b * z := by rw [h]
    exact ⟨hq, hsq, hO, hT, hB, hBX, hTB, htypes, ⟨z, hzT, hz1, hzc, hzB⟩, V, hVB, hV, hBV,
      hcomm, hV1, hc, hlift⟩
  have hvoid := fun h => false_of_list hB h htypes hVB hV hBV hcomm hV1 hc
  have hin := fun h => hconf (autFixInner_of_case (B := B) hE hS hq h)
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hsp (hZ.lie X T B (Or.inl h) (hin (by simp only [h, true_or])))
  · exact hsp (hZ.lie X T B (Or.inr h) (hin (by simp only [h, true_or, or_true])))
  · exact hZ.l45 X T B (Or.inl h) (hin (by simp only [h, true_or, or_true]))
  · exact hZ.l45 X T B (Or.inr h) (hin (by simp only [h, true_or, or_true]))
  · exact hvoid (by simp only [h, true_or])
  · exact hvoid (by simp only [h, true_or, or_true])
  · exact hvoid (by simp only [h, true_or, or_true])
  · exact hvoid (by simp only [h, true_or, or_true])
  · exact hvoid (by simp only [h, true_or, or_true])
  · exact hvoid (by simp only [h, true_or, or_true])
  · exact hZ.m22 X T B h (hin (by simp only [h, true_or, or_true]))
  · exact hZ.m23 X T B h (hin (by simp only [h, true_or, or_true]))
  · exact hZ.m24 X T B h (hin (by simp only [h, true_or, or_true]))
  · exact hvoid (by simp only [h, true_or, or_true])
  · exact hvoid (by simp only [h, true_or, or_true])
  · exact hZ.j4 X T B h (hin (by simp only [h, true_or, or_true]))
  · exact hZ.hs X T B h (hin (by simp only [h, true_or, or_true]))
  · exact hvoid (by simp only [h, or_true])
  · exact hZ.ru X T B h (hin (by simp only [h, or_true]))

end CFSG.Quasithin.Vol2.Ch10.A312A
