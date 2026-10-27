module

public import CFSG.Quasithin.Background.FFC4Tr1
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin

namespace FFC

namespace SplitTransport

open CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] {G G₁ G₂ : Subgroup (MulAut V)}

theorem res_compat (hstab : G₂ ≤ stabSub (fixV G₁))
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (g : ↥G₂) (w : ↥(fixV G₁)) :
    (fixV G₁).subtype (((resEquiv hstab hfaith g : ↥(autSub G₂ (fixV G₁))) :
      MulAut ↥(fixV G₁)) w) = (g : MulAut V) ((fixV G₁).subtype w) := rfl

theorem map_top_eq : (⊤ : Subgroup ↥(fixV G₁)).map (fixV G₁).subtype = fixV G₁ := by
  rw [Subgroup.map_top, Subgroup.range_subtype]

theorem map_fixV_eq (hstab : G₂ ≤ stabSub (fixV G₁)) (hfix : fixV G = fixV G₁ ⊓ fixV G₂) :
    (fixV (autSub G₂ (fixV G₁))).map (fixV G₁).subtype = fixV G := by
  rw [map_subtype_fixV_autSub hstab, hfix]

theorem map_modComm_eq (hstab : G₂ ≤ stabSub (fixV G₁)) :
    (modComm (autSub G₂ (fixV G₁)) ⊤).map (fixV G₁).subtype = modComm G₂ (fixV G₁) := by
  rw [modComm_eq_commSub, modComm_eq_commSub, map_commSub_autSub hstab, map_top_eq]

theorem realizes_transport (hstab : G₂ ≤ stabSub (fixV G₁))
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) {D : FFModel} {U Z : Subgroup ↥(fixV G₁)}
    (hr : D.Realizes (autSub G₂ (fixV G₁)) U Z) :
    D.Realizes G₂ (U.map (fixV G₁).subtype) (Z.map (fixV G₁).subtype) := by
  obtain ⟨π, hπ⟩ := hr
  exact ⟨_, RealizesVia.transport (fixV G₁).subtype (fixV G₁).subtype_injective
    (resEquiv hstab hfaith) (res_compat hstab hfaith) hπ⟩


theorem binaryNaturalSL_transport (hstab : G₂ ≤ stabSub (fixV G₁))
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hfix : fixV G = fixV G₁ ⊓ fixV G₂)
    {d a : ℕ}
    (hb : BinaryNaturalSL (autSub G₂ (fixV G₁)) ⊤ (fixV (autSub G₂ (fixV G₁))) d a) :
    BinaryNaturalSL G₂ (fixV G₁) (fixV G) d a := by
  obtain ⟨K, hK, hf, hc, hr⟩ := hb
  refine ⟨K, hK, hf, hc, ?_⟩
  have := realizes_transport hstab hfaith hr
  rwa [map_top_eq, map_fixV_eq hstab hfix] at this

theorem symmetricNatural_transport (hstab : G₂ ≤ stabSub (fixV G₁))
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hfix : fixV G = fixV G₁ ⊓ fixV G₂)
    {n : ℕ}
    (hb : SymmetricNatural (autSub G₂ (fixV G₁)) ⊤ (fixV (autSub G₂ (fixV G₁))) n) :
    SymmetricNatural G₂ (fixV G₁) (fixV G) n := by
  have := realizes_transport hstab hfaith hb
  rwa [map_top_eq, map_fixV_eq hstab hfix] at this

theorem directSum_transport (hstab : G₂ ≤ stabSub (fixV G₁))
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hfix : fixV G = fixV G₁ ⊓ fixV G₂)
    {D : FFModel} {k : ℕ}
    (hd : DirectSumOfCopies (autSub G₂ (fixV G₁)) ⊤ (fixV (autSub G₂ (fixV G₁))) D k) :
    DirectSumOfCopies G₂ (fixV G₁) (fixV G) D k := by
  obtain ⟨I, π, hZ, hind, hsup, hreal⟩ := hd
  have hι := (fixV G₁).subtype_injective
  have hF := map_fixV_eq hstab hfix
  refine ⟨fun i => (I i).map (fixV G₁).subtype,
    (resEquiv hstab hfaith).symm.toMonoidHom.comp π, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← hF]
    exact Subgroup.map_mono (hZ i)
  · intro i
    have h1 : (fixV G ⊔ ⨆ (j : Fin k) (_ : j ≠ i), (I j).map (fixV G₁).subtype) =
        ((fixV (autSub G₂ (fixV G₁))) ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j).map (fixV G₁).subtype := by
      rw [Subgroup.map_sup, hF]
      congr 1
      rw [Subgroup.map_iSup]
      congr 1
      ext1 j
      rw [Subgroup.map_iSup]
    show (I i).map (fixV G₁).subtype ⊓
      (fixV G ⊔ ⨆ (j : Fin k) (_ : j ≠ i), (I j).map (fixV G₁).subtype) = fixV G
    rw [h1, ← Subgroup.map_inf _ _ (fixV G₁).subtype hι, hind i, hF]
  · have h1 : (fixV G ⊔ ⨆ i, (I i).map (fixV G₁).subtype) =
        (fixV (autSub G₂ (fixV G₁)) ⊔ ⨆ i, I i).map (fixV G₁).subtype := by
      rw [Subgroup.map_sup, hF, Subgroup.map_iSup]
    rw [h1, hsup, map_top_eq]
  · intro i
    have := RealizesVia.transport (fixV G₁).subtype hι (resEquiv hstab hfaith)
      (res_compat hstab hfaith) (hreal i)
    rwa [hF] at this


theorem pieceC_transport (hstab : G₂ ≤ stabSub (fixV G₁))
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hfix : fixV G = fixV G₁ ⊓ fixV G₂)
    (hcomm : commV G₂ ≤ fixV G₁)
    (hc : Nonempty (↥(autSub G₂ (fixV G₁)) ≃* ↥(StatedSL 3 (ZMod 2))) ∧
      commV (autSub G₂ (fixV G₁)) ≤ ⊤ ∧
      Nat.card ↥(⊤ : Subgroup ↥(fixV G₁)) = 2 ^ 4 * Nat.card ↥(fixV (autSub G₂ (fixV G₁))) ∧
      (¬ ∃ A B : Subgroup ↥(fixV G₁), fixV (autSub G₂ (fixV G₁)) < A ∧
        fixV (autSub G₂ (fixV G₁)) < B ∧ XMod.IsInv ↥(autSub G₂ (fixV G₁)) A ∧
        XMod.IsInv ↥(autSub G₂ (fixV G₁)) B ∧ A ⊔ B = ⊤ ∧ A ⊓ B = fixV (autSub G₂ (fixV G₁))) ∧
      BinaryNaturalSL (autSub G₂ (fixV G₁))
        (modComm (autSub G₂ (fixV G₁)) ⊤ ⊔ fixV (autSub G₂ (fixV G₁)))
        (fixV (autSub G₂ (fixV G₁))) 3 1) :
    Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2))) ∧ commV G₂ ≤ fixV G₁ ∧
      Nat.card ↥(fixV G₁) = 2 ^ 4 * Nat.card ↥(fixV G) ∧
      (¬ ∃ A B : Subgroup V, fixV G < A ∧ fixV G < B ∧ XMod.IsInv ↥G₂ A ∧ XMod.IsInv ↥G₂ B ∧
        A ⊔ B = fixV G₁ ∧ A ⊓ B = fixV G) ∧
      BinaryNaturalSL G₂ (modComm G₂ (fixV G₁) ⊔ fixV G) (fixV G) 3 1 := by
  obtain ⟨⟨eH⟩, -, hcard, hdec, hnat⟩ := hc
  have hι := (fixV G₁).subtype_injective
  have hF := map_fixV_eq hstab hfix
  refine ⟨⟨(resEquiv hstab hfaith).trans eH⟩, ?_, ?_, ?_, ?_⟩
  · exact hcomm
  · have h1 : Nat.card ↥(fixV G₁) = Nat.card ↥(⊤ : Subgroup ↥(fixV G₁)) := by
      rw [Subgroup.card_top]
    have h2 : Nat.card ↥(fixV G) = Nat.card ↥(fixV (autSub G₂ (fixV G₁))) := by
      rw [← hF, Subgroup.card_map_of_injective hι]
    rw [h1, h2]
    exact hcard
  · rintro ⟨A, B, hA, hB, hAi, hBi, hsup, hinf⟩
    apply hdec
    have hAle : A ≤ fixV G₁ := hsup ▸ le_sup_left
    have hBle : B ≤ fixV G₁ := hsup ▸ le_sup_right
    have hAm : (A.comap (fixV G₁).subtype).map (fixV G₁).subtype = A := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.2 hAle
    have hBm : (B.comap (fixV G₁).subtype).map (fixV G₁).subtype = B := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.2 hBle
    have hinv : ∀ {A₀ : Subgroup ↥(fixV G₁)},
        XMod.IsInv ↥G₂ (A₀.map (fixV G₁).subtype) → XMod.IsInv ↥(autSub G₂ (fixV G₁)) A₀ := by
      intro A₀ hA₀ a l hl
      obtain ⟨g, rfl⟩ := (resEquiv hstab hfaith).surjective a
      have := hA₀ g ((fixV G₁).subtype l) ⟨l, hl, rfl⟩
      obtain ⟨l', hl', hl'e⟩ := this
      have : l' = (resEquiv hstab hfaith g : MulAut ↥(fixV G₁)) l := by
        apply hι
        exact hl'e.trans (res_compat hstab hfaith g l).symm
      show (resEquiv hstab hfaith g : MulAut ↥(fixV G₁)) l ∈ A₀
      rw [← this]
      exact hl'
    refine ⟨A.comap (fixV G₁).subtype, B.comap (fixV G₁).subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_lt_map_iff_of_injective hι, hAm, hF]; exact hA
    · rw [← Subgroup.map_lt_map_iff_of_injective hι, hBm, hF]; exact hB
    · exact hinv (by rw [hAm]; exact hAi)
    · exact hinv (by rw [hBm]; exact hBi)
    · apply Subgroup.map_injective hι
      rw [Subgroup.map_sup, hAm, hBm, hsup, map_top_eq]
    · apply Subgroup.map_injective hι
      rw [Subgroup.map_inf _ _ (fixV G₁).subtype hι, hAm, hBm, hinf, hF]
  · obtain ⟨K, hK, hf, hc, hr⟩ := hnat
    refine ⟨K, hK, hf, hc, ?_⟩
    have := realizes_transport hstab hfaith hr
    rwa [Subgroup.map_sup, map_modComm_eq hstab, hF] at this


end SplitTransport

end FFC

end CFSG.Quasithin
