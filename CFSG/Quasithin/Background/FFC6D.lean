module

public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.FFC4Res

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

namespace B59

section Map

variable {V : Type} [CommGroup V]

theorem res_compat' {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) (g : ↥L) (w : ↥W) :
    W.subtype (((resEquiv hst hf g : ↥(autSub L W)) : MulAut ↥W) w) = (g : MulAut V) (W.subtype w) := rfl

theorem realizes_map {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) {D : FFModel} {U Z : Subgroup ↥W}
    (hr : D.Realizes (autSub L W) U Z) : D.Realizes L (U.map W.subtype) (Z.map W.subtype) := by
  obtain ⟨π, hπ⟩ := hr
  exact ⟨_, RealizesVia.transport W.subtype W.subtype_injective (resEquiv hst hf)
    (res_compat' hst hf) hπ⟩

theorem directSum_map {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) {D : FFModel} {k : ℕ} {U Z : Subgroup ↥W}
    (hd : DirectSumOfCopies (autSub L W) U Z D k) :
    DirectSumOfCopies L (U.map W.subtype) (Z.map W.subtype) D k := by
  obtain ⟨I, π, hZ, hind, hsup, hreal⟩ := hd
  have hι := W.subtype_injective
  refine ⟨fun i => (I i).map W.subtype, (resEquiv hst hf).symm.toMonoidHom.comp π, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Subgroup.map_mono (hZ i)
  · intro i
    have h1 : (Z.map W.subtype ⊔ ⨆ (j : Fin k) (_ : j ≠ i), (I j).map W.subtype) =
        (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j).map W.subtype := by
      rw [Subgroup.map_sup]
      congr 1
      rw [Subgroup.map_iSup]
      congr 1
      ext1 j
      rw [Subgroup.map_iSup]
    show (I i).map W.subtype ⊓
      (Z.map W.subtype ⊔ ⨆ (j : Fin k) (_ : j ≠ i), (I j).map W.subtype) = Z.map W.subtype
    rw [h1, ← Subgroup.map_inf _ _ W.subtype hι, hind i]
  · have h1 : (Z.map W.subtype ⊔ ⨆ i, (I i).map W.subtype) = (Z ⊔ ⨆ i, I i).map W.subtype := by
      rw [Subgroup.map_sup, Subgroup.map_iSup]
    rw [h1, hsup]
  · intro i
    exact RealizesVia.transport W.subtype hι (resEquiv hst hf) (res_compat' hst hf) (hreal i)

end Map

end B59

end FFC

end CFSG.Quasithin
