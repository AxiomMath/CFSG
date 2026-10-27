module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

variable {V : Type*} [CommGroup V]

namespace B6

theorem isElemAbelian2_mono {A B : Subgroup (MulAut V)} (h : IsElemAbelian2 A) (hBA : B ≤ A) :
    IsElemAbelian2 B :=
  ⟨fun a ha b hb => h.1 a (hBA ha) b (hBA hb), fun a ha => h.2 a (hBA ha)⟩

theorem isElemAbelian2_conjSub {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) (g : MulAut V) :
    IsElemAbelian2 (conjSub g A) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [mem_conjSub] at ha hb
    have := h.1 _ ha _ hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group
  · rw [mem_conjSub] at ha
    have := h.2 _ ha
    have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    calc a ^ 2 = (g * (g⁻¹ * a * g) * g⁻¹) ^ 2 := by rw [← e]
      _ = g * (g⁻¹ * a * g) ^ 2 * g⁻¹ := conj_pow
      _ = 1 := by rw [this]; group

theorem fixV_conjSub (g : MulAut V) (A : Subgroup (MulAut V)) :
    fixV (conjSub g A) = (fixV A).map g.toMonoidHom :=
  CFSG.Quasithin.fixV_map_conj_eq A g

theorem card_fixV_conjSub (g : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card (fixV (conjSub g A)) = Nat.card (fixV A) :=
  CFSG.Quasithin.ConjTransport.card_fixV_map_conj A g

theorem isFFStarOffender_conjSub {X A : Subgroup (MulAut V)} (h : IsFFStarOffender X A)
    {g : MulAut V} (hg : g ∈ X) : IsFFStarOffender X (conjSub g A) :=
  isFFStarOffender_map_conj h hg

theorem exists_isFFStarOffender [Finite V] {X : Subgroup (MulAut V)} (h : IsFFModule X) :
    ∃ A, IsFFStarOffender X A := by
  obtain ⟨A, hAX, hA0, hAe, hle⟩ := h
  obtain ⟨B, -, hB, -⟩ := B1.exists_offender_below (X := X) ⟨hAX, hA0, hAe⟩ 0 (by simpa using hle)
  exact ⟨B, hB⟩

theorem ffJ_le (X : Subgroup (MulAut V)) : ffJ X ≤ X := iSup₂_le fun _ hA => hA.1

theorem le_ffJ {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) : A ≤ ffJ X :=
  le_iSup₂ (f := fun (A : Subgroup (MulAut V)) (_ : IsFFStarOffender X A) => A) A hA

theorem le_normalizer_ffJ (X : Subgroup (MulAut V)) :
    X ≤ Subgroup.normalizer (ffJ X : Set (MulAut V)) := by
  have key : ∀ g ∈ X, conjSub g (ffJ X) ≤ ffJ X := fun g hg => by
    unfold ffJ
    simp only [OrderIso.map_iSup]
    exact iSup₂_le fun A hA => le_iSup₂_of_le _ (isFFStarOffender_conjSub hA hg) le_rfl
  intro g hg
  exact mem_normalizer_of_conjSub_le (key g hg) (key g⁻¹ (X.inv_mem hg))

theorem isPGroup_two_of_isElemAbelian2 {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) :
    IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using h.2 g g.2)⟩

end B6

namespace MinParabolic

variable [Finite V] {X T M : Subgroup (MulAut V)}

theorem twoResidual_le_ffJ (h : MinParabolic X T M) (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) :
    twoResidual X ≤ ffJ X := by
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF
  rcases h.le_kerIn_or_twoResidual_le (B6.ffJ_le X) (B6.le_normalizer_ffJ X) with hJ | hK
  · exfalso
    have : ffJ X ≤ pCoreOf 2 X := by
      refine iSup₂_le fun B hB => ?_
      exact h.le_pCoreOf_of_isPGroup_of_le_kerIn
        (B6.isPGroup_two_of_isElemAbelian2 hB.2.2.1) ((B6.le_ffJ hB).trans hJ)
    rw [hO] at this
    exact hA.2.1 (le_bot_iff.mp ((B6.le_ffJ hA).trans this))
  · exact hK

theorem eq_sup_ffJ (h : MinParabolic X T M) (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) :
    X = ffJ X ⊔ T := by
  refine le_antisymm ?_ (sup_le (B6.ffJ_le X) h.isSylow.1)
  calc X = T ⊔ twoResidual X := (sup_twoResidual_eq h.isSylow).symm
    _ ≤ T ⊔ ffJ X := sup_le_sup_left (h.twoResidual_le_ffJ hO hFF) T
    _ = ffJ X ⊔ T := sup_comm _ _

end MinParabolic

end CFSG.Quasithin
