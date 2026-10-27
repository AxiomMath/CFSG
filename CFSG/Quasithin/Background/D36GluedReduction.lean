module

public import CFSG.Quasithin.Background.D36GluedOffender
public import CFSG.Quasithin.Background.D36GluedSupport
public import CFSG.Quasithin.Background.F918M6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Shapes

variable {Y : Type} [CommGroup Y]

@[expose] def OffenderShape (A : Subgroup (MulAut Y)) (U U' : Subgroup Y) : Prop :=
  1 ≤ rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ∧
    rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥(A ⊓ stabSub U) ∧
    (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U')) ≤
      2 * rk ↥(A ⊓ stabSub U) + 2

@[expose] def DiagShape (A L₀ : Subgroup (MulAut Y)) (U U' : Subgroup Y) : Prop :=
  rk ↥(U ⊓ U') ≤ rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) ∧
    rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) ≤ rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ∧
    rk ↥(A ⊓ stabSub U) * (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) +
      (rk ↥(A ⊓ stabSub U) + 1) *
        (rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) - rk ↥(U ⊓ U')) ≤ rk ↥U - rk ↥(U ⊓ U') ∧
    (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U')) ≤
      2 * rk ↥(A ⊓ stabSub U) + 2 ∧
    (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) +
      (rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) - rk ↥(U ⊓ U')) ≤ 2 ∧
    rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) < rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))

@[expose] def CubicBound (X A : Subgroup (MulAut Y)) (U U' : Subgroup Y) : Prop :=
  ∀ E : Subgroup (MulAut Y), IsA2 X E → commSeries E 3 = ⊥ → (∀ e ∈ E, ∀ u ∈ U', e u = u) →
    ((rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U'))) * rk ↥E ≤
      (rk ↥(A ⊓ stabSub U) + 1) * (rk ↥U - rk ↥(U ⊓ fixV E)) ∧
    rk ↥E ≤ rk ↥(A ⊓ stabSub U)

variable [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

theorem GluedSwap.cubicBound (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) :
    CubicBound X A U U' := fun _ hE hE3 hEU' =>
  ⟨h.compare_cubic hE hE3 hEU', h.rk_le_of_cubic hY hE hE3 hEU'⟩

theorem GluedSwap.offenderShape (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) :
    OffenderShape A U U' :=
  h.shape_B hY

theorem GluedSwap.diagShape (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀X : L₀ ≤ X)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) : DiagShape A L₀ U U' :=
  h.diag_bound hY hL₀X hL₀ hdiag

end Shapes

section Normalized

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d36_gluedSwap (hL38 : D3L38) (n : D36Norm M Mp T L V t) {A : Subgroup (MulAut W)}
    (hA : A ≤ T) (hQ : autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)))
    (hAU : ¬ A ≤ stabSub (commSub (orbSup T V) L)) :
    GluedSwap (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) := by
  obtain ⟨hP, hrank, -⟩ := d36_gluedPair_with_rank_centralizer hL38 n
  have hQ' := d36_qhatStar_transfer n hA hQ
  have hUU' : (commSub (orbSup T V) L).subgroupOf (orbSup T V) ≠
      ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) := by
    intro h
    rw [← h, inf_idem] at hrank
    omega
  have hAU' : ¬ autSub A (orbSup T V) ≤
      stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V)) := by
    intro hle
    apply hAU
    have hUV : commSub (orbSup T V) L ≤ orbSup T V := by
      rw [d36_U_eq hL38 n]
      exact orbSup_le fun s hs => map_le_orbSup hs.1
    intro a ha u
    have haS : a ∈ stabSub (orbSup T V) := le_stabSub_orbSup T V (hA ha)
    by_cases hu : u ∈ orbSup T V
    · exact hle (mem_autSub.mpr ⟨⟨a, haS⟩, ha, rfl⟩) ⟨u, hu⟩
    · have h1 : u ∉ commSub (orbSup T V) L := fun h => hu (hUV h)
      have h2 : a u ∉ orbSup T V := fun h => hu ((haS u).mp h)
      exact ⟨fun h => absurd (hUV h) h2, fun h => absurd h h1⟩
  exact ⟨hP, hUU', hrank, hQ', hAU'⟩

theorem d36_exp_VT (n : D36Norm M Mp T L V t) : ∀ y : ↥(orbSup T V), y ^ 2 = 1 := fun y =>
  Subtype.ext (by simpa using n.std.hyp.exp y.1)

@[expose] def GluedDiag (L A : Subgroup (MulAut W)) (VT U : Subgroup W) : Prop :=
  ∀ b ∈ autSub A VT ⊓ stabSub (U.subgroupOf VT), ∃ l ∈ autSub L VT,
    ∀ u ∈ U.subgroupOf VT, b u = l u

theorem d36_L_le_X (n : D36Norm M Mp T L V t) :
    autSub L (orbSup T V) ≤ autSub (Mp ⊔ T) (orbSup T V) :=
  autSub_mono (le_trans (d36t_L_le_Mp n) le_sup_left) _

theorem d36_L_fix_Ut' (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ l ∈ autSub L (orbSup T V), ∀ u ∈
      ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V), l u = u := by
  intro l hl u hu
  obtain ⟨g, hgL, rfl⟩ := mem_autSub.mp hl
  obtain ⟨u₀, hu₀, hu₀e⟩ := (Subgroup.mem_subgroupOf.mp hu : (u : W) ∈ _)
  apply Subtype.ext
  rw [resHom_apply, ← hu₀e]
  exact d36t_L_fix_Ut hL38 n u₀ hu₀ g hgL

theorem d36_offenderShape (hL38 : D3L38) (n : D36Norm M Mp T L V t) {A : Subgroup (MulAut W)}
    (hA : A ≤ T) (hQ : autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)))
    (hAU : ¬ A ≤ stabSub (commSub (orbSup T V) L)) :
    OffenderShape (autSub A (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) :=
  (d36_gluedSwap hL38 n hA hQ hAU).offenderShape (d36_exp_VT n)

theorem d36_cubicBound (hL38 : D3L38) (n : D36Norm M Mp T L V t) {A : Subgroup (MulAut W)}
    (hA : A ≤ T) (hQ : autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)))
    (hAU : ¬ A ≤ stabSub (commSub (orbSup T V) L)) :
    CubicBound (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) :=
  (d36_gluedSwap hL38 n hA hQ hAU).cubicBound (d36_exp_VT n)

theorem d36_diagShape (hL38 : D3L38) (n : D36Norm M Mp T L V t) {A : Subgroup (MulAut W)}
    (hA : A ≤ T) (hQ : autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)))
    (hAU : ¬ A ≤ stabSub (commSub (orbSup T V) L))
    (hD : GluedDiag L A (orbSup T V) (commSub (orbSup T V) L)) :
    DiagShape (autSub A (orbSup T V)) (autSub L (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) :=
  (d36_gluedSwap hL38 n hA hQ hAU).diagShape (d36_exp_VT n) (d36_L_le_X n)
    (d36_L_fix_Ut' hL38 n) hD

end Normalized

@[expose] def D36GluedDiag : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ¬ IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    ∀ A : Subgroup (MulAut W), A ≤ T → autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      ¬ A ≤ stabSub (commSub (orbSup T V) L) →
      GluedDiag L A (orbSup T V) (commSub (orbSup T V) L) →
      CubicBound (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) →
      DiagShape (autSub A (orbSup T V)) (autSub L (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) → False

@[expose] def D36GluedNonDiag : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ¬ IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    ∀ A : Subgroup (MulAut W), A ≤ T → autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      ¬ A ≤ stabSub (commSub (orbSup T V) L) →
      ¬ GluedDiag L A (orbSup T V) (commSub (orbSup T V) L) →
      CubicBound (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) →
      OffenderShape (autSub A (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) → False

theorem d36ActsGlued_of_cases (hL38 : D3L38) (h1 : D36GluedDiag) (h2 : D36GluedNonDiag) :
    D36ActsGlued := by
  intro W _ _ M Mp T L V t n hd A hA hQ
  by_contra hAU
  by_cases hdiag : GluedDiag L A (orbSup T V) (commSub (orbSup T V) L)
  · exact h1 W M Mp T L V t n hd A hA hQ hAU hdiag (d36_cubicBound hL38 n hA hQ hAU)
      (d36_diagShape hL38 n hA hQ hAU hdiag)
  · exact h2 W M Mp T L V t n hd A hA hQ hAU hdiag (d36_cubicBound hL38 n hA hQ hAU)
      (d36_offenderShape hL38 n hA hQ hAU)

end CFSG.Quasithin
