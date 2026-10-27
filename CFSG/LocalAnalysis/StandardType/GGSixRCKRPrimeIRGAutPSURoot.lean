module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSUAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgUC_isUTransGroup_range {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    {i : Fin n} (hi : i ≠ Fin.rev i) :
    CFSG.Timmesfeld.LieEmbed.IsUTransGroup σ (Pi.single i 1)
      (Unitary.longRootHom σ hi).range := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · constructor
    · rintro ⟨c, rfl⟩
      exact ⟨(c.toAdd : F), c.toAdd.2, by
        rw [CFSG.Timmesfeld.LieEmbed.suMat_apply, Unitary.coe_longRootHom,
          CFSG.Timmesfeld.LieEmbed.uTrans_single]⟩
    · rintro ⟨c, hc, hx⟩
      refine ⟨Multiplicative.ofAdd ⟨c, hc⟩, ?_⟩
      refine CFSG.Timmesfeld.LieEmbed.suMat_injective σ ?_
      rw [CFSG.Timmesfeld.LieEmbed.suMat_apply, Unitary.coe_longRootHom, hx,
        CFSG.Timmesfeld.LieEmbed.uTrans_single]
      rfl
  · exact ⟨Unitary.longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩), by
      rw [CFSG.Timmesfeld.LieEmbed.suMat_apply, Unitary.coe_longRootHom,
        CFSG.Timmesfeld.LieEmbed.uTrans_single]
      rfl⟩

private theorem irgUC_rootGroup_eq_range {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    (hσ : ∀ c, σ (σ c) = c) {i : Fin n} (hi : i ≠ Fin.rev i) {γ : Fin (n / 2) → ℤ}
    (hγ : Unitary.toStd n γ = 2 • Unitary.weight n i) :
    Unitary.rootGroup σ hσ n γ = (Unitary.longRootHom σ hi).range :=
  CFSG.Timmesfeld.LieEmbed.IsUTransGroup.eq
    (CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_long' hσ hi hγ)
    (irgUC_isUTransGroup_range hi)

theorem irgU_longRoot_shape {n g : ℕ}
    (hK : Nat.card (irgU_F g) = (2 ^ g) ^ 2)
    (β' : Fin (Unitary.rootDatum (p := 2) (f := g) hK n).rank → ℤ)
    (hβ' : β' ∈ (Unitary.rootDatum (p := 2) (f := g) hK n).roots)
    (hlong : GGLongRoot (Unitary.rootDatum (p := 2) (f := g) hK n) β') :
    ∃ i : Fin n, ∃ hi : i ≠ Fin.rev i,
      Unitary.rootGroup (irgU_sigma g) (irgU_sigma_involutive g hK) n β' =
        (longRootHom (irgU_sigma g) hi).range ∧
      Unitary.rootGroup (irgU_sigma g) (irgU_sigma_involutive g hK) n (-β') =
        (longRootHom (irgU_sigma g) (i := Fin.rev i)
          (fun h : Fin.rev i = Fin.rev (Fin.rev i) => hi (Fin.rev_injective h))).range := by
  obtain ⟨i, hi, hβi⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_weight_of_ggLongRoot hK hβ' hlong
  let b : Fin (n / 2) → ℤ := β'
  have hb : b = β' := rfl
  have hβib : Unitary.toStd n b = 2 • Unitary.weight n i := by
    rw [hb]
    exact hβi
  have hneg : Unitary.toStd n (-b) = 2 • Unitary.weight n (Fin.rev i) := by
    have hsum : Unitary.toStd n (-b) + Unitary.toStd n b = 0 := by
      have h1 := SUExtras.toStd_add' (n := n) (-b) b
      rw [neg_add_cancel, SUExtras.toStd_zero'] at h1
      exact h1.symm
    rw [eq_neg_of_add_eq_zero_left hsum, hβib, SUExtras.weight_rev', smul_neg]
  refine ⟨i, hi, ?_, ?_⟩
  · simpa only [hb] using irgUC_rootGroup_eq_range (irgU_sigma_involutive g hK) hi hβib
  · change Unitary.rootGroup (irgU_sigma g) (irgU_sigma_involutive g hK) n (-b) =
      (longRootHom (irgU_sigma g) (i := Fin.rev i)
        (fun h : Fin.rev i = Fin.rev (Fin.rev i) => hi (Fin.rev_injective h))).range
    exact irgUC_rootGroup_eq_range (irgU_sigma_involutive g hK)
      (fun h : Fin.rev i = Fin.rev (Fin.rev i) => hi (Fin.rev_injective h)) hneg

end CFSG.StandardType.RCKRP
