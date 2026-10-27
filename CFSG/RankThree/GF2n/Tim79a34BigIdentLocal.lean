module

public import CFSG.RankThree.GF2n.Tim79a34BigAssembly2
public import CFSG.RankThree.GF2n.Tim79a34BigDelta
public import CFSG.RankThree.GF2n.Tim79a34BigEpsGe
public import CFSG.RankThree.GF2n.Tim79a34BigDirectTrans

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

theorem bigIdent_centralizer_X_le_W (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G)
    (hH : BigEndHyp M V Q P H) {y : G} (hy : y ∈ xOf V H)
    (hfix : ∀ w ∈ wOf V H, y * w * y⁻¹ = w) : y ∈ wOf V H := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  obtain ⟨n, f, Φ, ψ, -, -, hequiv, -, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have hfix' : ∀ β, SpExtras.mat n (GaloisField 2 f)
      (Φ.symm (xToXbar hc.V_le_H ⟨y, hy⟩)) *ᵥ β = β := by
    intro β
    refine psiElt_injective ψ ?_
    exact (hNat.equiv ⟨y, hy⟩ β).trans (hfix _ (psiElt_mem ψ β))
  have hmat : SpExtras.mat n (GaloisField 2 f) (Φ.symm (xToXbar hc.V_le_H ⟨y, hy⟩)) = 1 :=
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [Matrix.one_mulVec]
      exact hfix' v
  have hτ : Φ.symm (xToXbar hc.V_le_H ⟨y, hy⟩) = 1 :=
    SpExtras.mat_injective (hmat.trans (map_one (SpExtras.mat n (GaloisField 2 f))).symm)
  have h1 : xToXbar hc.V_le_H ⟨y, hy⟩ = 1 := by
    rw [(Φ.symm_apply_eq).mp hτ, map_one]
  have h2 : piBar V H (Subgroup.inclusion (xOf_le_H hc.V_le_H) ⟨y, hy⟩) = 1 :=
    congrArg Subtype.val h1
  exact (piBar_eq_one_iff _).mp h2

theorem bigIdent_comm_mem_W (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H)
    {c : G} (hcM : c ∈ M) (hcW : ∀ w ∈ wOf V H, c * w = w * c) {x : G} (hx : x ∈ xOf V H) :
    ⁅c, x⁆ ∈ wOf V H := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hWc : conjSubgroup c (wOf V H) = wOf V H := by
    refine conjSubgroup_eq_of_le fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := hz
    have : c * w * c⁻¹ = w := by rw [hcW w hw]; group
    simpa [MulAut.conj_apply, this] using hw
  have hcX : conjSubgroup c (xOf V H) = xOf V H :=
    bigNormalizerXStatement_of_natural hZ hN G M V Q P H hH c hcM hWc
  have hxX' : c * x * c⁻¹ ∈ xOf V H := by
    have : c * x * c⁻¹ ∈ conjSubgroup c (xOf V H) := ⟨x, hx, rfl⟩
    rwa [hcX] at this
  have hWn : ∀ h ∈ H, ∀ w ∈ wOf V H, h * w * h⁻¹ ∈ wOf V H := fun h hh w hw =>
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hh) w).mp hw
  have hxH : x ∈ H := xOf_le_H hVH hx
  have hy : x⁻¹ * (c * x * c⁻¹) ∈ xOf V H := (xOf V H).mul_mem ((xOf V H).inv_mem hx) hxX'
  have hyW : x⁻¹ * (c * x * c⁻¹) ∈ wOf V H := by
    refine bigIdent_centralizer_X_le_W hZ hN G M V Q P H hH hy fun w hw => ?_
    have h1 : x * w * x⁻¹ ∈ wOf V H := hWn x hxH w hw
    have h2 : c * (x * w * x⁻¹) * c⁻¹ = x * w * x⁻¹ := by rw [hcW _ h1]; group
    calc x⁻¹ * (c * x * c⁻¹) * w * (x⁻¹ * (c * x * c⁻¹))⁻¹
        = x⁻¹ * (c * (x * (c⁻¹ * w * c) * x⁻¹) * c⁻¹) * x := by group
      _ = w := by
        have h3 : c⁻¹ * w * c = w := by rw [mul_assoc, ← hcW w hw]; group
        rw [h3, h2]
        group
  have e : ⁅c, x⁆ = x * (x⁻¹ * (c * x * c⁻¹)) * x⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact hWn x hxH _ hyW

end CFSG.RankThree.GF2n.Tim79a
