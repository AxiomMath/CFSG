module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem IsMinFam16.pCoreOf_conjClosure_eq_iSub16 (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (iSub16 V H) φ)
    (hO : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) :
    pCoreOf 2 (conjClosure V H) = iSub16 V H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Fam16 M U S H := hH.fam16
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun g hg z hz => H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  refine le_antisymm ?_ ?_
  ·
    let N : Subgroup X := (CFSG.pCore 2 ↥(conjClosure V H)).map φ
    have hNnorm : N.Normal :=
      Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := ↥(conjClosure V H))) φ hφ.surjective
    have hN2 : IsPGroup 2 N :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(conjClosure V H))).map φ
    have hNbot : N = ⊥ := hO N hNnorm hN2
    intro q hq
    have hqK : q ∈ conjClosure V H :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 (conjClosure V H) hq
    have hqcore : (⟨q, hqK⟩ : ↥(conjClosure V H)) ∈ CFSG.pCore 2 ↥(conjClosure V H) := by
      have hq' : q ∈ (CFSG.pCore 2 ↥(conjClosure V H)).map (conjClosure V H).subtype := hq
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq'
      have hx_eq : x = ⟨q, hqK⟩ := Subtype.ext (by simpa using hxq)
      rwa [hx_eq] at hx
    have hmemN : φ ⟨q, hqK⟩ ∈ N := Subgroup.mem_map.mpr ⟨⟨q, hqK⟩, hqcore, rfl⟩
    rw [hNbot] at hmemN
    exact (hφ.ker_iff ⟨q, hqK⟩).mp (Subgroup.mem_bot.mp hmemN)
  ·
    have hIK : iSub16 V H ≤ conjClosure V H := conjClosure_mono inf_le_left le_rfl
    have hI2 : IsPGroup 2 (iSub16 V H) := (h.isElemAbelian_iSub16 h1 hS hF).isPGroup
    have hInorm : ((iSub16 V H).subgroupOf (conjClosure V H)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hIK).mpr
        (hKH.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H))
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hIK hInorm hI2

end CFSG.LocalAnalysis.WeakClosure81

end
