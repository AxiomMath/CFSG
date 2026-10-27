module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofAut
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndMem
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndCore
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndCompat

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.StandardType.SpJoin
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem ggSpJoinEndNodeSomeInput_of_inputs (hMp : GGInnerDiagMpInput) (hlift : GGSpLiftInput)
    (hsub : GGNbrSubcomponentInput) : GGSpJoinEndNodeSomeInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hN.2.1; omega⟩
  subst hm
  have hm3 : 3 ≤ m := by have := hN.2.1; omega
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hnbr : GGNbr p B x D J y K := hN.2.2.2.1
  obtain ⟨hyL, hxK⟩ := ggSpEnd_mem hMp hlift hcfg hOp hInn hNoTr hN
  obtain ⟨φ₀, hφ₀inj, hφ₀range⟩ := hlift G L (m + 1) f hN.2.1 hInn.1.1 hN.1
  have hmarkK : GGInnerDiagOn Bs K := hInn.2 y K hnbr
  obtain ⟨φK, hφKinj, hφKrange⟩ := hlift G K (m + 1) f hN.2.1 hmarkK.1 hN.2.2.2.2.1
  have hLeviL := ggSpLeviInputAtL_of_inputs hMp hlift
  have hLeviK := ggSpLeviInputAtNbr_of hMp hlift hsub hLeviL
  obtain ⟨ψ₁, hψ₁inj, hψ₁range, hψ₁J⟩ :=
    hLeviL G p B Bs x L D J m f y K hcfg hOp hInn hNoTr hN φ₀ hφ₀inj hφ₀range
  obtain ⟨ψ₂, hψ₂inj, hψ₂range, hψ₂J⟩ :=
    hLeviK G p B Bs x L D J m f y K hcfg hOp hInn hNoTr hN y K hnbr le_sup_right
      φK hφKinj hφKrange
  obtain ⟨φ₂, hφ₂inj, hφ₂range, hφ₂β⟩ :=
    spEnd_exists_compat_lift hm3 ψ₁ ψ₂ hψ₁inj hψ₂inj (hψ₁J.trans hψ₂J.symm)
  have hφ₂rangeK : φ₂.range = K := hφ₂range.trans hψ₂range
  obtain ⟨_, _, _, hJD, _, hxD⟩ := hcfg.stdSub_facts
  have hyD : y ∈ D := by
    rw [hnbr.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyL' : y ∈ ψ₁.range := by rw [hψ₁range]; exact hyL
  obtain ⟨u₁, hu₁⟩ := hyL'
  have hu₁c : ∀ h : StatedSp m (GaloisField 2 f),
      u₁ * spLeviBlock m (GaloisField 2 f) h = spLeviBlock m (GaloisField 2 f) h * u₁ := by
    intro h
    apply hψ₁inj
    rw [map_mul, map_mul, hu₁]
    have hJmem : ψ₁ (spLeviBlock m (GaloisField 2 f) h) ∈ J := by
      rw [← hψ₁J]
      exact ⟨h, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hJD hJmem) y hyD
  obtain ⟨g, hg_eq⟩ := spEnd_exists_lam_zero_of_commute_levi (m := m) (by omega) hu₁c
  have hy : y = ψ₁ (lam (0 : Fin (m + 1)) g) := by rw [← hu₁, hg_eq]
  have hxK' : x ∈ φ₂.range := by rw [hφ₂rangeK]; exact hxK
  obtain ⟨u₂, hu₂⟩ := hxK'
  have hu₂c : ∀ h : StatedSp m (GaloisField 2 f),
      u₂ * spLeviBlock m (GaloisField 2 f) h = spLeviBlock m (GaloisField 2 f) h * u₂ := by
    intro h
    apply hφ₂inj
    rw [map_mul, map_mul, hu₂, hφ₂β h]
    have hJmem : ψ₁ (spLeviBlock m (GaloisField 2 f) h) ∈ J := by
      rw [← hψ₁J]
      exact ⟨h, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hJD hJmem) x hxD
  obtain ⟨g₂, hg₂_eq⟩ := spEnd_exists_lam_zero_of_commute_levi (m := m) (by omega) hu₂c
  have hx₂ : x = φ₂ (lam (0 : Fin (m + 1)) g₂) := by rw [← hu₂, hg₂_eq]
  have hyBs : y ∈ Bs := hBs.1 hnbr.1.2.1
  have hy1 : y ≠ 1 := hnbr.1.2.2.1
  have hyp : y ^ p = 1 := hBs.2.1.2 y hyBs
  have hxB : x ∈ B := (hcfg.1.2.2.2.2.2.2.1).2.1
  have hxBs : x ∈ Bs := hBs.1 hxB
  have hx1 : x ≠ 1 := (hcfg.1.2.2.2.2.2.2.1).2.2.1
  have hxp : x ^ p = 1 := hBs.2.1.2 x hxBs
  have hcomp₁inj : Function.Injective (ψ₁.comp (lam (0 : Fin (m + 1)))) :=
    hψ₁inj.comp (lam_injective (0 : Fin (m + 1)))
  have hcomp₂inj : Function.Injective (φ₂.comp (lam (0 : Fin (m + 1)))) :=
    hφ₂inj.comp (lam_injective (0 : Fin (m + 1)))
  have hg : g ^ p = 1 := by
    apply hcomp₁inj
    show ψ₁ (lam (0 : Fin (m + 1)) (g ^ p)) = ψ₁ (lam (0 : Fin (m + 1)) 1)
    simp only [map_pow, map_one]
    rw [← hy]
    exact hyp
  have hg1 : g ≠ 1 := by
    intro h
    apply hy1
    rw [hy, h]
    simp
  have hg₂ : g₂ ^ p = 1 := by
    apply hcomp₂inj
    show φ₂ (lam (0 : Fin (m + 1)) (g₂ ^ p)) = φ₂ (lam (0 : Fin (m + 1)) 1)
    simp only [map_pow, map_one]
    rw [← hx₂]
    exact hxp
  have hg₂1 : g₂ ≠ 1 := by
    intro h
    apply hx1
    rw [hx₂, h]
    simp
  obtain ⟨φ', hφ'inj, hφ'range, hφ'β, k, hk⟩ :=
    spEnd_exists_plane_zero_correction hp hp2 φ₂ hφ₂inj hg hg1 hg₂ hg₂1
  have hφ'rangeK : φ'.range = K := hφ'range.trans hφ₂rangeK
  have hβ' : ∀ h : StatedSp m (GaloisField 2 f),
      ψ₁ (spLeviBlock m (GaloisField 2 f) h) = φ' (spLeviBlock m (GaloisField 2 f) h) := by
    intro h
    exact (hφ₂β h).symm.trans (hφ'β h).symm
  have hx : x = φ' (lam (0 : Fin (m + 1)) (g ^ k)) := hx₂.trans hk
  have hLcomp : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hKpcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hnbr.1.2.2.2.2.1
  obtain ⟨T, hT, hnode, hKT⟩ :=
    spEnd_exists_endNode_of_compatible_lifts hp hp2 hm3 hLcomp hKpcomp ψ₁ φ' hψ₁inj hφ'inj
      hψ₁range hφ'rangeK hβ' hg hg1 hy hx hx1
  refine ⟨ψ₁, hψ₁inj, hψ₁range, T, hT, hnode, ?_⟩
  rw [hKT]
  exact le_sup_right

end CFSG.StandardType
