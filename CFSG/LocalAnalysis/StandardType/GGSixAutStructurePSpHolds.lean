module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpCore
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin

namespace AutPSp

section Iso

variable {n : ℕ} {K : Type} [Field K] {G : Type*} [Group G] {ψ : StatedSp n K →* G}

theorem ker_eq_spScalars (hker : ψ.ker ≤ Subgroup.center (StatedSp n K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) : ψ.ker = spScalars n K := by
  change ψ.ker = (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)
  rw [← CFSG.LieType.Universal.Symplectic.center_eq n K]
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

@[expose] noncomputable def projEquiv (hker : ψ.ker ≤ Subgroup.center (StatedSp n K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) : StatedProj (StatedSp n K) ≃* ψ.range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq_spScalars hker hC).symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)

theorem projEquiv_proj (hker : ψ.ker ≤ Subgroup.center (StatedSp n K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (y : StatedSp n K) :
    ((projEquiv hker hC (proj n K y) : ψ.range) : G) = ψ y :=
  rfl

theorem exists_conj_elt_of_rootInvolution [Finite K] [CharP K 2] {t : StatedLieTag} {r : G}
    (hr : GGRootInvolution (rootDatum n K) t ψ r) :
    ∃ (ρ : RootSubgroupIndex n) (w : StatedSp n K), r = ψ w * ψ (elt ρ 1) * (ψ w)⁻¹ := by
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  obtain ⟨ρ, hρ⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hρ).mp hz
  have hc : c ≠ 0 := by
    rintro rfl
    rw [elt_zero] at hr2
    simp at hr2
  obtain ⟨h, hh⟩ := exists_conj_elt_one ρ hc
  refine ⟨ρ, u * h, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hh, map_mul, map_inv]
  group

end Iso

end AutPSp

section Family

theorem ggAutStructureAt_PSp : GGAutStructureAt .PSp := by
  intro G _ _ n f ψ G₀ hadm hrank hrange hker _ _ hC hBs _ r hr
  have hn2 : 2 ≤ n := hrank
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  obtain ⟨p, Bs, hp, hp2, hBsE, hcard, -, hBsI⟩ := hBs
  have hn4 : 4 ≤ n :=
    AutPSp.four_le_of_bstar (K := GaloisField 2 f) hn2 ψ hker hC' hp hp2 hBsE hcard hBsI
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ρ, w, hw⟩ := AutPSp.exists_conj_elt_of_rootInvolution (K := GaloisField 2 f) hr
  set Θ : StatedProj (StatedSp n (GaloisField 2 f)) ≃* G₀ :=
    (AutPSp.projEquiv hker hC').trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨I', C', h1, h2, h3, h4, h5, h6⟩ :=
    AutPSL.autStructure_congr Θ (r := proj n (GaloisField 2 f) (elt ρ 1))
      ggSix_conj_range_normal le_rfl (by rw [Subgroup.relIndex_self]; exact odd_one)
      (AutPSp.exists_mul_compl (by omega)) AutPSp.inn_inf_compl
      (fun c hc _ _ e he => AutPSp.goodAut_conj (by omega) ρ hc (AutPSp.compl_core hc) he)
  refine ⟨I', C', h1, h2, h3, h4, h5, fun c hc hc2 hc1 e he => ?_⟩
  have hr' : r = Θ (proj n (GaloisField 2 f) w) * Θ (proj n (GaloisField 2 f) (elt ρ 1)) *
      (Θ (proj n (GaloisField 2 f) w))⁻¹ := by
    apply Subtype.ext
    rw [hw]
    rfl
  rw [ggGoodOuterAut_iff, hr']
  exact (h6 c hc hc2 hc1 e he).of_conj _

end Family

end CFSG.StandardType
