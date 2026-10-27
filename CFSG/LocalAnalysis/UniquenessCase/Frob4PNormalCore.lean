module

public import CFSG.Open.UniquenessExclusionRankFourMilestoneDefs
public import CFSG.GroupTheory.ABGLocalTools.PStabilityFrattini
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G]

private theorem pPrimeCore_sup_sylow_normal {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hsolv : Group.IsSolvable H) (S : Sylow p H)
    (hab : IsMulCommutative (S : Subgroup H)) :
    (pPrimeCore p H ⊔ (S : Subgroup H)).Normal := by
  classical
  let Q : Subgroup H := pPrimeCore p H
  let π : H →* H ⧸ Q := QuotientGroup.mk' Q
  have hker : π.ker = Q := QuotientGroup.ker_mk' Q
  let Sbar : Sylow p (H ⧸ Q) := S.mapSurjective (QuotientGroup.mk'_surjective Q)
  have hSbar_coe : (Sbar : Subgroup (H ⧸ Q)) = (S : Subgroup H).map π :=
    Sylow.coe_mapSurjective _ _
  have hSbar_comm : IsMulCommutative (Sbar : Subgroup (H ⧸ Q)) := by
    rw [hSbar_coe]
    letI : IsMulCommutative (S : Subgroup H) := hab
    infer_instance
  haveI : IsMulCommutative (Sbar : Subgroup (H ⧸ Q)) := hSbar_comm
  have hsolvQ : Group.IsSolvable (H ⧸ Q) := by infer_instance
  have hcoreQ : pPrimeCore p (H ⧸ Q) = ⊥ := by
    simpa [Q] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) p
  have hfit : fittingSubgroup (H ⧸ Q) = pCore p (H ⧸ Q) := Fitting_eq_pcore _ p hcoreQ
  have hF_le : pCore p (H ⧸ Q) ≤ (Sbar : Subgroup (H ⧸ Q)) :=
    IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := p) (G := H ⧸ Q)) Sbar
  have hSbar_le_cent : (Sbar : Subgroup (H ⧸ Q)) ≤
      Subgroup.centralizer (pCore p (H ⧸ Q) : Set (H ⧸ Q)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact setLike_mul_comm (hF_le hy) hx
  have hcent_le : Subgroup.centralizer (pCore p (H ⧸ Q) : Set (H ⧸ Q)) ≤
      pCore p (H ⧸ Q) := by
    have h := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := H ⧸ Q) hsolvQ
    rwa [hfit] at h
  have hSbar_eq : (Sbar : Subgroup (H ⧸ Q)) = pCore p (H ⧸ Q) :=
    le_antisymm (hSbar_le_cent.trans hcent_le) hF_le
  have hSbar_normal : (Sbar : Subgroup (H ⧸ Q)).Normal := by
    rw [hSbar_eq]; infer_instance
  have hnorm : ((Sbar : Subgroup (H ⧸ Q)).comap π).Normal := hSbar_normal.comap π
  have hcomap : (Sbar : Subgroup (H ⧸ Q)).comap π = (S : Subgroup H) ⊔ Q := by
    rw [hSbar_coe, Subgroup.comap_map_eq, hker]
  rw [hcomap, sup_comm] at hnorm
  simpa [Q] using hnorm

theorem frob4P_sylow_sup_primeCore_normal {p : ℕ} [Fact p.Prime] {M P : Subgroup G}
    (hM : Group.IsSolvable M) (hP : IsSylowOf p P M) (hab : IsMulCommutative P) :
    M ≤ normalizer ((P ⊔ uniqueFourPrimeCore p M : Subgroup G) : Set G) := by
  classical
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  have hPle : P ≤ M := hP.le
  have hQle : uniqueFourPrimeCore p M ≤ M := by
    rw [uniqueFourPrimeCore]; exact relPPrimeCore_le M
  have hS_comm : IsMulCommutative (S : Subgroup ↥M) := by
    rw [hS]
    letI : IsMulCommutative P := hab
    infer_instance
  have hnorm : (pPrimeCore p ↥M ⊔ (S : Subgroup ↥M)).Normal :=
    pPrimeCore_sup_sylow_normal (H := ↥M) hM S hS_comm
  have hQ'sub : (uniqueFourPrimeCore p M).subgroupOf M = pPrimeCore p ↥M := by
    rw [uniqueFourPrimeCore, relPPrimeCore_eq_map (Fact.out : p.Prime) M, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hsub : (P ⊔ uniqueFourPrimeCore p M).subgroupOf M =
      pPrimeCore p ↥M ⊔ (S : Subgroup ↥M) := by
    rw [Subgroup.subgroupOf_sup hPle hQle, hQ'sub, ← hS, sup_comm]
  have hnorm' : ((P ⊔ uniqueFourPrimeCore p M).subgroupOf M).Normal := by
    rw [hsub]; exact hnorm
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hPle hQle)).mp hnorm'

theorem frob4P_primeCore_sup_normal {p : ℕ} [Fact p.Prime] {M P P₀ : Subgroup G}
    (hM : Group.IsSolvable M) (hP : IsSylowOf p P M) (hab : IsMulCommutative P) (hP₀ : P₀ ≤ P)
    (hwc : ∀ g : G, uniqueFourConj g P₀ ≤ P → uniqueFourConj g P₀ = P₀) :
    M ≤ normalizer ((uniqueFourPrimeCore p M ⊔ P₀ : Subgroup G) : Set G) := by
  classical
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  have hPle : P ≤ M := hP.le
  have hQle : uniqueFourPrimeCore p M ≤ M := by
    rw [uniqueFourPrimeCore]; exact relPPrimeCore_le M
  have hS_comm : IsMulCommutative (S : Subgroup ↥M) := by
    rw [hS]
    letI : IsMulCommutative P := hab
    infer_instance
  have hnorm : (pPrimeCore p ↥M ⊔ (S : Subgroup ↥M)).Normal :=
    pPrimeCore_sup_sylow_normal (H := ↥M) hM S hS_comm
  have hQ'sub : (uniqueFourPrimeCore p M).subgroupOf M = pPrimeCore p ↥M := by
    rw [uniqueFourPrimeCore, relPPrimeCore_eq_map (Fact.out : p.Prime) M, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hnormP : (pPrimeCore p ↥M ⊔ P.subgroupOf M).Normal := by
    rwa [hS] at hnorm
  have hPp : IsPGroup p (P.subgroupOf M) := hP.isPGroup.comap_subtype
  have htop : pPrimeCore p ↥M ⊔ normalizer (P.subgroupOf M : Subgroup ↥M) = ⊤ :=
    pPrimeCore_sup_normalizer_eq_top (H := ↥M) hPp hnormP
  have hQ'norm : ((uniqueFourPrimeCore p M).subgroupOf M).Normal := by
    rw [hQ'sub]; infer_instance
  have hM_le_normQ' : M ≤ normalizer (uniqueFourPrimeCore p M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mp hQ'norm
  intro m hm
  let m' : ↥M := ⟨m, hm⟩
  have hm'top : m' ∈ pPrimeCore p ↥M ⊔ normalizer (P.subgroupOf M : Subgroup ↥M) := by
    rw [htop]; exact Subgroup.mem_top m'
  obtain ⟨q, hq, n, hn, hqn⟩ := Subgroup.mem_sup_of_normal_left.mp hm'top
  have hm_eq : m = (q : G) * (n : G) := by
    change (m' : G) = (q : G) * (n : G)
    rw [← hqn]; rfl
  have hqQ' : (q : G) ∈ uniqueFourPrimeCore p M := by
    rw [uniqueFourPrimeCore, relPPrimeCore_eq_map (Fact.out : p.Prime) M]
    exact Subgroup.mem_map_of_mem M.subtype hq
  have hq_norm : (q : G) ∈ normalizer (uniqueFourPrimeCore p M ⊔ P₀ : Subgroup G) :=
    le_normalizer (Subgroup.mem_sup_left hqQ')
  have hn_normP : (n : G) ∈ normalizer (P : Set G) := by
    have hn' : n ∈ (normalizer (P : Set G)).subgroupOf M := by
      rwa [Subgroup.subgroupOf_normalizer_eq hPle]
    exact hn'
  have hn_inv_normP : (n : G)⁻¹ ∈ normalizer (P : Set G) :=
    (normalizer (P : Set G)).inv_mem hn_normP
  have hmapP : P.map (MulAut.conj (n : G)⁻¹) = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn_inv_normP
  have hconj_le : uniqueFourConj (n : G) P₀ ≤ P := by
    rw [uniqueFourConj]
    calc P₀.map (MulAut.conj (n : G)⁻¹)
        ≤ P.map (MulAut.conj (n : G)⁻¹) := Subgroup.map_mono hP₀
      _ = P := hmapP
  have hP₀map : P₀.map (MulAut.conj (n : G)⁻¹) = P₀ := hwc (n : G) hconj_le
  have hn_normP₀ : (n : G) ∈ normalizer (P₀ : Set G) := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hP₀map
    simpa using (normalizer (P₀ : Set G)).inv_mem h
  have hn_normQ' : (n : G) ∈ normalizer (uniqueFourPrimeCore p M : Set G) :=
    hM_le_normQ' n.2
  have hn_norm : (n : G) ∈ normalizer (uniqueFourPrimeCore p M ⊔ P₀ : Subgroup G) :=
    Subgroup.inf_normalizer_le_normalizer_sup (uniqueFourPrimeCore p M) P₀
      ⟨hn_normQ', hn_normP₀⟩
  rw [hm_eq]
  exact mul_mem hq_norm hn_norm

end CFSG.LocalAnalysis.UniquenessCase.UC22
