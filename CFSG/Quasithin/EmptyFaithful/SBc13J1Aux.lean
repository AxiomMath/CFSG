module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc13

variable {G : Type*} [Group G]

theorem map_pCore_eq_pCoreOf_J1 (J : Subgroup G) :
    (CFSG.pCore 2 ↥J).map J.subtype = pCoreOf 2 J := by
  unfold pCoreOf
  try with_reducible rfl

theorem pCoreOf_subgroupOf_eq_pCore_J1 (J : Subgroup G) :
    (pCoreOf 2 J).subgroupOf J = CFSG.pCore 2 ↥J := CFSG.openPCoreOf_subgroupOf 2 J

theorem isSolvable_pCoreOf_J1 [Finite G] (J : Subgroup G) : Group.IsSolvable ↥(pCoreOf 2 J) := by
  have := (pCoreOf_isPGroup 2 J).isNilpotent
  infer_instance

theorem le_normalizer_of_commutator_solvable_J1 [Finite G] {X K J : Subgroup G} (hKX : K ≤ X)
    (hJ : J ∈ cComp X) (hsolv : Group.IsSolvable ↥⁅J, K⁆) :
    K ≤ Subgroup.normalizer (J : Set G) := by
  have hJX : J ≤ X := le_of_mem_cComp hJ
  have hJperf : ⁅J, J⁆ = J := perfect_of_mem_cComp hJ
  have hDX : ⁅J, K⁆ ≤ X := (Subgroup.commutator_mono hJX hKX).trans (A3.commutator_self_le X)
  have hcore := (cComp_commutator_perfectCore hJ hDX hsolv
    (A3.le_normalizer_commutator_left J K)).2
  have key : ∀ n ∈ K, ∀ y ∈ J, n * y * n⁻¹ ∈ J := by
    intro n hn y hy
    have hle : J.map (MulAut.conj n : G →* G) ≤ J ⊔ ⁅J, K⁆ := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 : ⁅n, z⁆ ∈ ⁅J, K⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hn hz
      have h2 : (MulAut.conj n : G →* G) z = ⁅n, z⁆ * z := by
        simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hz)
    have hperf : ⁅J.map (MulAut.conj n : G →* G), J.map (MulAut.conj n : G →* G)⁆ =
        J.map (MulAut.conj n : G →* G) := by
      rw [← Subgroup.map_commutator, hJperf]
    have h3 := le_perfectCore_of_perfect hle hperf
    rw [hcore] at h3
    exact h3 ⟨y, hy, rfl⟩
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key n hn y, fun hy => ?_⟩
  have h4 := key n⁻¹ (K.inv_mem hn) _ hy
  simpa [mul_assoc] using h4

theorem sup_pCoreOf_eq_or_commutator_le_J1 {J D : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hDJ : D ≤ J)
    (hDn : (D.subgroupOf J).Normal) :
    D ⊔ pCoreOf 2 J = J ∨ ⁅D, J⁆ ≤ pCoreOf 2 J := by
  have hRQ : (CFSG.pCore 2 ↥J).map J.subtype = pCoreOf 2 J := map_pCore_eq_pCoreOf_J1 J
  have hDb : ((D.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).Normal :=
    hDn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hDb with htop | hcen
  · left
    have h1 : D.subgroupOf J ⊔ CFSG.pCore 2 ↥J = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) (D.subgroupOf J)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have h2 := congrArg (Subgroup.map J.subtype) h1
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDJ, hRQ, Subgroup.map_top,
      Subgroup.range_subtype] at h2
    exact h2
  · right
    refine Subgroup.commutator_le.mpr fun d hd j hj => ?_
    let dJ : ↥J := ⟨d, hDJ hd⟩
    let jJ : ↥J := ⟨j, hj⟩
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥J) dJ ∈
        (D.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) :=
      Subgroup.mem_map_of_mem _ (show dJ ∈ D.subgroupOf J from hd)
    have hc : ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥J) dJ,
        QuotientGroup.mk' (CFSG.pCore 2 ↥J) jJ⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hcen hmem) (QuotientGroup.mk' (CFSG.pCore 2 ↥J) jJ)).symm
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⁅dJ, jJ⁆ = 1 := by
      rw [map_commutatorElement]
      exact hc
    have h2 : ⁅dJ, jJ⁆ ∈ (pCoreOf 2 J).subgroupOf J := by
      rw [pCoreOf_subgroupOf_eq_pCore_J1]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((⁅dJ, jJ⁆ : ↥J) : G) ∈ pCoreOf 2 J := h2
    simpa [commutatorElement_def] using h3

end SBc13

end CFSG.Quasithin
