module

public import CFSG.RankThree.GF2n.Stroth80.Sec84Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_mem_inSubgroup_pCore_of_mem_pCore_bar [(Q.subgroupOf M).Normal]
    (hQ2 : IsPGroup 2 Q) {K : Subgroup G} (hKM : K ≤ M) (y : ↥(bar M Q K))
    (hy : y ∈ pCore 2 ↥(bar M Q K)) :
    ∃ x : M, (x : G) ∈ inSubgroup (pCore 2) K ∧
      QuotientGroup.mk' (Q.subgroupOf M) x = (y : Mbar M Q) := by
  obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp y.2
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  set π := QuotientGroup.mk' (Q.subgroupOf M) with hπ
  set Pbar : Subgroup (Mbar M Q) := (pCore 2 ↥(bar M Q K)).map (bar M Q K).subtype with hPbar
  have hPbar2 : IsPGroup 2 Pbar := pCore_isPGroup.map _
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hQ2.comap_subtype
  have hPt : IsPGroup 2 (Pbar.comap π) := hPbar2.comap_of_ker_isPGroup π hker
  set Pk : Subgroup ↥K := (Pbar.comap π).comap (Subgroup.inclusion hKM) with hPk
  have hPk2 : IsPGroup 2 Pk :=
    hPt.comap_of_injective _ (Subgroup.inclusion_injective hKM)
  have hPkN : Pk.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : π (Subgroup.inclusion hKM n) ∈ Pbar := hn
    obtain ⟨z, hz, hzn⟩ := Subgroup.mem_map.mp hn'
    have hgK : π (Subgroup.inclusion hKM g) ∈ bar M Q K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr g.2)
    show π (Subgroup.inclusion hKM (g * n * g⁻¹)) ∈ Pbar
    have e : π (Subgroup.inclusion hKM (g * n * g⁻¹)) =
        π (Subgroup.inclusion hKM g) * π (Subgroup.inclusion hKM n) *
          (π (Subgroup.inclusion hKM g))⁻¹ := by
      simp only [map_mul, map_inv]
    rw [e, ← hzn]
    exact Subgroup.mem_map_of_mem (bar M Q K).subtype
      (pCore_normal.conj_mem z hz ⟨π (Subgroup.inclusion hKM g), hgK⟩)
  have hPkle : Pk ≤ pCore 2 ↥K := le_sSup ⟨hPkN, hPk2⟩
  refine ⟨k, ?_, hky⟩
  have hmem : (⟨k, hkK⟩ : ↥K) ∈ Pk := by
    show π (Subgroup.inclusion hKM ⟨k, hkK⟩) ∈ Pbar
    have : Subgroup.inclusion hKM ⟨(k : G), hkK⟩ = k := rfl
    rw [this, hky]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr ⟨⟨k, hkK⟩, hPkle hmem, rfl⟩

theorem step85O2_of_parts (h84 : Stroth84Statement) (hA : Sec8AExistsStatement)
    (hN : Step85CNNormalStatement) (hFirst : Step85FirstStatement)
    (hComm : Step85CommStatement) (hSyl : Step85SylowStatement) : Step85O2Statement := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0
  refine le_antisymm ?_ (hN G M Q Z B hc n t hs Z0 hZ0)
  intro y hy
  have hQ2 : IsPGroup 2 Q := by
    have h := (pCore_isPGroup (p := 2) (G := ↥M))
    rw [hc.hyp.hQ]
    have h2 : IsPGroup 2 ((pCore 2 ↥M).map M.subtype) := h.map _
    exact h2
  have hKM : NormH0 M Z Z0 ≤ M := fun x hx => hx.1.1
  obtain ⟨k, hkO, hky⟩ := exists_mem_inSubgroup_pCore_of_mem_pCore_bar hQ2 hKM y hy
  have hkCN : (k : G) ∈ hc.CN t := by
    by_contra hnot
    obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
    by_cases hcomm : ∀ z ∈ Z0, ⁅z, (k : G)⁆ ∈ Q
    · exact hComm G M Q Z B hc n t hs r hr Z0 hZ0 (k : G) hkO
        (hFirst G M Q Z B hc n t hs r hr Z0 hZ0 (k : G) hkO) hnot hcomm
    · push Not at hcomm
      obtain ⟨z, hz, hzq⟩ := hcomm
      exact hSyl G M Q Z B hc n t hs (h84 G M Q Z B hc n t hs) Z0 hZ0 (k : G) hkO hnot ⟨z, hz, hzq⟩
  rw [Subgroup.mem_subgroupOf, ← hky]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hkCN)

theorem stroth85_of_steps (hF2 : Step85F2Statement) (hO2 : Step85O2Statement) :
    Stroth85Statement := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0
  exact (hF2 G M Q Z B hc n t hs Z0 hZ0).trans (hO2 G M Q Z B hc n t hs Z0 hZ0)

end CFSG.RankThree.GF2n.Stroth80
