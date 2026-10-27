module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.corollary_4_19

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 4.20(a) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

private theorem CFSG.chiefFactor_isPFactor_of_solvable
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G) (cf : ChiefFactor G) :
    ∃ p : ℕ, p.Prime ∧ cf.IsPFactor p := by
  classical
  have : Group.IsSolvable G := hsolv
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin := chiefFactor_quotient_minimal (G := G) cf
  have hUq_min :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using hmin
  have : Uq.Normal := hUq_min.1
  have : IsMinimalNormal Uq := {
    minimal := by
      intro K _ hKU
      by_cases hK : K = ⊥
      · exact Or.inl hK
      · exact Or.inr (hUq_min.2.2 K inferInstance hKU hK)
  }
  have : Group.IsSolvable (G ⧸ cf.V) := by infer_instance
  have : Group.IsSolvable Uq := by infer_instance
  obtain ⟨p, hp, hUq_elem⟩ :=
    minimalNormal_solvable_exists_isElementaryAbelian (G := G ⧸ cf.V) (M := Uq)
  have : Fact p.Prime := ⟨hp⟩
  have hUq_p : IsPGroup p Uq := by
    let : IsElementaryAbelian p Uq := hUq_elem
    exact IsElementaryAbelian.isPGroup p Uq
  let : (cf.V.subgroupOf cf.U).Normal :=
    Subgroup.Normal.subgroupOf (G := G) (hH := cf.isChief.normal_K) cf.U
  let e : cf.U ⧸ cf.V.subgroupOf cf.U ≃* Uq :=
    quotientSubgroupRangeEquiv cf.U cf.V
  exact ⟨p, hp, hUq_p.of_equiv e.symm⟩

private theorem CFSG.derivedSubgroup_isNilpotent_of_groupRank_le_two
    {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hrank : groupRank G ≤ 2) :
    Group.IsNilpotent (derivedSubgroup G) := by
  classical
  let D : Subgroup G := derivedSubgroup G
  have hD_le_fittingOfD : D ≤ fittingSubgroupOf (G := G) D := by
    have hD_le_iInf :
        D ≤ ⨅ cf : ChiefFactor G, centralizerOfChiefFactor (G := G) D cf := by
      refine le_iInf (fun cf => ?_)
      obtain ⟨p, hp, hcf_p⟩ :=
        chiefFactor_isPFactor_of_solvable (G := G) hsolv cf
      let : Fact p.Prime := ⟨hp⟩
      have hprimeRank : primeRank p (⊤ : Subgroup G) ≤ 2 := by
        have hleG : primeRank p G ≤ 2 :=
          (primeRank_le_groupRank (R := G) hp).trans hrank
        exact (primeRank_le_of_subgroup (R := G) (S := ⊤) p).trans hleG
      have hD_le_top_cent :
          D ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
        simpa [D] using
          corollary_4_19 (G := G) (p := p) hsolv hodd (⊤ : Subgroup G)
            hprimeRank cf hcf_p (by simp)
      have hD_le_D_cent : D ≤ centralizerOfChiefFactor (G := G) D cf := by
        intro x hx
        exact (mem_centralizerOfChiefFactor (H := D) (cf := cf) (g := x)).2
          ⟨hx, (mem_centralizerOfChiefFactor (H := (⊤ : Subgroup G)) (cf := cf) (g := x)).1
            (hD_le_top_cent hx) |>.2⟩
      exact hD_le_D_cent
    have hProp := (proposition_1_2 (G := G) hsolv D inferInstance).1
    have hD_le_sInf :
        D ≤ sInf (centralizerOfChiefFactor (G := G) D '' (Set.univ : Set (ChiefFactor G))) := by
      simpa [sInf_centralizerOfChiefFactor_univ_eq_iInf (G := G) (H := D)] using hD_le_iInf
    simpa [hProp] using hD_le_sInf
  have hFit_le_D : fittingSubgroupOf (G := G) D ≤ D := fittingSubgroupOf_le (G := G) D
  have hFit_eq_D : fittingSubgroupOf (G := G) D = D := le_antisymm hFit_le_D hD_le_fittingOfD
  have hFit_nil : Group.IsNilpotent (fittingSubgroupOf (G := G) D) :=
    fittingSubgroupOf_isNilpotent (G := G) D
  exact Group.nilpotent_of_mulEquiv
    (G := fittingSubgroupOf (G := G) D) (G' := D) (MulEquiv.subgroupCongr hFit_eq_D)

public theorem CFSG.theorem_4_20_a {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2) :
    Group.IsNilpotent (derivedSubgroup G) := by
  classical
  rcases hrank with hG | hF
  · exact derivedSubgroup_isNilpotent_of_groupRank_le_two (G := G) hsolv hodd hG
  · let D : Subgroup G := derivedSubgroup G
    let F : Subgroup G := fittingSubgroup G
    have hD_le_fittingOfD : D ≤ fittingSubgroupOf (G := G) D := by
      let S : Set (Subgroup D) := centralizerOfChiefFactorIn (G := G) D ''
        {cf : ChiefFactor G | cf.U ≤ fittingSubgroupOf (G := G) D}
      let I_res : Subgroup D := sInf S
      have hD_le_I_res_map : D ≤ I_res.map D.subtype := by
        intro x hxD
        refine ⟨⟨x, hxD⟩, ?_, rfl⟩
        change (⟨x, hxD⟩ : D) ∈ sInf S
        rw [Subgroup.mem_sInf]
        intro K hK
        rcases hK with ⟨cf, hcf_le_fitD, rfl⟩
        have hcf_le_F : cf.U ≤ F := by
          exact hcf_le_fitD.trans (fittingSubgroupOf_le_fittingSubgroup (G := G) D inferInstance)
        obtain ⟨p, hp, hcf_p⟩ :=
          chiefFactor_isPFactor_of_solvable (G := G) hsolv cf
        let : Fact p.Prime := ⟨hp⟩
        have hprimeRank : primeRank p F ≤ 2 := by
          exact (primeRank_le_groupRank (R := F) hp).trans hF
        have hD_le_top_cent :
            D ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
          simpa [D, F] using
            corollary_4_19 (G := G) (p := p) hsolv hodd F hprimeRank cf hcf_p hcf_le_F
        have hx_top_cent : x ∈ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf :=
          hD_le_top_cent hxD
        have hx_D_cent : x ∈ centralizerOfChiefFactor (G := G) D cf := by
          exact (mem_centralizerOfChiefFactor (H := D) (cf := cf) (g := x)).2
            ⟨hxD, (mem_centralizerOfChiefFactor (H := (⊤ : Subgroup G)) (cf := cf) (g := x)).1
              hx_top_cent |>.2⟩
        change x ∈ centralizerOfChiefFactor (G := G) D cf
        exact hx_D_cent
      have hprop := (proposition_1_2 (G := G) hsolv D inferInstance).2
      exact hD_le_I_res_map.trans_eq hprop.symm
    have hFit_le_D : fittingSubgroupOf (G := G) D ≤ D := fittingSubgroupOf_le (G := G) D
    have hFit_eq_D : fittingSubgroupOf (G := G) D = D := le_antisymm hFit_le_D hD_le_fittingOfD
    have hFit_nil : Group.IsNilpotent (fittingSubgroupOf (G := G) D) :=
      fittingSubgroupOf_isNilpotent (G := G) D
    exact Group.nilpotent_of_mulEquiv
      (G := fittingSubgroupOf (G := G) D) (G' := D) (MulEquiv.subgroupCongr hFit_eq_D)

end Main
