module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairDefs

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.SectionRank.LargeRee CFSG.LieType.Ree CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.B45Sz

theorem reeNa_sq
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ} :
    reeNa K m * reeNa K m = 1 := by
  rw [reeNa]
  exact relNrepHom_blockGen_mul_self 0

theorem reeU_isPGroup
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ} :
    IsPGroup 2 (reeU K m) := by
  rw [reeU]
  have hU : IsPGroup 2 ((nativeData ReeTag.F4.tag K).U) :=
    (nativeRootSubgroups ReeTag.F4.tag K).isPGroup_U 2
  exact hU.comap_of_injective (reeFixed ReeTag.F4 K m).subtype
    (Subgroup.subtype_injective _)

theorem reeUb_le
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ} :
    reeUb K m ≤ reeU K m := by
  intro g hg
  simp only [reeUb, Subgroup.mem_comap] at hg
  simp only [reeU, Subgroup.mem_comap]
  have hpos : (((g : reeFixed ReeTag.F4 K m) : adjointGroup ReeTag.F4.tag K) :
      ModGL ReeTag.F4.tag K) ∈ posUnipotent ReeTag.F4.tag K :=
    parabolicRadical_le_posUnipotent ({1, 2} : Set (Fin ReeTag.F4.tag.rank)) hg
  have hU := ReeTag.mem_nativeData_U_of_mem_posUnipotent (t := ReeTag.F4) hpos
  simpa only [Subgroup.coe_subtype, Function.comp_apply] using hU

private theorem blockElt_one_smul_eq_foldr
    (v : Fin ReeTag.F4.tag.rank → ℤ) :
    (ReeTag.F4.blockElt (fi 1)) • v =
      (ReeTag.F4.reeOrbitWord (fi 1)).foldr (reflect ReeTag.F4.tag) v := by
  change ((coxeterSystem ReeTag.F4.tag).wordProd (ReeTag.F4.reeOrbitWord (fi 1))) • v = _
  rw [CFSG.LieType.Ree.wordProd_smul]

private theorem blockElt_zero_one_zero_smul_eq_foldr
    (v : Fin ReeTag.F4.tag.rank → ℤ) :
    (ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 * ReeTag.F4.blockElt 0) • v =
      (ReeTag.F4.reeOrbitWord 0 ++ ReeTag.F4.reeOrbitWord 1 ++
        ReeTag.F4.reeOrbitWord 0).foldr (reflect ReeTag.F4.tag) v := by
  change ((coxeterSystem ReeTag.F4.tag).wordProd (ReeTag.F4.reeOrbitWord 0) *
      (coxeterSystem ReeTag.F4.tag).wordProd (ReeTag.F4.reeOrbitWord 1) *
      (coxeterSystem ReeTag.F4.tag).wordProd (ReeTag.F4.reeOrbitWord 0)) • v = _
  rw [mul_assoc, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append,
    CFSG.LieType.Ree.wordProd_smul]
  rfl

private theorem blockElt_one_blockElt_zero_one_zero_root_check :
    ∀ k < ReeTag.F4.tag.witnesses.roots.length,
      0 < height (decodeVec (τ := ReeTag.F4.tag) (ReeTag.F4.tag.witnesses.roots.getD k 0)) →
      height ((ReeTag.F4.reeOrbitWord (fi 1)).foldr (reflect ReeTag.F4.tag)
        (decodeVec (τ := ReeTag.F4.tag) (ReeTag.F4.tag.witnesses.roots.getD k 0))) < 0 →
      0 < height ((ReeTag.F4.reeOrbitWord 0 ++ ReeTag.F4.reeOrbitWord 1 ++
        ReeTag.F4.reeOrbitWord 0).foldr (reflect ReeTag.F4.tag)
        (decodeVec (τ := ReeTag.F4.tag) (ReeTag.F4.tag.witnesses.roots.getD k 0))) := by
  decide +kernel

private theorem reeSz₁_mem_Uminus
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m)
    {x : suzukiGroup m K} (hx : x ∈ szUp m K) :
    ∃ y ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)),
      ((reeSz₁ hK hm x : reeFixed ReeTag.F4 K m) : adjointGroup ReeTag.F4.tag K) = y := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hWW : CFSG.LieType.Ree.suzukiWElt m K * CFSG.LieType.Ree.suzukiWElt m K = 1 := CFSG.LieType.Ree.suzukiWElt_mul_self
  have hinv : (CFSG.LieType.Ree.suzukiWElt m K)⁻¹ = CFSG.LieType.Ree.suzukiWElt m K := inv_eq_of_mul_eq_one_right hWW
  obtain ⟨u₀, v₀, rfl⟩ := (mem_suzukiU_iff (a := m) (by exact hK)).mp hu
  have hconj : MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)
      (MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K) (suzukiSElt m K u₀ v₀)) = suzukiSElt m K u₀ v₀ := by
    rw [MulAut.conj_apply, MulAut.conj_apply, hinv]
    calc CFSG.LieType.Ree.suzukiWElt m K * (CFSG.LieType.Ree.suzukiWElt m K * suzukiSElt m K u₀ v₀ * CFSG.LieType.Ree.suzukiWElt m K) *
          CFSG.LieType.Ree.suzukiWElt m K
        = (CFSG.LieType.Ree.suzukiWElt m K * CFSG.LieType.Ree.suzukiWElt m K) * suzukiSElt m K u₀ v₀ *
            (CFSG.LieType.Ree.suzukiWElt m K * CFSG.LieType.Ree.suzukiWElt m K) := by group
      _ = suzukiSElt m K u₀ v₀ := by rw [hWW, one_mul, mul_one]
  obtain ⟨x₀, hx₀, hx₀F, hx₀v⟩ := exists_reeFixed_vMat_eq_suzukiS (a := m) hK u₀ v₀
  have hx₀X : (⟨x₀, hx₀F⟩ : reeFixed ReeTag.F4 K m) ∈ blockX (K := K) m 1 := hx₀
  let y₀ : r2 K m hK := ⟨⟨x₀, hx₀F⟩, blockX_le_r2 hK hx₀X⟩
  have hmap : (r2EquivSuzuki K m hK hm) y₀ = suzukiSElt m K u₀ v₀ := by
    refine Subtype.ext ?_
    refine Units.ext ?_
    simp only [coe_r2EquivSuzuki, coe_r2Rep, coe_suzukiSElt, Subgroup.coe_subtype,
      Function.comp_apply]
    exact hx₀v
  have hsymm : (r2EquivSuzuki K m hK hm).symm (suzukiSElt m K u₀ v₀) = y₀ := by
    apply (r2EquivSuzuki K m hK hm).injective
    rw [MulEquiv.apply_symm_apply]
    exact hmap.symm
  have hreesz : reeSz₁ hK hm ((MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)).toMonoidHom
        (suzukiSElt m K u₀ v₀))
      = (r2 K m hK).subtype
          ((r2EquivSuzuki K m hK hm).symm (suzukiSElt m K u₀ v₀)) := by
    change (r2 K m hK).subtype ((r2EquivSuzuki K m hK hm).symm
      (MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)
        (MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K) (suzukiSElt m K u₀ v₀))))
      = (r2 K m hK).subtype ((r2EquivSuzuki K m hK hm).symm (suzukiSElt m K u₀ v₀))
    rw [hconj]
  refine ⟨x₀, hx₀, ?_⟩
  rw [hreesz, hsymm]
  rfl

private theorem reeSz₂_mem_U
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m)
    {x : suzukiGroup m K} (hx : x ∈ szUp m K) :
    ((reeSz₂ hK hm x : reeFixed ReeTag.F4 K m) :
      adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).U := by
  obtain ⟨y, hy, hxy⟩ := reeSz₁_mem_Uminus hK hm hx
  set g : reeFixed ReeTag.F4 K m := reeNa K m * reeNb K m * reeNa K m with hgdef
  have hw : ((blockGen 0 * blockGen 1 * blockGen 0 : ReeTag.F4.relWeylRee) :
      WeylGroup ReeTag.F4.tag) =
      ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 * ReeTag.F4.blockElt 0 := by
    simp only [Subgroup.coe_mul, coe_blockGen, blockIdx_zero, blockIdx_one]
    rfl
  have hgcoe : (g : adjointGroup ReeTag.F4.tag K) =
      nrep ReeTag.F4.tag K (ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 *
        ReeTag.F4.blockElt 0) := by
    rw [hgdef, reeNa, reeNb, ← map_mul, ← map_mul]
    change nrep ReeTag.F4.tag K
      ((blockGen 0 * blockGen 1 * blockGen 0 : ReeTag.F4.relWeylRee) :
        WeylGroup ReeTag.F4.tag) =
      nrep ReeTag.F4.tag K (ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 *
        ReeTag.F4.blockElt 0)
    rw [hw]
  have hpos : ∀ α : Root ReeTag.F4.tag, 0 < height α.1 →
      height (ReeTag.F4.blockElt (fi 1) • α.1) < 0 →
      0 < height ((ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 *
        ReeTag.F4.blockElt 0) • α.1) := by
    intro α hα hαz
    obtain ⟨hk, hdec⟩ := rootColumn_spec (τ := ReeTag.F4.tag) α.2
    have h1 : 0 < height (decodeVec (τ := ReeTag.F4.tag)
        (ReeTag.F4.tag.witnesses.roots.getD
          (rootColumn ReeTag.F4.tag α.1) 0)) := by
      rw [hdec]
      exact hα
    have h2 : height ((ReeTag.F4.reeOrbitWord (fi 1)).foldr (reflect ReeTag.F4.tag)
        (decodeVec (τ := ReeTag.F4.tag)
          (ReeTag.F4.tag.witnesses.roots.getD
            (rootColumn ReeTag.F4.tag α.1) 0))) < 0 := by
      rw [hdec, ← blockElt_one_smul_eq_foldr]
      exact hαz
    have h3 := blockElt_one_blockElt_zero_one_zero_root_check
      (rootColumn ReeTag.F4.tag α.1) hk h1 h2
    rw [← blockElt_zero_one_zero_smul_eq_foldr, hdec] at h3
    exact h3
  have hUU : Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) ≤
      Uplus ReeTag.F4.tag K (ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 *
        ReeTag.F4.blockElt 0) := by
    refine iSup₂_le fun α hα => ?_
    exact le_iSup₂_of_le α ⟨hα.1, hpos α hα.1 hα.2⟩ le_rfl
  have hyU : ((reeSz₁ hK hm x : reeFixed ReeTag.F4 K m) :
      adjointGroup ReeTag.F4.tag K) ∈
      Uplus ReeTag.F4.tag K (ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 *
        ReeTag.F4.blockElt 0) := by
    refine hUU ?_
    rw [hxy]
    exact hy
  have hgoal : ((MulAut.conj g (reeSz₁ hK hm x) : reeFixed ReeTag.F4 K m) :
      adjointGroup ReeTag.F4.tag K) =
      nrep ReeTag.F4.tag K (ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 *
        ReeTag.F4.blockElt 0) *
      ((reeSz₁ hK hm x : reeFixed ReeTag.F4 K m) : adjointGroup ReeTag.F4.tag K) *
      (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt 0 * ReeTag.F4.blockElt 1 *
        ReeTag.F4.blockElt 0))⁻¹ := by
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hgcoe]
  change ((MulAut.conj g (reeSz₁ hK hm x) : reeFixed ReeTag.F4 K m) :
    adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).U
  rw [hgoal]
  exact nrep_conj_mem_U hyU

theorem reeSz₁_up
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∀ x ∈ szUp m K, reeSz₁ hK hm x ∈ reeU K m := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := reeSz₁_mem_Uminus hK hm hx
  simp only [reeU, Subgroup.mem_comap]
  change ((reeSz₁ hK hm x : reeFixed ReeTag.F4 K m) :
    adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).U
  rw [hxy]
  exact Uminus_le_U ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) hy

theorem reeSz₂_up
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∀ x ∈ szUp m K, reeSz₂ hK hm x ∈ reeU K m := by
  intro x hx
  simp only [reeU, Subgroup.mem_comap]
  exact reeSz₂_mem_U hK hm hx

end CFSG.StandardType.ReeB2Fixed
