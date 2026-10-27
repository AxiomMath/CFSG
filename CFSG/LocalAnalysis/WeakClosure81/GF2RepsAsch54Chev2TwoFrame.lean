module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoOrbit
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Setup
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallCF
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Alm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem lGen_eq_top_of_bqSmall {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q}
    [hLn : L.Normal] (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hq : Group.IsSolvable (Q ⧸ L)) (hT : IsSylowIn 2 T ⊤)
    (hL0 : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L} {e : ℕ} (hbq : BorelQuotient D n H π e)
    (hunip : (T ⊓ L).subgroupOf L = (posUnipotent D).map π) (hsmall : BQSmall D)
    (hntr : ¬ NodeTransitive L T D H π) : lGen IsCalL0 ⊤ T = ⊤ := by
  classical
  have hRN : T ≤ Subgroup.normalizer (L : Set Q) :=
    @Subgroup.le_normalizer_of_normal Q _ L T hLn
  let 𝒜 : Subgroup (MulAut ↥L) := (actHom hRN).range
  have h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom =
      (posUnipotent D).map π := range_actHom_fix hRN hunip
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  let O : Fin D.rank → Set (Fin D.rank) := fun k => nodeOrbit hbq 𝒜 h𝒜 k
  let X : Fin D.rank → Subgroup Q := fun k => ((parJ D H (O k)).map π).map L.subtype
  let Y : Fin D.rank → Subgroup Q := fun k => X k ⊔ T
  have hkO : ∀ k, k ∈ O k := by
    intro k
    refine ⟨1, ?_⟩
    show nodeHom hbq 𝒜 h𝒜 1 k = k
    rw [map_one]
    rfl
  have hTX : ∀ k, T ⊓ L ≤ X k := by
    intro k x hx
    have hxL : x ∈ L := hx.2
    have hxsub : (⟨x, hxL⟩ : ↥L) ∈ (T ⊓ L).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hunip] at hxsub
    have hU : (⟨x, hxL⟩ : ↥L) ∈ (parJ D H (O k)).map π :=
      Subgroup.map_mono (f := π) (posUnipotent_le_borel.trans (borel_le_parJ (O k))) hxsub
    exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hU, rfl⟩
  have hN : ∀ k, T ≤ Subgroup.normalizer (X k : Set Q) := by
    intro k t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_parJ_orbit_subtype_conj hbq hRN h𝒜 ht k
  have hYinf : ∀ k, Y k ⊓ L = X k := by
    intro k
    have hNY : Y k ≤ Subgroup.normalizer (X k : Set Q) :=
      sup_le Subgroup.le_normalizer (hN k)
    have hnormXY : ((X k).subgroupOf (Y k)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNY
    apply le_antisymm
    · intro z hz
      have hzY : z ∈ Y k := hz.1
      have hzL : z ∈ L := hz.2
      have hsup : (X k).subgroupOf (Y k) ⊔ (T.subgroupOf (Y k)) = ⊤ := by
        apply Subgroup.map_injective (f := (Y k).subtype) (Y k).subtype_injective
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
          Subgroup.map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_top,
          Subgroup.range_subtype]
      have hmem : (⟨z, hzY⟩ : ↥(Y k)) ∈
          (X k).subgroupOf (Y k) ⊔ (T.subgroupOf (Y k)) := by
        rw [hsup]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, t, ht, hxt⟩ :=
        (@Subgroup.mem_sup_of_normal_left ↥(Y k) _ ((X k).subgroupOf (Y k))
          (T.subgroupOf (Y k)) hnormXY ⟨z, hzY⟩).mp hmem
      have hxX : (x : Q) ∈ X k := Subgroup.mem_subgroupOf.mp hx
      have htT : (t : Q) ∈ T := Subgroup.mem_subgroupOf.mp ht
      have hxL : (x : Q) ∈ L := Subgroup.map_subtype_le _ hxX
      have hzt : (x : Q) * (t : Q) = z := by
        simpa using congrArg Subtype.val hxt
      have htL : (t : Q) ∈ L := by
        have hteq : (t : Q) = (x : Q)⁻¹ * z := by
          rw [← hzt]
          group
        rw [hteq]
        exact L.mul_mem (L.inv_mem hxL) hzL
      have htX : (t : Q) ∈ X k := hTX k ⟨htT, htL⟩
      rw [← hzt]
      exact (X k).mul_mem hxX htX
    · intro z hz
      exact ⟨Subgroup.mem_sup_left hz, Subgroup.map_subtype_le _ hz⟩
  have hYno : ∀ k, ¬ HasCompFactor (Y k) IsCalL0 := by
    intro k
    have hPbar : ¬ HasCompFactor ((parJ D H (O k)).map π) IsCalL0 :=
      not_hasCompFactor_map_parJ_nodeOrbit hbq hLs hnab hT2 hL0 hRN h𝒜 hsmall hntr k
    have hXno : ¬ HasCompFactor (X k) IsCalL0 := by
      rintro ⟨Z, hgrpZ, hcf, hPZ⟩
      let e' : ↥((parJ D H (O k)).map π) ≃* ↥(X k) :=
        Subgroup.equivMapOfInjective ((parJ D H (O k)).map π) L.subtype
          L.subtype_injective
      exact hPbar ⟨Z, hgrpZ,
        (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e'.symm).mp hcf, hPZ⟩
    have hsub : ¬ HasCompFactor (L.subgroupOf (Y k)) IsCalL0 := by
      rintro ⟨Z, hgrpZ, hcf, hPZ⟩
      have hYeq : L.subgroupOf (Y k) = (Y k ⊓ L).subgroupOf (Y k) := by
        ext y
        simp [Subgroup.mem_subgroupOf]
      let e' : ↥(L.subgroupOf (Y k)) ≃* ↥(X k) :=
        (MulEquiv.subgroupCongr hYeq).trans
          ((Subgroup.subgroupOfEquivOfLe (show Y k ⊓ L ≤ Y k from inf_le_left)).trans
            (MulEquiv.subgroupCongr (hYinf k)))
      exact hXno ⟨Z, hgrpZ,
        (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e').mp hcf, hPZ⟩
    exact not_hasCompFactor_of_subgroupOf (fun Z _ _ hZ => hL0 Z hZ) hq (Y k)
      fun Z hZg hcf hZ => hsub ⟨Z, hZg, hcf, hZ⟩
  have hYmem : ∀ k, Y k ∈ calLT IsCalL0 ⊤ T := by
    intro k
    refine ⟨le_sup_right, ?_, hYno k⟩
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hXL : X k = L := by
      have h := hYinf k
      rw [htop, top_inf_eq] at h
      exact h.symm
    have huniv : O k = Set.univ := by
      ext j
      refine ⟨fun _ => Set.mem_univ j, fun _ => ?_⟩
      exact mem_of_map_parJ_map_subtype_eq_top hbq (J := O k) ⟨k, hkO k⟩ (k := j) hXL
    exact hntr (nodeTransitive_of_nodeOrbit_eq_univ hbq hRN h𝒜 huniv)
  have hLle : L ≤ lGen IsCalL0 ⊤ T := by
    rw [← iSup_map_rankOne_subtype_eq hbq]
    refine iSup_le fun k => ?_
    have h1 : (rankOne D.rootGroup k).map π ≤ (parJ D H (O k)).map π :=
      Subgroup.map_mono (f := π) (rankOne_le_parJ (hkO k))
    have h2 : ((rankOne D.rootGroup k).map π).map L.subtype ≤ X k :=
      Subgroup.map_mono (f := L.subtype) h1
    exact h2.trans (le_sup_left.trans (le_iSup₂_of_le (Y k) (hYmem k) le_rfl))
  let R : Subgroup Q := Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)
  have hTR : T ≤ R := by
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, (@Subgroup.le_normalizer_of_normal Q _ L T hLn) ht⟩
  have hRB : L ⊓ R = ((borel D H).map π).map L.subtype :=
    inf_normalizer_eq_map_borel hbq inf_le_right hunip
  have hRLsolv : Group.IsSolvable ↥(R ⊓ L) := by
    rw [inf_comm, hRB]
    exact isSolvable_map_borel_subtype hbq
  have hLeq : L.subgroupOf R = (R ⊓ L).subgroupOf R := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hcore : L.subgroupOf R = ((R ⊓ L).subgroupOf R).normalCore := by
    rw [hLeq, Subgroup.normalCore_eq_self]
  have hRq : Group.IsSolvable (↥R ⧸ ((R ⊓ L).subgroupOf R).normalCore) := by
    have h := CFSG.LocalAnalysis.WeakClosure81.isSolvable_quotient_subgroupOf hq R
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hcore).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hcore).surjective
  have hRsolv : Group.IsSolvable ↥R :=
    CFSG.LocalAnalysis.WeakClosure81.isSolvable_of_isSolvable_quot
      (show R ⊓ L ≤ R from inf_le_left) hRLsolv hRq
  have hRno : ¬ HasCompFactor R IsCalL0 :=
    not_hasCompFactor_of_isSolvable (fun Z _ _ hZ => hL0 Z hZ) hRsolv
  have hRmem : R ∈ calLT IsCalL0 ⊤ T := by
    refine ⟨hTR, ?_, hRno⟩
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hLR : L ≤ R := htop ▸ le_top
    have hLB : L = ((borel D H).map π).map L.subtype := by
      have h := hRB
      rw [inf_eq_left.mpr hLR] at h
      exact h
    have hLsolv : Group.IsSolvable ↥L := by
      rw [hLB]
      exact isSolvable_map_borel_subtype hbq
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (CFSG.LocalAnalysis.ComponentInitial.solvable_simple_abelian hLsolv a b)
  have hRle : R ≤ lGen IsCalL0 ⊤ T := le_iSup₂_of_le R hRmem le_rfl
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal ⟨hT.1, hT.2.1, hT.2.2⟩ le_top
      (Subgroup.normalizer_eq_top_iff.mpr hLn).ge
  have hfr : L ⊔ R = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (G := Q) (N := L) (B6.toSylow2 hS)
    rw [B6.toSylow2_coe hS, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
    rw [sup_comm]
    exact h
  have htop : (⊤ : Subgroup Q) ≤ lGen IsCalL0 ⊤ T := by
    calc (⊤ : Subgroup Q) = L ⊔ R := hfr.symm
      _ ≤ lGen IsCalL0 ⊤ T := sup_le hLle hRle
  exact top_le_iff.mp htop

private theorem lGen_eq_top_of_borelQuotient_small {Q : Type} [Group Q] [Finite Q]
    {L T : Subgroup Q} [hLn : L.Normal] (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hq : Group.IsSolvable (Q ⧸ L))
    (hT : IsSylowIn 2 T ⊤)
    (hL0 : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L} {e : ℕ} (hbq : BorelQuotient D n H π e)
    (hsmall : BQSmall D)
    (hdata : 3 ≤ D.rank ∨ ∃ i j : Fin D.rank,
      Nat.card ↥(D.rootGroup (Pi.single i 1)) ≠ Nat.card ↥(D.rootGroup (Pi.single j 1))) :
    lGen IsCalL0 ⊤ T = ⊤ := by
  classical
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal ⟨hT.1, hT.2.1, hT.2.2⟩ le_top
      (Subgroup.normalizer_eq_top_iff.mpr hLn).ge
  obtain ⟨π', hbq', hunip⟩ := exists_borelQuotient_conj hS hbq
  by_cases htr : NodeTransitive L T D H π'
  · exfalso
    have hr := rank_le_two_of_nodeTransitive hbq' hLn hLs hnab hT.2.1 hunip htr
    rcases hdata with h3 | ⟨i, j, hij⟩
    · omega
    · exact hij (card_rootGroup_eq_of_nodeTransitive hbq' htr i j)
  · exact lGen_eq_top_of_bqSmall hLs hnab hq hT hL0 hbq' hunip hsmall htr

theorem lGen_eq_top_of_hasBQSmall {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q}
    [hLn : L.Normal] (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hq : Group.IsSolvable (Q ⧸ L)) (hT : IsSylowIn 2 T ⊤)
    (hL0 : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    (h : HasBQSmall ↥L) : lGen IsCalL0 ⊤ T = ⊤ := by
  obtain ⟨K, hK, hKfin, D, n, H, π, e, hbq, hsmall, hdata⟩ := h
  exact @lGen_eq_top_of_borelQuotient_small Q _ _ L T hLn hLs hnab hq hT hL0 K hK hKfin
    D n H π e hbq hsmall hdata

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
