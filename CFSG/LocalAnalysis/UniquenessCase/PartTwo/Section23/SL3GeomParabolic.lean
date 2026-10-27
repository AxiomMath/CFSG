module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3GeomTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3SylowImage
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjointSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem closure_smul_mono {W H : Type} [Group W] [Group H] [MulAction H W]
    [MulAction H (Set W)] {K : Subgroup H} {A B : Subgroup W} (h : A ≤ B) :
    Subgroup.closure (⋃ k ∈ K, k • ((A : Set W))) ≤
      Subgroup.closure (⋃ k ∈ K, k • ((B : Set W))) := by
  refine (Subgroup.closure_le _).2 ?_
  intro w hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨k, hw⟩ := hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨hk, hw⟩ := hw
  rw [Set.mem_smul_set] at hw
  obtain ⟨a, ha, rfl⟩ := hw
  exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
    ⟨hk, Set.mem_smul_set.mpr ⟨a, h ha, rfl⟩⟩⟩)

private theorem phiL_smul_mkTil {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) :
    letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
    ∀ (x : ↥c.L) (v : CFSG.Quasithin.IntMod c.V hV),
      (c.phiL hV x) • mkTil (⊥ : Subgroup G) c.V hV v =
        mkTil (⊥ : Subgroup G) c.V hV
          (actStab (⊥ : Subgroup G) c.V hV ⟨(x : G), c.L_le_stabTil x.2⟩ v) := by
  letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
  intro x v
  rw [show (c.phiL hV x) • mkTil (⊥ : Subgroup G) c.V hV v =
    (c.phiL hV x : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) from rfl]
  exact Ctx23L.phiL_apply_mkTil c hV x v

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)

theorem normalizer_sylowStar_le_Pstar (hV : IsElemAbelian 2 c.V) :
    Subgroup.normalizer ((c.sylowStar hV : Subgroup ↥(c.H hV)) : Set ↥(c.H hV)) ≤
      c.Pstar hV := by
  have hparL : IsParabolicTwo ↥c.L (c.X.subgroupOf c.L) :=
    (parabolicOf_iff.mp c.hX.1).2
  have hXeq : ((c.X ⊓ c.L).subgroupOf c.L) = c.X.subgroupOf c.L := by
    rw [inf_eq_left.mpr c.hX.1.2.1]
  have hPstar : c.Pstar hV = (c.X.subgroupOf c.L).map (c.phiL hV) := by
    rw [show c.Pstar hV = ((c.X ⊓ c.L).subgroupOf c.L).map (c.phiL hV) from rfl, hXeq]
  have hparH : IsParabolicTwo ↥(c.H hV) (c.Pstar hV) := by
    rw [hPstar]
    exact hparL.map (c.phiL hV) (c.phiL_surjective hV)
  have hSP : (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ c.Pstar hV := by
    rw [c.sylowStar_coe hV, hPstar]
    refine Subgroup.map_mono ?_
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (c.hTX (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩))
  exact hparH.normalizer_le (c.sylowStar hV) hSP

private theorem mkTil_mem_Z_fixed {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {v : CFSG.Quasithin.IntMod c.V hV} (hvZ : v.val ∈ D.Z)
    {s : ↥(c.sylowStar hV)} :
    (s : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV v := by
  obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.1 (by rw [← c.sylowStar_coe hV]; exact s.2)
  have hxT : (x : G) ∈ D.T := Subgroup.mem_subgroupOf.1 hx
  have hcent : (x : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_omegaOneCenterIn D.T hxT
  have hxZ : (x : G) * v.val * (x : G)⁻¹ = v.val := by
    have h := (Subgroup.mem_centralizer_iff.mp hcent) v.val hvZ
    rw [← h]
    group
  have hs : (s : MulAut (c.W hV)) = c.phiL hV x := congrArg Subtype.val hxφ.symm
  rw [hs, Ctx23L.phiL_apply_mkTil c hV x v]
  have hfixz : actStab (⊥ : Subgroup G) c.V hV ⟨(x : G), c.L_le_stabTil x.2⟩ v = v := by
    apply CFSG.Quasithin.IntMod.val_injective
    rw [actStab_apply_val]
    exact hxZ
  rw [hfixz]

private theorem imgTil_Z_le_Ztil {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    imgTil (⊥ : Subgroup G) c.V hV D.Z ≤ c.Ztil hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) = c.Ztil hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L hV hm hSLH hnat
  intro z hz
  rw [← hℓ]
  change z ∈ FixedPoints.subgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV)
  rw [FixedPoints.mem_subgroup]
  intro s
  rw [mem_imgTil] at hz
  obtain ⟨v, hvZ, rfl⟩ := hz
  change (s : MulAut (c.toCtx23L.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) =
    mkTil (⊥ : Subgroup G) c.V hV v
  exact mkTil_mem_Z_fixed c.toCtx23L hV hvZ

private theorem Ztil_eq_imgTil_Z {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    c.Ztil hV = imgTil (⊥ : Subgroup G) c.V hV D.Z := by
  have himgcard : Nat.card (imgTil (⊥ : Subgroup G) c.V hV D.Z) = Nat.card D.Z := by
    rw [imgTil, Subgroup.card_map_of_injective (mkTil_injective_bot c.V hV)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (uc22p22v_le_conjClosure c.N D.Z)).toEquiv
  exact (Subgroup.eq_of_le_of_card_ge (imgTil_Z_le_Ztil c hV hm hSLH hnat) (by
    rw [c.card_Ztil hV, himgcard])).symm

theorem Pstar_ne_stabilizer (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    c.Pstar hV ≠
      MulAction.stabilizer ↥(c.H hV)
        (((fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) :
          Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  intro heq
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) = c.Ztil hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L hV hm hSLH hnat
  have hset : (((fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) :
        Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) =
      ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)) :=
    congrArg (fun s : Subgroup (c.toCtx23L.W hV) => (s : Set (c.toCtx23L.W hV))) hℓ
  have hXL : c.X ≤ c.L := c.hX.1.2.1
  obtain ⟨x, hxX, hxM⟩ :=
    Set.not_subset.mp (show ¬ (c.X : Set G) ⊆ (D.M : Set G) from c.hXM)
  have hxL : x ∈ c.L := hXL hxX
  have hxP : c.phiL hV ⟨x, hxL⟩ ∈ c.Pstar hV :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hxX, hxL⟩)
  rw [heq, MulAction.mem_stabilizer_iff] at hxP
  rw [hset] at hxP
  exact hxM ((c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 ⟨x, hxL⟩).mp
    (MulAction.mem_stabilizer_iff.mpr hxP))

theorem line_le_imgTil_W {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    closure (⋃ p ∈ c.Pstar hV,
        p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) ≤
      imgTil (⊥ : Subgroup G) c.V hV c.W := by
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  have hZ := Ztil_eq_imgTil_Z c hV hm hSLH hnat
  refine (Subgroup.closure_le _).2 ?_
  rintro w hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨p, hw⟩ := hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨hp, hw⟩ := hw
  rw [Set.mem_smul_set] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [hZ] at hz
  obtain ⟨v, hvZ, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) c.V hV D.Z z).1 hz
  obtain ⟨x, hxsub, rfl⟩ := Subgroup.mem_map.1 hp
  rw [phiL_smul_mkTil c.toCtx23L hV x v]
  refine (mem_imgTil (⊥ : Subgroup G) c.V hV c.W _).2 ⟨_, ?_, rfl⟩
  rw [actStab_apply_val]
  change (x : G) * v.val * (x : G)⁻¹ ∈ conjClosure c.X D.Z
  have hle : D.Z.map (MulAut.conj (x : G)).toMonoidHom ≤ conjClosure c.X D.Z :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf c.X D.Z) => K) _
      ⟨(x : G), (Subgroup.mem_subgroupOf.1 hxsub).1, rfl⟩ le_rfl
  simpa [MulAut.conj_apply] using
    hle (Subgroup.mem_map_of_mem (MulAut.conj (x : G)).toMonoidHom hvZ)

private theorem closure_smul_imgTil_W_le_imgTil_conjClosure {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
    closure (⋃ k ∈ Hinf (MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))),
        k • ((imgTil (⊥ : Subgroup G) c.V hV c.W : Subgroup (c.toCtx23L.W hV)) :
          Set (c.toCtx23L.W hV))) ≤
      imgTil (⊥ : Subgroup G) c.V hV (conjClosure c.K c.W) := by
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  have himgK := Ctx23L.map_Hinf_inf_eq c.toCtx23L hV h4 h1930
  refine (Subgroup.closure_le _).2 ?_
  rintro w hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨k, hw⟩ := hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨hk, hw⟩ := hw
  rw [Set.mem_smul_set] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  obtain ⟨v, hvW, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) c.V hV c.W s).1 hs
  rw [← himgK] at hk
  obtain ⟨k₀, hk₀, hk₀φ⟩ := Subgroup.mem_map.1 hk
  have hk₀K : (k₀ : G) ∈ c.K := Subgroup.mem_subgroupOf.1 hk₀
  rw [← hk₀φ, phiL_smul_mkTil c.toCtx23L hV k₀ v]
  refine (mem_imgTil (⊥ : Subgroup G) c.V hV (conjClosure c.K c.W) _).2 ⟨_, ?_, rfl⟩
  rw [actStab_apply_val]
  change (k₀ : G) * v.val * (k₀ : G)⁻¹ ∈ conjClosure c.K c.W
  have hle : c.W.map (MulAut.conj (k₀ : G)).toMonoidHom ≤ conjClosure c.K c.W :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf c.K c.W) => K) _
      ⟨(k₀ : G), hk₀K, rfl⟩ le_rfl
  simpa [MulAut.conj_apply] using
    hle (Subgroup.mem_map_of_mem (MulAut.conj (k₀ : G)).toMonoidHom hvW)

private theorem conjClosure_K_W_le_V (c : Ctx2311 D Ch) :
    conjClosure c.K c.W ≤ c.V :=
  uc22p22v_conjClosure_le (K_le_normalizer_V c) (W_le_V c)

theorem conjClosure_K_W_eq_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hKS : KSL3Span) (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    conjClosure c.K c.W = c.V := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) = c.Ztil hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L hV hm hSLH hnat
  have hmain := hKS (c.toCtx23L.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hSLH hnat hm
    (c.sylowStar hV)
  have hKS2 := hmain.2 (c.Pstar hV) (normalizer_sylowStar_le_Pstar c hV)
    (Pstar_isCoatom c hV hker) (Pstar_ne_stabilizer c hV h4 h1930 hm hSLH hnat)
  rw [hℓ] at hKS2
  have htop : imgTil (⊥ : Subgroup G) c.V hV (conjClosure c.K c.W) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hKS2]
    exact (closure_smul_mono (K := Hinf (MulAction.stabilizer ↥(c.H hV)
      (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))))
      (line_le_imgTil_W c hV hm hSLH hnat)).trans
      (closure_smul_imgTil_W_le_imgTil_conjClosure c hV h4 h1930)
  exact eq_of_imgTil_eq_top c.toCtx23L hV (conjClosure_K_W_le_V c) htop

theorem imgTil_W_le_line {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    imgTil (⊥ : Subgroup G) c.V hV c.W ≤
      closure (⋃ p ∈ c.Pstar hV,
        p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) := by
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  have hZtil := imgTil_Z_le_Ztil c hV hm hSLH hnat
  have hWle : c.W ≤ preTil (⊥ : Subgroup G) c.V hV (closure (⋃ p ∈ c.Pstar hV,
      p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))) := by
    change conjClosure c.X D.Z ≤ preTil (⊥ : Subgroup G) c.V hV _
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, hgX, rfl⟩ := hK
    rintro _ ⟨z, hzZ, rfl⟩
    have hgL : (g : G) ∈ c.L := c.hX.1.2.1 hgX
    have hzV : z ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hzZ
    refine (mem_preTil (⊥ : Subgroup G) c.V hV _).2
      ⟨actStab (⊥ : Subgroup G) c.V hV ⟨(g : G), c.L_le_stabTil hgL⟩
        (CFSG.Quasithin.IntMod.mk hV ⟨z, hzV⟩), ?_, ?_⟩
    · rw [actStab_apply_val]
      change (g : G) * z * (g : G)⁻¹ = MulAut.conj g z
      rw [MulAut.conj_apply]
    · rw [← phiL_smul_mkTil c.toCtx23L hV ⟨(g : G), hgL⟩
        (CFSG.Quasithin.IntMod.mk hV ⟨z, hzV⟩)]
      refine Subgroup.subset_closure (Set.mem_iUnion.mpr
        ⟨c.phiL hV ⟨(g : G), hgL⟩, ?_⟩)
      refine Set.mem_iUnion.mpr
        ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hgX, hgL⟩), ?_⟩
      exact Set.mem_smul_set.mpr ⟨_, hZtil ((mem_imgTil (⊥ : Subgroup G) c.V hV D.Z _).2
        ⟨CFSG.Quasithin.IntMod.mk hV ⟨z, hzV⟩, hzZ, rfl⟩), rfl⟩
  refine (Subgroup.map_le_iff_le_comap).mpr ?_
  intro u hu
  exact (mem_preTil_iff_of_mem (⊥ : Subgroup G) c.V hV _ u.2).1 (hWle hu)

private theorem mkTil_mem_line {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    ∀ (w : G) (hwW : w ∈ c.W),
      mkTil (⊥ : Subgroup G) c.V hV
          (CFSG.Quasithin.IntMod.mk hV ⟨w, W_le_V c hwW⟩) ∈
        closure (⋃ p ∈ c.Pstar hV,
          p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) := by
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  have hline : imgTil (⊥ : Subgroup G) c.V hV c.W = closure (⋃ p ∈ c.Pstar hV,
      p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) :=
    le_antisymm (imgTil_W_le_line c hV hm hSLH hnat) (line_le_imgTil_W c hV hm hSLH hnat)
  intro w hwW
  rw [← hline]
  exact (mem_imgTil (⊥ : Subgroup G) c.V hV c.W _).2
    ⟨CFSG.Quasithin.IntMod.mk hV ⟨w, W_le_V c hwW⟩, hwW, rfl⟩

theorem mem_conjSubgroup_of_phiL_smul {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {x : ↥c.L}
    {v : CFSG.Quasithin.IntMod c.V hV} (hvZ : v.val ∈ D.Z) {w : G} (hwV : w ∈ c.V)
    (h : (c.phiL hV x : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.IntMod.mk hV ⟨w, hwV⟩)) :
    w ∈ CFSG.Quasithin.conjSubgroup D.Z x⁻¹ := by
  have hval : actStab (⊥ : Subgroup G) c.V hV ⟨(x : G), c.L_le_stabTil x.2⟩ v =
      CFSG.Quasithin.IntMod.mk hV ⟨w, hwV⟩ :=
    mkTil_injective_bot c.V hV (by
      rw [← Ctx23L.phiL_apply_mkTil c hV x v]
      exact h)
  have hw_eq : w = (x : G) * v.val * (x : G)⁻¹ := by
    have h' := congrArg CFSG.Quasithin.IntMod.val hval
    rw [actStab_apply_val] at h'
    exact h'.symm
  rw [CFSG.Quasithin.mem_conjSubgroup_iff, hw_eq]
  have hgroup : (x : G)⁻¹ * ((x : G) * v.val * (x : G)⁻¹) * ((x : G)⁻¹)⁻¹ = v.val := by
    group
  rw [hgroup]
  exact hvZ

private theorem exists_conjSubgroup_of_mem_line {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D) (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hKL : KSL3Line) (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    ∀ (w : G) (hwW : w ∈ c.W),
      mkTil (⊥ : Subgroup G) c.V hV
          (CFSG.Quasithin.IntMod.mk hV ⟨w, W_le_V c hwW⟩) ∈
        closure (⋃ p ∈ c.Pstar hV,
          p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) →
      ∃ x ∈ c.X, w ∈ CFSG.Quasithin.conjSubgroup D.Z x := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) = c.Ztil hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L hV hm hSLH hnat
  have hZ := Ztil_eq_imgTil_Z c hV hm hSLH hnat
  have hfirst := (hKL (c.toCtx23L.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hSLH hnat hm
    (c.sylowStar hV) (c.Pstar hV) (normalizer_sylowStar_le_Pstar c hV)
    (Pstar_isCoatom c hV hker) (Pstar_ne_stabilizer c hV h4 h1930 hm hSLH hnat)).1
  rw [hℓ] at hfirst
  intro w hwW hmem
  obtain ⟨p, hp, hmem2⟩ := hfirst _ hmem
  rw [Set.mem_smul_set] at hmem2
  obtain ⟨z, hz, hwz⟩ := hmem2
  rw [hZ] at hz
  obtain ⟨v, hvZ, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) c.V hV D.Z z).1 hz
  obtain ⟨x, hxsub, rfl⟩ := Subgroup.mem_map.1 hp
  exact ⟨x⁻¹, c.X.inv_mem (Subgroup.mem_subgroupOf.1 hxsub).1,
    mem_conjSubgroup_of_phiL_smul c.toCtx23L hV hvZ (W_le_V c hwW) hwz⟩

theorem exists_mem_X_of_mem_W_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hKL : KSL3Line) (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    ∀ w ∈ c.W, ∃ x ∈ c.X, w ∈ CFSG.Quasithin.conjSubgroup D.Z x := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  intro w hwW
  exact exists_conjSubgroup_of_mem_line c h4 h1930 hV hm hSLH hnat hKL hker w hwW
    (mkTil_mem_line c hV hm hSLH hnat w hwW)

private theorem mkTil_commutator_eq {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (t : ↥D.T)
    (s : ↥(c.sylowStar hV)) (hs_eq : (s : MulAut (c.W hV)) = c.phiT hV t)
    (v : CFSG.Quasithin.IntMod c.V hV) :
    (mkTil (⊥ : Subgroup G) c.V hV v) *
        ((s : MulAut (c.W hV)) ((mkTil (⊥ : Subgroup G) c.V hV v)⁻¹)) =
      mkTil (⊥ : Subgroup G) c.V hV
        (v * (actStab (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩ v)⁻¹) := by
  rw [map_inv, hs_eq]
  have hphi : (c.phiT hV t) (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV
        (actStab (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩ v) := by
    change actTil (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩
        (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV
        (actStab (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩ v)
    exact actTil_mk (⊥ : Subgroup G) c.V hV _ v
  rw [hphi, ← map_inv, ← map_mul]

private theorem val_mul_actStab_inv {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (t : ↥D.T)
    (v : CFSG.Quasithin.IntMod c.V hV) {w : G} (hvw : v.val = w) :
    (v * (actStab (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩ v)⁻¹).val =
      ⁅w, (t : G)⁆ := by
  rw [CFSG.Quasithin.IntMod.val_mul, CFSG.Quasithin.IntMod.val_inv, actStab_apply_val,
    commutatorElement_def, hvw]
  group

private theorem commutator_mem_Z_of_mem_line {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    {π : Subgroup (c.toCtx23L.W hV)}
    (hline : ∀ s ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)), ∀ x ∈ π,
      x⁻¹ * ((s : MulAut (c.toCtx23L.W hV)) x) ∈ c.Ztil hV)
    {w : G} (hw : w ∈ c.W)
    (hπ : mkTil (⊥ : Subgroup G) c.V hV
      (CFSG.Quasithin.IntMod.mk hV ⟨w, W_le_V c hw⟩) ∈ π) (t : ↥D.T) :
    ⁅w, (t : G)⁆ ∈ D.Z := by
  let v : CFSG.Quasithin.IntMod c.V hV :=
    CFSG.Quasithin.IntMod.mk hV ⟨w, W_le_V c hw⟩
  obtain ⟨s, hsS, hs_eq⟩ :=
    c.toCtx23L.phiT_mem_sylowStar_of_sl3 hV (by omega) hnat t
  have hq := hline s hsS ((mkTil (⊥ : Subgroup G) c.V hV v)⁻¹)
    (Subgroup.inv_mem _ hπ)
  rw [inv_inv] at hq
  rw [mkTil_commutator_eq c.toCtx23L hV t ⟨s, hsS⟩ hs_eq v] at hq
  have hval := val_mul_actStab_inv c.toCtx23L hV t v rfl
  have hcommV : ⁅w, (t : G)⁆ ∈ c.V :=
    hval ▸ (v * (actStab (⊥ : Subgroup G) c.V hV
      ⟨(t : G), c.T_le_stabTil t.2⟩ v)⁻¹).2
  have heq : CFSG.Quasithin.IntMod.mk hV ⟨⁅w, (t : G)⁆, hcommV⟩ =
      v * (actStab (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩ v)⁻¹ :=
    CFSG.Quasithin.IntMod.val_injective hval.symm
  rw [← heq] at hq
  have hZ := Ztil_eq_imgTil_Z c hV hm hSLH hnat
  rw [hZ, mem_imgTil] at hq
  obtain ⟨x, hxZ, hxeq⟩ := hq
  have hx : x = CFSG.Quasithin.IntMod.mk hV ⟨⁅w, (t : G)⁆, hcommV⟩ :=
    mkTil_injective_bot c.V hV hxeq
  rw [hx] at hxZ
  exact hxZ

theorem commutator_W_T_le_Z_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hKL : KSL3Line) (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    ⁅c.W, D.T⁆ ≤ D.Z := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) = c.Ztil hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L hV hm hSLH hnat
  have hline0 := (hKL (c.toCtx23L.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hSLH hnat hm
    (c.sylowStar hV) (c.Pstar hV) (normalizer_sylowStar_le_Pstar c hV)
    (Pstar_isCoatom c hV hker) (Pstar_ne_stabilizer c hV h4 h1930 hm hSLH hnat)).2
  rw [hℓ] at hline0
  have hline : ∀ s ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)),
      ∀ x ∈ closure (⋃ p ∈ c.Pstar hV,
        p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))),
      x⁻¹ * ((s : MulAut (c.toCtx23L.W hV)) x) ∈ c.Ztil hV := by
    intro s hs x hx
    simpa only [MulAction.compHom_smul_def, MulAut.smul_def, Subgroup.coe_subtype] using
      hline0 s hs x hx
  refine Subgroup.commutator_le.2 ?_
  intro w hw t ht
  exact commutator_mem_Z_of_mem_line c hV hm hSLH hnat hline hw
    (mkTil_mem_line c hV hm hSLH hnat w hw) ⟨t, ht⟩

theorem geom2311_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hline : S23_5_line D Ch) (hKN : KNshape) (hK : KOrdNatural) (hS : KSchurL2)
    (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch)
    (hN3 : S23_9_NotLarge D Ch) (hKS : KSL3Span) (hKL : KSL3Line) :
    (H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch,
        c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch, ∀ w ∈ c.W, ∃ x ∈ c.X,
        w ∈ CFSG.Quasithin.conjSubgroup D.Z x) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN hK hS hS3 hN1 hN2 hN3
    exact conjClosure_K_W_eq_of_sl3 c h4 h1930 hV hm hSLH hnat hKS hker
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN hK hS hS3 hN1 hN2 hN3
    exact commutator_V_K_eq_of_sl3 c h4 h1930 hV hm hSLH hnat hKS
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN hK hS hS3 hN1 hN2 hN3
    exact L_inf_centralizer_V_eq_of_ker c hV hker
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN hK hS hS3 hN1 hN2 hN3
    exact exists_mem_X_of_mem_W_of_sl3 c h4 h1930 hV hm hSLH hnat hKL hker
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN hK hS hS3 hN1 hN2 hN3
    exact commutator_W_T_le_Z_of_sl3 c h4 h1930 hV hm hSLH hnat hKL hker

end Ctx2311

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
