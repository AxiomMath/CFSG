module

public import CFSG.GroupTheory.BinaryNaturalSLThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotLarge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3Geom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mkTil_injective_bot (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro a b h
  rw [← TwelveShort.mkTilEquiv_apply V hV a, ← TwelveShort.mkTilEquiv_apply V hV b] at h
  exact (TwelveShort.mkTilEquiv V hV).injective h

theorem eq_of_imgTil_eq_top {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {U : Subgroup G} (hU : U ≤ c.V)
    (h : imgTil (⊥ : Subgroup G) c.V hV U = ⊤) : U = c.V := by
  refine le_antisymm hU ?_
  intro v hv
  have hmem : mkTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩) ∈
      imgTil (⊥ : Subgroup G) c.V hV U := by
    rw [h]
    exact Subgroup.mem_top _
  rw [mem_imgTil] at hmem
  obtain ⟨u, hu, hmu⟩ := hmem
  have huinj : u = CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩ := mkTil_injective_bot c.V hV hmu
  have hval : u.val = v := congrArg CFSG.Quasithin.IntMod.val huinj
  rwa [← hval]

private theorem Ztil_le_fixedPointSubgroup_sylowStar {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    c.Ztil hV ≤ fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  intro z hz
  change z ∈ FixedPoints.subgroup ↥(c.sylowStar hV) (c.W hV)
  rw [FixedPoints.mem_subgroup]
  intro s
  obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.1 (by rw [← c.sylowStar_coe hV]; exact s.2)
  have hxT : (x : G) ∈ D.T := Subgroup.mem_subgroupOf.1 hx
  have hcent : (x : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_omegaOneCenterIn D.T hxT
  have hfixx : (c.phiL hV x) • z = z := by
    have hmem := (c.phiL_mem_fixingSubgroup_Ztil_iff hV x).2 hcent
    rw [fixingSubgroupOf, mem_fixingSubgroup_iff] at hmem
    exact hmem z hz
  have hs_eq : s = ⟨c.phiL hV x, by rw [hxφ]; exact s.2⟩ := by
    apply Subtype.ext
    exact hxφ.symm
  rw [hs_eq]
  exact hfixx

private theorem fixed_sylowStar_mem_Ztil_of_sl3_aux {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    ∀ w : c.W hV, (∀ s ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)),
      (s : MulAut (c.W hV)) w = w) → w ∈ c.Ztil hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hZel : IsElemAbelian 2 D.Z := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp b.2).2.1 a
        (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp a.2).1
    · exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hx).2.2
  have hZcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hZel
  have hY : Nat.card (c.Ztil hV) = 2 ^ CFSG.Open.pRank 2 D.Z := by
    rw [c.card_Ztil hV, hZcard]
  have hfixZ : ∀ s ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)), ∀ y ∈ c.Ztil hV,
      (s : MulAut (c.W hV)) y = y := by
    intro s hs y hy
    have hy' : y ∈ fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) :=
      Ztil_le_fixedPointSubgroup_sylowStar c hV hy
    change y ∈ FixedPoints.subgroup ↥(c.sylowStar hV) (c.W hV) at hy'
    rw [FixedPoints.mem_subgroup] at hy'
    exact hy' ⟨s, hs⟩
  intro w hw
  exact CFSG.Quasithin.BinaryNaturalSL.mem_of_fixed_sylow_three hnat (by omega)
    (c.sylowStar hV) hfixZ hY hw

theorem fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  refine le_antisymm ?_ (Ztil_le_fixedPointSubgroup_sylowStar c hV)
  intro w hw
  change w ∈ FixedPoints.subgroup ↥(c.sylowStar hV) (c.W hV) at hw
  rw [FixedPoints.mem_subgroup] at hw
  exact fixed_sylowStar_mem_Ztil_of_sl3_aux c hV hm hSLH hnat w fun s hs => hw ⟨s, hs⟩

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)

theorem L_inf_centralizer_V_eq_of_ker (hV : IsElemAbelian 2 c.V)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L := by
  ext x
  rw [Subgroup.mem_inf, CFSG.Open.pCoreOf, Subgroup.mem_map]
  constructor
  · rintro ⟨hxL, hxcent⟩
    have h1 : c.phiL hV ⟨x, hxL⟩ = 1 := (c.phiL_eq_one_iff hV ⟨x, hxL⟩).2 hxcent
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    rw [← hker, MonoidHom.mem_ker]
    exact h1
  · rintro ⟨y, hy, rfl⟩
    have h1 : c.phiL hV y = 1 := by
      rw [← hker, MonoidHom.mem_ker] at hy
      exact hy
    exact ⟨y.2, (c.phiL_eq_one_iff hV y).1 h1⟩

theorem W_le_V : c.W ≤ c.V := by
  obtain ⟨hpar, -, -⟩ := c.hX
  obtain ⟨-, hXL, -⟩ := hpar
  unfold Ctx2311.W Ctx23L.V
  exact uc22p22v_conjClosure_mono
    (hXL.trans (le_sup_left.trans (Ctx23L.sup_le_N D Ch c.toCtx23L))) D.Z

theorem K_le_L : c.K ≤ c.L := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right

theorem K_le_normalizer_V : c.K ≤ Subgroup.normalizer (c.V : Set G) := by
  unfold Ctx2311.K Ctx23L.V
  exact (K_le_L c).trans
    ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans ((Ctx23L.sup_le_N D Ch c.toCtx23L).trans
      (uc22p22v_le_normalizer_conjClosure c.N D.Z)))

theorem commutator_V_K_le_V : ⁅c.V, c.K⁆ ≤ c.V := by
  refine Subgroup.commutator_le.2 ?_
  intro v hv k hk
  have hconj : k * v⁻¹ * k⁻¹ ∈ c.V :=
    (Subgroup.mem_normalizer_iff.mp (K_le_normalizer_V c hk) v⁻¹).mp (c.V.inv_mem hv)
  have heq : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact c.V.mul_mem hv hconj

private theorem val_inv_mul_actStab {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) (k₀ : ↥c.L) (v : CFSG.Quasithin.IntMod c.V hV) :
    (v⁻¹ * actStab (⊥ : Subgroup G) c.V hV ⟨(k₀ : G), c.L_le_stabTil k₀.2⟩ v).val =
      ⁅(v.val)⁻¹, (k₀ : G)⁆ := by
  rw [CFSG.Quasithin.IntMod.val_mul, CFSG.Quasithin.IntMod.val_inv, actStab_apply_val,
    commutatorElement_def]
  group

private theorem closure_commutators_le_imgTil_commutator {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (hV : IsElemAbelian 2 c.V) :
    letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
    ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) =
        Hinf (MulAction.stabilizer ↥(c.H hV)
          (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))) →
      closure {w : c.toCtx23L.W hV | ∃ k ∈ Hinf (MulAction.stabilizer ↥(c.H hV)
          (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))),
          ∃ x : c.toCtx23L.W hV, w = x⁻¹ * (k • x)} ≤
        imgTil (⊥ : Subgroup G) c.V hV ⁅c.V, c.K⁆ := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  intro himgK
  refine (Subgroup.closure_le _).2 ?_
  rintro w ⟨k, hk, x, rfl⟩
  rw [← himgK] at hk
  obtain ⟨k₀, hk₀, hk₀φ⟩ := Subgroup.mem_map.1 hk
  have hk₀K : (k₀ : G) ∈ c.K := Subgroup.mem_subgroupOf.1 hk₀
  obtain ⟨v, -, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) c.V hV x
  have hsmul : k • mkTil (⊥ : Subgroup G) c.V hV v =
      mkTil (⊥ : Subgroup G) c.V hV
        (actStab (⊥ : Subgroup G) c.V hV ⟨(k₀ : G), c.L_le_stabTil k₀.2⟩ v) := by
    rw [← hk₀φ]
    exact Ctx23L.phiL_apply_mkTil c.toCtx23L hV k₀ v
  have hmul : (mkTil (⊥ : Subgroup G) c.V hV v)⁻¹ *
      mkTil (⊥ : Subgroup G) c.V hV
        (actStab (⊥ : Subgroup G) c.V hV ⟨(k₀ : G), c.L_le_stabTil k₀.2⟩ v) =
      mkTil (⊥ : Subgroup G) c.V hV
        (v⁻¹ * actStab (⊥ : Subgroup G) c.V hV ⟨(k₀ : G), c.L_le_stabTil k₀.2⟩ v) := by
    rw [← map_inv, ← map_mul]
  rw [hsmul, hmul]
  refine (mem_imgTil (⊥ : Subgroup G) c.V hV ⁅c.V, c.K⁆ _).2 ⟨_, ?_, rfl⟩
  rw [val_inv_mul_actStab c hV k₀ v]
  exact Subgroup.commutator_mem_commutator (c.V.inv_mem v.2) hk₀K

theorem commutator_V_K_eq_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hKS : KSL3Span) :
    ⁅c.V, c.K⁆ = c.V := by
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
  have hℓ := fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L hV hm hSLH hnat
  have himgK := Ctx23L.map_Hinf_inf_eq c.toCtx23L hV h4 h1930
  have hmain := hKS (c.toCtx23L.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hSLH hnat hm
    (c.sylowStar hV)
  have hfirst : closure {w : c.toCtx23L.W hV | ∃ k ∈ Hinf (MulAction.stabilizer ↥(c.H hV)
      (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))),
      ∃ x : c.toCtx23L.W hV, w = x⁻¹ * (k • x)} = ⊤ := by
    have h := hmain.1
    rwa [hℓ] at h
  have hgen := closure_commutators_le_imgTil_commutator c hV himgK
  exact eq_of_imgTil_eq_top c.toCtx23L hV (commutator_V_K_le_V c)
    (le_antisymm le_top (hfirst.symm.trans_le hgen))

@[expose] noncomputable def Pstar (hV : IsElemAbelian 2 c.V) : Subgroup ↥(c.H hV) :=
  ((c.X ⊓ c.L).subgroupOf c.L).map (c.phiL hV)

private theorem Pstar_ne_top {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    c.Pstar hV ≠ ⊤ := by
  obtain ⟨hpar, hXne, -⟩ := c.hX
  obtain ⟨hOX, hXL, -⟩ := hpar
  have hkerle : (c.phiL hV).ker ≤ ((c.X ⊓ c.L).subgroupOf c.L) := by
    rw [hker]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ⟨hOX (Subgroup.mem_map_of_mem c.L.subtype hx), x.2⟩
  intro htop
  have hmap : ((c.X ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = ⊤ := htop
  have hsup : ((c.X ⊓ c.L).subgroupOf c.L) ⊔ (c.phiL hV).ker = ⊤ := by
    rw [← Subgroup.comap_map_eq (f := c.phiL hV), hmap, Subgroup.comap_top]
  have hXtop : ((c.X ⊓ c.L).subgroupOf c.L) = ⊤ := by
    rw [← sup_eq_left.mpr hkerle, hsup]
  exact hXne (le_antisymm hXL ((Subgroup.subgroupOf_eq_top.mp hXtop).trans inf_le_left))

private theorem X_le_map_comap_of_Pstar_lt {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) {Q : Subgroup ↥(c.H hV)} (hQ : c.Pstar hV < Q) :
    c.X ≤ (Q.comap (c.phiL hV)).map c.L.subtype := by
  obtain ⟨hpar, -, -⟩ := c.hX
  obtain ⟨-, hXL, -⟩ := hpar
  have hXsub : ((c.X ⊓ c.L).subgroupOf c.L) = c.X.subgroupOf c.L := by
    rw [inf_eq_left.mpr hXL]
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, hXL hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  exact hQ.le (Subgroup.mem_map_of_mem _ (by
    rw [hXsub]
    exact Subgroup.mem_subgroupOf.mpr hx))

private theorem parabolicOf_map_comap_of_Pstar_lt {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (hV : IsElemAbelian 2 c.V) {Q : Subgroup ↥(c.H hV)}
    (hQ : c.Pstar hV < Q) :
    ParabolicOf c.L ((Q.comap (c.phiL hV)).map c.L.subtype) := by
  obtain ⟨hpar, -, -⟩ := c.hX
  obtain ⟨hOX, -, hparX⟩ := hpar
  have hXY := X_le_map_comap_of_Pstar_lt c hV hQ
  refine ⟨hOX.trans hXY, Subgroup.map_subtype_le _, ?_⟩
  have hmono : (c.X.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) ≤
      (((Q.comap (c.phiL hV)).map c.L.subtype).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono c.L hXY)
  obtain ⟨S, hS⟩ := hparX
  exact ⟨S, hS.trans hmono⟩

private theorem comap_eq_X_of_Pstar_lt {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) {Q : Subgroup ↥(c.H hV)} (hQ : c.Pstar hV < Q)
    (hQtop : Q ≠ ⊤) : Q.comap (c.phiL hV) = c.X.subgroupOf c.L := by
  obtain ⟨-, -, hmax⟩ := c.hX
  let Y : Subgroup G := (Q.comap (c.phiL hV)).map c.L.subtype
  have hYsub : Y.subgroupOf c.L = Q.comap (c.phiL hV) :=
    CFSG.Quasithin.A4.subgroupOf_map_subtype' c.L (Q.comap (c.phiL hV))
  have hXY : c.X ≤ Y := X_le_map_comap_of_Pstar_lt c hV hQ
  have hYpar : ParabolicOf c.L Y := parabolicOf_map_comap_of_Pstar_lt c hV hQ
  have hYne : Y ≠ c.L := by
    intro hYL
    have h1 : Q.comap (c.phiL hV) = ⊤ := by
      rw [← hYsub, hYL, Subgroup.subgroupOf_self]
    exact hQtop (by
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := c.phiL hV) (c.phiL_surjective hV) Q,
        h1, Subgroup.map_top_of_surjective _ (c.phiL_surjective hV)])
  have h := hYsub
  rw [hmax Y hYpar hXY hYne] at h
  exact h.symm

private theorem eq_Pstar_of_Pstar_lt {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) {Q : Subgroup ↥(c.H hV)} (hQ : c.Pstar hV < Q)
    (hQtop : Q ≠ ⊤) : Q = c.Pstar hV := by
  obtain ⟨hpar, -, -⟩ := c.hX
  obtain ⟨-, hXL, -⟩ := hpar
  have hXsub : ((c.X ⊓ c.L).subgroupOf c.L) = c.X.subgroupOf c.L := by
    rw [inf_eq_left.mpr hXL]
  have h2 := comap_eq_X_of_Pstar_lt c hV hQ hQtop
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := c.phiL hV) (c.phiL_surjective hV) Q, h2]
  change (c.X.subgroupOf c.L).map (c.phiL hV) = c.Pstar hV
  rw [show c.Pstar hV = ((c.X ⊓ c.L).subgroupOf c.L).map (c.phiL hV) from rfl, ← hXsub]

theorem Pstar_isCoatom (hV : IsElemAbelian 2 c.V)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) : IsCoatom (c.Pstar hV) := by
  refine ⟨Pstar_ne_top c hV hker, fun Q hQ => ?_⟩
  by_contra hQtop
  exact (ne_of_lt hQ) (eq_Pstar_of_Pstar_lt c hV hQ hQtop).symm

end Ctx2311

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
