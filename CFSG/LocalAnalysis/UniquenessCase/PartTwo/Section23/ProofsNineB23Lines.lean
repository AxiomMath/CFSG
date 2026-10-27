module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotLarge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.GroupTheory.Fitting.LayerProjection
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofBFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineBasic
public import CFSG.Quasithin.Background.RonanE111MemE2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineB23

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup CFSG.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem bar2_congr {X : Type} [Group X] {A B : Subgroup X} (h : A = B)
    {P : (T : Type) → [Group T] → Prop} (hP : P (Bar2 A)) : P (Bar2 B) := by
  subst h
  exact hP

theorem isSimpleGroup_of_b23Shape {S : Type} [Group S] [Finite S] (h : B23Shape S) :
    IsSimpleGroup S := by
  rcases h with ⟨a, hL2 | hSz⟩ | ⟨q, hq, hq2, hL2Odd⟩ | hJ1
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2Odd
  · exact (kJ1_holds S hJ1).2.1

theorem isSimpleGroup_of_isL2 {S : Type} [Group S] {m : ℕ} (h : IsL2 S m) : IsSimpleGroup S :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem center_eq_bot_of_b23Shape {S : Type} [Group S] [Finite S] (h : B23Shape S)
    (hq : CFSG.Open.IsQuasisimple S) : Subgroup.center S = ⊥ := by
  haveI : IsSimpleGroup S := isSimpleGroup_of_b23Shape h
  exact uc22p21k_center_eq_bot hq

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem Kstar_eq_stabilizer_Ztil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    Kstar c hV = Hinf (MulAction.stabilizer ↥(c.H hV)
      (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)))) := by
  let K₀ : Subgroup G := Hinf (D.M ⊓ c.L)
  have hKleL : K₀ ≤ c.L := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right
  have hmap : (⊤ : Subgroup ↥K₀).map (Subgroup.inclusion hKleL) = K₀.subgroupOf c.L := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  calc
    Kstar c hV = ((c.phiL hV).comp (Subgroup.inclusion hKleL)).range := rfl
    _ = (⊤ : Subgroup ↥K₀).map ((c.phiL hV).comp (Subgroup.inclusion hKleL)) :=
      MonoidHom.range_eq_map _
    _ = ((⊤ : Subgroup ↥K₀).map (Subgroup.inclusion hKleL)).map (c.phiL hV) := by
      rw [Subgroup.map_map]
    _ = (K₀.subgroupOf c.L).map (c.phiL hV) := by rw [hmap]
    _ = Hinf (MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)))) :=
      c.map_Hinf_inf_eq hV h4 h1930

theorem Kstar_eq_Hinf_stabilizer_sylowStar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)))) = Kstar c hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  rw [c.fixedPointSubgroup_sylowStar_eq_Ztil hV ha hnat h4 h1930]
  exact (c.Kstar_eq_stabilizer_Ztil hV h4 h1930).symm

theorem Hinf_inf_L_eq_bot_of_Kstar_eq_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hbot : Kstar c hV = ⊥) : Hinf (D.M ⊓ c.L) = ⊥ := by
  let K₀ : Subgroup G := Hinf (D.M ⊓ c.L)
  have hKleL : K₀ ≤ c.L := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right
  have hmem : ∀ k : ↥K₀, c.phiL hV ⟨(k : G), hKleL k.2⟩ = 1 := by
    intro k
    have hk : ((c.phiL hV).comp (Subgroup.inclusion hKleL)) k ∈ Kstar c hV := by
      exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
    rw [hbot] at hk
    exact Subgroup.mem_bot.mp hk
  have hleker : K₀.subgroupOf c.L ≤ (c.phiL hV).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hmem ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
  let e : ↥K₀ ≃* ↥(K₀.subgroupOf c.L) :=
    (Subgroup.subgroupOfEquivOfLe hKleL).symm
  let incl : ↥K₀ →* ↥(c.phiL hV).ker :=
    (Subgroup.inclusion hleker).comp e.toMonoidHom
  have hinj : Function.Injective incl :=
    (Subgroup.inclusion_injective hleker).comp e.injective
  haveI : Group.IsSolvable ↥(c.phiL hV).ker := c.phiL_ker_isSolvable hV hK hnat
  have hsolv : Group.IsSolvable ↥K₀ :=
    Group.isSolvable_of_isSolvable_injective (f := incl) hinj
  have hperf : ⁅K₀, K₀⁆ = K₀ := c.Hinf_inf_L_perfect
  haveI : Group.IsPerfect ↥K₀ := Subgroup.isPerfect_iff.mpr hperf
  by_contra hne
  haveI : Nontrivial ↥K₀ := (Subgroup.nontrivial_iff_ne_bot K₀).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥K₀ hsolv

theorem Hinf_inf_L_eq_bot_of_bot_lines (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (hK : KOrdNatural) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : (IsL2 ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
        CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 2 (CFSG.Open.pRank 2 D.Z)) ∨
      (IsOmegaMinus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) ∨
      (IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))) :
    Hinf (D.M ⊓ c.L) = ⊥ := by
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  have hℓ := c.fixedPointSubgroup_sylowStar_eq_Ztil hV ha hnat h4 h1930
  have hd' := hd (c.W hV) (c.H hV) n hnat (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hKstar_eq := c.Kstar_eq_stabilizer_Ztil hV h4 h1930
  have hKstar_bot : Kstar c hV = ⊥ := by
    rw [hKstar_eq]
    rcases hline with hL2 | hOm | hOp
    · have h := hd'.1 hL2
      rwa [hℓ] at h
    · have h := hd'.2.1 hOm
      rwa [hℓ] at h
    · have h := hd'.2.2.1 hOp
      rwa [hℓ] at h
  exact c.Hinf_inf_L_eq_bot_of_Kstar_eq_bot hV hK hnat hKstar_bot

private theorem RKbar_projection_eq_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C) (hshape : B23Shape C)
    (hS : KSub23) (hY : Kbar c ≤ CFSG.layer (Bar2 D.M))
    (hYp : ⁅Kbar c, Kbar c⁆ = Kbar c)
    (hR : Group.IsSolvable ↥(RKbar c hV)) :
    RKbar c hV ≤ (componentProjection hC hY
      (center_eq_bot_of_b23Shape hshape ⟨(Group.isPerfect_def.mp hC.1.1), hC.1.2.1⟩)).ker := by
  let ρ := componentProjection hC hY
    (center_eq_bot_of_b23Shape hshape ⟨(Group.isPerfect_def.mp hC.1.1), hC.1.2.1⟩)
  let Y : Subgroup C := ρ.range
  let ρY : ↥(Kbar c) →* ↥Y := ρ.codRestrict Y fun x => ⟨x, rfl⟩
  have hρY : Function.Surjective ρY := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  let R : Subgroup ↥Y := (RKbar c hV).map ρY
  have hRnorm : R.Normal := (RKbar_normal c hV).map ρY hρY
  haveI : Group.IsSolvable ↥(RKbar c hV) := hR
  have hRsolv : Group.IsSolvable ↥R :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective ρY (RKbar c hV))
  haveI : Group.IsPerfect ↥(Kbar c) := Subgroup.isPerfect_iff.mpr hYp
  haveI : Group.IsPerfect ↥Y := Group.IsPerfect.range ρ
  have hYpperf : ⁅Y, Y⁆ = Y := commutator_eq_self_of_isPerfect_subgroup
  have hRbot : R = ⊥ := hS.2.2 C hshape Y hYpperf R hRnorm hRsolv
  intro r hr
  rw [MonoidHom.mem_ker]
  have hrmem : ρY r ∈ R := Subgroup.mem_map_of_mem ρY hr
  rw [hRbot] at hrmem
  have h1 : ρY r = 1 := Subgroup.mem_bot.mp hrmem
  change (ρ r) = 1
  have h2 : (ρY r : C) = 1 := by rw [h1]; rfl
  exact h2

private theorem Kbar_eq_bot_of_large_lines (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hlarge : IsSLn (KstarBar c hV) 3 (CFSG.Open.pRank 2 D.Z) ∨
      IsSp4 (KstarBar c hV) (CFSG.Open.pRank 2 D.Z) ∨
      IsU4 (KstarBar c hV) (CFSG.Open.pRank 2 D.Z)) :
    Kbar c = ⊥ := by
  have hY : Kbar c ≤ CFSG.layer (Bar2 D.M) := c.barImage_Hinf_inf_L_le_layer hB1 h1930 h3
  have hYp : ⁅Kbar c, Kbar c⁆ = Kbar c := c.barImage_Hinf_inf_L_perfect
  haveI : Group.IsSolvable ↥(RKbar c hV) := RKbar_isSolvable c hV hK hnat
  have hcent : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C →
      Kbar c ≤ Subgroup.centralizer (C : Set (Bar2 D.M)) := by
    intro C hC
    obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC
    have hshape : B23Shape C := by
      rw [← hXC]
      exact shape_barImage_of_mem_calC (c := c) h8 h1930 hX
    have hZ : Subgroup.center C = ⊥ :=
      center_eq_bot_of_b23Shape hshape ⟨(Group.isPerfect_def.mp hC.1.1), hC.1.2.1⟩
    let ρ := componentProjection hC hY hZ
    have hRle : RKbar c hV ≤ ρ.ker :=
      RKbar_projection_eq_bot c hV hC hshape hS hY hYp inferInstance
    obtain ⟨f, hf⟩ := exists_surjective_KstarBar_range_of_RKbar_le_ker c hV ρ hRle
    have hbot : ρ.range = ⊥ := hS.2.1 (KstarBar c hV) C (CFSG.Open.pRank 2 D.Z) h3
      hlarge hshape ρ.range ⟨f, hf⟩
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hρy : ρ ⟨y, hy⟩ = 1 := by
      have hmem : ρ ⟨y, hy⟩ ∈ ρ.range := ⟨⟨y, hy⟩, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hconj := componentProjection_conj hC hY hZ (⟨y, hy⟩ : ↥(Kbar c)) hm
    rw [hρy] at hconj
    have hconj' : y * m * y⁻¹ = m := by simpa using hconj
    calc
      m * y = (y * m * y⁻¹) * y := by rw [hconj']
      _ = y * m := by group
  exact eq_bot_of_perfect_le_layer_of_centralizes_components hY hYp hcent

theorem Hinf_inf_L_eq_bot_of_Kbar_eq_bot (c : Ctx23L D Ch)
    (hbot : Kbar c = ⊥) : Hinf (D.M ⊓ c.L) = ⊥ := by
  let K₀ : Subgroup G := Hinf (D.M ⊓ c.L)
  have hKleM : K₀ ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hker : K₀.subgroupOf D.M ≤ CFSG.pCore 2 ↥D.M := by
    intro x hx
    have hxbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) x ∈ Kbar c := by
      rw [Kbar]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxbar
    have hx1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) x = 1 :=
      Subgroup.mem_bot.mp hxbar
    rw [← QuotientGroup.ker_mk' (N := CFSG.pCore 2 ↥D.M)]
    exact hx1
  have hle : K₀ ≤ CFSG.Open.pCoreOf 2 D.M := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKleM]
    exact Subgroup.map_mono hker
  have hp : IsPGroup 2 K₀ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) D.M).to_le hle
  have hperf : ⁅K₀, K₀⁆ = K₀ := c.Hinf_inf_L_perfect
  haveI : Group.IsPerfect ↥K₀ := Subgroup.isPerfect_iff.mpr hperf
  by_contra hne
  haveI : Nontrivial ↥K₀ := (Subgroup.nontrivial_iff_ne_bot K₀).mpr hne
  exact Group.IsPerfect.not_isNilpotent ↥K₀ hp.isNilpotent

private theorem T_le_normalizer_K (c : Ctx23L D Ch) :
    D.T ≤ Subgroup.normalizer (K c : Set G) := by
  have hM : D.T ≤ Subgroup.normalizer (D.M : Set G) :=
    D.sylowM.le.trans (Subgroup.le_normalizer (H := D.M))
  have hL : D.T ≤ Subgroup.normalizer (c.L : Set G) := fun t ht => c.hL.1.1 ht
  have hML : D.T ≤ Subgroup.normalizer ((D.M ⊓ c.L : Subgroup G) : Set G) :=
    (le_inf hM hL).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := D.M) (K := c.L))
  have h := CFSG.RankThree.PartTwo.Sec15.Proof155w2.le_normalizer_inSubgroup_perfectResidual_of
    (H := D.T) (B := D.M ⊓ c.L) hML
  change D.T ≤ Subgroup.normalizer (Hinf (D.M ⊓ c.L) : Set G)
  simpa only [Hinf] using h

private theorem barImage_T_le_normalizer_Kbar (c : Ctx23L D Ch) :
    barImage D.M D.T ≤ Subgroup.normalizer (Kbar c : Set (Bar2 D.M)) := by
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  have hTK := c.T_le_normalizer_K
  have hsub : D.T.subgroupOf D.M ≤
      Subgroup.normalizer ((K c).subgroupOf D.M : Set ↥D.M) := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hTK ht) (x : G)).1 hx
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hTK ht) (x : G)).2 hx
  calc
    barImage D.M D.T = (D.T.subgroupOf D.M).map π := rfl
    _ ≤ (Subgroup.normalizer ((K c).subgroupOf D.M)).map π := Subgroup.map_mono hsub
    _ ≤ Subgroup.normalizer (((K c).subgroupOf D.M).map π) := Subgroup.le_normalizer_map π
    _ = Subgroup.normalizer (Kbar c : Set (Bar2 D.M)) := rfl

private theorem component_normal_of_mem (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (h1930 : H1930 D) {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C) : C.Normal := by
  obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC
  rw [← hXC]
  exact ((h8 h1930 c X hX).1).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
    (QuotientGroup.mk'_surjective _)

theorem exists_sylow_component_le_normalizer_Kbar (c : Ctx23L D Ch)
    (h8 : S23_8 D Ch) (h1930 : H1930 D) {C : Subgroup (Bar2 D.M)}
    (hC : CFSG.IsComponent C) :
    ∃ T : Sylow 2 ↥C, ∀ t : T,
      ((t : ↥C) : Bar2 D.M) ∈ Subgroup.normalizer (Kbar c : Set (Bar2 D.M)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hCnorm : C.Normal := component_normal_of_mem c h8 h1930 hC
  have hTbar := c.barImage_T_le_normalizer_Kbar
  have hp : IsPGroup 2 (barImage D.M D.T) :=
    (D.sylowG.isPGroup.comap_subtype (K := D.M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
  have hidx : ¬ 2 ∣ (barImage D.M D.T).index := by
    have hTidx : ¬ 2 ∣ D.T.index := by
      obtain ⟨S, hS⟩ := uc22p2214_bor_sylow D.sylowG
      rw [← hS]
      exact S.not_dvd_index
    have h1 : ¬ 2 ∣ (D.T.subgroupOf D.M).index := by
      intro h
      have hdvd : (D.T.subgroupOf D.M).index ∣ D.T.index := by
        simpa only [Subgroup.relIndex] using
          Subgroup.relIndex_dvd_index_of_le (H := D.T) (K := D.M) D.sylowM.le
      exact hTidx (h.trans hdvd)
    exact fun h => h1 (h.trans (Subgroup.index_map_dvd
      (H := D.T.subgroupOf D.M) (f := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
      (QuotientGroup.mk'_surjective _)))
  let Sbar : Sylow 2 (Bar2 D.M) := hp.toSylow hidx
  let S : Sylow 2 ↥C := CFSG.QuasiDihedralFusion.sylowInfNormal Sbar C
  refine ⟨S, ?_⟩
  intro t
  have ht : ((t : ↥C) : Bar2 D.M) ∈ barImage D.M D.T := by
    have h := t.2
    dsimp only [S] at h
    change (t : ↥C) ∈
      ((CFSG.QuasiDihedralFusion.sylowInfNormal Sbar C : Sylow 2 ↥C) : Subgroup ↥C) at h
    rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe] at h
    simpa only [Subgroup.mem_subgroupOf, Sbar, IsPGroup.toSylow_coe] using h
  exact hTbar ht

private theorem RKbar_maximal (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hW : IsSimpleGroup (KstarBar c hV)) :
    ∀ N : Subgroup ↥(Kbar c), RKbar c hV ≤ N → N.Normal →
      N = RKbar c hV ∨ N = ⊤ := by
  intro N hRN hN
  by_cases htop : RKbar c hV = ⊤
  · exact Or.inl ((le_antisymm le_top (htop ▸ hRN)).trans htop.symm)
  · obtain ⟨q, hq⟩ := exists_surjective_KstarBar_quotient c hV
    haveI : Nontrivial (↥(Kbar c) ⧸ RKbar c hV) := QuotientGroup.nontrivial_iff.mpr htop
    haveI : IsSimpleGroup (↥(Kbar c) ⧸ RKbar c hV) :=
      hW.isSimpleGroup_of_surjective q hq
    let π : ↥(Kbar c) →* (↥(Kbar c) ⧸ RKbar c hV) := QuotientGroup.mk' (RKbar c hV)
    have hP : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
    rcases hP.isSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance with hbot | htop'
    · left
      refine le_antisymm ?_ hRN
      intro n hn
      have hmem : π n ∈ N.map π := Subgroup.mem_map_of_mem π hn
      rw [hbot] at hmem
      exact (QuotientGroup.eq_one_iff n).mp (Subgroup.mem_bot.mp hmem)
    · right
      refine le_antisymm le_top ?_
      intro g hg
      have hmem : π g ∈ N.map π := by
        rw [htop']
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hmem
      have hker : n⁻¹ * g ∈ RKbar c hV := by
        rw [← QuotientGroup.ker_mk' (RKbar c hV), MonoidHom.mem_ker]
        change π (n⁻¹ * g) = 1
        rw [map_mul, map_inv, hng]
        group
      have hg' : g = n * (n⁻¹ * g) := by group
      rw [hg']
      exact N.mul_mem hn (hRN hker)

theorem map_RKbar_le_centralizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C) :
    (RKbar c hV).map (Kbar c).subtype ≤
      Subgroup.centralizer (C : Set (Bar2 D.M)) := by
  have hY := c.barImage_Hinf_inf_L_le_layer hB1 h1930 h3
  have hYp := c.barImage_Hinf_inf_L_perfect
  obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC
  have hshape : B23Shape C := by
    rw [← hXC]
    exact shape_barImage_of_mem_calC (c := c) h8 h1930 hX
  have hZ : Subgroup.center C = ⊥ :=
    center_eq_bot_of_b23Shape hshape ⟨Group.isPerfect_def.mp hC.1.1, hC.1.2.1⟩
  let ρ := componentProjection hC hY hZ
  have hRle : RKbar c hV ≤ ρ.ker :=
    RKbar_projection_eq_bot c hV hC hshape hS hY hYp
      (RKbar_isSolvable c hV hK hnat)
  intro r hr
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hρ : ρ r' = 1 := MonoidHom.mem_ker.mp (hRle hr')
  have hconj := componentProjection_conj hC hY hZ r' hm
  rw [hρ] at hconj
  have hconj' : (r' : Bar2 D.M) * m * (r' : Bar2 D.M)⁻¹ = m := by simpa using hconj
  show m * (r' : Bar2 D.M) = (r' : Bar2 D.M) * m
  calc
    m * (r' : Bar2 D.M) =
        ((r' : Bar2 D.M) * m * (r' : Bar2 D.M)⁻¹) * (r' : Bar2 D.M) := by rw [hconj']
    _ = (r' : Bar2 D.M) * m := by group

private theorem Kbar_eq_bot_or_le_component (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hW : IsSimpleGroup (KstarBar c hV)) :
    Kbar c = ⊥ ∨ ∃ C₀ : Subgroup (Bar2 D.M), CFSG.IsComponent C₀ ∧ Kbar c ≤ C₀ := by
  let Y : Subgroup (Bar2 D.M) := Kbar c
  let R : Subgroup (Bar2 D.M) := (RKbar c hV).map Y.subtype
  have hY : Y ≤ CFSG.layer (Bar2 D.M) := c.barImage_Hinf_inf_L_le_layer hB1 h1930 h3
  have hYp : ⁅Y, Y⁆ = Y := c.barImage_Hinf_inf_L_perfect
  have hRY : R ≤ Y := Subgroup.map_subtype_le _
  have hRmax : ∀ N : Subgroup ↥Y, R.subgroupOf Y ≤ N → N.Normal →
      N = R.subgroupOf Y ∨ N = ⊤ := by
    intro N hN hNnorm
    have hRsub : R.subgroupOf Y = RKbar c hV := by
      ext x
      simp only [R, Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨r, hr, hrx⟩
        rw [← Subtype.ext hrx]
        exact hr
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hRsub] at hN ⊢
    exact RKbar_maximal c hV hW N hN hNnorm
  have hRcent : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C →
      R ≤ Subgroup.centralizer (C : Set (Bar2 D.M)) :=
    fun C hC => map_RKbar_le_centralizer c hV h8 hB1 hS hK h1930 h3 hnat hC
  have hZ : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C → Subgroup.center C = ⊥ := by
    intro C hC
    obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC
    have hshape : B23Shape C := by
      rw [← hXC]
      exact shape_barImage_of_mem_calC (c := c) h8 h1930 hX
    exact center_eq_bot_of_b23Shape hshape ⟨Group.isPerfect_def.mp hC.1.1, hC.1.2.1⟩
  have hT : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C →
      ∃ T : Sylow 2 ↥C, ∀ t : T,
        ((t : ↥C) : Bar2 D.M) ∈ Subgroup.normalizer (Y : Set (Bar2 D.M)) :=
    fun C hC => exists_sylow_component_le_normalizer_Kbar c h8 h1930 hC
  exact eq_bot_or_le_component_of_perfect_le_layer hY hYp hRY hRmax hRcent hZ hT

private theorem componentProjection_range_eq_subgroupOf (c : Ctx23L D Ch)
    {C₀ : Subgroup (Bar2 D.M)} (hC₀ : CFSG.IsComponent C₀)
    (hY : Kbar c ≤ CFSG.layer (Bar2 D.M)) (hZ : Subgroup.center C₀ = ⊥)
    (hle : Kbar c ≤ C₀) :
    (componentProjection hC₀ hY hZ).range = (Kbar c).subgroupOf C₀ := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hid := componentProjection_apply_self hC₀ hY hZ (y := r) (hle r.2)
    rw [hid]
    exact r.2
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    refine ⟨⟨(y : Bar2 D.M), hy⟩, Subtype.ext ?_⟩
    exact componentProjection_apply_self hC₀ hY hZ (y := ⟨(y : Bar2 D.M), hy⟩) y.2

private theorem exists_sylow_component_normalizer_subgroupOf (c : Ctx23L D Ch)
    (h8 : S23_8 D Ch) (h1930 : H1930 D) {C₀ : Subgroup (Bar2 D.M)}
    (hC₀ : CFSG.IsComponent C₀) :
    ∃ T : Sylow 2 ↥C₀, ∀ t : T,
      (t : ↥C₀) ∈ Subgroup.normalizer ((Kbar c).subgroupOf C₀ : Set ↥C₀) := by
  obtain ⟨T, hT⟩ := exists_sylow_component_le_normalizer_Kbar c h8 h1930 hC₀
  refine ⟨T, ?_⟩
  intro t
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hT t) (y : Bar2 D.M)).1 hy
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hT t) (y : Bar2 D.M)).2 hy

private theorem Kbar_eq_component_of_le_component (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    {m : ℕ} (hm : 3 ≤ m) (hL2 : IsL2 (KstarBar c hV) m)
    {C₀ : Subgroup (Bar2 D.M)} (hC₀ : CFSG.IsComponent C₀)
    (hKbar_le : Kbar c ≤ C₀) (hne : Kbar c ≠ ⊥) : Kbar c = C₀ := by
  have hY := c.barImage_Hinf_inf_L_le_layer hB1 h1930 h3
  have hYp := c.barImage_Hinf_inf_L_perfect
  obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC₀
  have hshape : B23Shape C₀ := by
    rw [← hXC]
    exact shape_barImage_of_mem_calC (c := c) h8 h1930 hX
  have hZ : Subgroup.center C₀ = ⊥ :=
    center_eq_bot_of_b23Shape hshape ⟨Group.isPerfect_def.mp hC₀.1.1, hC₀.1.2.1⟩
  let ρ := componentProjection hC₀ hY hZ
  let Y : Subgroup ↥C₀ := (Kbar c).subgroupOf C₀
  have hRle : RKbar c hV ≤ ρ.ker :=
    RKbar_projection_eq_bot c hV hC₀ hshape hS hY hYp
      (RKbar_isSolvable c hV hK hnat)
  obtain ⟨f, hf⟩ := exists_surjective_KstarBar_range_of_RKbar_le_ker c hV ρ hRle
  have hrange : ρ.range = Y :=
    c.componentProjection_range_eq_subgroupOf hC₀ hY hZ hKbar_le
  let f' : KstarBar c hV →* ↥Y :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp f
  have hf' : Function.Surjective f' :=
    (MulEquiv.subgroupCongr hrange).surjective.comp hf
  obtain ⟨T, hTnorm⟩ := c.exists_sylow_component_normalizer_subgroupOf h8 h1930 hC₀
  rcases hS.1 (KstarBar c hV) ↥C₀ m hm hL2 hshape Y ⟨f', hf'⟩ ⟨T, hTnorm⟩ with
    hbot | htop
  · exfalso
    apply hne
    refine eq_bot_iff.mpr ?_
    intro x hx
    have hmem : (⟨x, hKbar_le hx⟩ : ↥C₀) ∈ Y := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem))
  · exact le_antisymm hKbar_le fun x hx => by
      have hmem : (⟨x, hx⟩ : ↥C₀) ∈ Y := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem

private theorem toKbar_ker (c : Ctx23L D Ch) :
    (toKbar c).ker = (CFSG.pCore 2 ↥D.M).comap (Subgroup.inclusion (K_le_M c)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  constructor
  · intro hx
    have hx1 : toBar2M c x = 1 := by
      have := congrArg Subtype.val hx
      simpa [toKbar] using this
    exact (QuotientGroup.eq_one_iff _).mp hx1
  · intro hx
    apply Subtype.ext
    have hx1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
        (Subgroup.inclusion (K_le_M c) x) = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    simpa [toKbar, toBar2M] using hx1

private theorem pCore_K_eq_toKbar_ker (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (hS : KSub23) (h1930 : H1930 D)
    {C₀ : Subgroup (Bar2 D.M)} (hC₀ : CFSG.IsComponent C₀) (hKbar : Kbar c = C₀) :
    CFSG.pCore 2 ↥(K c) = (toKbar c).ker := by
  subst hKbar
  have hshape : B23Shape ↥(Kbar c) := by
    obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC₀
    rw [← hXC]
    exact shape_barImage_of_mem_calC (c := c) h8 h1930 hX
  have hpc_le_ker : CFSG.pCore 2 ↥(K c) ≤ (toKbar c).ker := by
    have hYp : ⁅Kbar c, Kbar c⁆ = Kbar c := c.barImage_Hinf_inf_L_perfect
    let R : Subgroup ↥(Kbar c) := (CFSG.pCore 2 ↥(K c)).map (toKbar c)
    have hRnorm : R.Normal := CFSG.pCore_normal.map (toKbar c) (toKbar_surjective c)
    have hRsolv : Group.IsSolvable ↥R := by
      haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥(K c)) := by
        have := (CFSG.pCore_isPGroup (p := 2) (G := ↥(K c))).isNilpotent
        infer_instance
      exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective (toKbar c) _)
    haveI : Group.IsPerfect ↥(Kbar c) := Subgroup.isPerfect_iff.mpr hYp
    have htop : ⁅(⊤ : Subgroup ↥(Kbar c)), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
    have hR'norm : (R.subgroupOf ⊤).Normal := inferInstance
    have hR'solv : Group.IsSolvable ↥(R.subgroupOf ⊤) := by
      haveI : Group.IsSolvable ↥R := hRsolv
      let e := Subgroup.subgroupOfEquivOfLe (le_top : R ≤ ⊤)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hR'bot : R.subgroupOf ⊤ = ⊥ :=
      hS.2.2 ↥(Kbar c) hshape ⊤ htop (R.subgroupOf ⊤) hR'norm hR'solv
    have hRbot : R = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le (le_top : R ≤ ⊤), hR'bot]
      exact Subgroup.map_bot _
    rw [← Subgroup.map_eq_bot_iff]
    exact hRbot
  have hker_le_pc : (toKbar c).ker ≤ CFSG.pCore 2 ↥(K c) := by
    have hp : IsPGroup 2 (toKbar c).ker := by
      rw [c.toKbar_ker]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).comap_of_injective
        (Subgroup.inclusion (K_le_M c)) (Subgroup.inclusion_injective (K_le_M c))
    exact le_sSup ⟨inferInstance, hp⟩
  exact le_antisymm hpc_le_ker hker_le_pc

private theorem bar2_K_mulEquiv_Kbar (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (hS : KSub23) (h1930 : H1930 D)
    {C₀ : Subgroup (Bar2 D.M)} (hC₀ : CFSG.IsComponent C₀) (hKbar : Kbar c = C₀) :
    Nonempty (Bar2 (K c) ≃* ↥(Kbar c)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
      (c.pCore_K_eq_toKbar_ker h8 hS h1930 hC₀ hKbar)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (toKbar c) (toKbar_surjective c))⟩

private theorem mem_calC_of_Kbar_eq_component (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (hS : KSub23) (h1930 : H1930 D)
    {C₀ : Subgroup (Bar2 D.M)} (hC₀ : CFSG.IsComponent C₀) (hKbar : Kbar c = C₀)
    (hne : K c ≠ ⊥) : K c ∈ calC D.M := by
  have hqbar : IsQuasisimple ↥(Kbar c) := by
    rw [hKbar]
    exact hC₀.1
  obtain ⟨e⟩ := c.bar2_K_mulEquiv_Kbar h8 hS h1930 hC₀ hKbar
  have hq : IsQuasisimple (Bar2 (K c)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqbar
  have hsub : CFSG.Open.IsSubnormal (barImage D.M (K c)) ⊤ := by
    rw [show barImage D.M (K c) = Kbar c from rfl, hKbar]
    exact CFSG.Open.IsSubnormal.top_iff.mpr hC₀.2
  have hcal := s23_9_C0_of (D := D) (Ch := Ch) h1930 c hne hq hsub
  simpa only [K] using hcal

private theorem exists_calC_ge_of_Kbar_le_component (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (h1930 : H1930 D) {C₀ : Subgroup (Bar2 D.M)} (hC₀ : CFSG.IsComponent C₀)
    (hle : Kbar c ≤ C₀) :
    ∃ X : Subgroup G, X ∈ calC D.M ∧ K c ≤ X := by
  obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC₀
  refine ⟨X, hX, ?_⟩
  have hKbar_le : Kbar c ≤ barImage D.M X := by rw [hXC]; exact hle
  have hmono : barImage D.M (K c) ≤ barImage D.M (X ⊔ CFSG.Open.pCoreOf 2 D.M) := by
    refine hKbar_le.trans ?_
    unfold barImage
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono D.M le_sup_left)
  have hKpre : K c ≤ barPreimage D.M (barImage D.M (K c)) := by
    intro k hk
    refine uc22p21c_mem_barPreimage.2 ⟨K_le_M c hk, ?_⟩
    rw [barImage]
    exact Subgroup.mem_map.mpr ⟨⟨k, K_le_M c hk⟩, hk, rfl⟩
  have hKle : K c ≤ X ⊔ CFSG.Open.pCoreOf 2 D.M :=
    hKpre.trans (uc22p22u_barPreimage_le (M := D.M)
      (X := X ⊔ CFSG.Open.pCoreOf 2 D.M) (D := barImage D.M (K c)) le_sup_right hmono)
  have hXM : X ≤ D.M := CFSG.Open.IsSubnormal.le hX.1
  have hnorm : D.M ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp (h8 h1930 c X hX).1
  have hSJ : CFSG.Open.pCoreOf 2 D.M ≤ Subgroup.normalizer (X : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M).trans hnorm
  have hpc := CFSG.Quasithin.RonanE111.perfectCore_le_of_le_sup_two
    (J := X) (S := CFSG.Open.pCoreOf 2 D.M) (P := K c) hSJ
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) D.M) hKle
  rw [show K c = Hinf (D.M ⊓ c.L) from rfl] at hpc
  rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect c.Hinf_inf_L_perfect] at hpc
  exact hpc

theorem large_shape_of_KTab23d (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : (IsSLn ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) ∧
        CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) ∨
      (IsSpn ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
        NatSpn (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) ∨
      (IsOmega8m ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaMinus (c.H hV) ⊤ ⊥ 8 (CFSG.Open.pRank 2 D.Z))) :
    IsSLn (KstarBar c hV) 3 (CFSG.Open.pRank 2 D.Z) ∨
      IsSp4 (KstarBar c hV) (CFSG.Open.pRank 2 D.Z) ∨
      IsU4 (KstarBar c hV) (CFSG.Open.pRank 2 D.Z) := by
  have hd' := hd (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hEq := c.Kstar_eq_Hinf_stabilizer_sylowStar hV ha h4 h1930 hnat
  rcases hd' with ⟨-, -, -, -, -, -, -, hSL4, -, hSp6, hO8⟩
  rcases hline with ⟨hSL4', hB4⟩ | ⟨hSp6', hNatSp6⟩ | ⟨hO8', hNatO8⟩
  · exact Or.inl (bar2_congr (P := fun T _ => IsSLn T 3 (CFSG.Open.pRank 2 D.Z)) hEq
      (hSL4 ⟨hSL4', hB4⟩))
  · exact Or.inr (Or.inl (bar2_congr (P := fun T _ => IsSp4 T (CFSG.Open.pRank 2 D.Z)) hEq
      (hSp6 ⟨hSp6', hNatSp6⟩)))
  · exact Or.inr (Or.inr (bar2_congr (P := fun T _ => IsU4 T (CFSG.Open.pRank 2 D.Z)) hEq
      (hO8 ⟨hO8', hNatO8⟩)))

private theorem isL2_KstarBar_of_Sp4 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsSp4 ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
      NatSpn (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) :
    IsL2 (KstarBar c hV) (CFSG.Open.pRank 2 D.Z) := by
  have hd' := hd (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hEq := c.Kstar_eq_Hinf_stabilizer_sylowStar hV ha h4 h1930 hnat
  rcases hd' with ⟨-, -, -, hSp4, -, -, -, -, -, -, -⟩
  exact bar2_congr (P := fun T _ => IsL2 T (CFSG.Open.pRank 2 D.Z)) hEq (hSp4 hline)

private theorem isL2_KstarBar_of_SL3 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z) ∧
      CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    IsL2 (KstarBar c hV) (CFSG.Open.pRank 2 D.Z) := by
  have hd' := hd (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hEq := c.Kstar_eq_Hinf_stabilizer_sylowStar hV ha h4 h1930 hnat
  rcases hd' with ⟨-, -, -, -, hSL3, -, -, -, -, -, -⟩
  exact bar2_congr (P := fun T _ => IsL2 T (CFSG.Open.pRank 2 D.Z)) hEq (hSL3 hline)

private theorem exists_isL2_KstarBar_of_SU4 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : ∃ a : ℕ, CFSG.Open.pRank 2 D.Z = 2 * a ∧
      IsSUn ↥(c.H hV) 4 a ∧ NatSUn (c.H hV) ⊤ ⊥ 4 a) :
    ∃ a : ℕ, CFSG.Open.pRank 2 D.Z = 2 * a ∧ IsL2 (KstarBar c hV) a := by
  have hd' := hd (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hEq := c.Kstar_eq_Hinf_stabilizer_sylowStar hV ha h4 h1930 hnat
  rcases hd' with ⟨-, -, -, -, -, hSU4, -, -, -, -, -⟩
  obtain ⟨a, ha', hL2⟩ := hSU4 hline
  exact ⟨a, ha', bar2_congr (P := fun T _ => IsL2 T a) hEq hL2⟩

private theorem isL2_KstarBar_of_OmegaMinus6 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsOmegaMinus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaMinus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) :
    IsL2 (KstarBar c hV) (2 * CFSG.Open.pRank 2 D.Z) := by
  have hd' := hd (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hEq := c.Kstar_eq_Hinf_stabilizer_sylowStar hV ha h4 h1930 hnat
  rcases hd' with ⟨-, -, -, -, -, -, hOm6, -, -, -, -⟩
  exact bar2_congr (P := fun T _ => IsL2 T (2 * CFSG.Open.pRank 2 D.Z)) hEq (hOm6 hline)

private theorem B23_nonOmega_quasisimple_of (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    {m : ℕ} (hm : 3 ≤ m) (hL2 : IsL2 (KstarBar c hV) m) :
    K c = ⊥ ∨ K c ∈ calC D.M := by
  have hsimple : IsSimpleGroup (KstarBar c hV) := isSimpleGroup_of_isL2 hL2
  rcases c.Kbar_eq_bot_or_le_component hV h8 hB1 hS hK h1930 h3 hnat hsimple with
    hbot | ⟨C₀, hC₀, hle⟩
  · exact Or.inl (c.Hinf_inf_L_eq_bot_of_Kbar_eq_bot hbot)
  · by_cases hKbot : K c = ⊥
    · exact Or.inl hKbot
    · have hKbar_ne : Kbar c ≠ ⊥ := fun h =>
        hKbot (c.Hinf_inf_L_eq_bot_of_Kbar_eq_bot h)
      have hCeq := c.Kbar_eq_component_of_le_component hV h8 hB1 hS hK h1930 h3 hnat
        hm hL2 hC₀ hle hKbar_ne
      exact Or.inr (c.mem_calC_of_Kbar_eq_component h8 hS h1930 hC₀ hCeq hKbot)

theorem s23_9_B23_nonOmega_large_of (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch)
    (hS : KSub23) (hK : KOrdNatural) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : (IsSLn ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) ∧
        CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) ∨
      (IsSpn ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
        NatSpn (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) ∨
      (IsOmega8m ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaMinus (c.H hV) ⊤ ⊥ 8 (CFSG.Open.pRank 2 D.Z))) :
    Hinf (D.M ⊓ c.L) = ⊥ :=
  c.Hinf_inf_L_eq_bot_of_Kbar_eq_bot
    (c.Kbar_eq_bot_of_large_lines hV h8 hB1 hS hK h1930 h3 hnat
      (c.large_shape_of_KTab23d hV ha hd h4 h1930 h3 hnat hline))

end Ctx23L

theorem s23_9_B23_nonOmega_of (D : Data G) (Ch : Choice2011 G)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h8 : S23_8 D Ch)
    (hB1 : S23_9_B1 D Ch) (ha : KTab23a) (hd : KTab23d) (hK : KOrdNatural) (hS : KSub23)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (h3rank : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hO : ¬ (∃ hV : IsElemAbelian 2 c.V,
        IsOmegaPlus ↥(barSub ⊥ c.V hV c.L) 6 (CFSG.Open.pRank 2 D.Z) ∧
          NatOmegaPlus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z))) :
    Hinf (D.M ⊓ c.L) = ⊥ ∨ Hinf (D.M ⊓ c.L) ∈ calC D.M ∨
      ((∃ hV : IsElemAbelian 2 c.V, ∃ a : ℕ, CFSG.Open.pRank 2 D.Z = 2 * a ∧
          IsSUn ↥(barSub ⊥ c.V hV c.L) 4 a ∧
            NatSUn (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 a) ∧
        ∃ X : Subgroup G, X ∈ calC D.M ∧ Hinf (D.M ⊓ c.L) ≤ X) := by
  obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  have hnat' : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) := hnat
  have hnat0 := hnat'
  rcases hnat' with hL2 | hOm4 | hOp4 | hSp4 | hSL3 | hSU4 | hOm6 | hSL4 | hOp6 | hSp6 | hO8
  · exact Or.inl (c.Hinf_inf_L_eq_bot_of_bot_lines hV ha hd hK h4 h1930 h3rank hnat0
      (Or.inl hL2))
  · exact Or.inl (c.Hinf_inf_L_eq_bot_of_bot_lines hV ha hd hK h4 h1930 h3rank hnat0
      (Or.inr (Or.inl hOm4)))
  · exact Or.inl (c.Hinf_inf_L_eq_bot_of_bot_lines hV ha hd hK h4 h1930 h3rank hnat0
      (Or.inr (Or.inr hOp4)))
  · rcases c.B23_nonOmega_quasisimple_of hV h8 hB1 hS hK h1930 h3rank hnat0
      h3rank (c.isL2_KstarBar_of_Sp4 hV ha hd h4 h1930 h3rank hnat0 hSp4) with
      hbot | hcal
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hcal)
  · rcases c.B23_nonOmega_quasisimple_of hV h8 hB1 hS hK h1930 h3rank hnat0
      h3rank (c.isL2_KstarBar_of_SL3 hV ha hd h4 h1930 h3rank hnat0 hSL3) with
      hbot | hcal
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hcal)
  · by_cases hKbar : c.Kbar = ⊥
    · exact Or.inl (c.Hinf_inf_L_eq_bot_of_Kbar_eq_bot hKbar)
    · obtain ⟨a, -, hL2a⟩ :=
        c.exists_isL2_KstarBar_of_SU4 hV ha hd h4 h1930 h3rank hnat0 hSU4
      have hW : IsSimpleGroup (Ctx23L.KstarBar c hV) := isSimpleGroup_of_isL2 hL2a
      rcases c.Kbar_eq_bot_or_le_component hV h8 hB1 hS hK h1930 h3rank hnat0 hW with
        hbot | ⟨C₀, hC₀, hle⟩
      · exact Or.inl (c.Hinf_inf_L_eq_bot_of_Kbar_eq_bot hbot)
      · obtain ⟨X, hXcal, hKX⟩ := c.exists_calC_ge_of_Kbar_le_component h8 h1930 hC₀ hle
        exact Or.inr (Or.inr ⟨⟨hV, hSU4⟩, ⟨X, hXcal, hKX⟩⟩)
  · rcases c.B23_nonOmega_quasisimple_of hV h8 hB1 hS hK h1930 h3rank hnat0
      (by omega : 3 ≤ 2 * CFSG.Open.pRank 2 D.Z)
      (c.isL2_KstarBar_of_OmegaMinus6 hV ha hd h4 h1930 h3rank hnat0 hOm6) with
      hbot | hcal
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hcal)
  · exact Or.inl (c.s23_9_B23_nonOmega_large_of hV ha hd h8 hB1 hS hK h4 h1930 h3rank
      hnat0 (Or.inl hSL4))
  · exact (hO ⟨hV, hOp6⟩).elim
  · exact Or.inl (c.s23_9_B23_nonOmega_large_of hV ha hd h8 hB1 hS hK h4 h1930 h3rank
      hnat0 (Or.inr (Or.inl hSp6)))
  · exact Or.inl (c.s23_9_B23_nonOmega_large_of hV ha hd h8 hB1 hS hK h4 h1930 h3rank
      hnat0 (Or.inr (Or.inr hO8)))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
