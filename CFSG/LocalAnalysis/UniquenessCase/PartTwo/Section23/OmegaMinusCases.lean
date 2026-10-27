module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem card_preTil_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (A₀ : Subgroup (c.W hV)) :
    Nat.card ↥(preTil (⊥ : Subgroup G) c.V hV A₀) = Nat.card ↥A₀ := by
  have hle : preTil (⊥ : Subgroup G) c.V hV A₀ ≤ c.V := preTil_le _ _ _ _
  calc Nat.card ↥(preTil (⊥ : Subgroup G) c.V hV A₀) =
        Nat.card ↥(((preTil (⊥ : Subgroup G) c.V hV A₀).subgroupOf c.V).map
          c.V.subtype) := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
    _ = Nat.card ↥((preTil (⊥ : Subgroup G) c.V hV A₀).subgroupOf c.V) :=
        Subgroup.card_subtype c.V _
    _ = Nat.card ↥(imgTil (⊥ : Subgroup G) c.V hV
          (preTil (⊥ : Subgroup G) c.V hV A₀)) := by
        rw [imgTil, intSub]
        exact (Subgroup.card_map_of_injective
          (TwelveShort.mkTilEquiv c.V hV).injective).symm
    _ = Nat.card ↥A₀ := by rw [imgTil_preTil]

private theorem map_Ztil_le_of_mem_normalizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {x : ↥c.L} (hxN : (x : G) ∈ Subgroup.normalizer (D.Z : Set G)) :
    (c.Ztil hV).map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom ≤ c.Ztil hV := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
  rw [Ctx23L.Ztil, mem_imgTil] at hz ⊢
  obtain ⟨u, huZ, rfl⟩ := hz
  refine ⟨actStab (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ u, ?_, ?_⟩
  · rw [actStab_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp hxN u.val).1 huZ
  · exact (c.phiL_apply_mkTil hV x u).symm

private theorem not_mem_M_of_moves_Ztil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) {x : ↥c.L}
    (hmove : (c.Ztil hV).map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom ≠ c.Ztil hV) :
    (x : G) ∉ D.M := by
  intro hxM
  have h4c := h4 h1930 c
  have hMN : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← h4c.1]
    exact h4c.2.2
  have hxN : (x : G) ∈ Subgroup.normalizer (D.Z : Set G) := hMN hxM
  have hle := map_Ztil_le_of_mem_normalizer c hV hxN
  have hcard : Nat.card ↥((c.Ztil hV).map
      (c.phiL hV x : MulAut (c.W hV)).toMonoidHom) = Nat.card ↥(c.Ztil hV) :=
    Subgroup.card_map_of_injective
      (f := ((c.phiL hV x : MulAut (c.W hV))).toMonoidHom)
      (c.phiL hV x : MulAut (c.W hV)).injective
  exact hmove (Subgroup.eq_of_le_of_card_ge hle hcard.symm.le)

private theorem mem_preTil_conj (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {A₀ : Subgroup (c.W hV)} {x : ↥c.L}
    (hstable : A₀.map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom = A₀)
    {z : G} (hz : z ∈ preTil (⊥ : Subgroup G) c.V hV A₀) :
    (x : G) * z * (x : G)⁻¹ ∈ preTil (⊥ : Subgroup G) c.V hV A₀ := by
  have hzV : z ∈ c.V := preTil_le _ _ _ _ hz
  have hzA₀ : mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩) ∈ A₀ :=
    (mem_preTil_iff_of_mem (⊥ : Subgroup G) c.V hV A₀ hzV).1 hz
  have hxV : (x : G) ∈ Subgroup.normalizer (c.V : Set G) :=
    (stabTil_le_normalizer (⊥ : Subgroup G) c.V) (c.L_le_stabTil x.2)
  have hconjV : (x : G) * z * (x : G)⁻¹ ∈ c.V :=
    (Subgroup.mem_normalizer_iff.mp hxV z).1 hzV
  rw [mem_preTil_iff_of_mem (⊥ : Subgroup G) c.V hV A₀ hconjV]
  have himg : (c.phiL hV x : MulAut (c.W hV))
      (mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩)) ∈ A₀ := by
    rw [← hstable]
    exact Subgroup.mem_map_of_mem _ hzA₀
  rw [c.phiL_apply_mkTil hV x] at himg
  have hval : actStab (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩
      (IntMod.mk hV ⟨z, hzV⟩) = IntMod.mk hV ⟨(x : G) * z * (x : G)⁻¹, hconjV⟩ := by
    apply IntMod.val_injective
    rw [actStab_apply_val]
    rfl
  rwa [hval] at himg

private theorem preTil_le_normalizer_of_map_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {A₀ : Subgroup (c.W hV)} {x : ↥c.L}
    (hstable : A₀.map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom = A₀) :
    (x : G) ∈ Subgroup.normalizer (preTil (⊥ : Subgroup G) c.V hV A₀ : Set G) := by
  have hle : (preTil (⊥ : Subgroup G) c.V hV A₀).map
      (MulAut.conj (x : G)).toMonoidHom ≤ preTil (⊥ : Subgroup G) c.V hV A₀ := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
    simpa [MulAut.conj_apply] using mem_preTil_conj c hV hstable hz
  have hcard : Nat.card ↥((preTil (⊥ : Subgroup G) c.V hV A₀).map
      (MulAut.conj (x : G)).toMonoidHom) =
      Nat.card ↥(preTil (⊥ : Subgroup G) c.V hV A₀) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj (x : G)).toMonoidHom)
      (MulAut.conj (x : G)).injective
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle hcard.symm.le)

private theorem V_le_jOne_of_jOf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA) :
    c.V ≤ jOneOf D.T := by
  have hVJ := c.V_le_jOf hV hA h4 h1930 hn2 hNat hKA
  have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have h1 : CFSG.Open.pRank 2 D.Z ≤ CFSG.Open.pRank 2 c.V :=
    CFSG.SectionRank.pRank_mono (by norm_num) hZV
  have h2 : CFSG.Open.pRank 2 c.V ≤ CFSG.Open.pRank 2 D.T :=
    CFSG.SectionRank.pRank_mono (by norm_num) (c.V_le_T h4 h1930)
  have hm : 1 < CFSG.Open.pRank 2 D.T := by omega
  have hm' : 1 < CFSG.pRank 2 ↥D.T := by
    rwa [CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
  have h01 : CFSG.higherElemThompson ↥D.T 0 ≤ CFSG.higherElemThompson ↥D.T 1 := by
    obtain ⟨-, -, h01, -⟩ :=
      (CFSG.Quasithin.SteinbergBK.higher_elementary_thompson_intersections_and_central_involutions
        (S := ↥D.T) (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG)).2.1 0 1
        (by omega) hm'
    exact h01
  have hJ : F12.jOf D.T ≤ jOneOf D.T := by
    rw [F12.jOf, CFSG.inSubgroup, ← CFSG.higherElemThompson_zero, jOneOf, CFSG.inSubgroup]
    exact Subgroup.map_mono h01
  exact hVJ.trans hJ

private theorem exists_weakOffender_of_family_one (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {A : Subgroup ↥D.T} (hAfam : A ∈ CFSG.higherElemThompsonFamily ↥D.T 1)
    (hAnle : ¬ A ≤ (Subgroup.centralizer (c.V : Set G)).subgroupOf D.T) :
    ∃ E : Subgroup (MulAut (c.W hV)),
      E = ((A.map D.T.subtype).subgroupOf D.T).map (c.phiT hV) ∧
      E ≤ c.Tstar hV ∧ IsElemAbelian 2 E ∧ E ≠ ⊥ ∧
      Nat.card (c.W hV) ≤ 2 * (Nat.card ↥E *
        Nat.card ↥(CFSG.Quasithin.fixV E)) := by
  have hAfam' := (CFSG.mem_higherElemThompsonFamily_iff 1 A).mp hAfam
  have hAelT : IsElemAbelian 2 A :=
    (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr hAfam'.1
  let AG : Subgroup G := A.map D.T.subtype
  have hAGel : IsElemAbelian 2 AG := hAelT.map D.T.subtype
  have hAGT : AG ≤ D.T := Subgroup.map_subtype_le A
  have hAGnle : ¬ AG ≤ Subgroup.centralizer (c.V : Set G) := by
    intro hle
    apply hAnle
    rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype] at hle
    exact hle
  have hrankAG : CFSG.Open.pRank 2 AG = CFSG.Open.pRank 2 D.T - 1 :=
    pRank_map_subtype_eq_of_family_one hAfam
  have hrk : CFSG.Open.pRank 2 D.T ≤ CFSG.Open.pRank 2 AG + 1 := by
    rw [hrankAG]; omega
  have hWle := c.card_W_le_of_pRank hV h4 h1930 hAGel hAGT (i := 1) hrk
  let E : Subgroup (MulAut (c.W hV)) := (AG.subgroupOf D.T).map (c.phiT hV)
  have hEel : IsElemAbelian 2 E :=
    (CFSG.Open.IsElemAbelian.subgroupOf hAGel D.T).map (c.phiT hV)
  have hEle : E ≤ c.Tstar hV := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hEne : E ≠ ⊥ := by
    intro hbot
    apply hAGnle
    intro x hx
    have hxT : x ∈ D.T := hAGT hx
    have hxE : (c.phiT hV ⟨x, hxT⟩) ∈ E :=
      Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hxE
    exact (c.phiT_eq_one_iff hV ⟨x, hxT⟩).1 hxE
  exact ⟨E, rfl, hEle, hEel, hEne, by simpa [E] using hWle⟩

private theorem kOmB_conclusion_of_not_caseA
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hframe : OmegaMinusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z)
      (c.sylowStar hV) (c.Tstar hV))
    (hKB : KOmB) (hnot : ¬ S23_23OmegaCaseA c) :
    CFSG.Open.pRank 2 D.Z = 2 ∧ ¬ c.Tstar hV ≤ c.H hV ∧
      ∃ A₀ : Subgroup (c.W hV), Nat.card ↥A₀ = 4 ∧
        (∀ E' : Subgroup (MulAut (c.W hV)), E' ≤ c.Tstar hV → IsElemAbelian 2 E' →
          Nat.card (c.W hV) ≤ 2 * (Nat.card ↥E' *
            Nat.card ↥(CFSG.Quasithin.fixV E')) →
          A₀ ≤ CFSG.Quasithin.fixV E') ∧
        ∃ h ∈ c.H hV, A₀.map (h : MulAut (c.W hV)).toMonoidHom = A₀ ∧
          (CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map
              (c.H hV).subtype)).map (h : MulAut (c.W hV)).toMonoidHom ≠
            CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map
              (c.H hV).subtype) := by
  obtain ⟨A, hAfam, hAnle⟩ := c.exists_family_one_not_le_centralizer hnot
  obtain ⟨E, -, hEle, hEel, hEne, hWle⟩ :=
    exists_weakOffender_of_family_one c hV h4 h1930 hAfam hAnle
  exact hKB (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) (c.sylowStar hV)
    (c.Tstar hV) hframe E hEle hEel hEne hWle

private theorem commute_of_fix_mkTil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {a : ↥D.T} {z : G} (hzV : z ∈ c.V)
    (hfix : (c.phiT hV a) (mkTil (⊥ : Subgroup G) c.V hV
        (IntMod.mk hV ⟨z, hzV⟩)) =
      mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩)) :
    (a : G) * z = z * (a : G) := by
  have hstep : (c.phiT hV a) (mkTil (⊥ : Subgroup G) c.V hV
      (IntMod.mk hV ⟨z, hzV⟩)) = mkTil (⊥ : Subgroup G) c.V hV
        (actStab (⊥ : Subgroup G) c.V hV ⟨a, c.T_le_stabTil a.2⟩
          (IntMod.mk hV ⟨z, hzV⟩)) := by
    change actTil (⊥ : Subgroup G) c.V hV ⟨a, c.T_le_stabTil a.2⟩
      (mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩)) = _
    rw [actTil_mk]
  rw [hstep] at hfix
  have hval : (actStab (⊥ : Subgroup G) c.V hV ⟨a, c.T_le_stabTil a.2⟩
      (IntMod.mk hV ⟨z, hzV⟩)).val = (a : G) * z * (a : G)⁻¹ := by
    rw [actStab_apply_val]
    rfl
  have hmem : (actStab (⊥ : Subgroup G) c.V hV ⟨a, c.T_le_stabTil a.2⟩
      (IntMod.mk hV ⟨z, hzV⟩)).val * z⁻¹ ∈ (⊥ : Subgroup G) :=
    (mkTil_eq_iff (⊥ : Subgroup G) c.V hV _ _).1 hfix
  rw [Subgroup.mem_bot, hval] at hmem
  have hEq : (a : G) * z * (a : G)⁻¹ = z := mul_inv_eq_one.mp hmem
  calc (a : G) * z = ((a : G) * z * (a : G)⁻¹) * (a : G) := by group
    _ = z * (a : G) := by rw [hEq]

private theorem family_one_centralizes_preTil (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hframe : OmegaMinusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z)
      (c.sylowStar hV) (c.Tstar hV))
    (hKB : KOmB) {A₀ : Subgroup (c.W hV)}
    (hA₀fix : ∀ E' : Subgroup (MulAut (c.W hV)), E' ≤ c.Tstar hV → IsElemAbelian 2 E' →
      Nat.card (c.W hV) ≤ 2 * (Nat.card ↥E' *
        Nat.card ↥(CFSG.Quasithin.fixV E')) →
      A₀ ≤ CFSG.Quasithin.fixV E')
    {A : Subgroup ↥D.T} (hAfam : A ∈ CFSG.higherElemThompsonFamily ↥D.T 1) :
    A.map D.T.subtype ≤ Subgroup.centralizer
      (preTil (⊥ : Subgroup G) c.V hV A₀ : Set G) := by
  rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
  intro a ha
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  intro z hz
  have hzV : z ∈ c.V := preTil_le _ _ _ _ hz
  have hzA₀ : mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩) ∈ A₀ :=
    (mem_preTil_iff_of_mem (⊥ : Subgroup G) c.V hV A₀ hzV).1 hz
  by_cases hAle : A ≤ (Subgroup.centralizer (c.V : Set G)).subgroupOf D.T
  · have haC : (a : G) ∈ Subgroup.centralizer (c.V : Set G) :=
      Subgroup.mem_subgroupOf.mp (hAle ha)
    exact Subgroup.mem_centralizer_iff.mp haC z hzV
  · obtain ⟨E, hEdef, hEle, hEel, hEne, hWle⟩ :=
      exists_weakOffender_of_family_one c hV h4 h1930 hAfam hAle
    have hmemE : (c.phiT hV a) ∈ E := by
      rw [hEdef]
      exact Subgroup.mem_map.mpr
        ⟨a, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem D.T.subtype ha), rfl⟩
    have hfix := (CFSG.Quasithin.mem_fixV.mp (hA₀fix E hEle hEel hWle hzA₀))
      (c.phiT hV a) hmemE
    exact (commute_of_fix_mkTil c hV hzV hfix).symm

private theorem higherElemThompson_centralizes (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hframe : OmegaMinusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z)
      (c.sylowStar hV) (c.Tstar hV))
    (hKB : KOmB) {A₀ : Subgroup (c.W hV)}
    (hA₀fix : ∀ E' : Subgroup (MulAut (c.W hV)), E' ≤ c.Tstar hV → IsElemAbelian 2 E' →
      Nat.card (c.W hV) ≤ 2 * (Nat.card ↥E' *
        Nat.card ↥(CFSG.Quasithin.fixV E')) →
      A₀ ≤ CFSG.Quasithin.fixV E') {a : G} (haT : a ∈ D.T)
    (ha : a ∈ preTil (⊥ : Subgroup G) c.V hV A₀) :
    CFSG.higherElemThompson ↥D.T 1 ≤
      Subgroup.centralizer ({⟨a, haT⟩} : Set ↥D.T) := by
  rw [CFSG.higherElemThompson]
  refine sSup_le fun A hAfam => ?_
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have hG := Subgroup.mem_centralizer_iff.mp
    (family_one_centralizes_preTil c hV h4 h1930 hframe hKB hA₀fix hAfam
      (Subgroup.mem_map_of_mem D.T.subtype hy)) a ha
  apply Subtype.ext
  exact hG

private theorem preTil_le_zJOneOf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hframe : OmegaMinusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z)
      (c.sylowStar hV) (c.Tstar hV))
    (hKB : KOmB) {A₀ : Subgroup (c.W hV)}
    (hA₀fix : ∀ E' : Subgroup (MulAut (c.W hV)), E' ≤ c.Tstar hV → IsElemAbelian 2 E' →
      Nat.card (c.W hV) ≤ 2 * (Nat.card ↥E' *
        Nat.card ↥(CFSG.Quasithin.fixV E')) →
      A₀ ≤ CFSG.Quasithin.fixV E') :
    preTil (⊥ : Subgroup G) c.V hV A₀ ≤ zJOneOf D.T := by
  have hVJ1 : c.V ≤ jOneOf D.T :=
    c.V_le_jOne_of_jOf hV hA h4 h1930 hn2 hNat hKA
  intro a ha
  have haV : a ∈ c.V := preTil_le _ _ _ _ ha
  have haT : a ∈ D.T := c.V_le_T h4 h1930 haV
  have haH : (⟨a, haT⟩ : ↥D.T) ∈ CFSG.higherElemThompson ↥D.T 1 := by
    have haJ1 : a ∈ jOneOf D.T := hVJ1 haV
    rw [jOneOf, CFSG.inSubgroup] at haJ1
    obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp haJ1
    have hy' : y = (⟨a, haT⟩ : ↥D.T) := Subtype.ext hyval
    rwa [hy'] at hy
  have hcomm : ∀ y ∈ CFSG.higherElemThompson ↥D.T 1,
      y * (⟨a, haT⟩ : ↥D.T) = (⟨a, haT⟩ : ↥D.T) * y := by
    have hle := higherElemThompson_centralizes c hV h4 h1930 hframe hKB hA₀fix haT ha
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) ⟨a, haT⟩
      (Set.mem_singleton _)).symm
  have hcent : (⟨⟨a, haT⟩, haH⟩ : ↥(CFSG.higherElemThompson ↥D.T 1)) ∈
      Subgroup.center (CFSG.higherElemThompson ↥D.T 1) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcomm (y : ↥D.T) y.2
  rw [zJOneOf]
  exact Subgroup.mem_map.mpr
    ⟨⟨a, haT⟩, Subgroup.mem_map.mpr ⟨⟨⟨a, haT⟩, haH⟩, hcent, rfl⟩, rfl⟩

private theorem phiT_eq_phiL_of_mul_mem_centralizer (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {t : ↥D.T} {l : G} (hlL : l ∈ c.L) {z : G}
    (hzC : z ∈ Subgroup.centralizer (c.V : Set G)) (htz : (t : G) = l * z) :
    c.phiT hV t = (c.phiL hV ⟨l, hlL⟩ : MulAut (c.W hV)) := by
  have hzstab : z ∈ stabTil (⊥ : Subgroup G) c.V := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer (c.V : Set G) hzC
    · rw [Subgroup.normalizer_eq_top_iff.mpr
        (inferInstance : (⊥ : Subgroup G).Normal)]
      exact Subgroup.mem_top z
  have hstab : (⟨(t : G), c.T_le_stabTil t.2⟩ : stabTil (⊥ : Subgroup G) c.V) =
      (⟨l, c.L_le_stabTil hlL⟩ : stabTil (⊥ : Subgroup G) c.V) * ⟨z, hzstab⟩ := by
    apply Subtype.ext
    change (t : G) = l * z
    exact htz
  have hactz : actTil (⊥ : Subgroup G) c.V hV ⟨z, hzstab⟩ = 1 := by
    rw [actTil_eq_one_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hc := Subgroup.mem_centralizer_iff.mp hzC v hv
    calc z * v * z⁻¹ * v⁻¹ = v * z * z⁻¹ * v⁻¹ := by rw [hc]
      _ = 1 := by group
  calc c.phiT hV t =
        actTil (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩ := rfl
    _ = actTil (⊥ : Subgroup G) c.V hV
          ((⟨l, c.L_le_stabTil hlL⟩ : stabTil (⊥ : Subgroup G) c.V) *
            ⟨z, hzstab⟩) := by rw [hstab]
    _ = actTil (⊥ : Subgroup G) c.V hV ⟨l, c.L_le_stabTil hlL⟩ *
          actTil (⊥ : Subgroup G) c.V hV ⟨z, hzstab⟩ := map_mul _ _ _
    _ = actTil (⊥ : Subgroup G) c.V hV ⟨l, c.L_le_stabTil hlL⟩ := by
          rw [hactz, mul_one]
    _ = (c.phiL hV ⟨l, hlL⟩ : MulAut (c.W hV)) := rfl

private theorem not_subset_mul_of_not_Tstar_le (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hT : ¬ c.Tstar hV ≤ c.H hV) :
    ¬ ((D.T : Set G) ⊆ (c.L : Set G) *
      (Subgroup.centralizer (c.V : Set G) : Set G)) := by
  intro hsub
  apply hT
  intro φ hφ
  obtain ⟨t, rfl⟩ := (c.mem_Tstar_iff hV φ).1 hφ
  have ht : (t : G) ∈ (D.T : Set G) := t.2
  obtain ⟨l, hlL, z, hzC, htz⟩ := Set.mem_mul.mp (hsub ht)
  rw [phiT_eq_phiL_of_mul_mem_centralizer c hV hlL hzC htz.symm]
  exact (c.phiL hV ⟨l, hlL⟩).2

private theorem kOmB_caseB_data (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hframe : OmegaMinusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z)
      (c.sylowStar hV) (c.Tstar hV))
    (hKB : KOmB) (hnot : ¬ S23_23OmegaCaseA c) :
    CFSG.Open.pRank 2 D.Z = 2 ∧ ¬ c.Tstar hV ≤ c.H hV ∧
      ∃ A₀' : Subgroup G, A₀' ≤ zJOneOf D.T ⊓ c.V ∧ Nat.card A₀' = 4 ∧
        ∃ x ∈ c.L, x ∈ Subgroup.normalizer (A₀' : Set G) ∧ x ∉ D.M := by
  obtain ⟨hm2, hTstarNot, A₀, hcardA₀, hA₀fix, h, hhH, hstable, hhmove⟩ :=
    kOmB_conclusion_of_not_caseA c hV h4 h1930 hframe hKB hnot
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inl ⟨isOmegaMinus_of_natOmegaMinus_four hNat, hNat⟩)
  have hfixS := c.fixV_sylowStar_eq_Ztil hV hA hnat h4 h1930
  obtain ⟨x, hxphi⟩ := c.phiL_surjective hV ⟨h, hhH⟩
  have hxval : ((c.phiL hV x : ↥(c.H hV)) : MulAut (c.W hV)) = h :=
    congrArg Subtype.val hxphi
  have hA₀k : (c.Ztil hV).map
      ((c.phiL hV x : ↥(c.H hV)) : MulAut (c.W hV)).toMonoidHom ≠ c.Ztil hV := by
    have hh := hhmove
    rw [hfixS] at hh
    rw [← hxval] at hh
    exact hh
  have hstable' : A₀.map
      ((c.phiL hV x : ↥(c.H hV)) : MulAut (c.W hV)).toMonoidHom = A₀ := by
    rw [hxval]
    exact hstable
  have hcard : Nat.card ↥(preTil (⊥ : Subgroup G) c.V hV A₀) = 4 := by
    rw [card_preTil_bot c hV A₀, hcardA₀]
  have hz : preTil (⊥ : Subgroup G) c.V hV A₀ ≤ zJOneOf D.T :=
    preTil_le_zJOneOf c hV hA h4 h1930 hn2 hNat hKA hframe hKB hA₀fix
  have hle : preTil (⊥ : Subgroup G) c.V hV A₀ ≤ zJOneOf D.T ⊓ c.V :=
    le_inf hz (preTil_le _ _ _ _)
  exact ⟨hm2, hTstarNot, preTil (⊥ : Subgroup G) c.V hV A₀, hle, hcard,
    (x : G), x.2, preTil_le_normalizer_of_map_eq c hV hstable',
    not_mem_M_of_moves_Ztil c hV h4 h1930 hA₀k⟩

private theorem omegaCaseB_of_not_caseA (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hKB : KOmB) (hnot : ¬ S23_23OmegaCaseA c) : S23_23OmegaCaseB c := by
  have hframe : OmegaMinusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z)
      (c.sylowStar hV) (c.Tstar hV) :=
    c.omegaMinusFrame_of hV hA h4 h1930 hn2 hNat
  obtain ⟨hm2, hTstarNot, A₀', hle, hcard, hxdata⟩ :=
    kOmB_caseB_data c hV hA h4 h1930 hn2 hNat hKA hframe hKB hnot
  exact ⟨hm2, ⟨A₀', hle, hcard, hxdata⟩,
    not_subset_mul_of_not_Tstar_le c hV hTstarNot⟩

end Ctx23L

theorem s23_23Cases_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h52 : S23_5_2Omega D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hA : KTab23a) (hKA : KOmA) (hKB : KOmB) : S23_23Cases D Ch := by
  intro h1930 c hOm hV hNat
  obtain ⟨-, hcn⟩ := h52 h1930 c hOm
  have h3n : 3 ≤ c.n := hn3 h1930 c.toCtx23.toCtx21
  have hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z := by omega
  by_cases hcaseA : S23_23OmegaCaseA c
  · exact Or.inl hcaseA
  · exact Or.inr (Ctx23L.omegaCaseB_of_not_caseA c hV hA h4 h1930 hn2 hNat hKA hKB hcaseA)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
