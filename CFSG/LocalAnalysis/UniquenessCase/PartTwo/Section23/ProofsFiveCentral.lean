module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CalLCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.GroupTheory.ABGLocalTools.RelativeStability
public import CFSG.GroupTheory.NormalizerInfCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem L_le_normalizer_inf_centralizer_V (c : Ctx23L D Ch) :
    c.L ≤ Subgroup.normalizer
      ((c.L ⊓ Subgroup.centralizer (c.V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  exact CFSG.GroupTheory.mem_normalizer_inf_centralizer (L := c.V) (Q := c.L)
    (sup_le_normalizer_V D Ch c (Subgroup.mem_sup_left hx)) (Subgroup.le_normalizer hx)

theorem T_le_normalizer_inf_centralizer_V (c : Ctx23L D Ch) :
    D.T ≤ Subgroup.normalizer
      ((c.L ⊓ Subgroup.centralizer (c.V : Set G) : Subgroup G) : Set G) := by
  intro t ht
  exact CFSG.GroupTheory.mem_normalizer_inf_centralizer (L := c.V) (Q := c.L)
    (sup_le_normalizer_V D Ch c (Subgroup.mem_sup_right ht)) (c.hL.1.1 ht)

theorem pCoreOf_le_centralizer_V (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    CFSG.Open.pCoreOf 2 c.L ≤ Subgroup.centralizer (c.V : Set G) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hmap : (CFSG.pCore 2 ↥c.L).map (c.phiL hV) ≤ CFSG.pCore 2 ↥(c.H hV) :=
    CFSG.ABGLocalTools.map_pCore_le_of_surjective (c.phiL hV) (c.phiL_surjective hV)
  have hone : c.phiL hV y = 1 := by
    have hmem := hmap (Subgroup.mem_map_of_mem (c.phiL hV) hy)
    rwa [hK.1 hnat, Subgroup.mem_bot] at hmem
  exact (c.phiL_eq_one_iff hV y).1 hone

private theorem map_subgroupOf_pCoreOf_eq_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    ((CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L).map (c.phiL hV) = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hh
  rw [Subgroup.mem_bot]
  exact (c.phiL_eq_one_iff hV x).2
    (pCoreOf_le_centralizer_V c hV hK hnat (Subgroup.mem_subgroupOf.mp hx))

private theorem map_subgroupOf_inf_centralizer_V_eq_bot (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) :
    (((c.L ⊓ Subgroup.centralizer (c.V : Set G) : Subgroup G)).subgroupOf c.L).map
      (c.phiL hV) = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hh
  rw [Subgroup.mem_bot]
  exact (c.phiL_eq_one_iff hV x).2 (Subgroup.mem_subgroupOf.mp hx).2

theorem not_le_centralizer_sup_pCoreOf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    ¬ c.L ≤ (c.L ⊓ Subgroup.centralizer (c.V : Set G)) ⊔ CFSG.Open.pCoreOf 2 c.L := by
  intro hle
  let R : Subgroup G := c.L ⊓ Subgroup.centralizer (c.V : Set G)
  have hRL : R ≤ c.L := inf_le_left
  have hRmap : (R.subgroupOf c.L).map (c.phiL hV) = ⊥ :=
    map_subgroupOf_inf_centralizer_V_eq_bot c hV
  have hPmap := map_subgroupOf_pCoreOf_eq_bot c hV hK hnat
  have hsubTop : R.subgroupOf c.L ⊔
      (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hRL (uc22main1_pCoreOf_le c.L)]
    exact (Subgroup.subgroupOf_eq_top).2 hle
  have htopBot : (⊤ : Subgroup ↥(c.H hV)) = ⊥ := by
    calc (⊤ : Subgroup ↥(c.H hV)) = (⊤ : Subgroup ↥c.L).map (c.phiL hV) := by
          rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr (c.phiL_surjective hV)]
      _ = (R.subgroupOf c.L ⊔
            (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L).map (c.phiL hV) := by rw [hsubTop]
      _ = (R.subgroupOf c.L).map (c.phiL hV) ⊔
            ((CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L).map (c.phiL hV) := by
          rw [Subgroup.map_sup]
      _ = ⊥ := by rw [hRmap, hPmap, sup_bot_eq]
  have hsub : Subsingleton ↥(c.H hV) := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := (Subgroup.eq_bot_iff_forall _).1 htopBot a (Subgroup.mem_top a)
    have hb : b = 1 := (Subgroup.eq_bot_iff_forall _).1 htopBot b (Subgroup.mem_top b)
    rw [ha, hb]
  exact (not_subsingleton_iff_nontrivial.mpr (hK.2.1 hnat)) hsub

theorem commutator_mem_pCoreOf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    ∀ x ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G), ∀ y ∈ c.L,
      x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
  commutator_mem_pCoreOf_of_mem_calL (T := D.T) (M := D.M) (L := c.L)
    (R := c.L ⊓ Subgroup.centralizer (c.V : Set G)) c.hL.1 inf_le_left
    (L_le_normalizer_inf_centralizer_V c) (T_le_normalizer_inf_centralizer_V c)
    (not_le_centralizer_sup_pCoreOf c hV hK hnat)

theorem inf_centralizer_V_le_of_parabolic (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    {P : Subgroup G} (hP : ParabolicOf c.L P) :
    c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ P := by
  let R : Subgroup G := c.L ⊓ Subgroup.centralizer (c.V : Set G)
  have hRL : R ≤ c.L := inf_le_left
  have hcentral : barImage c.L R ≤ Subgroup.center (Bar2 c.L) :=
    barImage_le_center_of_mem_calL (T := D.T) (M := D.M) (L := c.L) (R := R) c.hL.1
      hRL (L_le_normalizer_inf_centralizer_V c) (T_le_normalizer_inf_centralizer_V c)
      (not_le_centralizer_sup_pCoreOf c hV hK hnat)
  have hpar : IsParabolicTwo (Bar2 c.L) (barImage c.L P) := hP.2.2
  have hle : barImage c.L R ≤ barImage c.L P := hcentral.trans hpar.center_le
  have hleSup := CFSG.Quasithin.C1Pack.le_sup_pCoreOf_of_barImage_le hRL hle
  rwa [sup_eq_left.mpr hP.1] at hleSup

private theorem subgroupOf_preimage_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (N : Subgroup ↥(c.H hV)) :
    (((N.comap (c.phiL hV)).map c.L.subtype).subgroupOf c.L) = N.comap (c.phiL hV) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.mp hx)
    rw [← Subtype.ext hyx]
    exact hy
  · intro hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem c.L.subtype hx)

private theorem L_le_normalizer_preimage (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {N : Subgroup ↥(c.H hV)} (hN : N.Normal) :
    c.L ≤ Subgroup.normalizer
      (((N.comap (c.phiL hV)).map c.L.subtype : Subgroup G) : Set G) := by
  have hRle : ((N.comap (c.phiL hV)).map c.L.subtype : Subgroup G) ≤ c.L :=
    Subgroup.map_subtype_le _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).mp ?_
  rw [subgroupOf_preimage_eq c hV N]
  exact hN.comap (c.phiL hV)

private theorem T_le_normalizer_preimage (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {N : Subgroup ↥(c.H hV)}
    (hNinv : ∀ t ∈ c.Tstar hV,
      (N.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom = N.map (c.H hV).subtype) :
    D.T ≤ Subgroup.normalizer
      (((N.comap (c.phiL hV)).map c.L.subtype : Subgroup G) : Set G) := by
  have hstep : ∀ t ∈ D.T, ∀ r ∈ ((N.comap (c.phiL hV)).map c.L.subtype : Subgroup G),
      t * r * t⁻¹ ∈ ((N.comap (c.phiL hV)).map c.L.subtype : Subgroup G) := by
    intro t ht r hr
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hr
    have hyN : c.phiL hV y ∈ N := Subgroup.mem_comap.mp hy
    let tT : ↥D.T := ⟨t, ht⟩
    let y' : ↥c.L := ⟨t * (y : G) * t⁻¹, c.conj_mem tT y⟩
    have htstar : c.phiT hV tT ∈ c.Tstar hV :=
      MonoidHom.mem_range.mpr ⟨tT, rfl⟩
    have hA : (c.phiL hV y : MulAut (c.W hV)) ∈ N.map (c.H hV).subtype :=
      Subgroup.mem_map_of_mem _ hyN
    have hFA : (MulAut.conj (c.phiT hV tT)) (c.phiL hV y : MulAut (c.W hV)) ∈
        (N.map (c.H hV).subtype).map (MulAut.conj (c.phiT hV tT)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hA
    have hA' : (MulAut.conj (c.phiT hV tT)) (c.phiL hV y : MulAut (c.W hV)) ∈
        N.map (c.H hV).subtype := by
      rwa [hNinv _ htstar] at hFA
    have hconj : MulAut.conj (c.phiT hV tT) (c.phiL hV y : MulAut (c.W hV)) =
        (c.phiL hV y' : MulAut (c.W hV)) := c.phiT_conj_phiL hV tT y
    rw [hconj] at hA'
    have hy'N : c.phiL hV y' ∈ N := by
      obtain ⟨m, hm, hmval⟩ := Subgroup.mem_map.1 hA'
      exact (Subtype.ext hmval) ▸ hm
    exact Subgroup.mem_map_of_mem c.L.subtype (Subgroup.mem_comap.mpr hy'N)
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · exact hstep t ht r
  · intro hr
    have hmem := hstep t⁻¹ (D.T.inv_mem ht) (t * r * t⁻¹) hr
    have hval : t⁻¹ * (t * r * t⁻¹) * (t⁻¹)⁻¹ = r := by group
    rwa [hval] at hmem

private theorem eq_top_of_le_preimage (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    {N : Subgroup ↥(c.H hV)} (hNne : N ≠ ⊤)
    (hle : c.L ≤ (N.comap (c.phiL hV)).map c.L.subtype ⊔
      CFSG.Open.pCoreOf 2 c.L) : False := by
  let R : Subgroup G := (N.comap (c.phiL hV)).map c.L.subtype
  have hRL : R ≤ c.L := Subgroup.map_subtype_le _
  have hPmap := map_subgroupOf_pCoreOf_eq_bot c hV hK hnat
  have hRsub : R.subgroupOf c.L = N.comap (c.phiL hV) := subgroupOf_preimage_eq c hV N
  have hRmap : (R.subgroupOf c.L).map (c.phiL hV) = N := by
    rw [hRsub]
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    intro n hn
    obtain ⟨x, hx⟩ := c.phiL_surjective hV n
    have hxN : c.phiL hV x ∈ N := by rwa [← hx] at hn
    exact hx ▸ Subgroup.mem_map_of_mem (c.phiL hV) (Subgroup.mem_comap.mpr hxN)
  have hsubTop : R.subgroupOf c.L ⊔
      (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hRL (uc22main1_pCoreOf_le c.L)]
    exact (Subgroup.subgroupOf_eq_top).2 hle
  have htopN : (⊤ : Subgroup ↥(c.H hV)) = N := by
    calc (⊤ : Subgroup ↥(c.H hV)) = (⊤ : Subgroup ↥c.L).map (c.phiL hV) := by
          rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr (c.phiL_surjective hV)]
      _ = (R.subgroupOf c.L ⊔
            (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L).map (c.phiL hV) := by rw [hsubTop]
      _ = (R.subgroupOf c.L).map (c.phiL hV) ⊔
            ((CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L).map (c.phiL hV) := by
          rw [Subgroup.map_sup]
      _ = N := by rw [hRmap, hPmap, sup_bot_eq]
  exact hNne htopN.symm

theorem le_center_of_normal_of_ne_top (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    ∀ N : Subgroup ↥(c.H hV), N.Normal →
      (∀ t ∈ c.Tstar hV,
        (N.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom = N.map (c.H hV).subtype) →
      N ≠ ⊤ → N ≤ Subgroup.center ↥(c.H hV) := by
  intro N hNnorm hNinv hNne
  let R : Subgroup G := (N.comap (c.phiL hV)).map c.L.subtype
  have hRL : R ≤ c.L := Subgroup.map_subtype_le _
  have hLR : c.L ≤ Subgroup.normalizer (R : Set G) :=
    L_le_normalizer_preimage c hV hNnorm
  have hTR : D.T ≤ Subgroup.normalizer (R : Set G) :=
    T_le_normalizer_preimage c hV hNinv
  by_cases hle : c.L ≤ R ⊔ CFSG.Open.pCoreOf 2 c.L
  · exact (eq_top_of_le_preimage c hV hK hnat hNne hle).elim
  · have hcomm := commutator_mem_pCoreOf_of_mem_calL (T := D.T) (M := D.M) (L := c.L)
      (R := R) c.hL.1 hRL hLR hTR hle
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨x, hx⟩ := c.phiL_surjective hV n
    obtain ⟨y, hy⟩ := c.phiL_surjective hV h
    have hxN : c.phiL hV x ∈ N := by rwa [← hx] at hn
    have hxR : (x : G) ∈ R :=
      Subgroup.mem_map_of_mem c.L.subtype (Subgroup.mem_comap.mpr hxN)
    let z : ↥c.L := ⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹,
      c.L.mul_mem (c.L.mul_mem (c.L.mul_mem x.2 y.2) (c.L.inv_mem x.2))
        (c.L.inv_mem y.2)⟩
    have hz1 : c.phiL hV z = 1 :=
      (c.phiL_eq_one_iff hV z).2
        (pCoreOf_le_centralizer_V c hV hK hnat (hcomm x hxR y y.2))
    have h1 : c.phiL hV x * c.phiL hV y * (c.phiL hV x)⁻¹ * (c.phiL hV y)⁻¹ = 1 := by
      have hz_eq : z = x * y * x⁻¹ * y⁻¹ := Subtype.ext rfl
      rw [hz_eq] at hz1
      simpa only [map_mul, map_inv] using hz1
    have h2 : c.phiL hV x * c.phiL hV y * (c.phiL hV x)⁻¹ = c.phiL hV y :=
      mul_inv_eq_one.mp h1
    have hcomm_xy : c.phiL hV x * c.phiL hV y = c.phiL hV y * c.phiL hV x := by
      calc c.phiL hV x * c.phiL hV y
          = (c.phiL hV x * c.phiL hV y * (c.phiL hV x)⁻¹) * c.phiL hV x := by group
        _ = c.phiL hV y * c.phiL hV x := by rw [h2]
    rw [← hy, ← hx]
    exact hcomm_xy.symm

theorem map_L0_ne_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    (c.L0.subgroupOf c.L).map (c.phiL hV) ≠ ⊥ := by
  intro hbot
  have hL0R : c.L0 ≤ c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
    intro x hx
    have hxL : x ∈ c.L := c.hL0L hx
    have hxsub : (⟨x, hxL⟩ : ↥c.L) ∈ c.L0.subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hx
    have hφ : c.phiL hV ⟨x, hxL⟩ = 1 := by
      have hmem : c.phiL hV ⟨x, hxL⟩ ∈ (c.L0.subgroupOf c.L).map (c.phiL hV) :=
        Subgroup.mem_map_of_mem _ hxsub
      rwa [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_inf.mpr ⟨hxL, (c.phiL_eq_one_iff hV _).1 hφ⟩
  have hL0leO2 : c.L0 ≤ CFSG.Open.pCoreOf 2 c.L := by
    have hcommSub : ⁅c.L0, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact commutator_mem_pCoreOf c hV hK hnat x
        (Subgroup.mem_inf.mpr ⟨c.hL0L hx, (hL0R hx).2⟩) y (c.hL0L hy)
    rwa [c.hL0.prop.2.1] at hcommSub
  have hL0bot : c.L0 = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥c.L0 := (Subgroup.nontrivial_iff_ne_bot c.L0).2 hne
    haveI : Group.IsPerfect ↥c.L0 := Subgroup.isPerfect_iff.mpr c.hL0.prop.2.1
    have hL0p : IsPGroup 2 ↥c.L0 :=
      (uc22main1_isPGroup_pCoreOf c.L).to_le hL0leO2
    exact Group.IsPerfect.not_isNilpotent (G := ↥c.L0) hL0p.isNilpotent
  exact uc22p20i_not_le_M D c.hL0.prop (by simpa [hL0bot] using bot_le)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
