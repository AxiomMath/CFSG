module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeKeyLemma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveW0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem exists_component_H_eq_iSup_conj (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ∃ K : Subgroup G, K ∈ calC c.L ∧
      c.L = ⨆ t : ↥D.T, K.map (MulAut.conj (t : G)).toMonoidHom ∧
      c.H hV = ⨆ r ∈ c.Tstar hV,
        (barSub (⊥ : Subgroup G) c.V hV K).map (MulAut.conj r).toMonoidHom := by
  obtain ⟨K, hK, hgen⟩ := c.hL.1.2.2.2
  have hKL : K ≤ c.L := CFSG.Quasithin.A3.subnormal_le hK.1
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) c.V := hKL.trans c.L_le_stabTil
  have hKle : ∀ t : ↥D.T, K.map (MulAut.conj (t : G)).toMonoidHom ≤
      stabTil (⊥ : Subgroup G) c.V := by
    intro t x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    exact c.L_le_stabTil (c.conj_mem t ⟨k, hKL hk⟩)
  refine ⟨K, hK, hgen, ?_⟩
  have hbar : barSub (⊥ : Subgroup G) c.V hV
      (⨆ t : ↥D.T, K.map (MulAut.conj (t : G)).toMonoidHom) =
      ⨆ t : ↥D.T, (barSub (⊥ : Subgroup G) c.V hV K).map
        (MulAut.conj (c.phiT hV t)).toMonoidHom := by
    rw [barSub_iSup_of_le hV hKle]
    exact iSup_congr fun t => by
      rw [TwelveTwentyThree.barSub_map_conj (V₀ := ⊥) hV hKstab (c.T_le_stabTil t.2)]
      rfl
  have hsup : (⨆ t : ↥D.T, (barSub (⊥ : Subgroup G) c.V hV K).map
      (MulAut.conj (c.phiT hV t)).toMonoidHom) =
      ⨆ r ∈ c.Tstar hV, (barSub (⊥ : Subgroup G) c.V hV K).map
        (MulAut.conj r).toMonoidHom := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun t => ?_
      exact le_iSup₂_of_le (c.phiT hV t) (MonoidHom.mem_range.mpr ⟨t, rfl⟩) le_rfl
    · refine iSup_le fun r => iSup_le fun hr => ?_
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hr
      rw [← ht]
      exact le_iSup (fun t => (barSub (⊥ : Subgroup G) c.V hV K).map
        (MulAut.conj (c.phiT hV t)).toMonoidHom) t
  rw [show c.H hV = barSub (⊥ : Subgroup G) c.V hV c.L from rfl, hgen, hbar]
  exact hsup

theorem isComponentOf_barSub_L (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h208 : S20_8 D) (h1930 : H1930 D) {K : Subgroup G} (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : ↥D.T, K.map (MulAut.conj (t : G)).toMonoidHom) :
    IsComponentOf (barSub (⊥ : Subgroup G) c.V hV K) (c.H hV) := by
  have hKL : K ≤ c.L := CFSG.Quasithin.A3.subnormal_le hK.1
  have hcomp := isComponentOf_barSub_of_sup_conj c h208 h1930 hV le_rfl
    (uc22p22v_le_normalizer_conjClosure c.N D.Z) (c.ne_bot_V) hK hgen
  exact ⟨barSub_mono (⊥ : Subgroup G) c.V hV hKL,
    TwelveTwentyThree.isSubnormal_barSub hV hK.1, hcomp.2.2⟩

theorem le_M_of_barSub_le (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {B X : Subgroup G}
    (hB : B ≤ c.L) (hX : X ≤ c.L)
    (h : barSub (⊥ : Subgroup G) c.V hV B ≤ barSub (⊥ : Subgroup G) c.V hV X)
    (hXM : X ≤ D.M) : B ≤ D.M := by
  intro b hb
  have hb' : actTil (⊥ : Subgroup G) c.V hV ⟨b, c.L_le_stabTil (hB hb)⟩ ∈
      barSub (⊥ : Subgroup G) c.V hV X :=
    h ((mem_barSub (⊥ : Subgroup G) c.V hV B _).2
      ⟨⟨b, c.L_le_stabTil (hB hb)⟩, hb, rfl⟩)
  obtain ⟨x, hxX, hx⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV X _).1 hb'
  have hxker : (x : G)⁻¹ * b ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
    refine ⟨c.L.mul_mem (c.L.inv_mem (hX hxX)) (hB hb), ?_⟩
    change (x : G)⁻¹ * b ∈ Subgroup.centralizer (c.V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hact : actTil (⊥ : Subgroup G) c.V hV
        ⟨(x : G)⁻¹ * b, c.L_le_stabTil (c.L.mul_mem (c.L.inv_mem (hX hxX)) (hB hb))⟩ = 1 := by
      have hsub : (⟨(x : G)⁻¹ * b,
          c.L_le_stabTil (c.L.mul_mem (c.L.inv_mem (hX hxX)) (hB hb))⟩ :
          stabTil (⊥ : Subgroup G) c.V) = ⟨(x : G), c.L_le_stabTil (hX hxX)⟩⁻¹ *
          ⟨b, c.L_le_stabTil (hB hb)⟩ := Subtype.ext rfl
      rw [hsub, map_mul, map_inv, hx]
      simp
    have h2 := (actTil_eq_one_iff (⊥ : Subgroup G) c.V hV _).1 hact v hv
    rw [Subgroup.mem_bot] at h2
    have h3 : ((x : G)⁻¹ * b) * v * ((x : G)⁻¹ * b)⁻¹ = v := mul_inv_eq_one.mp h2
    exact (calc ((x : G)⁻¹ * b) * v =
        (((x : G)⁻¹ * b) * v * ((x : G)⁻¹ * b)⁻¹) * ((x : G)⁻¹ * b) := by group
      _ = v * ((x : G)⁻¹ * b) := by rw [h3]).symm
  have hbM : b = (x : G) * ((x : G)⁻¹ * b) := by group
  rw [hbM]
  exact D.M.mul_mem (hXM hxX) (c.inf_centralizer_V_le_M c.L hxker)

theorem barSub_inf_M_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h208 : S20_8 D) (h1930 : H1930 D) (hU : c.infCentralizer ≤ D.U) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) =
      c.H hV ⊓ stabSub (fixV (c.sylowStarImage hV)) := by
  obtain ⟨K, hK, hgen, hH⟩ := c.exists_component_H_eq_iSup_conj hV
  have hSyl := c.isSylowIn_sylowStarImage hV
  have hKcomp := c.isComponentOf_barSub_L hV h208 h1930 hK hgen
  have hTnormH := c.Tstar_le_normalizer hV
  have hTnormS : c.Tstar hV ≤ Subgroup.normalizer
      (c.sylowStarImage hV : Set (MulAut (c.W hV))) := by
    rw [← c.barSub_T_inf_L_eq_sylowStarImage hV]
    exact c.Tstar_le_normalizer_barSub hV inf_le_right
      ((le_inf Subgroup.le_normalizer c.hL.1.1).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hTnormX : c.Tstar hV ≤ Subgroup.normalizer
      (barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) : Set (MulAut (c.W hV))) :=
    c.Tstar_le_normalizer_barSub hV inf_le_left
      ((le_inf c.hL.1.1 (D.sylowM.le.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hstab : c.H hV ⊓ stabSub (fixV (c.sylowStarImage hV)) ≤
      barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) := by
    intro φ hφ
    obtain ⟨hφH, hφstab⟩ := hφ
    obtain ⟨x, hxL, hxact⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV c.L φ).1 hφH
    have hxN : (x : G) ∈ Subgroup.normalizer (c.infCentralizer : Set G) := by
      refine c.mem_normalizer_of_actTil_mem_stabSub hV inf_le_left (g := (x : G)) x.2 ?_
      show actTil (⊥ : Subgroup G) c.V hV x ∈ stabSub (imgTil (⊥ : Subgroup G) c.V hV (c.infCentralizer))
      rw [hxact]; rwa [← c.imgTil_inf_centralizer_eq_fixV hV] at hφstab
    exact (mem_barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) φ).2
      ⟨⟨(x : G), c.L_le_stabTil hxL⟩, ⟨hxL, c.inf_normalizer_le_M hU ⟨hxL, hxN⟩⟩, hxact⟩
  have hne : barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) ≠ c.H hV := fun h =>
    Ctx23L.L_not_le_M c
      (c.le_M_of_barSub_le hV le_rfl inf_le_left (le_of_eq h.symm) inf_le_right)
  have hproper : barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) < c.H hV :=
    lt_of_le_of_ne (barSub_mono (⊥ : Subgroup G) c.V hV inf_le_left) hne
  exact kNatParMax_holds (c.W hV) (c.H hV) (c.Tstar hV)
    (barSub (⊥ : Subgroup G) c.V hV K) (c.sylowStarImage hV)
    (barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M)) k hnat (c.commutator_H_eq hV)
    hTnormH hKcomp hH hSyl hTnormS hTnormX hstab hproper

theorem mem_centralizer_of_actTil_eq_one (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {g : G} (hg : g ∈ stabTil (⊥ : Subgroup G) c.V)
    (h : actTil (⊥ : Subgroup G) c.V hV ⟨g, hg⟩ = 1) :
    g ∈ Subgroup.centralizer (c.V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h2 := (actTil_eq_one_iff (⊥ : Subgroup G) c.V hV _).1 h v hv
  rw [Subgroup.mem_bot] at h2
  have h3 : g * v * g⁻¹ = v := mul_inv_eq_one.mp h2
  exact (calc g * v = (g * v * g⁻¹) * g := by group
    _ = v * g := by rw [h3]).symm

private theorem mem_centralizer_singleton_of_conj_eq {g v : G} (h : g * v * g⁻¹ = v) :
    g ∈ Subgroup.centralizer ({v} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have hcomm : g * v = v * g := by
    calc g * v = (g * v * g⁻¹) * g := by group
      _ = v * g := by rw [h]
  exact hcomm.symm

theorem mkTil_eq_one_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {v : G}
    (hv : v ∈ c.V) :
    mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv⟩) = 1 ↔ v = 1 := by
  constructor
  · intro h
    have hx : IntMod.mk hV ⟨v, hv⟩ = 1 :=
      (TwelveShort.mkTilEquiv c.V hV).injective (by
        rw [TwelveShort.mkTilEquiv_apply, h, map_one])
    have hval : (IntMod.mk hV ⟨v, hv⟩).val = v := rfl
    have hone : (1 : IntMod c.V hV).val = 1 := IntMod.val_one
    have := congrArg IntMod.val hx
    rwa [hval, hone] at this
  · rintro rfl
    exact map_one (mkTil (⊥ : Subgroup G) c.V hV)

theorem mkTil_mem_fixV_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {v : G}
    (hv : v ∈ c.V) :
    mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv⟩) ∈
        fixV (c.sylowStarImage hV) ↔ v ∈ c.infCentralizer := by
  constructor
  · intro h
    rw [← c.imgTil_inf_centralizer_eq_fixV hV] at h
    rw [mem_imgTil] at h
    obtain ⟨y, hy, hyq⟩ := h
    have hyx : y = IntMod.mk hV ⟨v, hv⟩ :=
      (TwelveShort.mkTilEquiv c.V hV).injective (by
        rw [TwelveShort.mkTilEquiv_apply, TwelveShort.mkTilEquiv_apply]; exact hyq)
    have hyv : y.val = v := by rw [hyx]; rfl
    rwa [hyv] at hy
  · intro h
    rw [← c.imgTil_inf_centralizer_eq_fixV hV, mem_imgTil]
    exact ⟨IntMod.mk hV ⟨v, hv⟩, h, rfl⟩

theorem actTil_mkTil_fixed_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {g : stabTil (⊥ : Subgroup G) c.V} {v : G} (hv : v ∈ c.V) :
    actTil (⊥ : Subgroup G) c.V hV g
        (mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv⟩)) =
      mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv⟩) ↔
      (g : G) * v * (g : G)⁻¹ = v := by
  rw [actTil_mk]
  constructor
  · intro h
    have h2 := (mkTil_eq_iff (⊥ : Subgroup G) c.V hV
      (actStab (⊥ : Subgroup G) c.V hV g (IntMod.mk hV ⟨v, hv⟩))
      (IntMod.mk hV ⟨v, hv⟩)).1 h
    rw [Subgroup.mem_bot, actStab_apply_val] at h2
    have hval : (IntMod.mk hV ⟨v, hv⟩).val = v := rfl
    simpa [hval] using mul_inv_eq_one.mp h2
  · intro h
    apply (mkTil_eq_iff (⊥ : Subgroup G) c.V hV
      (actStab (⊥ : Subgroup G) c.V hV g (IntMod.mk hV ⟨v, hv⟩))
      (IntMod.mk hV ⟨v, hv⟩)).2
    rw [Subgroup.mem_bot, actStab_apply_val]
    exact mul_inv_eq_one.mpr h

theorem inf_uCore_V (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    D.U ⊓ c.V = c.infCentralizer := by
  have hU := c.le_uCore_of_natural hV h207 h209 h1930 hnat
  have hF := c.barSub_inf_M_eq hV h208 h1930 hU hnat
  refine le_antisymm ?_ (le_inf hU inf_le_left)
  intro v hv
  by_contra hvℓ
  have hv1 : v ≠ 1 := fun h => hvℓ (h ▸ (c.infCentralizer).one_mem)
  let xv : IntMod c.V hV := IntMod.mk hV ⟨v, hv.2⟩
  let q : c.W hV := mkTil (⊥ : Subgroup G) c.V hV xv
  have hq1 : q ≠ 1 := fun h =>
    hv1 ((mkTil_eq_one_iff c hV hv.2).1 (by simpa [q, xv] using h))
  have hqℓ : q ∉ fixV (c.sylowStarImage hV) := fun h =>
    hvℓ ((mkTil_mem_fixV_iff c hV hv.2).1 (by simpa [q, xv] using h))
  obtain ⟨h, hhH, hfixq, hstab⟩ := kNatCentMove_holds (c.W hV) (c.H hV)
    (c.sylowStarImage hV) k hnat (c.commutator_H_eq hV)
    (c.isSylowIn_sylowStarImage hV) q hq1 hqℓ
  obtain ⟨x, hxL, hxeq⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV c.L h).1 hhH
  have hxcomm : (x : G) * v * (x : G)⁻¹ = v :=
    (actTil_mkTil_fixed_iff c hV hv.2).1 (by
      simpa [q, xv] using (show actTil (⊥ : Subgroup G) c.V hV x
        (mkTil (⊥ : Subgroup G) c.V hV xv) = mkTil (⊥ : Subgroup G) c.V hV xv by
          rw [hxeq]; exact hfixq))
  have hxv : (x : G) ∈ Subgroup.centralizer ({v} : Set G) :=
    mem_centralizer_singleton_of_conj_eq hxcomm
  have hxM : (x : G) ∈ D.M :=
    Ctx23.centralizer_le_M c.toCtx23 hv.1 hv1 hxv
  have hmem : h ∈ barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) :=
    (mem_barSub (⊥ : Subgroup G) c.V hV (c.L ⊓ D.M) h).2
      ⟨⟨(x : G), x.2⟩, ⟨hxL, hxM⟩, hxeq⟩
  rw [hF] at hmem
  exact hstab hmem.2

theorem U0_eq_infCentralizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    c.U0 = c.infCentralizer := by
  have hUV := c.inf_uCore_V hV h207 h208 h209 h1930 hnat
  have hU0V : c.U0 ≤ c.V := by
    rw [Ctx23L.U0, Ctx23L.V]
    exact uc22p22v_conjClosure_le
      (inf_le_left.trans (uc22p22v_le_normalizer_conjClosure c.N D.Z))
      (uc22p22v_le_conjClosure c.N D.Z)
  have hU0U : c.U0 ≤ D.U := by
    rw [Ctx23L.U0]
    exact uc22p22v_conjClosure_le (inf_le_right.trans (le_normalizer_uCore D.M D.T))
      (Data.Z_le_U D)
  exact le_antisymm ((le_inf hU0U hU0V).trans (le_of_eq hUV))

    (c.le_U0_of_natural hV h207 h209 h1930 hnat)

theorem sylowStar_le_parabolic_barSub (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P) :
    (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤
      (barSub (⊥ : Subgroup G) c.V hV P).subgroupOf (c.H hV) := by
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hAN : c.N ≤ Subgroup.normalizer (c.V : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.N D.Z
  let Pstar : Subgroup (MulAut (c.W hV)) := barSub (⊥ : Subgroup G) c.V hV P
  let Psub : Subgroup ↥(c.H hV) := Pstar.subgroupOf (c.H hV)
  let R : Subgroup ↥(c.H hV) := (c.sylowStar hV : Subgroup ↥(c.H hV))
  have hpar : IsParabolicTwo ↥(c.H hV) Psub := by
    simpa [Psub, Pstar] using isParabolicTwo_barSub (c := c) (A := c.V) (P := P) hV hAN hP.1.1
  have hSstarN : c.sylowStarImage hV ≤
      Subgroup.normalizer (Pstar : Set (MulAut (c.W hV))) :=
    (c.sylowStar_le_Tstar hV).trans
      (c.Tstar_le_normalizer_barSub hV hPL hP.1.2.1)
  have hRmem : ∀ {r : ↥(c.H hV)}, r ∈ R →
      (r : MulAut (c.W hV)) ∈ c.sylowStarImage hV := by
    intro r hr
    exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
  have hRp : IsPGroup 2 R := by
    simpa [R] using (c.sylowStar hV).isPGroup'
  refine IsParabolicTwo.le_of_le_normalizer hpar hRp ?_
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hSstarN (hRmem hr)) (y : MulAut (c.W hV))).1
        (Subgroup.mem_subgroupOf.mp hy))
  · intro hy
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hSstarN (hRmem hr)) (y : MulAut (c.W hV))).2
        (Subgroup.mem_subgroupOf.mp hy))

theorem normalizer_sylowStar_le_parabolic_barSub (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P) :
    c.H hV ⊓ Subgroup.normalizer
      (c.sylowStarImage hV : Set (MulAut (c.W hV))) ≤
      barSub (⊥ : Subgroup G) c.V hV P := by
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hAN : c.N ≤ Subgroup.normalizer (c.V : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.N D.Z
  let Pstar : Subgroup (MulAut (c.W hV)) := barSub (⊥ : Subgroup G) c.V hV P
  let Psub : Subgroup ↥(c.H hV) := Pstar.subgroupOf (c.H hV)
  have hpar : IsParabolicTwo ↥(c.H hV) Psub := by
    simpa [Psub, Pstar] using isParabolicTwo_barSub (c := c) (A := c.V) (P := P) hV hAN hP.1.1
  have hNH : Subgroup.normalizer ((c.sylowStar hV : Subgroup ↥(c.H hV)) : Set ↥(c.H hV)) ≤ Psub :=
    IsParabolicTwo.normalizer_le hpar (c.sylowStar hV) (c.sylowStar_le_parabolic_barSub hV hP)
  intro φ hφ
  have hRmem : ∀ {r : ↥(c.H hV)}, r ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)) →
      (r : MulAut (c.W hV)) ∈ c.sylowStarImage hV :=
    fun hr => Subgroup.mem_map.mpr ⟨_, hr, rfl⟩
  have hmem : (⟨φ, hφ.1⟩ : ↥(c.H hV)) ∈
      Subgroup.normalizer ((c.sylowStar hV : Subgroup ↥(c.H hV)) : Set ↥(c.H hV)) := by
    rw [Subgroup.mem_normalizer_iff]; intro r
    constructor
    · intro hr
      have hmemS : (φ * (r : MulAut (c.W hV)) * φ⁻¹) ∈ c.sylowStarImage hV :=
        (Subgroup.mem_normalizer_iff.mp hφ.2 (r : MulAut (c.W hV))).1 (hRmem hr)
      obtain ⟨x, hxR, hx⟩ := Subgroup.mem_map.mp hmemS
      have hx' : (⟨φ, hφ.1⟩ : ↥(c.H hV)) * r * (⟨φ, hφ.1⟩ : ↥(c.H hV))⁻¹ = x :=
        Subtype.ext (by simpa [mul_assoc] using hx.symm)
      rw [hx']; exact hxR
    · intro hr
      have hr' : (φ * (r : MulAut (c.W hV)) * φ⁻¹) ∈ c.sylowStarImage hV := hRmem hr
      have hinv : φ⁻¹ ∈ Subgroup.normalizer (c.sylowStarImage hV : Set (MulAut (c.W hV))) :=
        (Subgroup.normalizer _).inv_mem hφ.2
      have hmove : (φ⁻¹ * (φ * (r : MulAut (c.W hV)) * φ⁻¹) * φ) ∈ c.sylowStarImage hV :=
        (Subgroup.mem_normalizer_iff.mp hinv (φ * (r : MulAut (c.W hV)) * φ⁻¹)).1 hr'
      obtain ⟨x, hxR, hx⟩ := Subgroup.mem_map.mp hmove
      rw [show r = x from Subtype.ext (by simpa [mul_assoc] using hx.symm)]
      exact hxR
  exact Subgroup.mem_subgroupOf.mp (hNH hmem)

theorem mem_barSub_inf_M_of_mem_barSub_L0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h209 : S20_9 D) (h1930 : H1930 D) {φ : MulAut (c.W hV)}
    (hφ1 : φ ∈ barSub (⊥ : Subgroup G) c.V hV c.L0)
    (hφ2 : φ ∈ Subgroup.normalizer (c.sylowStarImage hV : Set (MulAut (c.W hV)))) :
    φ ∈ barSub (⊥ : Subgroup G) c.V hV (c.L0 ⊓ D.M) := by
  obtain ⟨x, hxL0, hxφ⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV c.L0 φ).1 hφ1
  have hφH : φ ∈ c.H hV := (barSub_mono (⊥ : Subgroup G) c.V hV c.hL0L) hφ1
  have hφ2bar : φ ∈ barSub (⊥ : Subgroup G) c.V hV
      (c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G))) := by
    rw [c.barSub_normalizer_eq hV]
    exact ⟨hφH, hφ2⟩
  obtain ⟨y, hyN, hyφ⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV
    (c.L ⊓ Subgroup.normalizer (((D.T ⊓ c.L : Subgroup G) : Set G))) φ).1 hφ2bar
  have hyL : (y : G) ∈ c.L := hyN.1
  have hyM : (y : G) ∈ D.M :=
    c.borel_le_M h207 h209 kBorelSolv20_7_holds h1930 ⟨hyL, hyN.2⟩
  have hz : (y : G)⁻¹ * x ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
    refine ⟨c.L.mul_mem (c.L.inv_mem hyL) (c.hL0L hxL0), ?_⟩
    apply c.mem_centralizer_of_actTil_eq_one hV (g := (y : G)⁻¹ * x)
    have hsub : (⟨(y : G)⁻¹ * x,
        c.L_le_stabTil (c.L.mul_mem (c.L.inv_mem hyL) (c.hL0L hxL0))⟩ :
        stabTil (⊥ : Subgroup G) c.V) = ⟨(y : G), c.L_le_stabTil hyL⟩⁻¹ *
        ⟨(x : G), c.L_le_stabTil (c.hL0L hxL0)⟩ := Subtype.ext rfl
    rw [hsub, map_mul, map_inv, hyφ, hxφ]
    simp
  have hzM : (y : G)⁻¹ * x ∈ D.M := c.inf_centralizer_V_le_M c.L hz
  have hxM : (x : G) ∈ D.M := by
    have hxy : (x : G) = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [hxy]
    exact D.M.mul_mem hyM hzM
  exact (mem_barSub (⊥ : Subgroup G) c.V hV (c.L0 ⊓ D.M) φ).2
    ⟨⟨(x : G), c.L_le_stabTil (c.hL0L hxL0)⟩, ⟨hxL0, hxM⟩, hxφ⟩

theorem Hinf_barSub_inf_normalizer_le (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h209 : S20_9 D) (h1930 : H1930 D) {P : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P) :
    Hinf (barSub (⊥ : Subgroup G) c.V hV P) ⊓
        Subgroup.normalizer (c.sylowStarImage hV : Set (MulAut (c.W hV))) ≤
      barSub (⊥ : Subgroup G) c.V hV (c.L0 ⊓ D.M) := by
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hAN : c.N ≤ Subgroup.normalizer (c.V : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.N D.Z
  have hHinf := Hinf_barSub_eq c (A := c.V) (P := P) hV hAN hPL hL0P
  intro φ hφ
  obtain ⟨hφ1, hφ2⟩ := hφ
  have hφ1' : φ ∈ barSub (⊥ : Subgroup G) c.V hV c.L0 := by
    rwa [hHinf] at hφ1
  exact c.mem_barSub_inf_M_of_mem_barSub_L0 hV h207 h209 h1930 hφ1' hφ2

theorem not_le_stabSub_of_parabolic (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) {P : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P) :
    ¬ barSub (⊥ : Subgroup G) c.V hV P ≤
      stabSub (fixV (c.sylowStarImage hV)) := by
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hU := c.le_uCore_of_natural hV h207 h209 h1930 hnat
  have hF := c.barSub_inf_M_eq hV h208 h1930 hU hnat
  intro hstab
  refine hP.1.2.2 (c.le_M_of_barSub_le hV hPL inf_le_left ?_ inf_le_right)
  exact (le_inf (barSub_mono (⊥ : Subgroup G) c.V hV hPL) hstab).trans (le_of_eq hF.symm)

theorem irrOn_barSub_inf_L0_M (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) {P : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P) :
    ∀ J : Subgroup (c.W hV), J ≤ fixV (c.sylowStarImage hV) →
      StableUnder (barSub (⊥ : Subgroup G) c.V hV (c.L0 ⊓ D.M)) J →
      J = ⊥ ∨ J = fixV (c.sylowStarImage hV) := by
  intro J hJ hst
  have hPleH : barSub (⊥ : Subgroup G) c.V hV P ≤ c.H hV :=
    barSub_mono (⊥ : Subgroup G) c.V hV (parabolicOf_iff.mp hP.1.1).1
  have hNP := c.normalizer_sylowStar_le_parabolic_barSub hV hP
  have hnot := c.not_le_stabSub_of_parabolic hV h207 h208 h209 h1930 hnat hP
  have hB0 := c.Hinf_barSub_inf_normalizer_le hV h207 h209 h1930 hP hL0P
  exact kNatBorelIrr_holds (c.W hV) (c.H hV) (c.sylowStarImage hV)
    (barSub (⊥ : Subgroup G) c.V hV P) k hnat (c.commutator_H_eq hV)
    (c.isSylowIn_sylowStarImage hV) hNP hPleH hnot J hJ
    (fun x hx => hst x (hB0 hx))

theorem irrOn_barSub_inf_L0_M_exists (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    ∀ J : Subgroup (c.W hV), J ≤ fixV (c.sylowStarImage hV) →
      StableUnder (barSub (⊥ : Subgroup G) c.V hV (c.L0 ⊓ D.M)) J →
      J = ⊥ ∨ J = fixV (c.sylowStarImage hV) := by
  obtain ⟨P, hP, hL0P⟩ := c.exists_minTInvParabolic h209 h1930
  exact c.irrOn_barSub_inf_L0_M hV h207 h208 h209 h1930 hnat hP hL0P

theorem U0_eq_conjClosure (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z := by
  have hU0 := c.U0_eq_infCentralizer hV h207 h208 h209 h1930 hnat
  have hirr := c.irrOn_barSub_inf_L0_M_exists hV h207 h208 h209 h1930 hnat
  have hU1leU0 : conjClosure (c.L0 ⊓ D.M) D.Z ≤ c.U0 := by
    rw [Ctx23L.U0]
    exact uc22p22v_conjClosure_mono
      (le_inf (inf_le_left.trans (c.hL0L.trans (Ctx23L.L_le_N c))) inf_le_right) D.Z
  have hU1leℓ : conjClosure (c.L0 ⊓ D.M) D.Z ≤ c.infCentralizer :=
    hU1leU0.trans (le_of_eq hU0)
  have hU1leV : conjClosure (c.L0 ⊓ D.M) D.Z ≤ c.V := hU1leℓ.trans inf_le_left
  have hJle : imgTil (⊥ : Subgroup G) c.V hV (conjClosure (c.L0 ⊓ D.M) D.Z) ≤
      fixV (c.sylowStarImage hV) := by
    rw [← c.imgTil_inf_centralizer_eq_fixV hV]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono c.V hU1leℓ)
  have hJstable : StableUnder (barSub (⊥ : Subgroup G) c.V hV (c.L0 ⊓ D.M))
      (imgTil (⊥ : Subgroup G) c.V hV (conjClosure (c.L0 ⊓ D.M) D.Z)) :=
    c.stableUnder_imgTil hV (inf_le_left.trans (c.hL0L.trans c.L_le_stabTil))
      (uc22p22v_le_normalizer_conjClosure (c.L0 ⊓ D.M) D.Z)
  have hJne : imgTil (⊥ : Subgroup G) c.V hV (conjClosure (c.L0 ⊓ D.M) D.Z) ≠ ⊥ := by
    intro h
    have hpre := CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le (V₀ := ⊥) hV hU1leV bot_le
    rw [h, preTil_bot, inf_bot_eq] at hpre
    have hU1ne : conjClosure (c.L0 ⊓ D.M) D.Z ≠ ⊥ := fun h0 => uc22main1_Z_ne_bot D
      (le_bot_iff.mp (h0 ▸ uc22p22v_le_conjClosure (c.L0 ⊓ D.M) D.Z))
    exact hU1ne hpre.symm
  have hJeq : imgTil (⊥ : Subgroup G) c.V hV (conjClosure (c.L0 ⊓ D.M) D.Z) =
      fixV (c.sylowStarImage hV) := by
    rcases hirr _ hJle hJstable with h | h
    · exact absurd h hJne
    · exact h
  have hU1eq : conjClosure (c.L0 ⊓ D.M) D.Z = c.infCentralizer := by
    rw [← CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le
        (V₀ := ⊥) hV hU1leV bot_le,
      hJeq, ← c.imgTil_inf_centralizer_eq_fixV hV,
      CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le (V₀ := ⊥) hV inf_le_left bot_le]
  exact hU0.trans hU1eq.symm

theorem card_U0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    Nat.card c.U0 = 2 ^ k := by
  have hU0 := c.U0_eq_infCentralizer hV h207 h208 h209 h1930 hnat
  have hU0V : c.U0 ≤ c.V := by rw [hU0]; exact inf_le_left
  have himg : imgTil (⊥ : Subgroup G) c.V hV c.U0 = fixV (c.sylowStarImage hV) := by
    rw [hU0, c.imgTil_inf_centralizer_eq_fixV hV]
  have hcardImg : Nat.card (imgTil (⊥ : Subgroup G) c.V hV c.U0) = Nat.card c.U0 := by
    rw [imgTil]
    rw [Subgroup.card_map_of_injective (fun x y hxy => by
      apply (TwelveShort.mkTilEquiv c.V hV).injective
      simpa [TwelveShort.mkTilEquiv_apply] using hxy)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU0V).toEquiv
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have htab := kTab23a_holds (c.W hV) (c.H hV) k hnat (c.commutator_H_eq hV) (c.sylowStar hV)
  have hfix : (fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) =
      fixV (c.sylowStarImage hV) := by
    ext w
    rw [FixedPoints.mem_subgroup, mem_fixV]
    constructor
    · intro hw φ hφ
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hφ
      exact hw ⟨s, hs⟩
    · intro hw s
      exact hw (s : MulAut (c.W hV)) (Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩)
  calc Nat.card c.U0 = Nat.card (imgTil (⊥ : Subgroup G) c.V hV c.U0) := hcardImg.symm
    _ = Nat.card (fixV (c.sylowStarImage hV)) := by rw [himg]
    _ = Nat.card (fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)) := by rw [hfix]
    _ = 2 ^ k := htab.1

theorem IrrOn_U0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    IrrOn (c.L0 ⊓ D.M) c.U0 := by
  intro W hWle hWN
  have hU0 := c.U0_eq_infCentralizer hV h207 h208 h209 h1930 hnat
  have hirr := c.irrOn_barSub_inf_L0_M_exists hV h207 h208 h209 h1930 hnat
  have hWleℓ : W ≤ c.infCentralizer := hWle.trans (le_of_eq hU0)
  have hWleV : W ≤ c.V := hWleℓ.trans inf_le_left
  have himg : imgTil (⊥ : Subgroup G) c.V hV W ≤ fixV (c.sylowStarImage hV) := by
    rw [← c.imgTil_inf_centralizer_eq_fixV hV]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono c.V hWleℓ)
  have hstable : StableUnder (barSub (⊥ : Subgroup G) c.V hV (c.L0 ⊓ D.M))
      (imgTil (⊥ : Subgroup G) c.V hV W) :=
    c.stableUnder_imgTil hV (inf_le_left.trans (c.hL0L.trans c.L_le_stabTil)) hWN
  rcases hirr _ himg hstable with h | h
  · left
    have hpre := CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le
      (V₀ := ⊥) hV hWleV bot_le
    rw [h, preTil_bot, inf_bot_eq] at hpre
    exact hpre.symm
  · right
    have hpre := CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le
      (V₀ := ⊥) hV hWleV bot_le
    rw [h, ← c.imgTil_inf_centralizer_eq_fixV hV,
      CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le (V₀ := ⊥) hV inf_le_left bot_le] at hpre
    rw [hU0]
    exact hpre.symm

theorem inf_uCore_V_eq_U0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    D.U ⊓ c.V = c.U0 := by
  rw [c.inf_uCore_V hV h207 h208 h209 h1930 hnat,
    ← c.U0_eq_infCentralizer hV h207 h208 h209 h1930 hnat]

theorem package_U0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D) {k : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) k) :
    Nat.card c.U0 = 2 ^ k ∧ c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z ∧
      D.U ⊓ c.V = c.U0 ∧ IrrOn (c.L0 ⊓ D.M) c.U0 :=
  ⟨c.card_U0 hV h207 h208 h209 h1930 hnat,
    c.U0_eq_conjClosure hV h207 h208 h209 h1930 hnat,
    c.inf_uCore_V_eq_U0 hV h207 h208 h209 h1930 hnat,
    c.IrrOn_U0 hV h207 h208 h209 h1930 hnat⟩
