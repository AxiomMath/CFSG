module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeKeyLemma
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.KFact
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FourInputN.LineComm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds
public import CFSG.Quasithin.Background.F918M0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem fixedPointSubgroup_sylowStar_eq_imgTil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    CFSG.fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) =
      imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer := by
  let : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  rw [fixedPointSubgroup_sylow_map (S := c.sylowStar hV)]
  rw [fixedPointSubgroup_eq_fixV (c.sylowStarImage hV)]
  exact (c.imgTil_inf_centralizer_eq_fixV hV).symm

theorem phiL_mem_pointStab_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (x : ↥c.L) :
    c.phiL hV x ∈ KTabD.pointStab (c.H hV) (c.sylowStar hV) ↔
      (x : G) ∈ normalizer (c.infCentralizer : Set G) := by
  have hU : c.infCentralizer ≤ c.V := inf_le_left
  have hstab : c.phiL hV x ∈ KTabD.pointStab (c.H hV) (c.sylowStar hV) ↔
      (c.phiL hV x : MulAut (c.W hV)) ∈
        stabSub (imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer) := by
    rw [KTabD.pointStab, MulAction.mem_stabilizer_iff,
      c.fixedPointSubgroup_sylowStar_eq_imgTil hV]
    have hcoe : (c.phiL hV x) •
        (imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer : Set (c.W hV)) =
        (((imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer).map
          (c.phiL hV x : MulAut (c.W hV)).toMonoidHom) : Set (c.W hV)) := by
      rw [Subgroup.coe_map, ← Set.image_smul]
      rfl
    change (c.phiL hV x) •
        (imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer : Set (c.W hV)) =
        (imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer : Set (c.W hV)) ↔
      (c.phiL hV x : MulAut (c.W hV)) ∈
        stabSub (imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer)
    rw [hcoe]
    constructor
    · intro hset
      exact mem_stabSub_iff_map_eq.mpr (Subgroup.ext (Set.ext_iff.mp hset))
    · intro hsub
      rw [mem_stabSub_iff_map_eq.mp hsub]
  rw [hstab]
  constructor
  · intro hsub
    exact c.mem_normalizer_of_actTil_mem_stabSub hV hU (c.L_le_stabTil x.2) hsub
  · intro hx
    have hB : Subgroup.zpowers (x : G) ≤ stabTil (⊥ : Subgroup G) c.V :=
      Subgroup.zpowers_le.mpr (c.L_le_stabTil x.2)
    have hBU : Subgroup.zpowers (x : G) ≤ normalizer (c.infCentralizer : Set G) :=
      Subgroup.zpowers_le.mpr hx
    have hstable := c.stableUnder_imgTil hV hB hBU
    have hxbar : actTil (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ ∈
        barSub (⊥ : Subgroup G) c.V hV (Subgroup.zpowers (x : G)) :=
      actTil_mem_barSub (⊥ : Subgroup G) c.V hV (Subgroup.mem_zpowers (x : G))
        (c.L_le_stabTil x.2)
    have hxinv : actTil (⊥ : Subgroup G) c.V hV
        ⟨x⁻¹, (stabTil (⊥ : Subgroup G) c.V).inv_mem (c.L_le_stabTil x.2)⟩ ∈
        barSub (⊥ : Subgroup G) c.V hV (Subgroup.zpowers (x : G)) :=
      actTil_mem_barSub (⊥ : Subgroup G) c.V hV
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers (x : G)))
        ((stabTil (⊥ : Subgroup G) c.V).inv_mem (c.L_le_stabTil x.2))
    change actTil (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ ∈
      stabSub (imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer)
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := hstable _ hxinv
        (actTil (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ u) hu
      have hxinv_eq : actTil (⊥ : Subgroup G) c.V hV
          ⟨x⁻¹, (stabTil (⊥ : Subgroup G) c.V).inv_mem (c.L_le_stabTil x.2)⟩ =
          (actTil (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩)⁻¹ := by
        rw [← map_inv]
        congr 1
      rwa [hxinv_eq, MulAut.inv_apply_self] at h
    · intro hu
      exact hstable _ hxbar u hu

theorem card_infCentralizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) n) :
    Nat.card ↥c.infCentralizer = 2 ^ n := by
  let : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  let : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  let : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have hmain := kTab23a_holds (c.W hV) (c.H hV) n hnat (c.commutator_H_eq hV)
  let : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓcard : Nat.card (CFSG.fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)) = 2 ^ n :=
    (hmain (c.sylowStar hV)).1
  rw [c.fixedPointSubgroup_sylowStar_eq_imgTil hV] at hℓcard
  rw [← hℓcard, imgTil,
    Subgroup.card_map_of_injective (TwelveShort.mkTilEquiv c.V hV).injective]
  exact (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (H := c.infCentralizer) (K := c.V) inf_le_left).toEquiv).symm

theorem eq_infCentralizer_of_card (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) n) {U : Subgroup G} (hUV : U ≤ c.V)
    (hUT : D.T ⊓ c.L ≤ centralizer (U : Set G)) (hcard : Nat.card U = 2 ^ n) :
    U = c.infCentralizer := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · refine le_inf hUV ?_
    rw [Subgroup.le_centralizer_iff]
    exact hUT
  · rw [c.card_infCentralizer hV hnat, hcard]

private theorem mkTil_mem_fixedPointSubgroup (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {x : IntMod c.V hV} (hx : x.val ∈ c.infCentralizer) :
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    mkTil (⊥ : Subgroup G) c.V hV x ∈
      CFSG.fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) := by
  let : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  rw [c.fixedPointSubgroup_sylowStar_eq_imgTil hV]
  exact (mem_imgTil (⊥ : Subgroup G) c.V hV c.infCentralizer _).2 ⟨x, hx, rfl⟩

private theorem mkTil_ne_one (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {x : IntMod c.V hV} (hx : x.val ≠ 1) :
    mkTil (⊥ : Subgroup G) c.V hV x ≠ 1 := by
  intro h1
  have h2 : x = 1 := by
    apply (TwelveShort.mkTilEquiv c.V hV).injective
    simpa [TwelveShort.mkTilEquiv_apply] using h1
  refine hx ?_
  have h3 := congrArg IntMod.val h2
  rwa [IntMod.val_one] at h3

theorem exists_zpowers_transitive (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) n) :
    ∃ y ∈ c.L, y ∈ normalizer (c.infCentralizer : Set G) ∧
      ∀ u ∈ c.infCentralizer, ∀ w ∈ c.infCentralizer, u ≠ 1 → w ≠ 1 →
          ∃ k : ℤ, y ^ k * u * (y ^ k)⁻¹ = w := by
  let : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  obtain ⟨h, hhstab, htrans⟩ :=
    AutZC.kLineTransitive_holds (c.W hV) (c.H hV) n hnat (c.commutator_H_eq hV)
      (c.sylowStar hV)
  obtain ⟨yL, hyL⟩ := c.phiL_surjective hV h
  refine ⟨(yL : G), yL.2, ?_, ?_⟩
  · rw [← hyL] at hhstab
    exact (c.phiL_mem_pointStab_iff hV yL).mp hhstab
  · intro u hu w hw hu1 hw1
    let u' : IntMod c.V hV := IntMod.mk hV ⟨u, (Subgroup.mem_inf.mp hu).1⟩
    let w' : IntMod c.V hV := IntMod.mk hV ⟨w, (Subgroup.mem_inf.mp hw).1⟩
    have hu'ℓ := c.mkTil_mem_fixedPointSubgroup hV (x := u') hu
    have hw'ℓ := c.mkTil_mem_fixedPointSubgroup hV (x := w') hw
    have hu'ne := c.mkTil_ne_one hV (x := u') hu1
    have hw'ne := c.mkTil_ne_one hV (x := w') hw1
    obtain ⟨k, hk⟩ := htrans _ hu'ℓ _ hw'ℓ hu'ne hw'ne
    refine ⟨k, ?_⟩
    have hkH : h ^ k = c.phiL hV (yL ^ k) := by
      rw [← hyL, ← map_zpow]
    have hk' : (c.phiL hV (yL ^ k) : MulAut (c.W hV))
        (mkTil (⊥ : Subgroup G) c.V hV u') = mkTil (⊥ : Subgroup G) c.V hV w' := by
      rw [← hkH]
      exact hk
    rw [c.phiL_apply_mkTil hV (yL ^ k) u', mkTil_eq_iff, Subgroup.mem_bot,
      actStab_apply_val, Subgroup.coe_zpow] at hk'
    simpa [u', w', IntMod.mk, IntMod.val] using (mul_inv_eq_one.mp hk')

private theorem conj_formula (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) n) {a b : G} (ha : a ∈ c.L) (hb : b ∈ c.L)
    (haN : a ∈ normalizer (c.infCentralizer : Set G))
    (hbN : b ∈ normalizer (c.infCentralizer : Set G)) :
    ∀ z ∈ c.infCentralizer,
      a * (b * z * b⁻¹) * a⁻¹ = b * (a * z * a⁻¹) * b⁻¹ := by
  let : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let aL : ↥c.L := ⟨a, ha⟩
  let bL : ↥c.L := ⟨b, hb⟩
  have haL : c.phiL hV aL ∈ KTabD.pointStab (c.H hV) (c.sylowStar hV) :=
    (c.phiL_mem_pointStab_iff hV aL).mpr haN
  have hbL : c.phiL hV bL ∈ KTabD.pointStab (c.H hV) (c.sylowStar hV) :=
    (c.phiL_mem_pointStab_iff hV bL).mpr hbN
  have hcomm := AutZC.kLineComm_holds (c.W hV) (c.H hV) n hnat (c.commutator_H_eq hV)
    (c.sylowStar hV)
  intro z hz
  let z' : IntMod c.V hV := IntMod.mk hV ⟨z, (Subgroup.mem_inf.mp hz).1⟩
  have hzℓ := c.mkTil_mem_fixedPointSubgroup hV (x := z') hz
  have h := hcomm (c.phiL hV aL) haL (c.phiL hV bL) hbL _ hzℓ
  change (c.phiL hV aL : MulAut (c.W hV))
      ((c.phiL hV bL : MulAut (c.W hV))
        (mkTil (⊥ : Subgroup G) c.V hV z')) =
    (c.phiL hV bL : MulAut (c.W hV))
      ((c.phiL hV aL : MulAut (c.W hV))
        (mkTil (⊥ : Subgroup G) c.V hV z')) at h
  rw [c.phiL_apply_mkTil hV bL z'] at h
  rw [c.phiL_apply_mkTil hV aL
    (actStab (⊥ : Subgroup G) c.V hV ⟨bL, c.L_le_stabTil bL.2⟩ z')] at h
  rw [c.phiL_apply_mkTil hV aL z'] at h
  rw [c.phiL_apply_mkTil hV bL
    (actStab (⊥ : Subgroup G) c.V hV ⟨aL, c.L_le_stabTil aL.2⟩ z')] at h
  rw [mkTil_eq_iff, Subgroup.mem_bot] at h
  simp only [actStab_apply_val] at h
  simpa [aL, bL, z', IntMod.mk, IntMod.val] using (mul_inv_eq_one.mp h)

theorem commutator_mem_centralizer_infCentralizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) {a b : G} (ha : a ∈ c.L)
    (hb : b ∈ c.L)
    (haN : a ∈ normalizer (c.infCentralizer : Set G))
    (hbN : b ∈ normalizer (c.infCentralizer : Set G)) :
    ⁅a, b⁆ ∈ centralizer (c.infCentralizer : Set G) := by
  have hformula := c.conj_formula hV hnat ha hb haN hbN
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hbInvN : b⁻¹ ∈ normalizer (c.infCentralizer : Set G) := Subgroup.inv_mem _ hbN
  have haInvN : a⁻¹ ∈ normalizer (c.infCentralizer : Set G) := Subgroup.inv_mem _ haN
  have hbu : b⁻¹ * u * b ∈ c.infCentralizer := by
    simpa using (Subgroup.mem_normalizer_iff.mp hbInvN u).mp hu
  have hv : a⁻¹ * (b⁻¹ * u * b) * a ∈ c.infCentralizer := by
    simpa using (Subgroup.mem_normalizer_iff.mp haInvN (b⁻¹ * u * b)).mp hbu
  let v : G := a⁻¹ * (b⁻¹ * u * b) * a
  have hv' : v ∈ c.infCentralizer := hv
  have hform := hformula v hv'
  have hleft : a * (b * v * b⁻¹) * a⁻¹ = ⁅a, b⁆ * u * ⁅a, b⁆⁻¹ := by
    rw [show v = a⁻¹ * (b⁻¹ * u * b) * a from rfl]
    simp only [commutatorElement_def]
    group
  have hright : b * (a * v * a⁻¹) * b⁻¹ = u := by
    rw [show v = a⁻¹ * (b⁻¹ * u * b) * a from rfl]
    group
  rw [hleft, hright] at hform
  have hcu : ⁅a, b⁆ * u = u * ⁅a, b⁆ := by
    calc ⁅a, b⁆ * u = (⁅a, b⁆ * u * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by group
      _ = u * ⁅a, b⁆ := by rw [hform]
  exact hcu.symm

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
