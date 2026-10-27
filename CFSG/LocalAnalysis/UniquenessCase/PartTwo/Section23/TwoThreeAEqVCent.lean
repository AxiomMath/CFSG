module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNormalCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNineLP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem surjective_mk'_of_sup_eq_top {L X : Subgroup G} (hXL : X ≤ L)
    (hXn : (X.subgroupOf L).Normal)
    (hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L) :
    Function.Surjective
      ((QuotientGroup.mk' (X.subgroupOf L)).comp
        (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 L))) := by
  haveI := hXn
  have hOle : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hsup' : (X.subgroupOf L) ⊔ (CFSG.Open.pCoreOf 2 L).subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXL hOle, hsup, Subgroup.subgroupOf_self]
  have hqtop : (((CFSG.Open.pCoreOf 2 L).subgroupOf L).map
      (QuotientGroup.mk' (X.subgroupOf L))) = ⊤ := by
    have h1 : (((X.subgroupOf L) ⊔ (CFSG.Open.pCoreOf 2 L).subgroupOf L).map
        (QuotientGroup.mk' (X.subgroupOf L))) = ⊤ := by
      rw [hsup', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
  intro y
  have hy : y ∈ ((CFSG.Open.pCoreOf 2 L).subgroupOf L).map
      (QuotientGroup.mk' (X.subgroupOf L)) := hqtop ▸ Subgroup.mem_top y
  obtain ⟨o, ho, hoo⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(o : G), Subgroup.mem_subgroupOf.mp ho⟩, ?_⟩
  change QuotientGroup.mk' (X.subgroupOf L)
    (Subgroup.inclusion hOle ⟨(o : G), Subgroup.mem_subgroupOf.mp ho⟩) = y
  rw [← hoo]
  exact congrArg (QuotientGroup.mk' (X.subgroupOf L)) (Subtype.ext rfl)

private theorem eq_of_le_sup_pCoreOf {L X : Subgroup G} (hXL : X ≤ L)
    (hXn : (X.subgroupOf L).Normal) (hperf : ⁅L, L⁆ = L)
    (h : L ≤ X ⊔ CFSG.Open.pCoreOf 2 L) : X = L := by
  have hOle : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L := le_antisymm (sup_le hXL hOle) h
  haveI hPerfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hO2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  let φ : ↥(CFSG.Open.pCoreOf 2 L) →* (↥L ⧸ (X.subgroupOf L)) :=
    (QuotientGroup.mk' (X.subgroupOf L)).comp (Subgroup.inclusion hOle)
  have hφ : Function.Surjective φ := surjective_mk'_of_sup_eq_top hXL hXn hsup
  have hP : IsPGroup 2 (↥L ⧸ (X.subgroupOf L)) := IsPGroup.of_surjective hO2 φ hφ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNil : Group.IsNilpotent (↥L ⧸ (X.subgroupOf L)) := IsPGroup.isNilpotent hP
  haveI hPerf : Group.IsPerfect (↥L ⧸ (X.subgroupOf L)) :=
    Group.IsPerfect.instQuotientSubgroup
  have hsub : Subsingleton (↥L ⧸ (X.subgroupOf L)) := by
    by_contra hns
    haveI : Nontrivial (↥L ⧸ (X.subgroupOf L)) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isNilpotent (G := ↥L ⧸ (X.subgroupOf L)) hNil
  exact le_antisymm hXL
    (Subgroup.subgroupOf_eq_top.mp (QuotientGroup.subgroup_eq_top_of_subsingleton _ hsub))

theorem Ctx23L.commutator_le_pCoreOf_or_eq {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {X : Subgroup G} (hXL : X ≤ c.L)
    (hXn : (X.subgroupOf c.L).Normal)
    (hTX : D.T ≤ Subgroup.normalizer (X : Set G)) :
    X = c.L ∨ ⁅X, c.L⁆ ≤ CFSG.Open.pCoreOf 2 c.L := by
  have hLX : c.L ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mp hXn
  by_cases h : c.L ≤ X ⊔ CFSG.Open.pCoreOf 2 c.L
  · exact Or.inl (eq_of_le_sup_pCoreOf hXL hXn c.hL.1.2.1 h)
  · exact Or.inr (commutator_le_pCoreOf_of_mem_calL c.hL.1 hXL hLX hTX h)

private theorem pCoreOf_L_le_centralizer_V {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D) :
    CFSG.Open.pCoreOf 2 c.L ≤ Subgroup.centralizer (c.V : Set G) := by
  have hsub : IsSubnormal c.L c.N := (Ctx23L.N_facts c h208 h1930).2.2.1
  have hp : CFSG.Open.pCoreOf 2 c.L ≤ CFSG.Open.pCoreOf 2 c.N :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (Ctx23L.V_le_centralizer_pCore c hv) z (hp hz)).symm

private theorem mem_centralizer_of_actTil_mem_centSub {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hAV : A ≤ V) {g : G} (hg : g ∈ stabTil ⊥ V)
    (h : actTil ⊥ V hV ⟨g, hg⟩ ∈ centSub (imgTil ⊥ V hV A)) :
    g ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haV : a ∈ V := hAV ha
  have hq : mkTil ⊥ V hV (IntMod.mk hV ⟨a, haV⟩) ∈ imgTil ⊥ V hV A :=
    (mem_imgTil ⊥ V hV A _).2 ⟨IntMod.mk hV ⟨a, haV⟩, ha, rfl⟩
  have hfix : mkTil ⊥ V hV (actStab ⊥ V hV ⟨g, hg⟩ (IntMod.mk hV ⟨a, haV⟩)) =
      mkTil ⊥ V hV (IntMod.mk hV ⟨a, haV⟩) := by
    simpa [actTil_mk] using (mem_centSub.mp h) _ hq
  have h1 : g * a * g⁻¹ * a⁻¹ = 1 := by
    have h2 := (mkTil_eq_iff ⊥ V hV
      (actStab ⊥ V hV ⟨g, hg⟩ (IntMod.mk hV ⟨a, haV⟩))
      (IntMod.mk hV ⟨a, haV⟩)).1 hfix
    rw [Subgroup.mem_bot, actStab_apply_val] at h2
    simpa [IntMod.mk, IntMod.val] using h2
  have h2 : g * a * g⁻¹ = a := mul_inv_eq_one.mp h1
  calc a * g = (g * a * g⁻¹) * g := by rw [h2]
    _ = g * a := by group

private theorem mem_imgTil_bot_iff {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (x : IntMod V hV) : mkTil ⊥ V hV x ∈ imgTil ⊥ V hV A ↔ x.val ∈ A := by
  rw [mem_imgTil]
  constructor
  · rintro ⟨y, hyA, hyx⟩
    have h1 : y.val * x.val⁻¹ ∈ (⊥ : Subgroup G) := (mkTil_eq_iff ⊥ V hV y x).1 hyx
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
    rwa [← h1]
  · intro hxA
    exact ⟨x, hxA, rfl⟩

private theorem commutator_mem_of_actTil_mem_centQuot {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) {g : G} (hg : g ∈ stabTil ⊥ V)
    (h : actTil ⊥ V hV ⟨g, hg⟩ ∈ centQuot (imgTil ⊥ V hV A)) :
    ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ A := by
  intro v hv
  have hq := (mem_centQuot.mp h) (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩))
  rw [actTil_mk] at hq
  set z : IntMod V hV := actStab ⊥ V hV ⟨g, hg⟩ (IntMod.mk hV ⟨v, hv⟩) *
    (IntMod.mk hV ⟨v, hv⟩)⁻¹ with hzdef
  have hq' : mkTil ⊥ V hV z ∈ imgTil ⊥ V hV A := by
    rw [hzdef]
    rwa [map_mul, map_inv]
  have hzA : z.val ∈ A := (mem_imgTil_bot_iff hV z).1 hq'
  have hzval : z.val = g * v * g⁻¹ * v⁻¹ := by
    change ((actStab ⊥ V hV ⟨g, hg⟩ (IntMod.mk hV ⟨v, hv⟩)) *
      (IntMod.mk hV ⟨v, hv⟩)⁻¹).val = g * v * g⁻¹ * v⁻¹
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
    rfl
  rwa [hzval] at hzA

private theorem actTil_eq_one_of_mem_pCore {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hO2 : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 L) (hzs : z ∈ stabTil ⊥ V) :
    actTil ⊥ V hV ⟨z, hzs⟩ = 1 := by
  rw [actTil_eq_one_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hc : z * v = v * z :=
    (Subgroup.mem_centralizer_iff.mp (hO2 hz) v hv).symm
  calc z * v * z⁻¹ * v⁻¹ = v * z * z⁻¹ * v⁻¹ := by rw [hc]
    _ = 1 := by group

private theorem actTil_mem_center_of_commutator_le_pCore {V L X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hLS : L ≤ stabTil ⊥ V)
    (hO2 : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hXL : X ≤ L) (hcomm : ⁅X, L⁆ ≤ CFSG.Open.pCoreOf 2 L)
    {x : G} (hxS : x ∈ stabTil ⊥ V) (hxX : x ∈ X) :
    (⟨actTil ⊥ V hV ⟨x, hxS⟩, actTil_mem_barSub ⊥ V hV (hXL hxX) hxS⟩ :
      ↥(barSub ⊥ V hV L)) ∈ Subgroup.center ↥(barSub ⊥ V hV L) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨gy, hgyL, hgy⟩ := (mem_barSub ⊥ V hV L (y : MulAut (Vtil ⊥ V hV))).1 y.2
  have hgyS : (gy : G) ∈ stabTil ⊥ V := gy.2
  have hcommG : ⁅x, (gy : G)⁆ ∈ CFSG.Open.pCoreOf 2 L :=
    Subgroup.commutator_le.mp hcomm x hxX (gy : G) hgyL
  have hcommS : ⁅x, (gy : G)⁆ ∈ stabTil ⊥ V := by
    rw [commutatorElement_def]
    exact ((stabTil ⊥ V).mul_mem ((stabTil ⊥ V).mul_mem
      ((stabTil ⊥ V).mul_mem hxS hgyS) ((stabTil ⊥ V).inv_mem hxS))
      ((stabTil ⊥ V).inv_mem hgyS))
  have hz1 : actTil ⊥ V hV ⟨⁅x, (gy : G)⁆, hcommS⟩ = 1 :=
    actTil_eq_one_of_mem_pCore hV hO2 hcommG hcommS
  have hmap : actTil ⊥ V hV ⟨⁅x, (gy : G)⁆, hcommS⟩ =
      ⁅actTil ⊥ V hV ⟨x, hxS⟩, actTil ⊥ V hV ⟨gy, hgyS⟩⁆ := by
    have h := map_commutatorElement (actTil ⊥ V hV)
      (⟨x, hxS⟩ : ↥(stabTil ⊥ V)) (⟨gy, hgyS⟩ : ↥(stabTil ⊥ V))
    have h1 : (⟨⁅x, (gy : G)⁆, hcommS⟩ : ↥(stabTil ⊥ V)) =
        ⁅(⟨x, hxS⟩ : ↥(stabTil ⊥ V)), ⟨gy, hgyS⟩⁆ := Subtype.ext rfl
    exact (congrArg (actTil ⊥ V hV) h1).trans h
  have hcomm1 : ⁅actTil ⊥ V hV ⟨x, hxS⟩, (y : MulAut (Vtil ⊥ V hV))⁆ = 1 := by
    rw [← hgy, ← hmap]
    exact hz1
  exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm

private theorem mem_preBarSub_centQuot_iff {V A L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLstab : L ≤ stabTil ⊥ V) {x : G} (hx : x ∈ L) :
    x ∈ preBarSub L ⊥ V hV (centQuot (imgTil ⊥ V hV A)) ↔
      actTil ⊥ V hV ⟨x, hLstab hx⟩ ∈ centQuot (imgTil ⊥ V hV A) := by
  rw [mem_preBarSub]
  constructor
  · rintro ⟨-, hxs, hxS⟩
    have he : (⟨x, hxs⟩ : ↥(stabTil ⊥ V)) = ⟨x, hLstab hx⟩ := Subtype.ext rfl
    rwa [he] at hxS
  · exact fun hxS => ⟨hx, hLstab hx, hxS⟩

private theorem actTil_conj_of_mem_normalizer {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLstab : L ≤ stabTil ⊥ V) {g a : G} (hgst : g ∈ stabTil ⊥ V) (ha : a ∈ L)
    (hga : g * a * g⁻¹ ∈ L) :
    actTil ⊥ V hV ⟨g * a * g⁻¹, hLstab hga⟩ =
      actTil ⊥ V hV ⟨g, hgst⟩ * actTil ⊥ V hV ⟨a, hLstab ha⟩ *
        (actTil ⊥ V hV ⟨g, hgst⟩)⁻¹ := by
  have h1 : (⟨g * a * g⁻¹, hLstab hga⟩ : ↥(stabTil ⊥ V)) =
      ⟨g, hgst⟩ * ⟨a, hLstab ha⟩ * ⟨g, hgst⟩⁻¹ := Subtype.ext rfl
  rw [h1, map_mul, map_mul, map_inv]

private theorem mul_conj_not_mem_of_not_mem {L : Subgroup G} {g a : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (ha : a ∉ L) : g * a * g⁻¹ ∉ L := by
  intro h
  apply ha
  have hginv : g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).inv_mem hg
  have h1 : g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hginv (g * a * g⁻¹)).mp h
  rwa [show g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a by group] at h1

private theorem mem_normalizer_preBarSub {V A L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLstab : L ≤ stabTil ⊥ V) {g : G} (hgst : g ∈ stabTil ⊥ V)
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgS : actTil ⊥ V hV ⟨g, hgst⟩ ∈ stabSub (imgTil ⊥ V hV A)) :
    g ∈ Subgroup.normalizer
      ((preBarSub L ⊥ V hV (centQuot (imgTil ⊥ V hV A)) : Subgroup G) : Set G) := by
  set X := preBarSub L ⊥ V hV (centQuot (imgTil ⊥ V hV A)) with hXdef
  have hXL : X ≤ L := hXdef.le.trans inf_le_left
  rw [Subgroup.mem_normalizer_iff]
  intro a
  by_cases ha : a ∈ L
  · have hga : g * a * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL a).mp ha
    rw [mem_preBarSub_centQuot_iff hV hLstab ha,
      mem_preBarSub_centQuot_iff hV hLstab hga]
    rw [actTil_conj_of_mem_normalizer hV hLstab hgst ha hga]
    constructor
    · exact fun hz => CFSG.Quasithin.conj_mem_centQuot hgS hz
    · intro hz
      have hgSinv : (actTil ⊥ V hV ⟨g, hgst⟩)⁻¹ ∈ stabSub (imgTil ⊥ V hV A) :=
        (stabSub (imgTil ⊥ V hV A)).inv_mem hgS
      have h1 := CFSG.Quasithin.conj_mem_centQuot hgSinv hz
      have h2 : (actTil ⊥ V hV ⟨g, hgst⟩)⁻¹ * (actTil ⊥ V hV ⟨g, hgst⟩ *
          actTil ⊥ V hV ⟨a, hLstab ha⟩ * (actTil ⊥ V hV ⟨g, hgst⟩)⁻¹) *
          ((actTil ⊥ V hV ⟨g, hgst⟩)⁻¹)⁻¹ = actTil ⊥ V hV ⟨a, hLstab ha⟩ := by group
      rwa [h2] at h1
  · exact ⟨fun hx => absurd (hXL hx) ha,
      fun hx => absurd (hXL hx) (mul_conj_not_mem_of_not_mem hgL ha)⟩

private theorem le_normalizer_inf_centralizer {L A : Subgroup G}
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) :
    L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
  (le_inf Subgroup.le_normalizer
    (hLA.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer A))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem le_normalizer_inf_centralizer_of {T L A : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTA : T ≤ Subgroup.normalizer (A : Set G)) :
    T ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
  (le_inf hTL (hTA.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer A))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem false_of_le_centralizer {V L A : Subgroup G} (hAV : A ≤ V) (hAne : A ≠ ⊥)
    (hfix : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hLle : L ≤ Subgroup.centralizer (A : Set G)) : False := by
  have hAleC : A ≤ Subgroup.centralizer (L : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLle hl) a ha).symm
  have hAle : A ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hAV hAleC
  rw [hfix] at hAle
  exact hAne (le_bot_iff.mp hAle)

theorem Ctx23L.centSub_le_center {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) {A : Subgroup G} (hAV : A ≤ c.V)
    (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    ∀ h : ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L),
      (h : MulAut (Vtil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c))) ∈
        centSub (imgTil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) A) →
      h ∈ Subgroup.center ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L) := by
  intro h hh
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  let H := barSub ⊥ c.V hV c.L
  let A' := imgTil ⊥ c.V hV A
  set X : Subgroup G := c.L ⊓ Subgroup.centralizer (A : Set G) with hXdef
  have hXL : X ≤ c.L := hXdef.le.trans inf_le_left
  have hLstab : c.L ≤ stabTil ⊥ c.V :=
    le_inf ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLA : c.L ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.L_le_N c).trans hAN
  have hLX : c.L ≤ Subgroup.normalizer (X : Set G) := le_normalizer_inf_centralizer hLA
  have hTA : D.T ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.T_le_N c).trans hAN
  have hTX : D.T ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_inf_centralizer_of c.hL.1.1 hTA
  have hXn : (X.subgroupOf c.L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr hLX
  obtain ⟨g, hgL, hgeq⟩ := (mem_barSub ⊥ c.V hV c.L (h : MulAut _)).1 h.2
  have hh' : actTil ⊥ c.V hV g ∈ centSub A' := by
    rw [hgeq]
    exact hh
  have hcentA : (g : G) ∈ Subgroup.centralizer (A : Set G) :=
    mem_centralizer_of_actTil_mem_centSub hV hAV g.2 hh'
  have hgX : (g : G) ∈ X := ⟨hgL, hcentA⟩
  rcases Ctx23L.commutator_le_pCoreOf_or_eq c hXL hXn hTX with hXeq | hcomm
  · exfalso
    exact false_of_le_centralizer hAV hAne (Ctx23L.fixed_L_eq_bot c)
      (hXeq ▸ hXdef.le.trans inf_le_right)
  · have hcenter := actTil_mem_center_of_commutator_le_pCore hV hLstab
        (pCoreOf_L_le_centralizer_V c h208 h1930) hXL hcomm g.2 hgX
    have he : (⟨actTil ⊥ c.V hV g, actTil_mem_barSub ⊥ c.V hV (hXL hgX) g.2⟩ : ↥H) = h :=
      Subtype.ext hgeq
    rwa [he] at hcenter

private theorem centQuot_kernel_subgroupOf_normal {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G}
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    ((preBarSub c.L ⊥ c.V (Ctx23L.isElemAbelian_V_basic c)
      (centQuot (imgTil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) A))).subgroupOf c.L).Normal := by
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  let W := Vtil ⊥ c.V hV
  let A' : Subgroup W := imgTil ⊥ c.V hV A
  let S : Subgroup (MulAut W) := centQuot A'
  have hLstab : c.L ≤ stabTil ⊥ c.V :=
    le_inf ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLA : c.L ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.L_le_N c).trans hAN
  have hLsub : barSub ⊥ c.V hV c.L ≤ stabSub A' :=
    s15_LP_barSub_le_stabSub_imgTil (V₀ := ⊥) (V := c.V) (B := c.L) (U := A) hV hLstab hLA
  have hF : (S.comap ((actTil ⊥ c.V hV).comp (Subgroup.inclusion hLstab))).Normal := by
    refine Subgroup.Normal.mk fun n hn m => ?_
    have hmS : actTil ⊥ c.V hV ⟨(m : G), hLstab m.2⟩ ∈ stabSub A' :=
      hLsub (actTil_mem_barSub ⊥ c.V hV m.2 (hLstab m.2))
    have hconj := CFSG.Quasithin.conj_mem_centQuot hmS hn
    have hFm : ((actTil ⊥ c.V hV).comp (Subgroup.inclusion hLstab)) m =
        actTil ⊥ c.V hV ⟨(m : G), hLstab m.2⟩ := rfl
    change ((actTil ⊥ c.V hV).comp (Subgroup.inclusion hLstab)) (m * n * m⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv, hFm]
    exact hconj
  have hXsub : (preBarSub c.L ⊥ c.V hV S).subgroupOf c.L =
      S.comap ((actTil ⊥ c.V hV).comp (Subgroup.inclusion hLstab)) := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_preBarSub_centQuot_iff hV hLstab y.2]
    rfl
  exact hXsub.symm ▸ hF

private theorem le_normalizer_centQuot_kernel_T {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G}
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    D.T ≤ Subgroup.normalizer
      ((preBarSub c.L ⊥ c.V (Ctx23L.isElemAbelian_V_basic c)
        (centQuot (imgTil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) A)) : Subgroup G) : Set G) := by
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  let A' := imgTil ⊥ c.V hV A
  have hTstab : D.T ≤ stabTil ⊥ c.V :=
    le_inf ((le_sup_right : D.T ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hTA : D.T ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.T_le_N c).trans hAN
  have hTsub : barSub ⊥ c.V hV D.T ≤ stabSub A' :=
    s15_LP_barSub_le_stabSub_imgTil (V₀ := ⊥) (V := c.V) (B := D.T) (U := A) hV hTstab hTA
  intro t ht
  exact mem_normalizer_preBarSub hV (le_inf ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans
      (Ctx23L.sup_le_normalizer_V D Ch c)) (by rw [Subgroup.normalizer_eq_top]; exact le_top))
    (hTstab ht) (c.hL.1.1 ht)
    (hTsub (actTil_mem_barSub ⊥ c.V hV ht (hTstab ht)))

private theorem commutator_le_of_centQuot_kernel_eq_top {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hAV : A ≤ c.V)
    (hXeq : preBarSub c.L ⊥ c.V (Ctx23L.isElemAbelian_V_basic c)
      (centQuot (imgTil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) A)) = c.L) :
    ⁅c.L, c.V⁆ ≤ A := by
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  have hLstab : c.L ≤ stabTil ⊥ c.V :=
    le_inf ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  refine Subgroup.commutator_le.mpr fun x hxL v hvV => ?_
  have hxX : x ∈ preBarSub c.L ⊥ c.V hV
      (centQuot (imgTil ⊥ c.V hV A)) := by
    rw [hXeq]
    exact hxL
  have hxS : actTil ⊥ c.V hV ⟨x, hLstab hxL⟩ ∈
      centQuot (imgTil ⊥ c.V hV A) :=
    (mem_preBarSub_centQuot_iff hV hLstab hxL).mp hxX
  simpa only [commutatorElement_def] using
    commutator_mem_of_actTil_mem_centQuot hV (hLstab hxL) hxS v hvV

theorem Ctx23L.centQuot_le_center {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) {A : Subgroup G} (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hVL : ¬ ⁅c.V, c.L⁆ ≤ A) :
    ∀ h : ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L),
      (h : MulAut (Vtil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c))) ∈
        centQuot (imgTil ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) A) →
      h ∈ Subgroup.center ↥(barSub ⊥ c.V (Ctx23L.isElemAbelian_V_basic c) c.L) := by
  intro h hh
  let hV : IsElemAbelian 2 c.V := Ctx23L.isElemAbelian_V_basic c
  let W := Vtil ⊥ c.V hV
  let A' : Subgroup W := imgTil ⊥ c.V hV A
  let S : Subgroup (MulAut W) := centQuot A'
  set X : Subgroup G := preBarSub c.L ⊥ c.V hV S with hXdef
  have hLstab : c.L ≤ stabTil ⊥ c.V :=
    le_inf ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hXL : X ≤ c.L := hXdef.le.trans inf_le_left
  have hXn : (X.subgroupOf c.L).Normal :=
    hXdef.symm ▸ centQuot_kernel_subgroupOf_normal c hAN
  have hTX : D.T ≤ Subgroup.normalizer (X : Set G) :=
    hXdef.symm ▸ le_normalizer_centQuot_kernel_T c hAN
  obtain ⟨g, hgL, hgeq⟩ := (mem_barSub ⊥ c.V hV c.L (h : MulAut W)).1 h.2
  have hh' : actTil ⊥ c.V hV g ∈ S := by
    rw [hgeq]
    exact hh
  have hgX : (g : G) ∈ X := by
    rw [hXdef, mem_preBarSub]
    exact ⟨hgL, ⟨g.2, hh'⟩⟩
  rcases Ctx23L.commutator_le_pCoreOf_or_eq c hXL hXn hTX with hXeq | hcomm
  · exfalso
    have hcommA : ⁅c.L, c.V⁆ ≤ A := commutator_le_of_centQuot_kernel_eq_top c hAV
      (hXdef.symm.trans hXeq)
    rw [Subgroup.commutator_comm c.V c.L] at hVL
    exact hVL hcommA
  · have hcenter := actTil_mem_center_of_commutator_le_pCore hV hLstab
        (pCoreOf_L_le_centralizer_V c h208 h1930) hXL hcomm g.2 hgX
    have he : (⟨actTil ⊥ c.V hV g, actTil_mem_barSub ⊥ c.V hV (hXL hgX) g.2⟩ :
        ↥(barSub ⊥ c.V hV c.L)) = h := Subtype.ext hgeq
    rwa [he] at hcenter

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
