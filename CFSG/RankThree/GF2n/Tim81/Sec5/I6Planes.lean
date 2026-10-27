module

public import CFSG.RankThree.GF2n.Tim81.Sec5.I6Basic
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthSec5
public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs
public import CFSG.RankThree.GF2n.Tim81.Sec4.SecRepFixed

public section


namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.RankThree.GF2n.Tim81.Sec4 CFSG.LocalAnalysis.EvenBN.Common
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {M V : Subgroup G}

theorem mul_self_mem_of_mem_Pc (h : Hyp M V) {x : G} (hx : x ∈ Pc M V) : x * x ∈ V := by
  letI : Fact (IsPGroup 2 (Pc M V)) :=
    ⟨(inSubgroup_pCore_two M).1.to_le inf_le_left⟩
  have hfr : (⟨x, hx⟩ : Pc M V) ^ 2 ∈ frattini (Pc M V) :=
    CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x, hx⟩ : Pc M V)
  exact h.frattini_Pc_le
    (Subgroup.mem_map_of_mem (Pc M V).subtype (by simpa [pow_two] using hfr))

end Hyp

namespace Sec45Shape

variable {M V H : Subgroup G} {h₀ : G}

private theorem fixedSub_zpowers_piK {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {X : Type} [Group X] (ψ : HBar V H ≃* X) {x : G} (hxH : x ∈ H) :
    fixedSub (repW hW ψ) (Subgroup.zpowers (ψ (piK V H ⟨x, hxH⟩))) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hsub : (Subgroup.zpowers x).subgroupOf H = Subgroup.zpowers ⟨x, hxH⟩ := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext hk⟩, fun ⟨k, hk⟩ => ⟨k, congrArg Subtype.val hk⟩⟩
  have hmap : (imgK V H (Subgroup.zpowers x)).map (ψ : HBar V H →* X) =
      Subgroup.zpowers (ψ (piK V H ⟨x, hxH⟩)) := by
    rw [imgK, hsub, Subgroup.map_map]
    exact MonoidHom.map_zpowers ((ψ : HBar V H →* X).comp (piK V H)) ⟨x, hxH⟩
  rw [← hmap, fixedSub_repW hW ψ (Subgroup.zpowers_le.mpr hxH)]
  show subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) =
    subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G))
  rw [show Subgroup.centralizer (Subgroup.zpowers x : Set G) =
    Subgroup.centralizer ({x} : Set G) by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]]

theorem commutator_zpowers_eq_range {V H : Subgroup G}
    {A : Subgroup G} {x : G}
    (hZA : Tim79a.xOf V H ≤ Subgroup.centralizer (A : Set G))
    (hxA : ∀ a ∈ A, ⁅x, a⁆ ∈ Tim79a.xOf V H)
    (hBx : ⁅A, Subgroup.zpowers x⁆ ≤ Subgroup.centralizer ({x} : Set G)) :
    ⁅A, Subgroup.zpowers x⁆ =
      (commutatorElementHom x hZA hxA).range.map (Tim79a.xOf V H).subtype := by
  classical
  let φ : A →* ↥(Tim79a.xOf V H) := commutatorElementHom x hZA hxA
  have hφcoe : ∀ a : A, (((φ a : ↥(Tim79a.xOf V H)) : G)) = ⁅x, (a : G)⁆ := fun a => rfl
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hBmem : ⁅a, x⁆ ∈ ⁅A, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers x)
    have hcx : Commute x ⁅a, x⁆ := (Subgroup.mem_centralizer_singleton_iff.mp (hBx hBmem)).symm
    have hmem_inv : (φ ⟨a, ha⟩)⁻¹ ∈ φ.range :=
      φ.range.inv_mem (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
    have hcoe_inv : (((φ ⟨a, ha⟩)⁻¹ : ↥(Tim79a.xOf V H)) : G) = ⁅a, x⁆ := by
      rw [Subgroup.coe_inv, hφcoe, commutatorElement_inv]
    have hzN : ∀ m : ℕ, x ^ (Int.ofNat m) = x ^ m := fun m => zpow_natCast x m
    cases n with
    | ofNat m =>
      rw [hzN m]
      refine Subgroup.mem_map.mpr ⟨(φ ⟨a, ha⟩)⁻¹ ^ m, φ.range.pow_mem hmem_inv m, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_pow, hcoe_inv]
      exact hcx.commutatorElement_pow_right m
    | negSucc m =>
      rw [zpow_negSucc]
      refine Subgroup.mem_map.mpr ⟨((φ ⟨a, ha⟩)⁻¹ ^ (m + 1))⁻¹,
        φ.range.inv_mem (φ.range.pow_mem hmem_inv (m + 1)), ?_⟩
      have hxm : x ^ (m + 1) ∈ Subgroup.zpowers x := by
        refine Subgroup.mem_zpowers_iff.mpr ⟨((m + 1 : ℕ) : ℤ), ?_⟩
        rw [zpow_natCast]
      have hBmem2 : ⁅a, x ^ (m + 1)⁆ ∈ ⁅A, Subgroup.zpowers x⁆ :=
        Subgroup.commutator_mem_commutator ha hxm
      have hcx1 : Commute ⁅a, x ^ (m + 1)⁆ x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hBx hBmem2)
      have hcx' : Commute (x ^ (m + 1)) ⁅a, x ^ (m + 1)⁆ := (hcx1.pow_right (m + 1)).symm
      have hpow := hcx.commutatorElement_pow_right (m + 1)
      have hshift : ⁅a, x ^ (m + 1)⁆⁻¹ * x ^ (m + 1) =
          x ^ (m + 1) * ⁅a, x ^ (m + 1)⁆⁻¹ := hcx'.inv_right.eq.symm
      simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_pow, hcoe_inv]
      rw [commutatorElement_inv_right, ← commutatorElement_inv a (x ^ (m + 1)), mul_assoc, hshift,
        ← mul_assoc, inv_mul_cancel, one_mul, ← hpow]
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hz
    show (((φ a : ↥(Tim79a.xOf V H)) : G)) ∈ ⁅A, Subgroup.zpowers x⁆
    rw [hφcoe, ← commutatorElement_inv]
    exact (⁅A, Subgroup.zpowers x⁆).inv_mem
      (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_zpowers x))

private theorem inf_eq_bot_and_card_of_card_sup {V H : Subgroup G}
    {hwAb : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    {B : Subgroup G} (hVW : V ≤ Tim79a.xOf V H) (hBW : B ≤ Tim79a.xOf V H)
    (hcardSup : Nat.card ↥(V ⊔ B) = Nat.card V ^ 2)
    (hcardB : Nat.card ↥B ≤ Nat.card V) :
    V ⊓ B = ⊥ ∧ Nat.card ↥B = Nat.card V := by
  have hcomm : ∀ x ∈ V, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hwAb.1.is_comm.comm ⟨x, hVW hx⟩ ⟨y, hBW hy⟩)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V B hcomm).1
  have hq : 0 < Nat.card V := Nat.card_pos
  have h1 : Nat.card V ^ 2 * Nat.card ↥(V ⊓ B) = Nat.card V * Nat.card ↥B := by
    rw [← hcardSup]
    exact hprod
  have h2 : Nat.card V * Nat.card ↥(V ⊓ B) = Nat.card ↥B := by
    exact Nat.eq_of_mul_eq_mul_left hq (by rw [← h1]; ring)
  have h3 : Nat.card ↥(V ⊓ B) ≤ 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ hq
    rw [mul_one, h2]
    exact hcardB
  have hone : Nat.card ↥(V ⊓ B) = 1 := by
    have hpos : 0 < Nat.card ↥(V ⊓ B) := Nat.card_pos
    omega
  refine ⟨Subgroup.card_eq_one.mp hone, ?_⟩
  rw [← h2, hone, mul_one]

theorem xOf_inf_centralizer_le_and_card (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x : G} (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) ≤ Pc M V ∧
      Nat.card ↥(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card V ^ 2 := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  have hxH : x ∈ H := hS.Pc_le hx
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))
  let xbar : SL(2, F) := ψ (piK V H ⟨x, hxH⟩)
  have hA2 : ∀ a ∈ A, a * a = 1 :=
    (h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ).1
  have hAcard : Nat.card A = 2 ^ (2 * l) := by
    rw [show A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) from rfl,
      Subgroup.card_map_of_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective,
      h.card_imgK_eq_two_pow hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl]
  have hxbar_mem : xbar ∈ A := by
    refine Subgroup.mem_map.mpr ⟨piK V H ⟨x, hxH⟩, ?_, rfl⟩
    exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hxbar1 : xbar ≠ 1 := fun h1 =>
    hxK ((piK_eq_one_iff ⟨x, hxH⟩).mp (ψ.injective (by simpa [xbar] using h1)))
  obtain ⟨hM2fix, hM2le⟩ :=
    Sec2.IsOrthModule.fixedSub_zpowers_eq_commSub horth A hA2 hAcard hxbar_mem hxbar1
  have hfix : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    fixedSub_zpowers_piK (hW := hW) ψ hxH
  have hcardfix :=
    Sec2.IsOrthModule.card_fixedSub_zpowers hl horth A hA2 hAcard hxbar_mem hxbar1
  refine ⟨?_, ?_⟩
  · intro a ha
    have hcommA : commSub (repW (hW := hW) ψ) ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) =
        subW hW (Pc M V ⊓ Tim79a.xOf V H) := by
      rw [commSub_repW hW ψ hS.Pc_le, ← hS.inf_Pc_xOf_eq_commutator h]
    have hle_sub : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) ≤ subW hW (Pc M V) := by
      refine hM2le.trans ?_
      rw [show A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) from rfl, hcommA]
      exact subW_mono inf_le_left
    have hmem : ofW hW ⟨a, ha.1⟩ ∈ fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) := by
      rw [hfix]
      exact (mem_subW_iff hW).mpr ha
    simpa using (mem_subW_iff hW).mp (hle_sub hmem)
  · have h1 : Nat.card ↥(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) =
        Nat.card ↥(fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar)) := by
      rw [hfix, natCard_subW hW inf_le_left]
    rw [h1, hcardfix, hw.card_V, ← pow_mul, mul_comm]

private theorem commutator_conj_zpowers_le_xOf {V H : Subgroup G} {y x : G}
    (hy : y ∈ H) (hxH : x ∈ H) :
    ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤ Tim79a.xOf V H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haW : a ∈ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hy ha
  have hbH : b ∈ H := (Subgroup.zpowers_le.mpr hxH) hb
  have hbab : b * a * b⁻¹ ∈ Tim79a.xOf V H :=
    (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hbH) a).mp haW
  have hcomm : ⁅a, b⁆ = a * (b * a * b⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hcomm]
  exact (Tim79a.xOf V H).mul_mem haW ((Tim79a.xOf V H).inv_mem hbab)

private theorem plane_model_eq {M V H : Subgroup G} {h₀ : G} (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {F : Type} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] (l : ℕ) (hl : Fintype.card F = 2 ^ (2 * l))
    (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ))
    {y x : G} (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hx : x ∈ Pc M V)
    (hxK : x ∉ kOf V H) :
    fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers (ψ (piK V H ⟨x, hS.Pc_le hx⟩))) ⊓
        commSub (repW (hW := hW) ψ)
          ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) =
      fixedSub (repW (hW := hW) ψ)
          ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) ⊔
        (fixedSub (repW (hW := hW) ψ)
          ((imgK V H (conjSubgroup y (Pc M V))).map (ψ : HBar V H →* SL(2, F)))).map
          (repW (hW := hW) ψ (ψ (piK V H ⟨x, hS.Pc_le hx⟩)) - 1) := by
  classical
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))
  let A' : Subgroup SL(2, F) :=
    (imgK V H (conjSubgroup y (Pc M V))).map (ψ : HBar V H →* SL(2, F))
  let xbar : SL(2, F) := ψ (piK V H ⟨x, hS.Pc_le hx⟩)
  have hA2 : ∀ a ∈ A, a * a = 1 :=
    (h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ).1
  have hAcard : Nat.card A = 2 ^ (2 * l) := by
    rw [show A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) from rfl,
      Subgroup.card_map_of_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective,
      h.card_imgK_eq_two_pow hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl]
  have hxbar_mem : xbar ∈ A :=
    Subgroup.mem_map.mpr ⟨piK V H ⟨x, hS.Pc_le hx⟩,
      ⟨⟨x, hS.Pc_le hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  have hxbar1 : xbar ≠ 1 := fun h1 =>
    hxK ((piK_eq_one_iff ⟨x, hS.Pc_le hx⟩).mp (ψ.injective (by simpa [xbar] using h1)))
  have hA'eq : A' = conjSubgroup (ψ (piK V H ⟨y, hy⟩)) A := by
    rw [show A' = (imgK V H (conjSubgroup y (Pc M V))).map
        (ψ : HBar V H →* SL(2, F)) from rfl,
      imgK_conjSubgroup hy hS.Pc_le,
      map_conjSubgroup (ψ : HBar V H →* SL(2, F)) (piK V H ⟨y, hy⟩) (imgK V H (Pc M V))]
    rfl
  have hA'2 : ∀ a ∈ A', a * a = 1 := by
    intro a ha
    rw [hA'eq] at ha
    have h1 : (ψ (piK V H ⟨y, hy⟩))⁻¹ * a * (ψ (piK V H ⟨y, hy⟩)) ∈ A := mem_conjSubgroup.mp ha
    have h2 := hA2 _ h1
    calc a * a = ψ (piK V H ⟨y, hy⟩) *
          ((ψ (piK V H ⟨y, hy⟩))⁻¹ * a * (ψ (piK V H ⟨y, hy⟩)) *
            ((ψ (piK V H ⟨y, hy⟩))⁻¹ * a * (ψ (piK V H ⟨y, hy⟩)))) *
          (ψ (piK V H ⟨y, hy⟩))⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hA'card : Nat.card A' = 2 ^ (2 * l) := by rw [hA'eq, card_conjSubgroup, hAcard]
  have hne : A ≠ A' := by
    intro heq
    refine hS.imgK_conj_ne h hy hyV ?_
    exact Subgroup.map_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective (heq.symm)
  obtain ⟨w, hwA', hword⟩ :=
    Sec2.exists_mem_orderOf_mul_eq_three hA2 (hAcard.trans hl.symm) hA'2
      (hA'card.trans hl.symm) hne hxbar_mem hxbar1
  exact Sec2.IsOrthModule.fixedSub_zpowers_inf_commSub_eq_sup_map hl horth A A'
    hA2 hAcard hA'2 hA'card hne hxbar_mem hxbar1

private theorem plane_left_eq {M V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    {ψ : HBar V H ≃* SL(2, F)} {xbar : SL(2, F)} {x : G}
    (hfix : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)))
    (hcommA : commSub (repW (hW := hW) ψ)
        ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) =
      subW hW (Pc M V ⊓ Tim79a.xOf V H))
    (hle : Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) ≤ Pc M V) :
    fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) ⊓
        commSub (repW (hW := hW) ψ)
          ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) := by
  rw [hfix, hcommA, ← subW_inf]
  congr 1
  exact inf_eq_left.mpr (le_inf hle inf_le_left)

private theorem plane_right_eq {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    {ψ : HBar V H ≃* SL(2, F)} {A A' : Subgroup SL(2, F)} {xbar : SL(2, F)} {y x : G}
    (hfixA : fixedSub (repW (hW := hW) ψ) A = subW hW V)
    (hfixA' : fixedSub (repW (hW := hW) ψ) A' = subW hW (conjSubgroup y V))
    (hH3 : subW hW ⁅conjSubgroup y V, Subgroup.zpowers x⁆ =
      (subW hW (conjSubgroup y V)).map (repW (hW := hW) ψ xbar - 1))
    (hBW : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤ Tim79a.xOf V H) :
    fixedSub (repW (hW := hW) ψ) A ⊔
        (fixedSub (repW (hW := hW) ψ) A').map (repW (hW := hW) ψ xbar - 1) =
      subW hW (V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆) := by
  rw [hfixA, hfixA', ← hH3, subW_sup (le_xOf_self V H) hBW]

private theorem plane_fixators {M V H : Subgroup G} {h₀ : G} (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {F : Type} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] {ψ : HBar V H ≃* SL(2, F)}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {y : G} (hy : y ∈ H) :
    fixedSub (repW (hW := hW) ψ)
        ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) = subW hW V ∧
      fixedSub (repW (hW := hW) ψ)
        ((imgK V H (conjSubgroup y (Pc M V))).map (ψ : HBar V H →* SL(2, F))) =
        subW hW (conjSubgroup y V) := by
  constructor
  · rw [fixedSub_repW hW ψ hS.Pc_le, h.xOf_inf_centralizer_Pc_eq_V]
  · rw [fixedSub_repW hW ψ (conjSubgroup_le_of_le_of_mem hS.Pc_le hy),
      h.xOf_inf_centralizer_conj_Pc hy]

private theorem plane_eq_sup_commutator {M V : Subgroup G} (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {y x : G} (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V)
    (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) =
      V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ := by
  classical
  have hxH : x ∈ H := hS.Pc_le hx
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))
  let A' : Subgroup SL(2, F) :=
    (imgK V H (conjSubgroup y (Pc M V))).map (ψ : HBar V H →* SL(2, F))
  let xbar : SL(2, F) := ψ (piK V H ⟨x, hxH⟩)
  have hmodel := plane_model_eq (h := h) (hS := hS) (l := l) (hl := hl) (ψ := ψ)
    (hW := hW) (horth := horth) hy hyV hx hxK
  change fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) ⊓
      commSub (repW (hW := hW) ψ) A =
      fixedSub (repW (hW := hW) ψ) A ⊔
        (fixedSub (repW (hW := hW) ψ) A').map (repW (hW := hW) ψ xbar - 1) at hmodel
  have hfix : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    fixedSub_zpowers_piK (hW := hW) ψ hxH
  have hcommA : commSub (repW (hW := hW) ψ)
      ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) =
      subW hW (Pc M V ⊓ Tim79a.xOf V H) := by
    rw [commSub_repW hW ψ hS.Pc_le, ← hS.inf_Pc_xOf_eq_commutator h]
  obtain ⟨hfixA, hfixA'⟩ :=
    plane_fixators (h := h) (hS := hS) (hW := hW) (ψ := ψ) hy
  change fixedSub (repW (hW := hW) ψ) A = subW hW V at hfixA
  change fixedSub (repW (hW := hW) ψ) A' = subW hW (conjSubgroup y V) at hfixA'
  have hx2V : x * x ∈ V := h.mul_self_mem_of_mem_Pc hx
  have hx2K : x * x ∈ kOf V H :=
    h.xOf_le_kOf hS.Pc_le hS.le_pCore (le_xOf_self V H hx2V)
  have hH3 : subW hW ⁅conjSubgroup y V, Subgroup.zpowers x⁆ =
      (subW hW (conjSubgroup y V)).map (repW (hW := hW) ψ xbar - 1) :=
    subW_commutator_zpowers (hW := hW) ψ (conjSubgroup_le_xOf_of_mem hy) hxH hx2K
  have hL := plane_left_eq hfix hcommA (xOf_inf_centralizer_le_and_card h hS hx hxK).1
  have hR := plane_right_eq hfixA hfixA' hH3 (commutator_conj_zpowers_le_xOf hy hxH)
  have heq : subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) =
      subW hW (V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆) := by
    rw [← hL, ← hR]
    exact hmodel
  exact (subW_inj (hW := hW) (E := Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G))
    (F := V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆) inf_le_left
    (sup_le (le_xOf_self V H) (commutator_conj_zpowers_le_xOf hy hxH))).mp heq

private theorem card_commutator_conj_le_card_V (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {y x : G} (hy : y ∈ H)
    (hx : x ∈ Pc M V)
    (hEq1 : Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) =
      V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆) :
    Nat.card ↥⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤ Nat.card V := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have hxH : x ∈ H := hS.Pc_le hx
  have hZA : Tim79a.xOf V H ≤ Subgroup.centralizer (conjSubgroup y V : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (congrArg Subtype.val (hW.1.is_comm.comm ⟨z, hz⟩
        ⟨a, conjSubgroup_le_xOf_of_mem hy ha⟩)).symm
  have hxA : ∀ a ∈ conjSubgroup y V, ⁅x, a⁆ ∈ Tim79a.xOf V H := by
    intro a ha
    have haW : a ∈ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hy ha
    have hxax : x * a * x⁻¹ ∈ Tim79a.xOf V H :=
      (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hxH) a).mp haW
    have hcomm : ⁅x, a⁆ = x * a * x⁻¹ * a⁻¹ := rfl
    rw [hcomm]
    exact (Tim79a.xOf V H).mul_mem hxax ((Tim79a.xOf V H).inv_mem haW)
  have hBx : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤
      Subgroup.centralizer ({x} : Set G) := by
    have h1 : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤
        V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ := le_sup_right
    rw [← hEq1] at h1
    exact h1.trans inf_le_right
  have hrange := commutator_zpowers_eq_range hZA hxA hBx
  have hAcard' : Nat.card ↥(conjSubgroup y V) = Nat.card V := card_conjSubgroup y V
  have hrangecard : Nat.card ↥(commutatorElementHom x hZA hxA).range =
      Nat.card ↥⁅conjSubgroup y V, Subgroup.zpowers x⁆ := by
    rw [hrange]
    exact (Subgroup.card_map_of_injective (f := (Tim79a.xOf V H).subtype)
      (fun p q h => Subtype.ext h)).symm
  have hkr := Subgroup.card_ker_mul_card_range (commutatorElementHom x hZA hxA)
  rw [hrangecard, hAcard'] at hkr
  exact Nat.le_of_dvd (Nat.card_pos) ⟨Nat.card ↥(commutatorElementHom x hZA hxA).ker,
    by rw [mul_comm]; exact hkr.symm⟩

theorem sup_commutator_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y x : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ =
        Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) ∧
      V ⊓ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ = ⊥ ∧
      Nat.card ↥⁅conjSubgroup y V, Subgroup.zpowers x⁆ = Nat.card V := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  have hEq1 : Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) =
      V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ :=
    plane_eq_sup_commutator h hS hy hyV hx hxK
  have hcardPlane : Nat.card ↥(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card V ^ 2 := (xOf_inf_centralizer_le_and_card h hS hx hxK).2
  have hBW : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤ Tim79a.xOf V H :=
    commutator_conj_zpowers_le_xOf hy (hS.Pc_le hx)
  have hcardB_le : Nat.card ↥⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤ Nat.card V :=
    card_commutator_conj_le_card_V h hS hy hx hEq1
  have hcardSup : Nat.card ↥(V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆) = Nat.card V ^ 2 := by
    rw [← hEq1]
    exact hcardPlane
  obtain ⟨hinf, hcard⟩ := inf_eq_bot_and_card_of_card_sup (hwAb := hW) (le_xOf_self V H) hBW
    hcardSup hcardB_le
  exact ⟨hEq1.symm, hinf, hcard⟩

theorem mem_kOf_of_commutator_mem (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y v p : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hv : v ∈ conjSubgroup y V) (hv1 : v ≠ 1)
    (hp : p ∈ Pc M V) (hpv : ⁅p, v⁆ ∈ V) : p ∈ kOf V H := by
  classical
  by_contra hpK
  obtain ⟨hsup, hinf, hcard⟩ := sup_commutator_eq h hS hy hyV hp hpK
  have hW := hS.isElemAbelian h
  have hBmem : ⁅v, p⁆ ∈ ⁅conjSubgroup y V, Subgroup.zpowers p⁆ :=
    Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers p)
  have h1 : ⁅v, p⁆ = 1 := by
    have hmem : ⁅v, p⁆ ∈ V ⊓ ⁅conjSubgroup y V, Subgroup.zpowers p⁆ :=
      Subgroup.mem_inf.mpr ⟨by rw [← commutatorElement_inv p v]; exact V.inv_mem hpv, hBmem⟩
    rwa [hinf] at hmem
  have hpv1 : ⁅p, v⁆ = 1 := by
    rw [← commutatorElement_inv v p, h1]
    simp
  have hAW : conjSubgroup y V ≤ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hy
  have hZA : Tim79a.xOf V H ≤ Subgroup.centralizer (conjSubgroup y V : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (congrArg Subtype.val (hW.1.is_comm.comm ⟨z, hz⟩ ⟨a, hAW ha⟩)).symm
  have hxN : p ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Tim79a.H_le_normalizer_xOf V H (hS.Pc_le hp)
  have hxA : ∀ a ∈ conjSubgroup y V, ⁅p, a⁆ ∈ Tim79a.xOf V H := by
    intro a ha
    exact (Tim79a.xOf V H).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN a).mp (hAW ha))
      ((Tim79a.xOf V H).inv_mem (hAW ha))
  have hBx : ⁅conjSubgroup y V, Subgroup.zpowers p⁆ ≤ Subgroup.centralizer ({p} : Set G) := by
    have h1 : ⁅conjSubgroup y V, Subgroup.zpowers p⁆ ≤
        V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers p⁆ := le_sup_right
    rw [hsup] at h1
    exact h1.trans inf_le_right
  have hrange := commutator_zpowers_eq_range hZA hxA hBx
  have hAcard : Nat.card ↥(conjSubgroup y V) = Nat.card V := card_conjSubgroup y V
  have hrangecard : Nat.card ↥(commutatorElementHom p hZA hxA).range =
      Nat.card ↥⁅conjSubgroup y V, Subgroup.zpowers p⁆ := by
    rw [hrange]
    exact (Subgroup.card_map_of_injective (f := (Tim79a.xOf V H).subtype)
      (fun a b hab => Subtype.ext hab)).symm
  have hker1 : Nat.card ↥(commutatorElementHom p hZA hxA).ker = 1 := by
    have hkr := Subgroup.card_ker_mul_card_range (commutatorElementHom p hZA hxA)
    rw [hrangecard, hcard, hAcard] at hkr
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) (by rw [hkr, one_mul])
  have hkerbot : (commutatorElementHom p hZA hxA).ker = ⊥ := Subgroup.card_eq_one.mp hker1
  have hvker : (⟨v, hv⟩ : ↥(conjSubgroup y V)) ∈ (commutatorElementHom p hZA hxA).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (by
      show (((commutatorElementHom p hZA hxA) ⟨v, hv⟩ : ↥(Tim79a.xOf V H)) : G) = 1
      exact hpv1)
  have hv1' : (⟨v, hv⟩ : ↥(conjSubgroup y V)) = 1 := by
    have := hvker
    rw [hkerbot] at this
    exact Subgroup.mem_bot.mp this
  exact hv1 (congrArg Subtype.val hv1')

private theorem centralizer_iff_mem_fixator {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    {ψ : HBar V H ≃* SL(2, F)}
    {A : Subgroup SL(2, F)} {xbar : SL(2, F)} {C : Subgroup SL(2, F)} {x b : G}
    (hfixA : fixedSub (repW (hW := hW) ψ) A = subW hW V)
    (hfixx : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)))
    (hCfix : ∀ w ∈ fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar),
      w ∉ fixedSub (repW (hW := hW) ψ) A → ∀ g ∈ A, (repW (hW := hW) ψ g w = w ↔ g ∈ C))
    (hbW : b ∈ Tim79a.xOf V H)
    (hbC : b ∈ Subgroup.centralizer ({x} : Set G)) (hbV : b ∉ V) {p : G} (hpH : p ∈ H)
    (hψA : ψ (piK V H ⟨p, hpH⟩) ∈ A) :
    p * b = b * p ↔ ψ (piK V H ⟨p, hpH⟩) ∈ C := by
  have hb_mem : ofW hW ⟨b, hbW⟩ ∈
      fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) := by
    rw [hfixx]
    exact (mem_subW_iff hW).mpr (Subgroup.mem_inf.mpr ⟨hbW, hbC⟩)
  have hb_not : ofW hW ⟨b, hbW⟩ ∉ fixedSub (repW (hW := hW) ψ) A := by
    rw [hfixA]
    intro hmem
    exact hbV ((mem_subW_iff hW).mp hmem)
  have hconj_iff : repW (hW := hW) ψ (ψ (piK V H ⟨p, hpH⟩)) (ofW hW ⟨b, hbW⟩) =
      ofW hW ⟨b, hbW⟩ ↔ p * b = b * p := by
    rw [repW_apply_piK_ofMul]
    constructor
    · intro h
      have h1 := congrArg Subtype.val (ofW_injective hW h)
      rw [conjH_apply_coe] at h1
      calc p * b = (p * b * p⁻¹) * p := by group
        _ = b * p := by rw [h1]
    · intro h
      refine congrArg (ofW hW) (Subtype.ext ?_)
      rw [conjH_apply_coe]
      calc p * b * p⁻¹ = (b * p) * p⁻¹ := by rw [h]
        _ = b := by group
  exact hconj_iff.symm.trans (hCfix _ hb_mem hb_not _ hψA)

private theorem card_Pc_inf_centralizer_range {M V H : Subgroup G} {h₀ : G}
    (hS : Sec45Shape M V H h₀) {x a : G}
    (ha : a ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) (haV : a ∉ V)
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    {ψ : HBar V H ≃* SL(2, F)} {A C : Subgroup SL(2, F)} {xbar : SL(2, F)}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (hA : A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)))
    (hCA : C ≤ A)
    (hCfix : ∀ w ∈ fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar),
      w ∉ fixedSub (repW (hW := hW) ψ) A → ∀ g ∈ A, (repW (hW := hW) ψ g w = w ↔ g ∈ C))
    (hfixA : fixedSub (repW (hW := hW) ψ) A = subW hW V)
    (hfixx : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)))
    (hψA : ∀ (p : G) (hp : p ∈ Pc M V), ψ (piK V H ⟨p, hS.Pc_le hp⟩) ∈ A)
    (φ : ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) →* SL(2, F))
    (hφcoe : ∀ p : ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)),
      φ p = ψ (piK V H ⟨(p : G), hS.Pc_le (Subgroup.mem_inf.mp p.2).1⟩)) :
    φ.range = C := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨p, rfl⟩
    have hpP : (p : G) ∈ Pc M V := (Subgroup.mem_inf.mp p.2).1
    have hpa : (p : G) ∈ Subgroup.centralizer ({a} : Set G) := (Subgroup.mem_inf.mp p.2).2
    have hpab : (p : G) * a = a * (p : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hpa
    have h := (centralizer_iff_mem_fixator hfixA hfixx hCfix ha.1 ha.2 haV
      (hS.Pc_le hpP) (hψA _ hpP)).mp hpab
    rw [hφcoe]
    exact h
  · intro c hc
    have hcA : c ∈ (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) := by
      rw [← hA]
      exact hCA hc
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hcA
    obtain ⟨p, hpP, hpy⟩ := (mem_imgK_iff).mp hy
    have hψ : ψ (piK V H p) = c := by
      rw [hpy]
      exact hyc
    have hψA' : ψ (piK V H p) ∈ A := by
      rw [hψ, hA]
      exact Subgroup.mem_map.mpr ⟨y, hy, hyc⟩
    have hψC : ψ (piK V H p) ∈ C := by
      rw [hψ]
      exact hc
    have hpab : (p : G) * a = a * (p : G) :=
      (centralizer_iff_mem_fixator hfixA hfixx hCfix ha.1 ha.2 haV p.2 hψA').mpr hψC
    refine ⟨⟨(p : G), Subgroup.mem_inf.mpr ⟨hpP, ?_⟩⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hpab
    · rw [hφcoe]
      exact hψ

private theorem card_Pc_inf_centralizer_ker {M V H : Subgroup G} {h₀ : G}
    (hS : Sec45Shape M V H h₀) {a : G} {F : Type} [Field F] [Fintype F] [CharP F 2]
    {ψ : HBar V H ≃* SL(2, F)}
    (φ : ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) →* SL(2, F))
    (hφcoe : ∀ p : ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)),
      φ p = ψ (piK V H ⟨(p : G), hS.Pc_le (Subgroup.mem_inf.mp p.2).1⟩)) :
    φ.ker =
      (Pc M V ⊓ kOf V H).subgroupOf (Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) := by
  ext p
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφcoe]
  constructor
  · intro hp
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp p.2).1, ?_⟩
    have hπ : piK V H ⟨(p : G), hS.Pc_le (Subgroup.mem_inf.mp p.2).1⟩ = 1 :=
      ψ.injective (by rw [hp, map_one])
    exact (piK_eq_one_iff _).mp hπ
  · intro hp
    obtain ⟨-, hpK⟩ := Subgroup.mem_inf.mp hp
    rw [(piK_eq_one_iff _).mpr hpK, map_one]

private theorem Pc_inf_kOf_le_centralizer {M V : Subgroup G} {a : G}
    (ha : a ∈ Tim79a.xOf V H) :
    Pc M V ⊓ kOf V H ≤ Pc M V ⊓ Subgroup.centralizer ({a} : Set G) := by
  refine le_inf inf_le_left fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr ?_
  exact (Subgroup.mem_centralizer_iff.mp
    ((mem_kOf_iff.mp (Subgroup.mem_inf.mp hk).2).2) a ha).symm

private theorem card_Pc_inf_centralizer_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x a : G} (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (ha : a ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) (haV : a ∉ V) :
    Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card V * Nat.card ↥(Pc M V ⊓ kOf V H) := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))
  let xbar : SL(2, F) := ψ (piK V H ⟨x, hS.Pc_le hx⟩)
  have hA2 : ∀ b ∈ A, b * b = 1 :=
    (h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ).1
  have hAcard : Nat.card A = 2 ^ (2 * l) := by
    rw [show A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) from rfl,
      Subgroup.card_map_of_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective,
      h.card_imgK_eq_two_pow hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl]
  have hxbar_mem : xbar ∈ A := by
    refine Subgroup.mem_map.mpr ⟨piK V H ⟨x, hS.Pc_le hx⟩, ?_, rfl⟩
    exact ⟨⟨x, hS.Pc_le hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hxbar1 : xbar ≠ 1 := fun h1 =>
    hxK ((piK_eq_one_iff ⟨x, hS.Pc_le hx⟩).mp (ψ.injective (by simpa [xbar] using h1)))
  obtain ⟨C, hCA, hCcard, hCfix⟩ :=
    Sec2.IsOrthModule.exists_fixator_fixedSub_zpowers horth A hA2 hAcard hxbar_mem hxbar1
  have hfixA : fixedSub (repW (hW := hW) ψ) A = subW hW V := by
    rw [show A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) from rfl,
      fixedSub_repW hW ψ hS.Pc_le, h.xOf_inf_centralizer_Pc_eq_V]
  have hfixx : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    fixedSub_zpowers_piK (hW := hW) ψ (hS.Pc_le hx)
  have hψA : ∀ (p : G) (hp : p ∈ Pc M V), ψ (piK V H ⟨p, hS.Pc_le hp⟩) ∈ A := by
    intro p hp
    refine Subgroup.mem_map.mpr ⟨piK V H ⟨p, hS.Pc_le hp⟩, ?_, rfl⟩
    exact ⟨⟨p, hS.Pc_le hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
  let φ : ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) →* SL(2, F) :=
    (ψ : HBar V H →* SL(2, F)).comp
      ((piK V H).comp (Subgroup.inclusion (inf_le_left.trans hS.Pc_le)))
  have hφcoe : ∀ p : ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)),
      φ p = ψ (piK V H ⟨(p : G), hS.Pc_le (Subgroup.mem_inf.mp p.2).1⟩) := fun p => rfl
  have hrange : φ.range = C :=
    card_Pc_inf_centralizer_range hS ha haV rfl hCA hCfix hfixA hfixx hψA φ hφcoe
  have hker : φ.ker =
      (Pc M V ⊓ kOf V H).subgroupOf (Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) :=
    card_Pc_inf_centralizer_ker hS φ hφcoe
  have hkercard : Nat.card ↥φ.ker = Nat.card ↥(Pc M V ⊓ kOf V H) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Pc_inf_kOf_le_centralizer (M := M) (V := V) (H := H) (a := a) ha.1)).toEquiv
  have hkr := Subgroup.card_ker_mul_card_range φ
  rw [hkercard, hrange, hCcard.trans hw.card_V.symm] at hkr
  rw [← hkr, mul_comm]

private theorem Pc_inf_centralizer_le_of_mem (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x a : G} (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (ha : a ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) (haV : a ∉ V) :
    Pc M V ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Pc M V ⊓ Subgroup.centralizer
        (↑(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))
  let xbar : SL(2, F) := ψ (piK V H ⟨x, hS.Pc_le hx⟩)
  have hA2 : ∀ b ∈ A, b * b = 1 :=
    (h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ).1
  have hAcard : Nat.card A = 2 ^ (2 * l) := by
    rw [show A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) from rfl,
      Subgroup.card_map_of_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective,
      h.card_imgK_eq_two_pow hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl]
  have hxbar_mem : xbar ∈ A := by
    refine Subgroup.mem_map.mpr ⟨piK V H ⟨x, hS.Pc_le hx⟩, ?_, rfl⟩
    exact ⟨⟨x, hS.Pc_le hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hxbar1 : xbar ≠ 1 := fun h1 =>
    hxK ((piK_eq_one_iff ⟨x, hS.Pc_le hx⟩).mp (ψ.injective (by simpa [xbar] using h1)))
  obtain ⟨C, -, -, hCfix⟩ :=
    Sec2.IsOrthModule.exists_fixator_fixedSub_zpowers horth A hA2 hAcard hxbar_mem hxbar1
  have hfixA : fixedSub (repW (hW := hW) ψ) A = subW hW V := by
    rw [show A = (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) from rfl,
      fixedSub_repW hW ψ hS.Pc_le, h.xOf_inf_centralizer_Pc_eq_V]
  have hfixx : fixedSub (repW (hW := hW) ψ) (Subgroup.zpowers xbar) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    fixedSub_zpowers_piK (hW := hW) ψ (hS.Pc_le hx)
  have hψA : ∀ (p : G) (hp : p ∈ Pc M V), ψ (piK V H ⟨p, hS.Pc_le hp⟩) ∈ A := by
    intro p hp
    refine Subgroup.mem_map.mpr ⟨piK V H ⟨p, hS.Pc_le hp⟩, ?_, rfl⟩
    exact ⟨⟨p, hS.Pc_le hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
  intro p hp
  obtain ⟨hpP, hpa⟩ := Subgroup.mem_inf.mp hp
  have hpab : p * a = a * p := Subgroup.mem_centralizer_singleton_iff.mp hpa
  have hψC : ψ (piK V H ⟨p, hS.Pc_le hpP⟩) ∈ C :=
    (centralizer_iff_mem_fixator hfixA hfixx hCfix ha.1 ha.2 haV (hS.Pc_le hpP)
      (hψA p hpP)).mp hpab
  refine Subgroup.mem_inf.mpr ⟨hpP, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  by_cases heV : e ∈ V
  · have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
      rw [h.toHyp.centralizer_Pc]
    exact (Subgroup.mem_centralizer_iff.mp (hVP heV) p hpP).symm
  · have hpe : p * e = e * p :=
      (centralizer_iff_mem_fixator hfixA hfixx hCfix he.1 he.2 heV (hS.Pc_le hpP)
        (hψA p hpP)).mpr hψC
    exact hpe.symm

theorem Pc_inf_centralizer_eq_of_mem (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x a : G} (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (ha : a ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) (haV : a ∉ V) :
    Pc M V ⊓ Subgroup.centralizer ({a} : Set G) =
      Pc M V ⊓ Subgroup.centralizer
        (↑(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) := by
  refine le_antisymm (Pc_inf_centralizer_le_of_mem h hS hx hxK ha haV) ?_
  refine inf_le_inf le_rfl (Subgroup.centralizer_le ?_)
  intro e he
  rw [Set.mem_singleton_iff] at he
  exact he ▸ ha

theorem card_Pc_inf_centralizer_plane (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x : G} (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    Nat.card ↥(Pc M V ⊓ Subgroup.centralizer
        (↑(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G)) * Nat.card V =
      Nat.card ↥(Pc M V) := by
  classical
  have hcardE : Nat.card ↥(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card V ^ 2 := (xOf_inf_centralizer_le_and_card h hS hx hxK).2
  have hVE : V ≤ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf (le_xOf_self V H) ?_
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by rw [h.toHyp.centralizer_Pc]
    exact (Subgroup.mem_centralizer_iff.mp (hVP hv) x hx).symm
  have hne : Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) ≠ V := by
    intro heq
    have h1 : Nat.card V ^ 2 = Nat.card V := by rw [← hcardE, heq]
    have hpos : 0 < Nat.card V := Nat.card_pos
    have h2 : Nat.card V = 1 := by nlinarith
    have h4 := h.four_le_card
    omega
  have hex : ∃ a : G, a ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) ∧ a ∉ V := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hcon hVE)
  obtain ⟨a, ha, haV⟩ := hex
  rw [← Pc_inf_centralizer_eq_of_mem h hS hx hxK ha haV,
    card_Pc_inf_centralizer_eq h hS hx hxK ha haV]
  have hb4 := hS.card_Pc_inf_kOf h
  rw [show Nat.card V * Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card V =
    Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card V ^ 2 by ring]
  exact hb4

private theorem commutator_Pc_conj_le (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hy : y ∈ H) : ⁅Pc M V, conjSubgroup y V⁆ ≤ Pc M V ⊓ Tim79a.xOf V H := by
  rw [hS.inf_Pc_xOf_eq_commutator h]
  exact (Subgroup.commutator_mono le_rfl (conjSubgroup_le_xOf_of_mem hy)).trans
    (Subgroup.commutator_comm_le (Pc M V) (Tim79a.xOf V H))

theorem range_commutatorElementHom_eq_top {M V H : Subgroup G} {x v : G}
    (hZV : V ≤ Subgroup.centralizer (Pc M V : Set G))
    (hwVV : ∀ p ∈ Pc M V, ⁅⁅x, v⁆, p⁆ ∈ V)
    (hd1 : Pc M V ⊓ Subgroup.centralizer ({⁅x, v⁆} : Set G) =
      Pc M V ⊓ Subgroup.centralizer
        (↑(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G))
    (hd2 : Nat.card ↥(Pc M V ⊓ Subgroup.centralizer
        (↑(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G)) *
        Nat.card V = Nat.card ↥(Pc M V)) :
    (commutatorElementHom ⁅x, v⁆ hZV hwVV).range = ⊤ := by
  let φ : ↥(Pc M V) →* ↥V := commutatorElementHom ⁅x, v⁆ hZV hwVV
  have hker : φ.ker = (Pc M V ⊓ Subgroup.centralizer ({⁅x, v⁆} : Set G)).subgroupOf
      (Pc M V) :=
    ker_commutatorElementHom ⁅x, v⁆ hZV hwVV
  have hkercard : Nat.card ↥φ.ker =
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({⁅x, v⁆} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hkerE : Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({⁅x, v⁆} : Set G)) =
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer
        (↑(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G)) := by
    rw [hd1]
  have hrangecard : Nat.card ↥φ.range = Nat.card V := by
    have hkr := Subgroup.card_ker_mul_card_range φ
    rw [hkercard, hkerE] at hkr
    have hq : 0 < Nat.card ↥(Pc M V ⊓ Subgroup.centralizer
        (↑(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hq (hkr.trans hd2.symm)
  exact Subgroup.eq_top_of_card_eq φ.range (by rw [hrangecard])

private theorem le_commutator_Pc_conj (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    V ≤ ⁅Pc M V, conjSubgroup y V⁆ := by
  classical
  have hN_le := commutator_Pc_conj_le h hS hy
  have hPN : Pc M V ≤ Subgroup.normalizer ((⁅Pc M V, conjSubgroup y V⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left (Pc M V) (conjSubgroup y V)
  have hNP : ⁅⁅Pc M V, conjSubgroup y V⁆, Pc M V⁆ ≤ ⁅Pc M V, conjSubgroup y V⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hPN
  obtain ⟨x, hxP, hxK⟩ := h.exists_mem_Pc_not_mem_kOf hS.Pc_le hS.hH hS.not_le
  have hAy_card : Nat.card ↥(conjSubgroup y V) = Nat.card V := card_conjSubgroup y V
  have hAy_ne : conjSubgroup y V ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(conjSubgroup y V) = 1 := by rw [hbot]; simp
    rw [hAy_card] at h1
    have h4 := h.four_le_card
    omega
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAy_ne
  have hv1' : (v : G) ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  have hwN : ⁅x, (v : G)⁆ ∈ ⁅Pc M V, conjSubgroup y V⁆ :=
    Subgroup.commutator_mem_commutator hxP v.2
  have hwP : ⁅x, (v : G)⁆ ∈ Pc M V := (Subgroup.mem_inf.mp (hN_le hwN)).1
  have hwV : ⁅x, (v : G)⁆ ∉ V := by
    intro hmem
    exact hxK (mem_kOf_of_commutator_mem h hS hy hyV v.2 hv1' hxP hmem)
  have hwAx : ⁅x, (v : G)⁆ ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [← (sup_commutator_eq h hS hy hyV hxP hxK).1]
    exact Subgroup.mem_sup_right (commutatorElement_inv (↑v) x ▸
      ((⁅conjSubgroup y V, Subgroup.zpowers x⁆).inv_mem_iff.mpr
        (Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_zpowers x))))
  have hd1 := Pc_inf_centralizer_eq_of_mem h hS hxP hxK hwAx hwV
  have hd2 := card_Pc_inf_centralizer_plane h hS hxP hxK
  have hZV : V ≤ Subgroup.centralizer (Pc M V : Set G) := by rw [h.toHyp.centralizer_Pc]
  have hwVV : ∀ p ∈ Pc M V, ⁅⁅x, (v : G)⁆, p⁆ ∈ V := by
    intro p hp
    have hmem := Subgroup.commutator_mem_commutator hwP hp
    rw [hS.commutator_Pc h] at hmem
    exact hmem
  have hrange_top : (commutatorElementHom ⁅x, (v : G)⁆ hZV hwVV).range = ⊤ :=
    range_commutatorElementHom_eq_top hZV hwVV hd1 hd2
  let φ : ↥(Pc M V) →* ↥V := commutatorElementHom ⁅x, (v : G)⁆ hZV hwVV
  have hφcoe : ∀ p : ↥(Pc M V), ((φ p : ↥V) : G) = ⁅⁅x, (v : G)⁆, (p : G)⁆ := fun p => rfl
  intro v0 hv0
  have hmem : (⟨v0, hv0⟩ : ↥V) ∈ φ.range := by
    rw [hrange_top]
    exact Subgroup.mem_top _
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hmem
  have hcoe : ((φ p : ↥V) : G) = v0 := congrArg Subtype.val hp
  rw [← hcoe, hφcoe]
  exact hNP (Subgroup.commutator_mem_commutator hwN p.2)

theorem commutator_Pc_conj_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    ⁅Pc M V, conjSubgroup y V⁆ = Pc M V ⊓ Tim79a.xOf V H := by
  classical
  refine le_antisymm (commutator_Pc_conj_le h hS hy) ?_
  have hVN : V ≤ ⁅Pc M V, conjSubgroup y V⁆ := le_commutator_Pc_conj h hS hy hyV
  have hPN : Pc M V ≤ Subgroup.normalizer ((⁅Pc M V, conjSubgroup y V⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left (Pc M V) (conjSubgroup y V)
  have hNP : ⁅⁅Pc M V, conjSubgroup y V⁆, Pc M V⁆ ≤ ⁅Pc M V, conjSubgroup y V⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hPN
  intro u hu
  obtain ⟨x, hxP, hxK, huC⟩ := hS.exists_centralizing_not_mem_kOf h hu
  have huAx : u ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hu.2, huC⟩
  have hx'N : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤ ⁅Pc M V, conjSubgroup y V⁆ :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxP)).trans
      (Subgroup.commutator_comm_le (conjSubgroup y V) (Pc M V))
  exact sup_le hVN hx'N ((sup_commutator_eq h hS hy hyV hxP hxK).1 ▸ huAx)

theorem Pc_inf_centralizer_commutator (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, conjSubgroup y V⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V H := by
  rw [commutator_Pc_conj_eq h hS hy hyV, hS.Pc_inf_centralizer_inf_xOf h]

private theorem conj_pow_mem_kOf {V H : Subgroup G} {b : G}
    (hbK : ∀ x ∈ H, ⁅b, x⁆ ∈ kOf V H) {k : ℕ} (hb : b ^ 2 ^ k = 1) :
    (∀ n : ℕ, ∀ x ∈ kOf V H, b ^ n * x * (b ^ n)⁻¹ ∈ kOf V H) ∧
      ∀ x ∈ kOf V H, b⁻¹ * x * b ∈ kOf V H := by
  have hconj : ∀ n : ℕ, ∀ x ∈ kOf V H, b ^ n * x * (b ^ n)⁻¹ ∈ kOf V H := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have h1 : b ^ n * x * (b ^ n)⁻¹ ∈ kOf V H := ih x hx
      have h2 : b * (b ^ n * x * (b ^ n)⁻¹) * b⁻¹ ∈ kOf V H := by
        rw [show b * (b ^ n * x * (b ^ n)⁻¹) * b⁻¹ =
          ⁅b, (b ^ n * x * (b ^ n)⁻¹)⁆ * (b ^ n * x * (b ^ n)⁻¹) from by
            rw [commutatorElement_def]; group]
        exact (kOf V H).mul_mem (hbK _ (kOf_le V H h1)) h1
      rwa [← show b * (b ^ n * x * (b ^ n)⁻¹) * b⁻¹ =
        b ^ (n + 1) * x * (b ^ (n + 1))⁻¹ from by group]
  have hbinv : b⁻¹ = b ^ (2 ^ k - 1) := by
    have h2 : 0 < 2 ^ k := pow_pos (by norm_num : (0:ℕ) < 2) k
    have h3 : b ^ (2 ^ k - 1) * b = 1 := by
      rw [← pow_succ, Nat.sub_one_add_one (Nat.ne_of_gt h2), hb]
    calc b⁻¹ = (b ^ (2 ^ k - 1) * b) * b⁻¹ := by rw [h3, one_mul]
      _ = b ^ (2 ^ k - 1) := by group
  refine ⟨hconj, ?_⟩
  intro x hx
  have h := hconj (2 ^ k - 1) x hx
  rwa [← hbinv, inv_inv] at h

private theorem normalizes_xOf_of_commutator_mem_kOf {V H : Subgroup G} {b : G}
    (hbK : ∀ x ∈ H, ⁅b, x⁆ ∈ kOf V H) {k : ℕ} (hb : b ^ 2 ^ k = 1)
    (hcenter : kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) = Tim79a.xOf V H) :
    b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) := by
  obtain ⟨hconj, hbK'⟩ := conj_pow_mem_kOf hbK hb
  have hWK : Tim79a.xOf V H ≤ kOf V H := by
    rw [← hcenter]
    exact inf_le_left
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hwW
    have hwC : w ∈ Subgroup.centralizer (kOf V H : Set G) := by
      have hmem : w ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := by
        rw [hcenter]
        exact hwW
      exact hmem.2
    have hbwK : b * w * b⁻¹ ∈ kOf V H := by
      rw [show b * w * b⁻¹ = b ^ 1 * w * (b ^ 1)⁻¹ from by group]
      exact hconj 1 w (hWK hwW)
    rw [← hcenter]
    refine Subgroup.mem_inf.mpr ⟨hbwK, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k1 hk1
    have h1 : b⁻¹ * k1 * b ∈ kOf V H := hbK' k1 hk1
    have h2 : (b⁻¹ * k1 * b) * w = w * (b⁻¹ * k1 * b) :=
      Subgroup.mem_centralizer_iff.mp hwC _ h1
    calc k1 * (b * w * b⁻¹) = b * ((b⁻¹ * k1 * b) * w) * b⁻¹ := by group
      _ = b * (w * (b⁻¹ * k1 * b)) * b⁻¹ := by rw [h2]
      _ = (b * w * b⁻¹) * k1 := by group
  · intro hwW
    have hwW' : b * w * b⁻¹ ∈ kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) := by
      rw [hcenter]
      exact hwW
    have hwK : w ∈ kOf V H := by
      have h1 : b⁻¹ * (b * w * b⁻¹) * b ∈ kOf V H := hbK' _ hwW'.1
      rwa [show b⁻¹ * (b * w * b⁻¹) * b = w from by group] at h1
    rw [← hcenter]
    refine Subgroup.mem_inf.mpr ⟨hwK, ?_⟩
    have hwC : b * w * b⁻¹ ∈ Subgroup.centralizer (kOf V H : Set G) := hwW'.2
    rw [Subgroup.mem_centralizer_iff]
    intro k1 hk1
    have hb1 : b * k1 * b⁻¹ ∈ kOf V H := by
      rw [show b * k1 * b⁻¹ = b ^ 1 * k1 * (b ^ 1)⁻¹ from by group]
      exact hconj 1 k1 hk1
    have h2 : (b * k1 * b⁻¹) * (b * w * b⁻¹) = (b * w * b⁻¹) * (b * k1 * b⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hwC _ hb1
    calc k1 * w = b⁻¹ * ((b * k1 * b⁻¹) * (b * w * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * w * b⁻¹) * (b * k1 * b⁻¹)) * b := by rw [h2]
      _ = w * k1 := by group

private noncomputable def conjAddEnd {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {b : G} (hbW : b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G)) :
    Additive (IntMod (Tim79a.xOf V H) hW) →+ Additive (IntMod (Tim79a.xOf V H) hW) :=
  { toFun := fun v =>
      ofW hW ((Tim79a.xOf V H).normalizerMonoidHom ⟨b, hbW⟩ (toW hW v))
    map_zero' := by simp
    map_add' := by
      intro u v
      simp only [toW_add, map_mul, ofW_mul] }

private theorem conjAddEnd_commute_repW {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    {ψ : HBar V H ≃* SL(2, F)} {b : G}
    (hbK : ∀ x ∈ H, ⁅b, x⁆ ∈ kOf V H)
    (hbW : b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G)) :
    ∀ (g : SL(2, F)) (v : Additive (IntMod (Tim79a.xOf V H) hW)),
      conjAddEnd hbW (repW (hW := hW) ψ g v) =
        repW (hW := hW) ψ g (conjAddEnd hbW v) := by
  intro g v
  obtain ⟨y, rfl⟩ := ψ.surjective g
  obtain ⟨z, rfl⟩ := piK_surjective V H y
  simp only [conjAddEnd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, repW_apply_piK, toW_ofW]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, conjH_apply_coe]
  have hbz : ⁅b, (z : G)⁆ ∈ kOf V H := hbK z z.2
  have hbXW : b * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * b⁻¹ ∈ Tim79a.xOf V H := by
    rw [← Subgroup.normalizerMonoidHom_apply_apply_coe (Tim79a.xOf V H) ⟨b, hbW⟩
      (toW hW v)]
    exact ((Tim79a.xOf V H).normalizerMonoidHom ⟨b, hbW⟩ (toW hW v)).2
  have hXW : (z : G) * (b * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * b⁻¹) * (z : G)⁻¹ ∈
      Tim79a.xOf V H :=
    (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H z.2)
      (b * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * b⁻¹)).mp hbXW
  have hcent : (⁅b, (z : G)⁆ : G) *
      ((z : G) * (b * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * b⁻¹) * (z : G)⁻¹) =
      ((z : G) * (b * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * b⁻¹) * (z : G)⁻¹) *
        ⁅b, (z : G)⁆ :=
    (Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp hbz).2) _ hXW).symm
  calc b * ((z : G) * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * (z : G)⁻¹) * b⁻¹
      = (⁅b, (z : G)⁆ : G) *
          ((z : G) * (b * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * b⁻¹) * (z : G)⁻¹) *
          ⁅b, (z : G)⁆⁻¹ := by
        rw [commutatorElement_def]; group
    _ = (z : G) * (b * ((toW hW v : ↥(Tim79a.xOf V H)) : G) * b⁻¹) * (z : G)⁻¹ := by
        rw [hcent]; group

private theorem conjAddEnd_iterate_eq {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {b : G} (hbW : b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G))
    {k : ℕ} (hb : b ^ 2 ^ k = 1) :
    ∀ v, (conjAddEnd hbW)^[2 ^ k] v = v := by
  have hcbpow : ∀ n : ℕ, ∀ w : ↥(Tim79a.xOf V H),
      (((Tim79a.xOf V H).normalizerMonoidHom ⟨b, hbW⟩)^[n] w : G) =
        b ^ n * w * (b ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply, ih,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      group
  have hcbId : ∀ w : ↥(Tim79a.xOf V H),
      ((Tim79a.xOf V H).normalizerMonoidHom ⟨b, hbW⟩)^[2 ^ k] w = w := by
    intro w
    have h := hcbpow (2 ^ k) w
    rw [hb] at h
    simp only [one_mul, inv_one, mul_one] at h
    exact Subtype.ext h
  have hpow : ∀ n : ℕ, ∀ v, (conjAddEnd hbW)^[n] v =
      ofW hW (((Tim79a.xOf V H).normalizerMonoidHom ⟨b, hbW⟩)^[n] (toW hW v)) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply, ih]
      simp only [conjAddEnd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toW_ofW]
      rw [Function.iterate_succ_apply]
  intro v
  rw [hpow, hcbId, ofW_toW]

theorem mem_centralizer_xOf_of_commutator_mem_kOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {b : G} (hbK : ∀ x ∈ H, ⁅b, x⁆ ∈ kOf V H) {k : ℕ} (hb : b ^ 2 ^ k = 1) :
    b ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  have hbW : b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    normalizes_xOf_of_commutator_mem_kOf hbK hb hw.center_K
  let φ : Additive (IntMod (Tim79a.xOf V H) hW) →+
      Additive (IntMod (Tim79a.xOf V H) hW) := conjAddEnd (hW := hW) hbW
  have hcomm : ∀ (g : SL(2, F)) (v : Additive (IntMod (Tim79a.xOf V H) hW)),
      φ (repW (hW := hW) ψ g v) = repW (hW := hW) ψ g (φ v) :=
    conjAddEnd_commute_repW (hW := hW) hbK hbW
  have hiter : ∀ v, φ^[2 ^ k] v = v := conjAddEnd_iterate_eq (hW := hW) hbW hb
  have hfix := Sec2.IsOrthModule.eq_of_commute_of_iterate horth φ hcomm hiter
  intro w hw'
  have h1 : (((Tim79a.xOf V H).normalizerMonoidHom ⟨b, hbW⟩) ⟨w, hw'⟩ : G) = w := by
    have h2 : φ (ofW hW ⟨w, hw'⟩) = ofW hW ⟨w, hw'⟩ := hfix _
    change ofW hW ((Tim79a.xOf V H).normalizerMonoidHom ⟨b, hbW⟩
      (toW hW (ofW hW ⟨w, hw'⟩))) = ofW hW ⟨w, hw'⟩ at h2
    rw [toW_ofW] at h2
    have h3 := ofW_injective hW h2
    exact congrArg Subtype.val h3
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  calc w * b = (b * w * b⁻¹) * b := by rw [h1]
    _ = b * w := by group

end Sec45Shape

private theorem cap_step {M V : Subgroup G} {E₁ E₂ C₁ C₂ : Subgroup G}
    (hE₁P : E₁ ≤ Pc M V) (hE₂P : E₂ ≤ Pc M V) (hC₁P : C₁ ≤ Pc M V)
    (hC₁E₁ : C₁ ≤ Subgroup.centralizer (E₁ : Set G))
    (hC₂E₂ : C₂ ≤ Subgroup.centralizer (E₂ : Set G))
    (hE₂norm : Pc M V ≤ Subgroup.normalizer (E₂ : Set G))
    (hcardE₂ : Nat.card ↥E₂ = Nat.card V ^ 3)
    (hcardC₁ : Nat.card ↥C₁ * Nat.card V ^ 2 = Nat.card ↥(Pc M V))
    (hVE₁ : V ≤ E₁) (hVC₂ : V ≤ C₂)
    (hZP : Pc M V ⊓ Subgroup.centralizer (Pc M V : Set G) = V)
    (hcap : E₂ ⊓ C₁ = V) : E₁ ⊓ C₂ = V := by
  classical
  have hq : 0 < Nat.card V := Nat.card_pos
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := C₁) (B := E₂) (hC₁P.trans hE₂norm)
  rw [inf_comm, hcap, hcardE₂] at hprod
  have hsup : C₁ ⊔ E₂ = Pc M V := by
    have h1 : Nat.card ↥(C₁ ⊔ E₂) * Nat.card V = Nat.card ↥(Pc M V) * Nat.card V := by
      rw [hprod]
      calc Nat.card ↥C₁ * Nat.card V ^ 3 =
          Nat.card ↥C₁ * Nat.card V ^ 2 * Nat.card V := by ring
        _ = Nat.card ↥(Pc M V) * Nat.card V := by rw [hcardC₁]
    refine Subgroup.eq_of_le_of_card_ge (sup_le hC₁P hE₂P) (le_of_eq ?_)
    exact (Nat.eq_of_mul_eq_mul_right hq h1).symm
  refine le_antisymm ?_ (le_inf hVE₁ hVC₂)
  intro x hx
  obtain ⟨hxE₁, hxC₂⟩ := Subgroup.mem_inf.mp hx
  have hxE₂ : x ∈ Subgroup.centralizer (E₂ : Set G) := hC₂E₂ hxC₂
  have hxC₁ : x ∈ Subgroup.centralizer (C₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (hC₁E₁ hc) x hxE₁).symm
  have hxCP : x ∈ Subgroup.centralizer (Pc M V : Set G) := by
    have hpow : Subgroup.zpowers x ≤ Subgroup.centralizer (Pc M V : Set G) := by
      rw [← hsup, Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr hxC₁
      · rw [Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr hxE₂
    exact hpow (Subgroup.mem_zpowers x)
  exact hZP ▸ Subgroup.mem_inf.mpr ⟨hE₁P hxE₁, hxCP⟩

theorem Sec5Hyp.commutator_facts_of_mem_sigmaSet {M V : Subgroup G} (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    ∃ g : G, U = conjSubgroup g V ∧
      ⁅Pc M V, U⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g) ∧
      Nat.card ↥⁅Pc M V, U⁆ = Nat.card V ^ 3 ∧
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer
        ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) * Nat.card V ^ 2 =
        Nat.card ↥(Pc M V) ∧
      V ≤ ⁅Pc M V, U⁆ ∧
      V ≤ Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) ∧
      Pc M V ⊓ Subgroup.centralizer (Pc M V : Set G) = V := by
  classical
  have h := hS.toRootHyp
  obtain ⟨g, hUeq, hHg⟩ := hU
  have hUg : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hSg := hS.shape hUg
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSg.Pc_le hSg.hH
  have hyV : conjSubgroup y V ≠ V := fun hc =>
    ne_of_mem_sigmaSet h ⟨g, hUeq, hHg⟩ (hUeq.trans (hVy.trans hc))
  have hEg : ⁅Pc M V, U⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
    rw [hUeq, hVy]
    exact Sec45Shape.commutator_Pc_conj_eq h hSg hyH hyV
  have hCg : Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V (hOf M V g) := by
    rw [hEg]
    exact hSg.Pc_inf_centralizer_inf_xOf h
  have hcardE : Nat.card ↥⁅Pc M V, U⁆ = Nat.card V ^ 3 := by
    rw [hEg]
    exact hSg.card_inf_Pc_xOf h
  have hcardC : Nat.card ↥(Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) * Nat.card V ^ 2 =
      Nat.card ↥(Pc M V) := by
    rw [hCg]
    exact hSg.card_Pc_inf_kOf h
  have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [h.toHyp.centralizer_Pc]
  have hVE : V ≤ ⁅Pc M V, U⁆ := by
    rw [hEg]
    exact le_inf h.toHyp.le_Pc (le_xOf_self V (hOf M V g))
  have hVC : V ≤ Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G) := by
    refine le_inf h.toHyp.le_Pc ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heP : e ∈ Pc M V := by
      rw [hEg] at he
      exact he.1
    exact Subgroup.mem_centralizer_iff.mp (hVP hv) e heP
  have hZP : Pc M V ⊓ Subgroup.centralizer (Pc M V : Set G) = V := by
    have h2 := (hSg.pCore_eq_and h).2.1
    rw [(hSg.pCore_eq_and h).1] at h2
    rw [show Pc M V ⊓ Subgroup.centralizer (Pc M V : Set G) =
      (Subgroup.center ↥(Pc M V)).map (Pc M V).subtype from
      CFSG.GroupTheory.inf_centralizer_eq_map_center _]
    exact h2
  exact ⟨g, hUeq, hEg, hcardE, hcardC, hVE, hVC, hZP⟩

theorem Sec5Hyp.cap_symm {M V : Subgroup G} (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V)
    (hU' : U' ∈ sigmaSet M V) :
    ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V ↔
      ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
        ((⁅Pc M V, U'⁆ : Subgroup G) : Set G)) = V := by
  classical
  have h := hS.toRootHyp
  obtain ⟨g, hUeq, hE, hcardE, hcardC, hVE, hVC, hZP⟩ := hS.commutator_facts_of_mem_sigmaSet hU
  obtain ⟨g', hU'eq, hE', hcardE', hcardC', hVE', hVC', -⟩ := hS.commutator_facts_of_mem_sigmaSet hU'
  constructor
  · intro hcap
    exact cap_step (E₁ := ⁅Pc M V, U⁆) (E₂ := ⁅Pc M V, U'⁆)
      (C₁ := Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G))
      (C₂ := Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G))
      (by rw [hE]; exact inf_le_left) (by rw [hE']; exact inf_le_left)
      inf_le_left inf_le_right inf_le_right
      (Subgroup.normalizer_commutator_ge_left (Pc M V) U') hcardE'
      hcardC hVE hVC' hZP hcap
  · intro hcap
    exact cap_step (E₁ := ⁅Pc M V, U'⁆) (E₂ := ⁅Pc M V, U⁆)
      (C₁ := Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G))
      (C₂ := Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G))
      (by rw [hE']; exact inf_le_left) (by rw [hE]; exact inf_le_left)
      inf_le_left inf_le_right inf_le_right
      (Subgroup.normalizer_commutator_ge_left (Pc M V) U) hcardE
      hcardC' hVE' hVC hZP hcap

end CFSG.RankThree.GF2n.Tim81

end

