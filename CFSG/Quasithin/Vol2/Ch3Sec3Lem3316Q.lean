module

public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open (pCoreOf GriessAllModelsStatement)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def FactSp4BlockZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsSp4Block L → Nat.card ↥(blockZ L) ≤ 4

namespace L3316

theorem lieModel_sp4 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    CFSG.Models.LieModel (StatedProj (StatedSp 2 F)) .PSp 2 2 2 := by
  have hadm : StatedLieAdmissible .PSp 2 2 2 := ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩
  refine ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, ?_, ⟨MulEquiv.refl _⟩⟩⟩
  rw [Nat.card_eq_fintype_card, hF]
  norm_num

theorem card_hopfMultiplier_sp4 (hGA : GriessAllModelsStatement) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) :
    Nat.card ↥(RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSp 2 F))) = 1 := by
  obtain ⟨-, ⟨e⟩⟩ := hGA _ .PSp 2 2 2 (lieModel_sp4 hF)
  rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr e.toEquiv]
  have hgen : Blueprint.Multiplier.genericOrders .PSp 2 2 2 = (1, 1) := by decide
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSp 2 2 2 = (1, 1) := by decide
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem commutator_statedSp (hGA : GriessAllModelsStatement) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 4) : commutator ↥(StatedSp 2 F) = ⊤ := by
  have h := (hGA _ .PSp 2 2 2 (lieModel_sp4 hF)).1
  have hs : Function.Surjective
      (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm.toMonoidHom :=
    (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm.surjective
  have h1 := map_commutator_eq (StatedProj (StatedSp 2 F))
    (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm.toMonoidHom
  rw [h, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hs] at h1
  exact h1.symm

variable {G : Type} [Group G] [Finite G]

theorem blockQ_le_blockU (hGA : GriessAllModelsStatement) {L : Subgroup G} (hL : IsSp4Block L) :
    blockQ L ≤ blockU L := by
  obtain ⟨hS, F, _, _, hF, α, hαs, hαk, -⟩ := hL
  have : CharP F 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [hF]; norm_num)
  have hperf : commutator ↥L = ⊤ := by
    apply C1GN.isShort2_eq_top_of_sup_pCore hS (commutator ↥L)
    have hmap : (commutator ↥L).map α = ⊤ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hαs]
      exact commutator_statedSp hGA hF
    have h := Subgroup.comap_map_eq α (commutator ↥L)
    rw [hmap, Subgroup.comap_top, hαk] at h
    exact h.symm
  have : Group.IsPerfect ↥L := Group.isPerfect_def.2 hperf
  set U' : Subgroup ↥L := (blockU L).subgroupOf L with hU'
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hS).trans (C1.blockQ_le L)
  have : U'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr (C1.le_normalizer_blockU L)
  have hUker : U' ≤ α.ker := by
    intro u hu
    rw [hαk]
    have h1 : (u : G) ∈ blockQ L := C1.blockU_le_blockQ hS hu
    rw [blockQ, pCoreOf] at h1
    obtain ⟨u', hu', hue⟩ := h1
    rwa [show u = u' from Subtype.ext hue.symm]
  set q : ↥L ⧸ U' →* StatedProj (StatedSp 2 F) :=
    (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).toMonoidHom.comp (QuotientGroup.lift U' α hUker)
    with hq
  have hqmk : ∀ l : ↥L, q (l : ↥L ⧸ U') = CFSG.QuasithinUnique.Lin2.Five.projEquiv F (α l) :=
    fun l => rfl
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨l, hl⟩ := hαs ((CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm y)
    exact ⟨l, by rw [hqmk, hl, MulEquiv.apply_symm_apply]⟩
  have : Group.IsPerfect (↥L ⧸ U') := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective U')
  have hker1 : ∀ l : ↥L, q (l : ↥L ⧸ U') = 1 → (l : G) ∈ blockQ L := by
    intro l hl
    rw [hqmk, map_eq_one_iff _ (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).injective] at hl
    have h1 : l ∈ α.ker := hl
    rw [hαk] at h1
    rw [blockQ, pCoreOf]
    exact ⟨l, h1, rfl⟩
  have hqker : q.ker ≤ Subgroup.center (↥L ⧸ U') := by
    intro z hz
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    have hwQ := hker1 w hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hU',
      Subgroup.mem_subgroupOf]
    have hc := C1.commutator_mem_blockU (L := L) (inv_mem hwQ) (inv_mem g'.2)
    convert hc using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hqs hqker
  have hcard : Nat.card ↥q.ker = 1 := by
    have h1 := Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedSp 2 F))) (RankThree.PerfectCover.hopfLift q hqs hqker)
    rw [hmap, card_hopfMultiplier_sp4 hGA hF] at h1
    exact Nat.dvd_one.mp h1
  have hbot : q.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  intro w hw
  have hw' := hw
  rw [blockQ, pCoreOf] at hw'
  obtain ⟨w', hw'', rfl⟩ := hw'
  have h1 : (w' : ↥L ⧸ U') ∈ q.ker := by
    show q (w' : ↥L ⧸ U') = 1
    rw [hqmk]
    have : w' ∈ α.ker := by rw [hαk]; exact hw''
    rw [show α w' = 1 from this, map_one]
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hU', Subgroup.mem_subgroupOf] at h1
  exact h1

omit [Finite G] in
theorem card_blockU {L : Subgroup G} (hL : IsSp4Block L) :
    Nat.card ↥(blockU L) = Nat.card ↥(blockZ L) * 2 ^ 8 := by
  obtain ⟨-, F, _, _, hF, -, -, -, β, hβs, hβk, -⟩ := hL
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk] at h1
  have h2 : Nat.card (Multiplicative (Fin 2 ⊕ Fin 2 → F)) = 2 ^ 8 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have h3 : Nat.card ↥((blockZ L).subgroupOf (blockU L)) = Nat.card ↥(blockZ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : blockZ L ≤ blockU L)).toEquiv
  rw [h1, h2, h3, mul_comm]

theorem card_pCoreOf_le (hGA : GriessAllModelsStatement) (hZ : FactSp4BlockZ) {L : Subgroup G}
    (hL : IsSp4Block L) : Nat.card ↥(pCoreOf 2 L) ≤ 2 ^ 10 := by
  have h1 : pCoreOf 2 L = blockU L :=
    le_antisymm (blockQ_le_blockU hGA hL) (C1.blockU_le_blockQ hL.1)
  rw [h1, card_blockU hL]
  calc Nat.card ↥(blockZ L) * 2 ^ 8 ≤ 4 * 2 ^ 8 := Nat.mul_le_mul_right _ (hZ G L hL)
    _ = 2 ^ 10 := by norm_num

end L3316

end CFSG.Quasithin.H13
