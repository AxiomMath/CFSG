module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueHatA6
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GH74.GLS.Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.QuasithinUnique CFSG.Quasithin

variable {X : Type} [Group X] [Finite X]

section Generic

variable {G : Type} [Group G]

private theorem sbtypes_constWeight_eq_evenWeightOnes (m : ℕ) :
    constWeight m = evenWeightOnes m := by
  ext x
  rw [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hx
    have hx' : ∀ i j, (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j := hx
    by_cases hm : Nonempty (Fin m)
    · obtain ⟨i₀⟩ := hm
      refine ⟨((x : Fin m → ZMod 2) i₀).val, funext fun i => ?_⟩
      simp [allOnes, hx' i i₀]
    · refine ⟨0, funext fun i => ?_⟩
      exact absurd ⟨i⟩ hm
  · rintro ⟨k, hk⟩
    have hi : ∀ i, (x : Fin m → ZMod 2) i = (k : ZMod 2) := fun i => by
      rw [← hk]
      simp [allOnes]
    intro i j
    exact (hi i).trans (hi j).symm

private noncomputable def sbtypes_heartEquiv (m : ℕ) : AltHeart m ≃+ altHeart m :=
  QuotientAddGroup.quotientAddEquivOfEq (sbtypes_constWeight_eq_evenWeightOnes m)

private theorem sbtypes_heartEquiv_mk (m : ℕ) (x : ↥(evenWeight m)) :
    sbtypes_heartEquiv m (QuotientAddGroup.mk x) = QuotientAddGroup.mk x :=
  QuotientAddGroup.quotientAddEquivOfEq_mk _ x

private theorem sbtypes_isAltNaturalType_of_isAltBlockTypeWith {L : Subgroup G} {m : ℕ}
    {α : ↥L →* alternatingGroup (Fin m)} (h : IsAltBlockTypeWith L m α) :
    IsAltNaturalType L m := by
  obtain ⟨hαs, hαk, β, hβs, hβk, hR⟩ := h
  have hinj : Function.Injective
      (AddMonoidHom.toMultiplicative (sbtypes_heartEquiv m).toAddMonoidHom) :=
    fun a b hab => (sbtypes_heartEquiv m).injective (congrArg Multiplicative.toAdd hab)
  refine ⟨α, hαs, hαk,
    (AddMonoidHom.toMultiplicative (sbtypes_heartEquiv m).toAddMonoidHom).comp β,
    (Function.Surjective.comp (sbtypes_heartEquiv m).surjective hβs : _), ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective β _ hinj, hβk]
  · intro ℓ u v huv x hx
    have hx0 : sbtypes_heartEquiv m (Multiplicative.toAdd (β u)) = QuotientAddGroup.mk x := hx
    have hx' : (QuotientAddGroup.mk x : AltHeart m) = Multiplicative.toAdd (β u) :=
      (sbtypes_heartEquiv m).injective ((sbtypes_heartEquiv_mk m x).trans hx0.symm)
    have h2 := hR ℓ u v huv x hx'
    change sbtypes_heartEquiv m (Multiplicative.toAdd (β v)) = _
    rw [← h2, sbtypes_heartEquiv_mk]
    rfl

private theorem sbtypes_isAltNaturalType_of_isAltType {L : Subgroup G} {m : ℕ} (hm : Odd m)
    (h : IsAltType L m) : IsAltNaturalType L m := by
  obtain ⟨α, hα⟩ := (isAltType_iff_exists_isAltBlockTypeWith hm).1 h
  exact sbtypes_isAltNaturalType_of_isAltBlockTypeWith hα

private theorem sbtypes_isElementaryAbelian_tildeU {L : Subgroup G} (hL : IsShort2 L) :
    IsElementaryAbelian 2 (tildeU L) := by
  have hcomm : ∀ a b : tildeU L, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext ((CFSG.QuasithinUnique.C1.elemAb2_blockU hL).1 a a.2 b b.2)
  refine { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    have h2 : a ^ 2 = 1 := Subtype.ext ((CFSG.QuasithinUnique.C1.elemAb2_blockU hL).2 a a.2)
    rw [h2]
    rfl

private theorem sbtypes_pRank_tildeU [Finite G] {L : Subgroup G} (hL : IsShort2 L) {k : ℕ}
    (hk : ((blockZ L).subgroupOf (blockU L)).index = 2 ^ k) :
    CFSG.pRank 2 (tildeU L) = k := by
  haveI := sbtypes_isElementaryAbelian_tildeU hL
  exact CFSG.pRank_eq_of_card_eq_pow Nat.one_lt_two hk

private theorem sbtypes_isScriptLBlock_of_isChiBlock2 [Finite G] {X L : Subgroup G}
    (h : IsChiBlock2 X L) : IsScriptLBlock X L := by
  obtain ⟨hb, hn | ⟨m, hm, ha⟩⟩ := h
  · obtain ⟨n, -, hn⟩ := hn
    exact ⟨IsBlock2.isBlock hb, Or.inl ⟨n, hn⟩⟩
  · exact ⟨IsBlock2.isBlock hb,
      Or.inr (Or.inl ⟨m, sbtypes_isAltNaturalType_of_isAltType hm ha⟩)⟩

private theorem sbtypes_isScriptLBlock_of_isAltBlockType [Finite G] {X L : Subgroup G} {m : ℕ}
    (hb : IsBlock2 X L) (h : IsAltBlockType L m) : IsScriptLBlock X L := by
  obtain ⟨-, α, hα⟩ := h
  exact ⟨IsBlock2.isBlock hb,
    Or.inr (Or.inl ⟨m, sbtypes_isAltNaturalType_of_isAltBlockTypeWith hα⟩)⟩

private theorem sbtypes_isScriptLBlock_of_isExcA7Block [Finite G] {X L : Subgroup G}
    (hb : IsBlock2 X L) (h : IsExcA7Block L) : IsScriptLBlock X L := by
  obtain ⟨hsh, hα, hidx⟩ := h
  exact ⟨IsBlock2.isBlock hb,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hα, sbtypes_pRank_tildeU hsh hidx⟩))))⟩

private theorem sbtypes_exists_tripleCover {L : Subgroup G}
    (h : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (alternatingGroup (Fin 6))) :
    ∃ α : ↥L →* alternatingGroup (Fin 6), Function.Surjective α ∧ CFSG.pCore 2 ↥L ≤ α.ker ∧
      Nat.card α.ker = 3 * Nat.card (CFSG.pCore 2 ↥L) := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  set α : ↥L →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with hα
  have hαs : Function.Surjective α :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hN : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)), Nat.card_congr e.toEquiv, h360, hc]
  have hL1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  have hL2 := Subgroup.card_ker_mul_card_of_surjective hαs
  refine ⟨α, hαs, fun x hx => ?_, ?_⟩
  · rw [MonoidHom.mem_ker, hα]
    simp [(QuotientGroup.eq_one_iff x).mpr hx]
  · rw [h360] at hL2
    rw [hN] at hL1
    omega

private theorem sbtypes_blockZ_eq_bot_of_isHatA6Block [Finite G] {L : Subgroup G}
    (h : IsHatA6Block L) : blockZ L = ⊥ := by
  obtain ⟨hsh, hHat, hcard, hcent⟩ := h
  have hU : CFSG.Open.IsElemAbelian 2 (blockU L) :=
    CFSG.QuasithinUnique.C5.isElemAbelian_two_iff.2 (CFSG.QuasithinUnique.C1.elemAb2_blockU hsh)
  have hLN : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    CFSG.QuasithinUnique.C1.le_normalizer_blockU L
  have hker : (convHom hU L hLN).ker = CFSG.pCore 2 ↥L := by
    rw [ker_convHom, hcent]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  let E : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(autI hU L) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (convHom hU L hLN)).trans
        (MulEquiv.subgroupCongr (range_convHom hU L hLN)))
  obtain ⟨hq, hc, ⟨e⟩⟩ := IsHat.of_mulEquiv E hHat
  obtain ⟨hfix, -⟩ := CFSG.Quasithin.H13.hatA6SixIrreducible (IntMod (blockU L) hU)
    IntMod.sq_eq_one hcard (autI hU L) hq.1 hc ⟨e⟩
  refine eq_bot_iff.mpr fun u hu => ?_
  have hmem : IntMod.mk hU ⟨u, hu.1⟩ ∈ fixV (autI hU L) := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hφ
    apply IntMod.val_injective
    rw [convI_apply_val]
    show (g : G) * u * (g : G)⁻¹ = u
    rw [Subgroup.mem_centralizer_iff.mp hu.2 g hg, mul_inv_cancel_right]
  rw [hfix, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg IntMod.val hmem

private theorem sbtypes_isScriptLBlock_of_isHatA6Block [Finite G] {X L : Subgroup G}
    (hb : IsBlock2 X L) (h : IsHatA6Block L) : IsScriptLBlock X L := by
  have hZ := sbtypes_blockZ_eq_bot_of_isHatA6Block h
  refine ⟨IsBlock2.isBlock hb,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sbtypes_exists_tripleCover h.2.1, ?_⟩))))⟩
  refine sbtypes_pRank_tildeU h.1 (k := 6) ?_
  rw [hZ, Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact h.2.2.1

end Generic

theorem isScriptLBlock_of_isChiBlock2 (h : CFSG.Quasithin.IsChiBlock2 ⊤ (oResidual 2 X)) :
    IsScriptLBlock ⊤ (oResidual 2 X) :=
  sbtypes_isScriptLBlock_of_isChiBlock2 h

theorem isScriptLBlock_of_isExcA7Block (hb : CFSG.QuasithinUnique.IsBlock2 ⊤ (oResidual 2 X))
    (h : CFSG.Quasithin.IsExcA7Block (oResidual 2 X)) : IsScriptLBlock ⊤ (oResidual 2 X) :=
  sbtypes_isScriptLBlock_of_isExcA7Block hb h

theorem isScriptLBlock_of_isAltBlockType6 (hb : CFSG.QuasithinUnique.IsBlock2 ⊤ (oResidual 2 X))
    (h : CFSG.Quasithin.IsAltBlockType (oResidual 2 X) 6) : IsScriptLBlock ⊤ (oResidual 2 X) :=
  sbtypes_isScriptLBlock_of_isAltBlockType hb h

theorem isScriptLBlock_of_isHatA6Block (hb : CFSG.QuasithinUnique.IsBlock2 ⊤ (oResidual 2 X))
    (h : CFSG.Quasithin.IsHatA6Block (oResidual 2 X)) : IsScriptLBlock ⊤ (oResidual 2 X) :=
  sbtypes_isScriptLBlock_of_isHatA6Block hb h

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
