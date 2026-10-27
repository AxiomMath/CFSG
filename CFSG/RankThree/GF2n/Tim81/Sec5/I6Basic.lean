module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Shape
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbGamma
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbZPK
public import CFSG.RankThree.GF2n.Tim81.Sec4.OrthExt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.CentralizerLiftOfOddCenter
public import CFSG.LocalAnalysis.EvenBN.Common.ProductSplit

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.RankThree.GF2n.Tim81.Sec4
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec45Shape

variable {M V H : Subgroup G} {h₀ : G}

theorem imgK_conj_ne (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G} (hy : y ∈ H)
    (hyV : conjSubgroup y V ≠ V) :
    imgK V H (conjSubgroup y (Pc M V)) ≠ imgK V H (Pc M V) := by
  intro heq
  have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hS.Pc_le hy
  have hsup : conjSubgroup y (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq hPyH hS.Pc_le).mp heq
  exact hyV (h.conjSubgroup_eq_self_of_sup_conj_Pc_eq hS.Pc_le hy hsup).2.2

theorem imgK_inf_normalizer_conj_eq_bot (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {y : G} (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    imgK V H (Pc M V) ⊓
      Subgroup.normalizer (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) = ⊥ := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  exact h.inf_imgK_normalizer_conj_eq_bot_of_ne hS.Pc_le hy
    (hS.imgK_conj_ne h hy hyV) ψ

end Sec45Shape

private theorem commutator_zpowers_le_subgroupOfSubW {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] {X : Type} [Group X]
    (ψ : HBar V H ≃* X) {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H) {b : G} (hb : b ∈ H)
    (hb2 : b * b ∈ kOf V H) :
    ⁅E, Subgroup.zpowers b⁆ ≤ subgroupOfSubW hW
      ((subW hW E).map (repW hW ψ (ψ (piK V H ⟨b, hb⟩)) - 1)) := by
  refine (Subgroup.commutator_le).mpr ?_
  intro e he c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  let eW : ↥(Tim79a.xOf V H) := ⟨e, hE he⟩
  let t : HBar V H := piK V H ⟨b, hb⟩
  have hbkH : b ^ k ∈ H := H.zpow_mem hb k
  have ht2 : t * t = 1 := by
    have hmul : (⟨b, hb⟩ : ↥H) * ⟨b, hb⟩ = ⟨b * b, H.mul_mem hb hb⟩ := rfl
    have h1 : piK V H ((⟨b, hb⟩ : ↥H) * ⟨b, hb⟩) = 1 := by
      rw [hmul]
      exact (piK_eq_one_iff _).mpr hb2
    rwa [map_mul] at h1
  have hpi : piK V H ⟨b ^ k, hbkH⟩ = t ^ k := by
    have hz : (⟨b ^ k, hbkH⟩ : ↥H) = ⟨b, hb⟩ ^ k := Subtype.ext (by simp)
    rw [hz, map_zpow]
  have hcases := CFSG.GorensteinWalter.zpow_eq_one_or_self_of_sq_eq_one_local ht2 k
  have hrep := repW_apply_piK_sub (hW := hW) ψ (⟨b ^ k, hbkH⟩ : ↥H) eW
  rw [hpi] at hrep
  have hg : ⁅e, b ^ k⁆ ∈ Tim79a.xOf V H := by
    rw [← commutatorElement_inv]
    exact (Tim79a.xOf V H).inv_mem (mem_commutator_xOf
      (z := (⟨b ^ k, hbkH⟩ : ↥H)) (w := eW))
  have hneg : ofW hW ⟨⁅e, b ^ k⁆, hg⟩ =
      -(ofW hW ⟨⁅b ^ k, e⁆,
        mem_commutator_xOf (z := (⟨b ^ k, hbkH⟩ : ↥H)) (w := eW)⟩) := by
    rw [← ofW_inv]
    apply ofW_injective hW
    apply Subtype.ext
    change ⁅e, b ^ k⁆ = (⁅b ^ k, e⁆)⁻¹
    exact (commutatorElement_inv _ _).symm
  rw [mem_subgroupOfSubW_iff]
  refine ⟨hg, ?_⟩
  rw [hneg]
  refine Submodule.neg_mem _ ?_
  rcases hcases with h1 | h1
  · have hzero : ofW hW ⟨⁅b ^ k, e⁆,
        mem_commutator_xOf (z := (⟨b ^ k, hbkH⟩ : ↥H)) (w := eW)⟩ = 0 := by
      refine hrep.symm.trans ?_
      rw [h1, map_one ψ, map_one (repW hW ψ), Module.End.one_apply, sub_self]
    rw [hzero]
    simp
  · refine Submodule.mem_map.mpr ⟨ofW hW eW, (mem_subW_iff hW).mpr he, ?_⟩
    rw [h1] at hrep
    change (repW hW ψ (ψ t)) (ofW hW eW) - ofW hW eW =
      ofW hW ⟨⁅b ^ k, e⁆,
        mem_commutator_xOf (z := (⟨b ^ k, hbkH⟩ : ↥H)) (w := eW)⟩
    exact hrep

theorem subW_commutator_zpowers {V H : Subgroup G}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] {X : Type} [Group X]
    (ψ : HBar V H ≃* X) {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H) {b : G} (hb : b ∈ H)
    (hb2 : b * b ∈ kOf V H) :
    subW hW ⁅E, Subgroup.zpowers b⁆ =
      (subW hW E).map (repW hW ψ (ψ (piK V H ⟨b, hb⟩)) - 1) := by
  have hB : ⁅E, Subgroup.zpowers b⁆ ≤ Tim79a.xOf V H := by
    refine (Subgroup.commutator_le).mpr ?_
    intro e he c hc
    have heW : e ∈ Tim79a.xOf V H := hE he
    have hcH : c ∈ H := (Subgroup.zpowers_le.mpr hb) hc
    have h1 : c * e * c⁻¹ ∈ Tim79a.xOf V H :=
      (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hcH) e).mp heW
    rw [commutatorElement_def,
      show e * c * e⁻¹ * c⁻¹ = e * (c * e * c⁻¹)⁻¹ by group]
    exact (Tim79a.xOf V H).mul_mem heW ((Tim79a.xOf V H).inv_mem h1)
  refine le_antisymm ?_ ?_
  · rw [← subW_subgroupOfSubW hW
      ((subW hW E).map (repW hW ψ (ψ (piK V H ⟨b, hb⟩)) - 1))]
    exact subW_mono (commutator_zpowers_le_subgroupOfSubW ψ hE hb hb2)
  · exact subW_map_repW_sub_le ψ hb le_rfl

noncomputable def hBarConj {V H : Subgroup G} {b : G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G))
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G)) : MulAut (HBar V H) :=
  QuotientGroup.congr ((kOf V H).subgroupOf H) ((kOf V H).subgroupOf H)
    (H.normalizerMonoidHom ⟨b, hbH⟩) (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change ((H.normalizerMonoidHom ⟨b, hbH⟩ y : ↥H) : G) ∈ kOf V H
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact (Subgroup.mem_normalizer_iff.mp hbK ((y : G))).mp
          (Subgroup.mem_subgroupOf.mp hy)
      · intro hx
        have hxK : (x : G) ∈ kOf V H := Subgroup.mem_subgroupOf.mp hx
        have hxH : (x : G) ∈ H := (kOf_le V H) hxK
        refine ⟨⟨b⁻¹ * (x : G) * b, ?_⟩, ?_, ?_⟩
        · simpa using
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbH) (x : G)).mp hxH
        · exact Subgroup.mem_subgroupOf.mpr (by
            simpa using
              (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbK) (x : G)).mp hxK)
        · apply Subtype.ext
          change (((H.normalizerMonoidHom ⟨b, hbH⟩) ⟨b⁻¹ * (x : G) * b, _⟩ :
            ↥H) : G) = (x : G)
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
          group)

theorem hBarConj_piK {V H : Subgroup G} {b : G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G))
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G)) (z : ↥H) :
    hBarConj hbH hbK (piK V H z) =
      piK V H ⟨b * (z : G) * b⁻¹,
        (Subgroup.mem_normalizer_iff.mp hbH (z : G)).mp z.2⟩ := by
  rw [hBarConj]
  change QuotientGroup.congr ((kOf V H).subgroupOf H) ((kOf V H).subgroupOf H)
      (H.normalizerMonoidHom ⟨b, hbH⟩) _ (QuotientGroup.mk' _ z) =
    QuotientGroup.mk' _ ⟨b * (z : G) * b⁻¹,
      (Subgroup.mem_normalizer_iff.mp hbH (z : G)).mp z.2⟩
  rw [QuotientGroup.congr_mk']
  congr 1

theorem hBarConj_eq_one_iff {V H : Subgroup G} {b : G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G))
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G)) :
    hBarConj hbH hbK = 1 ↔ ∀ x ∈ H, ⁅b, x⁆ ∈ kOf V H := by
  constructor
  · intro hb x hx
    let z : ↥H := ⟨x, hx⟩
    have h1 : hBarConj hbH hbK (piK V H z) = piK V H z := by
      rw [hb]
      rfl
    rw [hBarConj_piK] at h1
    have hdiv : (⟨b * (z : G) * b⁻¹,
        (Subgroup.mem_normalizer_iff.mp hbH (z : G)).mp z.2⟩ / z) ∈
        (kOf V H).subgroupOf H := (QuotientGroup.eq_iff_div_mem).mp h1
    have hcoe : ((⟨b * (z : G) * b⁻¹,
        (Subgroup.mem_normalizer_iff.mp hbH (z : G)).mp z.2⟩ / z : ↥H) : G) = ⁅b, x⁆ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
        div_eq_mul_inv, commutatorElement_def, z]
    have hmem : ⁅b, x⁆ ∈ kOf V H := by
      have := Subgroup.mem_subgroupOf.mp hdiv
      rwa [hcoe] at this
    exact hmem
  · intro hb
    refine MulEquiv.ext fun y => ?_
    obtain ⟨z, rfl⟩ := piK_surjective V H y
    rw [hBarConj_piK]
    have hdiv : (⟨b * (z : G) * b⁻¹,
        (Subgroup.mem_normalizer_iff.mp hbH (z : G)).mp z.2⟩ / z) ∈
        (kOf V H).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((⟨b * (z : G) * b⁻¹,
          (Subgroup.mem_normalizer_iff.mp hbH (z : G)).mp z.2⟩ / z : ↥H) : G) = ⁅b, (z : G)⁆ := by
        simp only [Subgroup.coe_div, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
          div_eq_mul_inv, commutatorElement_def]
      rw [hcoe]
      exact hb z z.2
    exact (QuotientGroup.eq_iff_div_mem).mpr hdiv

namespace Sec45Shape

variable {M V H : Subgroup G} {h₀ : G}

theorem Pc_inf_centralizer_conj (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup y V : Set G) = Pc M V ⊓ kOf V H := by
  refine le_antisymm ?_ ?_
  · intro p hp
    obtain ⟨hpP, hpC⟩ := Subgroup.mem_inf.mp hp
    have hN : piK V H ⟨p, hS.Pc_le hpP⟩ ∈
        Subgroup.normalizer (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) :=
      (h.normalizer_imgK_iff hS.Pc_le hS.le_pCore hy hyV hpP).mpr hpC
    have hmem : piK V H ⟨p, hS.Pc_le hpP⟩ ∈ imgK V H (Pc M V) ⊓
        Subgroup.normalizer (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) :=
      ⟨Subgroup.mem_map.mpr ⟨⟨p, hS.Pc_le hpP⟩, Subgroup.mem_subgroupOf.mpr hpP, rfl⟩, hN⟩
    rw [hS.imgK_inf_normalizer_conj_eq_bot h hy hyV] at hmem
    exact Subgroup.mem_inf.mpr
      ⟨hpP, (piK_eq_one_iff _).mp (Subgroup.mem_bot.mp hmem)⟩
  · intro p hp
    obtain ⟨hpP, hpK⟩ := Subgroup.mem_inf.mp hp
    refine Subgroup.mem_inf.mpr ⟨hpP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvW : v ∈ Tim79a.xOf V H :=
      Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hy) hv
    exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hpK).2 v hvW

theorem Pc_inf_centralizer_inf_xOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    Pc M V ⊓ Subgroup.centralizer ((Pc M V ⊓ Tim79a.xOf V H : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V H := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW := hS.isElemAbelian h
  letI := moduleOfElemAbelian hW
  exact RootHyp.inf_centralizer_inf_xOf_eq_inf_kOf h hS.Pc_le hS.le_pCore hS.hH hS.not_le
    ψ hl (hw.orth_subRepW hW)

theorem conj_Pc_inf_M (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    conjSubgroup h₀ (Pc M V) ⊓ M = conjSubgroup h₀ (Pc M V) ⊓ kOf V H := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxP, hxM⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ H := by
      rw [hS.hH]
      exact Subgroup.mem_sup_right hxP
    have hxN : x ∈ Subgroup.normalizer (Pc M V : Set G) := h.toHyp.le_normalizer_Pc hxM
    have hconjP : conjSubgroup x (Pc M V) = Pc M V := conjSubgroup_eq_self_iff.mpr hxN
    have hxbarP : piK V H ⟨x, hxH⟩ ∈ imgK V H (conjSubgroup h₀ (Pc M V)) :=
      Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    have hxbarN : piK V H ⟨x, hxH⟩ ∈
        Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
      rw [← conjSubgroup_eq_self_iff, ← imgK_conjSubgroup hxH hS.Pc_le, hconjP]
    have hbot := RootHyp.imgK_conj_inf_normalizer_eq_bot_of_sl2 h hS.Pc_le
      hS.hH hS.not_le ψ
    have hmem : piK V H ⟨x, hxH⟩ ∈ (⊥ : Subgroup (HBar V H)) := by
      rw [← hbot]
      exact ⟨hxbarP, hxbarN⟩
    exact Subgroup.mem_inf.mpr ⟨hxP, (piK_eq_one_iff _).mp (Subgroup.mem_bot.mp hmem)⟩
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨hx.1, hS.kOf_le_M h hx.2⟩

theorem conj_Pc_inf_centralizer (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    conjSubgroup h₀ (Pc M V) ⊓ Subgroup.centralizer (V : Set G) =
      conjSubgroup h₀ (Pc M V) ⊓ kOf V H := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxM : x ∈ M := by
      rw [← h.toHyp.normalizer_eq]
      exact Subgroup.centralizer_le_normalizer (V : Set G) hxC
    exact (conj_Pc_inf_M h hS).le (Subgroup.mem_inf.mpr ⟨hxP, hxM⟩)
  · intro x hx
    obtain ⟨hxP, hxK⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvW : v ∈ Tim79a.xOf V H := le_xOf_self V H hv
    exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hxK).2 v hvW

theorem commutator_commutator_eq_one (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x w : G} (hx : x ∈ Pc M V) (hw : w ∈ Tim79a.xOf V H) : ⁅⁅w, x⁆, x⁆ = 1 := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hwS⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  let z : ↥H := ⟨x, hS.Pc_le hx⟩
  let xbar : SL(2, F) := ψ (piK V H z)
  have hxbar2 : xbar * xbar = 1 := by
    have hmem : xbar ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨piK V H z,
        Subgroup.mem_map.mpr ⟨z, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
    exact (h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ).1 xbar hmem
  let wW : ↥(Tim79a.xOf V H) := ⟨w, hw⟩
  have hxw : ⁅x, w⁆ ∈ Tim79a.xOf V H := mem_commutator_xOf (z := z) (w := wW)
  let cW : ↥(Tim79a.xOf V H) := ⟨⁅x, w⁆, hxw⟩
  let ex : Module.End (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    repW hW ψ (ψ (piK V H z))
  have hex_sq : ex * ex = 1 := by
    change repW hW ψ (ψ (piK V H z)) * repW hW ψ (ψ (piK V H z)) = 1
    rw [← map_mul, hxbar2, map_one]
  have hex_apply : ex (ex (ofW hW wW)) = ofW hW wW := by
    have h := congrArg (fun e : Module.End (ZMod 2)
        (Additive (IntMod (Tim79a.xOf V H) hW)) => e (ofW hW wW)) hex_sq
    simpa [Module.End.mul_apply, Module.End.one_apply] using h
  have hcw_eq : ofW hW cW = ex (ofW hW wW) - ofW hW wW := by
    change ofW hW cW = repW hW ψ (ψ (piK V H z)) (ofW hW wW) - ofW hW wW
    rw [repW_apply_piK_sub]
  have hfix : ex (ofW hW cW) = ofW hW cW := by
    rw [hcw_eq]
    have hsub : ex (ex (ofW hW wW) - ofW hW wW) =
        ex (ex (ofW hW wW)) - ex (ofW hW wW) := ex.map_sub _ _
    rw [hsub, hex_apply]
    rw [show ofW hW wW - ex (ofW hW wW) =
      -(ex (ofW hW wW) - ofW hW wW) by abel]
    rw [ZModModule.neg_eq_self]
  have hconj : conjH V H z cW = cW := by
    change repW hW ψ (ψ (piK V H z)) (ofW hW cW) = ofW hW cW at hfix
    rw [repW_apply_piK, toW_ofW] at hfix
    exact ofW_injective hW hfix
  have hcx : x * ⁅x, w⁆ * x⁻¹ = ⁅x, w⁆ := by
    have := congrArg Subtype.val hconj
    simpa [cW, conjH_apply_coe] using this
  have hgoal : ⁅⁅w, x⁆, x⁆ = 1 := by
    have h1 : ⁅w, x⁆ = (⁅x, w⁆)⁻¹ := (commutatorElement_inv x w).symm
    rw [h1, commutatorElement_def, inv_inv]
    rw [show (⁅x, w⁆)⁻¹ * x * ⁅x, w⁆ * x⁻¹ =
      (⁅x, w⁆)⁻¹ * (x * ⁅x, w⁆ * x⁻¹) by group]
    rw [hcx]
    group
  exact hgoal

theorem exists_centralizing_not_mem_kOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {w : G} (hw : w ∈ Pc M V ⊓ Tim79a.xOf V H) :
    ∃ x ∈ Pc M V, x ∉ kOf V H ∧ w ∈ Subgroup.centralizer ({x} : Set G) := by
  classical
  have hDZ : ⁅Pc M V, Pc M V⁆ ≤ V := by rw [hS.commutator_Pc h]
  have hZD : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [h.toHyp.centralizer_Pc]
  have hrel := CFSG.LocalAnalysis.EvenBN.Common.relIndex_inf_centralizer_le
    (D := Pc M V) (Z := V) (A := Pc M V) hDZ hZD le_rfl hw.1
  have hcardK : (Pc M V ⊓ kOf V H).relIndex (Pc M V) = Nat.card V ^ 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Pc M V ⊓ kOf V H) (K := Pc M V)
    rw [show (Pc M V ⊓ kOf V H) ⊓ Pc M V = Pc M V ⊓ kOf V H from
      inf_eq_left.mpr inf_le_left] at h1
    have h2 := hS.card_Pc_inf_kOf h
    have h2' : Nat.card V ^ 2 * Nat.card ↥(Pc M V ⊓ kOf V H) =
        Nat.card ↥(Pc M V) := by
      rw [mul_comm, h2]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) (by rw [h1, h2'])
  by_contra hno
  have hle : Pc M V ⊓ Subgroup.centralizer ({w} : Set G) ≤ Pc M V ⊓ kOf V H := by
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxP, ?_⟩
    by_contra hxK
    have hwx : w ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
    exact hno ⟨x, hxP, hxK, hwx⟩
  have hne : (Pc M V ⊓ Subgroup.centralizer ({w} : Set G)).relIndex (Pc M V) ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card
      (H := Pc M V ⊓ Subgroup.centralizer ({w} : Set G)) (K := Pc M V)
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hle_rel := (Subgroup.relIndex_le_of_le_left hle hne).trans hrel
  rw [hcardK] at hle_rel
  have h4 : 4 ≤ Nat.card V := h.four_le_card
  nlinarith [pow_two (Nat.card V)]

theorem exists_mem_eq_of_conj_le_xOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {k : G}
    (hk : conjSubgroup k V ≤ Tim79a.xOf V H) :
    ∃ y ∈ H, conjSubgroup k V = conjSubgroup y V := by
  classical
  have hcard : Nat.card (conjSubgroup k V) = Nat.card V := card_conjSubgroup k V
  have hne : conjSubgroup k V ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (conjSubgroup k V) = 1 := by rw [hbot]; simp
    rw [hcard] at h1
    have := h.four_le_card
    omega
  obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hv1 : (v : G) ≠ 1 := fun h1 => hvne (Subtype.ext h1)
  have hvD : (v : G) ∈ Tim78.classD V := by
    obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp v.2
    have hz1 : z ≠ 1 := by
      intro hz1
      apply hv1
      have h := hzv.symm
      rw [hz1] at h
      simpa using h
    exact ⟨k, z, hz, hz1, hzv.symm⟩
  have hvW : (v : G) ∈ Tim79a.xOf V H := hk v.2
  obtain ⟨y, hy, hvy⟩ := hS.exists_mem_conj_of_mem_classD h hvW hvD
  refine ⟨y, hy, ?_⟩
  by_contra hky
  have hne' : conjSubgroup (k⁻¹ * y) V ≠ V := by
    intro heq
    apply hky
    have h1 : conjSubgroup k (conjSubgroup (k⁻¹ * y) V) = conjSubgroup k V := by rw [heq]
    rw [← conjSubgroup_mul, show k * (k⁻¹ * y) = y by group] at h1
    exact h1.symm
  have hvK : k⁻¹ * (v : G) * k ∈ V := mem_conjSubgroup.mp v.2
  have hvY : (k⁻¹ * y)⁻¹ * (k⁻¹ * (v : G) * k) * (k⁻¹ * y) ∈ V := by
    have h1 : y⁻¹ * (v : G) * y ∈ V := mem_conjSubgroup.mp hvy
    have h2 : (k⁻¹ * y)⁻¹ * (k⁻¹ * (v : G) * k) * (k⁻¹ * y) =
        y⁻¹ * (v : G) * y := by group
    rwa [h2]
  have hmem : k⁻¹ * (v : G) * k ∈ V ⊓ conjSubgroup (k⁻¹ * y) V :=
    Subgroup.mem_inf.mpr ⟨hvK, mem_conjSubgroup.mpr hvY⟩
  rw [inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hne'] at hmem
  have h1 : k⁻¹ * (v : G) * k = 1 := Subgroup.mem_bot.mp hmem
  have hv_eq_one : (v : G) = 1 := by
    calc (v : G) = k * (k⁻¹ * (v : G) * k) * k⁻¹ := by group
      _ = k * 1 * k⁻¹ := by rw [h1]
      _ = 1 := by group
  exact hv1 hv_eq_one

private theorem le_of_inf_centralizer_ne_bot (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {W₁ : Subgroup G} (hW₁ : W₁ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₁ : Set G))
    (hfix : W₁ ⊓ Subgroup.centralizer (Pc M V : Set G) ≠ ⊥) : V ≤ W₁ := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW := hS.isElemAbelian h
  letI := moduleOfElemAbelian hW
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have horth : Sec2.IsOrthModule hl (repW hW ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  obtain ⟨u, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfix
  have hu1 : (u : G) ≠ 1 := fun h1 => hu1' (Subtype.ext h1)
  have huW₁ : (u : G) ∈ W₁ := (Subgroup.mem_inf.mp u.2).1
  have huV : (u : G) ∈ V := by
    have hmem : (u : G) ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer (Pc M V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hW₁ huW₁, (Subgroup.mem_inf.mp u.2).2⟩
    rwa [h.xOf_inf_centralizer_Pc_eq_V] at hmem
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact W₁.one_mem
  obtain ⟨z, hzH, hvz⟩ := h.exists_conj_eq_of_isOrthModule hS.Pc_le hS.le_pCore hS.hH
    hS.not_le hW ψ hl horth (le_xOf_self V H hv) huV hu1 ⟨1, v, hv, hv1, by group⟩
  rw [hvz]
  exact (Subgroup.mem_normalizer_iff.mp (hN hzH) u).mp huW₁

theorem eq_xOf_of_le (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {W₁ : Subgroup G}
    (hW₁ : W₁ ≤ Tim79a.xOf V H) (hne : W₁ ≠ ⊥)
    (hN : H ≤ Subgroup.normalizer (W₁ : Set G)) : W₁ = Tim79a.xOf V H := by
  have hW := hS.isElemAbelian h
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hW12 : IsPGroup 2 W₁ := hW.isPGroup.to_le hW₁
  have hfix : W₁ ⊓ Subgroup.centralizer (Pc M V : Set G) ≠ ⊥ :=
    CFSG.LocalAnalysis.EvenBN.Common.inf_centralizer_ne_bot_of_isPGroup hP2 hW12 hne
      (hS.Pc_le.trans hN)
  have hVle : V ≤ W₁ := le_of_inf_centralizer_ne_bot h hS hW₁ hN hfix
  refine le_antisymm hW₁ ?_
  refine iSup₂_le ?_
  intro U hU
  obtain ⟨y, hy, rfl⟩ := hU
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
  exact (Subgroup.mem_normalizer_iff.mp (hN hy) v).mp (hVle hv)

private theorem inv_mul_mem_centralizer_of_coboundary
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] {X : Type} [Group X]
    (ψ : HBar V H ≃* X) {L : Subgroup G} (hL : L ≤ H) {v : G}
    (hvL : ∀ g ∈ L, ⁅g, v⁆ ∈ Tim79a.xOf V H) {w : Additive (IntMod (Tim79a.xOf V H) hW)}
    (hw : ∀ a : ↥L, ofW hW ⟨⁅(a : G), v⁆, hvL a a.2⟩ =
      repW hW ψ (ψ (piK V H ⟨(a : G), hL a.2⟩)) w - w) :
    (toW hW w)⁻¹ * v ∈ Subgroup.centralizer (L : Set G) := by
  classical
  let w' : G := toW hW w
  have hneg : ∀ x : Additive (IntMod (Tim79a.xOf V H) hW),
      toW hW (-x) = (toW hW x)⁻¹ := by
    intro x
    apply ofW_injective hW
    rw [ofW_inv, ofW_toW, ofW_toW]
  have hgrp : ∀ a : ↥L, ⁅(a : G), v⁆ = (a : G) * w' * (a : G)⁻¹ * w'⁻¹ := by
    intro a
    have h1 := congrArg (toW hW) (hw a)
    rw [toW_ofW] at h1
    have hsub : toW hW (repW hW ψ (ψ (piK V H ⟨(a : G), hL a.2⟩)) w - w) =
        toW hW (repW hW ψ (ψ (piK V H ⟨(a : G), hL a.2⟩)) w) * (toW hW w)⁻¹ := by
      rw [sub_eq_add_neg, toW_add, hneg]
    rw [hsub] at h1
    have h2 : toW hW (repW hW ψ (ψ (piK V H ⟨(a : G), hL a.2⟩)) w) =
        conjH V H ⟨(a : G), hL a.2⟩ (toW hW w) := by
      rw [repW_apply_piK, toW_ofW]
    rw [h2] at h1
    have h3 := congrArg Subtype.val h1
    simpa [w', conjH_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def] using h3
  intro g hg
  have hga := hgrp ⟨g, hg⟩
  have h1 : g * w' * g⁻¹ = ⁅g, v⁆ * w' := by
    calc g * w' * g⁻¹ = (g * w' * g⁻¹ * w'⁻¹) * w' := by group
      _ = ⁅g, v⁆ * w' := by rw [← hga]
  have h2 : g * v * g⁻¹ = ⁅g, v⁆ * v := by
    rw [commutatorElement_def]
    group
  calc g * (w'⁻¹ * v) = ((g * w' * g⁻¹)⁻¹) * (g * v * g⁻¹) * g := by group
    _ = (⁅g, v⁆ * w')⁻¹ * (⁅g, v⁆ * v) * g := by rw [h1, h2]
    _ = w'⁻¹ * v * g := by group

theorem exists_mem_xOf_inv_mul_mem_centralizer (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {L : Subgroup G} (hL : L ≤ H) (hKL : kOf V H ⊔ L = H) {v : G}
    (hvK : ∀ k ∈ L ⊓ kOf V H, k * v = v * k)
    (hvL : ∀ g ∈ L, ⁅g, v⁆ ∈ Tim79a.xOf V H) :
    ∃ w ∈ Tim79a.xOf V H, w⁻¹ * v ∈ Subgroup.centralizer (L : Set G) := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW hW ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  let iLH : ↥L →* ↥H := Subgroup.inclusion hL
  let π : ↥L →* SL(2, F) := ψ.toMonoidHom.comp ((piK V H).comp iLH)
  have hπa : ∀ a : ↥L, π a = ψ (piK V H ⟨(a : G), hL a.2⟩) := fun _ => rfl
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨y, hy⟩ := ψ.surjective s
    obtain ⟨x, rfl⟩ := piK_surjective V H y
    have hxKL : (x : G) ∈ kOf V H ⊔ L := by
      rw [hKL]
      exact x.2
    obtain ⟨k, hk, l, hlL, hkl⟩ := exists_mul_of_mem_sup (V := kOf V H) (U := L)
      (hL.trans (le_normalizer_kOf V H)) hxKL
    refine ⟨⟨l, hlL⟩, ?_⟩
    have hxe : (⟨x, x.2⟩ : ↥H) = ⟨k, kOf_le V H hk⟩ * ⟨l, hL hlL⟩ :=
      Subtype.ext (by simpa using hkl)
    calc π ⟨l, hlL⟩ = ψ (piK V H ⟨l, hL hlL⟩) := rfl
      _ = ψ (piK V H (⟨k, kOf_le V H hk⟩ * ⟨l, hL hlL⟩)) := by
          rw [map_mul, (piK_eq_one_iff (⟨k, kOf_le V H hk⟩ : ↥H)).mpr hk, one_mul]
      _ = ψ (piK V H ⟨x, x.2⟩) := by rw [← hxe]
      _ = s := hy
  let c : ↥L → Additive (IntMod (Tim79a.xOf V H) hW) := fun a =>
    ofW hW ⟨⁅(a : G), v⁆, hvL a a.2⟩
  have hc : ∀ a b : ↥L, c (a * b) = c a + repW hW ψ (π a) (c b) := by
    intro a b
    have hρ : repW hW ψ (π a) (c b) =
        ofW hW (conjH V H ⟨(a : G), hL a.2⟩ ⟨⁅(b : G), v⁆, hvL b b.2⟩) := by
      rw [hπa a, repW_apply_piK, toW_ofW]
    have hcab : c (a * b) = ofW hW ⟨⁅((a : G) * (b : G)), v⁆,
        hvL (a * b) (a * b).2⟩ := rfl
    have hca : c a = ofW hW ⟨⁅(a : G), v⁆, hvL a a.2⟩ := rfl
    have hgroup : (⟨⁅((a : G) * (b : G)), v⁆, hvL (a * b) (a * b).2⟩ :
          ↥(Tim79a.xOf V H)) =
        conjH V H ⟨(a : G), hL a.2⟩ ⟨⁅(b : G), v⁆, hvL b b.2⟩ *
          ⟨⁅(a : G), v⁆, hvL a a.2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, conjH_apply_coe, commutatorElement_def]
      group
    rw [hcab, hca, hρ, add_comm, ← ofW_mul]
    exact congrArg (ofW hW) hgroup
  have hker : ∀ a : ↥L, π a = 1 → c a = 0 := by
    intro a ha
    have hpi : piK V H ⟨(a : G), hL a.2⟩ = 1 := by
      apply ψ.injective
      simpa using (show ψ (piK V H ⟨(a : G), hL a.2⟩) = 1 from by rwa [hπa a] at ha)
    have haK : (a : G) ∈ kOf V H := (piK_eq_one_iff _).mp hpi
    have hcomm : (a : G) * v = v * (a : G) := hvK (a : G) ⟨a.2, haK⟩
    have h1 : ⁅(a : G), v⁆ = 1 := by
      rw [commutatorElement_def]
      rw [hcomm]
      group
    change ofW hW ⟨⁅(a : G), v⁆, hvL a a.2⟩ = 0
    have h2 : (⟨⁅(a : G), v⁆, hvL a a.2⟩ : ↥(Tim79a.xOf V H)) = 1 := Subtype.ext h1
    rw [h2]
    exact ofW_one hW
  have hl0 : 0 < l := Nat.lt_of_lt_of_le Nat.zero_lt_one hw.one_le
  obtain ⟨w, hw_eq⟩ := horth.exists_eq_sub_of_cocycle_comp hl hl0 π hπ hc hker
  have hwfun : ∀ a : ↥L, ofW hW ⟨⁅(a : G), v⁆, hvL a a.2⟩ =
      repW hW ψ (ψ (piK V H ⟨(a : G), hL a.2⟩)) w - w := by
    intro a
    have h := hw_eq a
    rw [hπa a] at h
    simpa [c] using h
  exact ⟨toW hW w, (toW hW w).2,
    inv_mul_mem_centralizer_of_coboundary ψ hL hvL hwfun⟩

end Sec45Shape

end CFSG.RankThree.GF2n.Tim81

end
