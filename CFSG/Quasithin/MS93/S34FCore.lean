module

public import CFSG.Quasithin.MS93.S34FFlat
public import CFSG.Quasithin.MS93.S4APair
import CFSG.Quasithin.MS93.S4A35
import CFSG.Quasithin.MS93.S5BAux
import CFSG.Quasithin.MS93.S5ABase
import CFSG.Quasithin.MS93.S33Crit
public import CFSG.Quasithin.MS93.S34DAsm

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Group

variable {G : Type} [Group G]

theorem commutator_sup_eq_of_le_centralizer {W U K : Subgroup G}
    (hWU : W ≤ Subgroup.centralizer (U : Set G)) (hWK : W ≤ Subgroup.centralizer (K : Set G)) :
    ⁅W ⊔ U, K⁆ = ⁅U, K⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_right le_rfl)
  rw [Subgroup.commutator_le]
  intro x hx k hk
  have hUW : U ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp hWU)
  obtain ⟨w, hw, u, hu, rfl⟩ := S34D.exists_mul_of_mem_sup hUW hx
  have h1 : Commute w u := (Subgroup.mem_centralizer_iff.mp (hWU hw) u hu).symm
  have h2 : Commute w k := (Subgroup.mem_centralizer_iff.mp (hWK hw) k hk).symm
  have hc : Commute w (u * k * u⁻¹) := (h1.mul_right h2).mul_right h1.inv_right
  have e : ⁅w * u, k⁆ = ⁅u, k⁆ := by
    calc ⁅w * u, k⁆ = w * (u * k * u⁻¹) * w⁻¹ * k⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = u * k * u⁻¹ * w * w⁻¹ * k⁻¹ := by rw [hc.eq]
      _ = ⁅u, k⁆ := by simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.commutator_mem_commutator hu hk

end Group

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

private theorem uloc_eq_uSub (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    Uloc h.le L δ = S5.uSub h.le L δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rw [Uloc, puTrans_smul h.le (S33.uq_subgroupOf_normal h), S5.uSub_smul h.le hLn,
    S5.uSub_baseA h, puTrans_baseA h.le (S33.uq_subgroupOf_normal h)]

theorem zm_eq_zh_sup_uloc (h : PUHyp M T L) {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) : ZM _ δ = ZH _ ρ ⊔ Uloc h.le L δ := by
  have h1 := S5B.zm_eq_zh_sup_uSub h hδ hδρ
  rw [← uloc_eq_uSub h hδ] at h1
  exact h1

theorem uloc_le_zm' (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    Uloc h.le L δ ≤ ZM _ δ := by
  obtain ⟨ρ, hδρ⟩ := exists_adj (puAmalgam h.le) δ
  rw [zm_eq_zh_sup_uloc h hδ hδρ]
  exact le_sup_right

end Vertex

section Crit

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hC : CentHyp (puAmalgam h.le))
include hC

theorem zh_le_centralizer_zm {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    ZH _ (geo _ α α' 1) ≤ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _) := by
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hc
  exact (zh_le_centralizer _ _).trans
    (Subgroup.centralizer_le (zm_le_qv_geo_one_left _ h.hyp20 h.critDist_pos hC hc'))

theorem zm_inf_centralizer_uloc {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    ZM _ α ⊓ Subgroup.centralizer (Uloc h.le L α' : Set _) = ZM _ α ⊓ Qv _ α' := by
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hc
  have hadj := adj_geo_one_of_isCritical _ h.critDist_pos hc'
  have hZ := zm_le_qv_geo_one_left _ h.hyp20 h.critDist_pos hC hc
  rw [← S33.qv_inf_centralizer_puTrans h hc'.1 hadj, ← inf_assoc, inf_of_le_left hZ]

theorem uloc_inf_centralizer_uloc {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    Uloc h.le L α ⊓ Subgroup.centralizer (Uloc h.le L α' : Set _) =
      Uloc h.le L α ⊓ Qv _ α' := by
  have hU := uloc_le_zm' h hc.1
  calc Uloc h.le L α ⊓ Subgroup.centralizer (Uloc h.le L α' : Set _) =
      Uloc h.le L α ⊓ (ZM _ α ⊓ Subgroup.centralizer (Uloc h.le L α' : Set _)) := by
        rw [← inf_assoc, inf_of_le_left hU]
    _ = Uloc h.le L α ⊓ Qv _ α' := by
        rw [zm_inf_centralizer_uloc h hC hc, ← inf_assoc, inf_of_le_left hU]

theorem uloc_inf_centralizer_zm {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    Uloc h.le L α ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _) =
      Uloc h.le L α ⊓ Qv _ α' := by
  have hU := uloc_le_zm' h hc.1
  calc Uloc h.le L α ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _) =
      Uloc h.le L α ⊓ (ZM _ α ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _)) := by
        rw [← inf_assoc, inf_of_le_left hU]
    _ = Uloc h.le L α ⊓ Qv _ α' := by
        rw [zm_inf_centralizer_eq_inf_qv _ h.hyp20 h.critDist_pos hC hc, ← inf_assoc,
          inf_of_le_left hU]

theorem critR_eq_commutator_uloc {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    critR _ α α' = ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ := by
  have hb := h.critDist_pos
  have hadj := adj_geo_one_of_isCritical _ hb hc
  have hZab : ZM (puAmalgam h.le) α ≤ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) :=
    (Subgroup.le_centralizer_iff_isMulCommutative).mpr (isElemAbelian_zm _ h.hyp20 hb hc.1).1
  have hW : ZH (puAmalgam h.le) (geo _ α α' 1) ≤
      Subgroup.centralizer (Uloc h.le L α : Set _) :=
    ((zh_le_zm _ hadj).trans hZab).trans (Subgroup.centralizer_le (uloc_le_zm' h hc.1))
  rw [critR, zm_eq_zh_sup_uloc h hc.1 hadj]
  exact commutator_sup_eq_of_le_centralizer hW (zh_le_centralizer_zm h hC hc)

variable {F : Type} [Field F]

theorem natImage_zm_eq_natImage_uloc {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') {K : Subgroup (puAmalgam h.le).Universal}
    {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K (Uloc h.le L α') ⊥ ψ false 1) (hZK : ZM _ α ≤ K) :
    natImage ψ (ZM _ α) = natImage ψ (Uloc h.le L α) := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  have hadj := adj_geo_one_of_isCritical _ hb hc
  have hW : ZH (puAmalgam h.le) (geo _ α α' 1) ≤ ZM _ α := zh_le_zm _ hadj
  have hWK := hW.trans hZK
  have hUK := (uloc_le_zm' h hc.1).trans hZK
  have hWc : ZH (puAmalgam h.le) (geo _ α α' 1) ≤
      Subgroup.centralizer (Uloc h.le L α' : Set _) :=
    (zh_le_centralizer_zm h hC hc).trans (Subgroup.centralizer_le (uloc_le_zm' h hc'.1))
  have hbot : ((ZH (puAmalgam h.le) (geo _ α α' 1)).subgroupOf K).map (toSL3 ψ) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_bot]
    refine (toSL3_eq_one_iff hψ w).mpr fun v hv => ?_
    have := Subgroup.mem_centralizer_iff.mp (hWc (Subgroup.mem_subgroupOf.mp hw)) v hv
    rw [← this, mul_inv_cancel_right]
  rw [natImage, natImage, zm_eq_zh_sup_uloc h hc.1 hadj, Subgroup.subgroupOf_sup hWK hUK,
    Subgroup.map_sup, hbot, bot_sup_eq]

theorem card_natImage_zm_eq {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') {K : Subgroup (puAmalgam h.le).Universal}
    {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K (Uloc h.le L α') ⊥ ψ false 1) (hZK : ZM _ α ≤ K) :
    Nat.card ↥(natImage ψ (ZM _ α)) = (Qv _ α').relIndex (ZM _ α) := by
  have hb := h.critDist_pos
  have h1 := card_natImage_mul hψ hZK
  rw [zm_inf_centralizer_uloc h hC hc] at h1
  have h2 := relIndex_mul_card_inf (Qv (puAmalgam h.le) α') (ZM _ α)
  rw [inf_comm] at h2
  have hβ := adj_geo_one_of_isCritical _ hb hc
  have hfin : Finite ↥(Qv (puAmalgam h.le) (geo _ α α' 1)) :=
    finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hβ]; exact hc.1)
  have hZQ : ZM (puAmalgam h.le) α ≤ Qv _ (geo _ α α' 1) :=
    qv_le_qv _ h.hyp20 hc.1 hβ |>.trans' (zm_le_qv_self _ hc.1 hb)
  have : Finite ↥(ZM (puAmalgam h.le) α ⊓ Qv _ α') :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans hZQ))
  have hpos : 0 < Nat.card ↥(ZM (puAmalgam h.le) α ⊓ Qv _ α') := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem card_natImage_mul_card_fixN [Finite F] {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') {K K' : Subgroup (puAmalgam h.le).Universal}
    {ψ : ↥K →* ↥(StatedSL 3 F)} {ψ' : ↥K' →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K (Uloc h.le L α) ⊥ ψ false 1)
    (hψ' : IsSumOfNaturalModulesVia K' (Uloc h.le L α') ⊥ ψ' false 1)
    (hZK : ZM _ α' ≤ K) (hZK' : ZM _ α ≤ K') :
    Nat.card ↥(natImage ψ' (ZM _ α)) * Nat.card ↥(fixN (natImage ψ (ZM _ α'))) =
      Nat.card F ^ 3 := by
  rw [natImage_zm_eq_natImage_uloc h hC hc hψ' hZK', ← card_inf_centralizer_eq hψ hZK,
    uloc_inf_centralizer_zm h hC hc, ← card_eq_of_natural hψ]
  have h1 := card_natImage_mul hψ' ((uloc_le_zm' h hc.1).trans hZK')
  rwa [uloc_inf_centralizer_uloc h hC hc] at h1

theorem card_commN_eq_card_critR' {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') {K : Subgroup (puAmalgam h.le).Universal}
    {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K (Uloc h.le L α) ⊥ ψ false 1) (hZK : ZM _ α' ≤ K) :
    Nat.card ↥(commN (natImage ψ (ZM _ α'))) = Nat.card ↥(critR (puAmalgam h.le) α α') := by
  rw [← card_commutator_eq hψ hZK, critR_eq_commutator_uloc h hC hc]

end Crit

section Core

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem s35_core_gen (h : PUHyp M T L) (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {n : ℕ} (hcard : Fintype.card F = 2 ^ n) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') {K K' : Subgroup (puAmalgam h.le).Universal}
    {ψ : ↥K →* ↥(StatedSL 3 F)} {ψ' : ↥K' →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K (Uloc h.le L α) ⊥ ψ false 1)
    (hψ' : IsSumOfNaturalModulesVia K' (Uloc h.le L α') ⊥ ψ' false 1)
    (hZK : ZM _ α' ≤ K) (hZK' : ZM _ α ≤ K') :
    Module.finrank F (fixN (natImage ψ' (ZM (puAmalgam h.le) α))) =
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Nat.card ↥(natImage ψ' (ZM (puAmalgam h.le) α)) = (Qv _ α').relIndex (ZM _ α) ∧
      (Qv _ α').relIndex (ZM _ α) =
        Nat.card F ^ (3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α')))) ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') =
        Nat.card F ^ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      natImage ψ (ZM (puAmalgam h.le) α') ≠ ⊥ := by
  have hb := h.critDist_pos
  have h20 := h.hyp20
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc' := ms22_iii _ h20 hb hC hc
  have hα := hc.1
  have hα' := hc'.1
  set E := natImage ψ' (ZM (puAmalgam h.le) α) with hE
  set E' := natImage ψ (ZM (puAmalgam h.le) α') with hE'
  set q := Nat.card F with hqdef
  have hcardE : Nat.card ↥E = (Qv _ α').relIndex (ZM _ α) :=
    card_natImage_zm_eq h hC hc hψ' hZK'
  have hcardE' : Nat.card ↥E' = (Qv _ α).relIndex (ZM _ α') :=
    card_natImage_zm_eq h hC hc' hψ hZK
  have hfix' : Nat.card ↥E * Nat.card ↥(fixN E') = q ^ 3 :=
    card_natImage_mul_card_fixN h hC hc hψ hψ' hZK hZK'
  have hfix : Nat.card ↥E' * Nat.card ↥(fixN E) = q ^ 3 :=
    card_natImage_mul_card_fixN h hC hc' hψ' hψ hZK' hZK
  have hcommE' : Nat.card ↥(commN E') = Nat.card ↥(critR (puAmalgam h.le) α α') :=
    card_commN_eq_card_critR' h hC hc hψ hZK
  have hcommE : Nat.card ↥(commN E) = Nat.card ↥(critR (puAmalgam h.le) α α') := by
    rw [card_commN_eq_card_critR' h hC hc' hψ' hZK', critR, critR, Subgroup.commutator_comm]
  have hE2 := natImage_zm_sq h hα (ψ := ψ')
  have hEc := natImage_zm_comm h hα (ψ := ψ')
  have hE'2 := natImage_zm_sq h hα' (ψ := ψ)
  have hE'c := natImage_zm_comm h hα' (ψ := ψ)
  set f := Module.finrank F (fixN E) with hfdef
  set f' := Module.finrank F (fixN E') with hf'def
  set w := Module.finrank F (commN E) with hwdef
  set w' := Module.finrank F (commN E') with hw'def
  have hfixc : Nat.card ↥(fixN E) = q ^ f := card_fixN E
  have hfixc' : Nat.card ↥(fixN E') = q ^ f' := card_fixN E'
  have hcommc : Nat.card ↥(commN E) = q ^ w := Module.natCard_eq_pow_finrank
  have hcommc' : Nat.card ↥(commN E') = q ^ w' := Module.natCard_eq_pow_finrank
  have hww' : w = w' := by
    have : q ^ w = q ^ w' := by rw [← hcommc, ← hcommc', hcommE, hcommE']
    exact Nat.pow_right_injective hq this
  have hwf : w ≤ f := finrank_commN_le_finrank_fixN_of_elemAb hE2 hEc
  have hwf' : w' ≤ f' := finrank_commN_le_finrank_fixN_of_elemAb hE'2 hE'c
  have hf3 : f ≤ 3 := (Submodule.finrank_le (fixN E)).trans (by simp)
  have hf'3 : f' ≤ 3 := (Submodule.finrank_le (fixN E')).trans (by simp)
  have hpow : ∀ {a e : ℕ}, e ≤ 3 → a * q ^ e = q ^ 3 → a = q ^ (3 - e) := by
    intro a e he hae
    have hpos : 0 < q ^ e := pow_pos (by omega) e
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hae, ← pow_add, Nat.sub_add_cancel he]
  have haE : Nat.card ↥E = q ^ (3 - f') := hpow hf'3 (hfixc' ▸ hfix')
  have haE' : Nat.card ↥E' = q ^ (3 - f) := hpow hf3 (hfixc ▸ hfix)
  have hne : Nat.card ↥E ≠ 1 := by
    rw [hcardE, Ne, Subgroup.relIndex_eq_one]
    exact hc.2.2
  have hne' : Nat.card ↥E' ≠ 1 := by
    rw [hcardE', Ne, Subgroup.relIndex_eq_one]
    exact hc'.2.2
  have hf2 : f ≤ 2 := by
    by_contra hcon
    apply hne'
    rw [haE', show 3 - f = 0 by omega, pow_zero]
  have hf'2 : f' ≤ 2 := by
    by_contra hcon
    apply hne
    rw [haE, show 3 - f' = 0 by omega, pow_zero]
  have hE'ne : E' ≠ ⊥ := by
    intro hbot
    apply hne'
    rw [hbot, Subgroup.card_bot]
  have hw'1 : 1 ≤ w' := by
    rw [Nat.one_le_iff_ne_zero, hw'def, Ne, Submodule.finrank_eq_zero]
    exact commN_ne_bot hE'ne
  have hb1 : 3 - f' ≤ (3 - f) * w := by
    have := card_le_of_elemAb hE2 hEc
    rw [haE] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hb2 : 3 - f ≤ (3 - f') * w := by
    have := card_le_of_elemAb hE'2 hE'c
    rw [haE', ← hw'def, ← hww'] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hff' : f = f' :=
    s35_arith (hww' ▸ hw'1) hwf (hww' ▸ hwf') hf2 hf'2 hb1 hb2
  exact ⟨hff', hcardE, hcardE ▸ haE, by rw [← hcommE', hcommc'], hwf', hE'ne⟩

theorem s35_core_flat (h : PUHyp M T L) (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    {ψ : ↥(flat h α) →* ↥(StatedSL 3 F)} {ψ' : ↥(flat h α') →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (flat h α) (Uloc h.le L α) ⊥ ψ false 1)
    (hψ' : IsSumOfNaturalModulesVia (flat h α') (Uloc h.le L α') ⊥ ψ' false 1) :
    Module.finrank F (fixN (natImage ψ' (ZM (puAmalgam h.le) α))) =
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Nat.card ↥(natImage ψ' (ZM (puAmalgam h.le) α)) = (Qv _ α').relIndex (ZM _ α) ∧
      (Qv _ α').relIndex (ZM _ α) =
        Nat.card F ^ (3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α')))) ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') =
        Nat.card F ^ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      natImage ψ (ZM (puAmalgam h.le) α') ≠ ⊥ :=
  s35_core_gen h hC hcard hc hψ hψ'
    (zm_le_flat h hU (ms22_iii _ h.hyp20 h.critDist_pos hC hc)) (zm_le_flat h hU hc)

end Core

end CFSG.Quasithin.MS93.S34F
