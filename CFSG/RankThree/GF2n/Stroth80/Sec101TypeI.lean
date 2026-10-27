module

public import CFSG.RankThree.GF2n.Stroth80.Sec101SLCard
public import CFSG.RankThree.GF2n.Stroth80.Sec101Cent
public import CFSG.RankThree.GF2n.Stroth80.Sec101Comp
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.Goldschmidt75.B1Out
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Goldschmidt75
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem isPGroup_inSubgroup_pCore {G : Type} [Group G] (p : ℕ) (H : Subgroup G) :
    IsPGroup p (inSubgroup (CFSG.pCore p) H) :=
  IsPGroup.map CFSG.pCore_isPGroup H.subtype

theorem Ctx.exists_perfect_le_bar_Rt [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {m : ℕ} (hm2 : 2 ≤ m) (hm : SLMNat hc t m) :
    ∃ P : Subgroup (Mbar M Q), P ≤ bar M Q (Rt M (LB M Q B) t) ∧ ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
  obtain ⟨K, fK, finK, hK, π, hπ, hker⟩ := hc.exists_bar_hom_of_SLMNat ht hm
  have hq4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  have hq : CFSG.IsQuasisimple ↥(StatedSL m K) := statedSL_quasisimple_of_card m K hm2 hq4
  haveI hsimple : IsSimpleGroup (↥(StatedSL m K) ⧸ Subgroup.center ↥(StatedSL m K)) := hq.2.1
  have hnt : Nontrivial ↥(StatedSL m K) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(StatedSL m K) ⧸ Subgroup.center ↥(StatedSL m K))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨x, y, fun h => hab (by rw [h])⟩⟩
  have hperf : ⁅(⊤ : Subgroup ↥(StatedSL m K)), (⊤ : Subgroup ↥(StatedSL m K))⁆ = ⊤ := by
    simpa [commutator] using hq.1.commutator_eq_top
  obtain ⟨P, hPR, hPperf, -, hcover⟩ :=
    endg_exists_perfCore (X := Mbar M Q) (R := bar M Q (Rt M (LB M Q B) t))
  refine ⟨P, hPR, hPperf, ?_⟩
  intro hPbot
  have hRN : bar M Q (Rt M (LB M Q B) t) ≤ bar M Q (hc.CN t) := by
    have := hcover ↥(StatedSL m K) π hπ hperf (bar M Q (hc.CN t)) hker
    simpa [hPbot] using this
  have hsingle : Subsingleton ↥(StatedSL m K) :=
    ⟨fun a b => by
      obtain ⟨r, rfl⟩ := hπ a
      obtain ⟨s, rfl⟩ := hπ b
      rw [(hker r).mpr (hRN r.2), (hker s).mpr (hRN s.2)]⟩
  exact not_subsingleton ↥(StatedSL m K) hsingle

theorem Ctx.le_layer_of_perfect [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hB : fusionIsBenderGroup ↥(layer (Mbar M Q))) {P : Subgroup (Mbar M Q)}
    (hPH : P ≤ bar M Q (H0 M Z)) (hP : ⁅P, P⁆ = P) : P ≤ layer (Mbar M Q) := by
  set L := layer (Mbar M Q)
  haveI hLc : L.Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLn : L.Normal := inferInstance
  haveI hsol : Group.IsSolvable (Outer ↥L) := outer_solvable_of_bender hB
  have hLleH : L ≤ bar M Q (H0 M Z) := hc.layer_le_bar_H0 h34 hw hn hno hgen
  have hnormal : ∀ k ∈ P, ∀ l ∈ L, k * l * k⁻¹ ∈ L := fun k _ l hl => hLn.conj_mem l hl k
  intro p hp
  obtain ⟨l, hlL, hl⟩ := (endg_outerHom_eq_one_iff L P hnormal ⟨p, hp⟩).mp
    (endg_perfect_hom_trivial hP (endgOuterHom L P hnormal) ⟨p, hp⟩)
  set x : Mbar M Q := p * l⁻¹
  have hxH : x ∈ bar M Q (H0 M Z) :=
    (bar M Q (H0 M Z)).mul_mem (hPH hp) ((bar M Q (H0 M Z)).inv_mem (hLleH hlL))
  have hxcomm : ∀ y ∈ L, x * y = y * x := by
    intro y hy
    have hy' : l⁻¹ * y * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hlL) hy) hlL
    have hconj : x * y * x⁻¹ = y := by
      calc x * y * x⁻¹ = p * (l⁻¹ * y * l) * p⁻¹ := by simp [x, mul_assoc]
        _ = l * (l⁻¹ * y * l) * l⁻¹ := hl _ hy'
        _ = y := by group
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hconj]
  have hx1 : p * l⁻¹ = 1 := hc.eq_one_of_centralizes_layer h44 hw hn hno hgen hxH hxcomm
  rw [mul_inv_eq_one] at hx1
  rwa [hx1]

private theorem isPGroup_bar_CN [(Q.subgroupOf M).Normal] (hNt : StrothNtStatement)
    (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : t ∈ LB M Q B)
    (htQ : t ∉ Q) : IsPGroup 2 ↥(bar M Q (hc.CN t)) := by
  have hNbar2 : bar M Q (hc.CN t) = bar M Q (Nt M (LB M Q B) t) := by
    rw [← hNt G M Q Z B hc n H.width H.n_gt H.noA2 H.gen t ht htQ]
  have hNtM : Nt M (LB M Q B) t ≤ M :=
    (Subgroup.map_subtype_le (CFSG.pCore 2 ↥(Rt M (LB M Q B) t))).trans (hc.Rt_le_M t)
  have hNt2 : IsPGroup 2 ↥(bar M Q (Nt M (LB M Q B) t)) := by
    have h2 : IsPGroup 2 ↥((Nt M (LB M Q B) t).subgroupOf M) :=
      (isPGroup_inSubgroup_pCore 2 (Rt M (LB M Q B) t)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hNtM).symm
    exact h2.map (QuotientGroup.mk' (Q.subgroupOf M))
  rwa [hNbar2]

private theorem isPGroup_bar_CN_inf_layer [(Q.subgroupOf M).Normal]
    (hNt : StrothNtStatement) (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q) :
    IsPGroup 2 ↥(bar M Q (hc.CN t) ⊓ layer (Mbar M Q)) :=
  (isPGroup_bar_CN hNt hc H ht htQ).to_inf_left

private theorem eq_of_mem_bar_LB_inf_CN_of_conj_eq [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : t ∈ LB M Q B)
    (hU : bar M Q (hc.CN t) ⊓ layer (Mbar M Q) = ⊥) {x l : Mbar M Q}
    (hxA : x ∈ bar M Q (LB M Q B ⊓ hc.CN t)) (hlL : l ∈ layer (Mbar M Q))
    (hconj : ∀ y ∈ layer (Mbar M Q), x * y * x⁻¹ = l * y * l⁻¹) : x = 1 := by
  set L := layer (Mbar M Q) with hLdef
  haveI hLc : L.Characteristic := CFSG.LocalCores.layer_characteristic
  have hLleH : L ≤ bar M Q (H0 M Z) := hc.layer_le_bar_H0 h34 H.width H.n_gt H.noA2 H.gen
  have hAleNbar : bar M Q (LB M Q B ⊓ hc.CN t) ≤ bar M Q (hc.CN t) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_right)
  have hAleH : bar M Q (LB M Q B ⊓ hc.CN t) ≤ bar M Q (H0 M Z) :=
    (Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_left)).trans
      (hc.bar_LB_le_bar_Lgen.trans hc.bar_Lgen_le_bar_H0)
  set y : Mbar M Q := x * l⁻¹ with hydef
  have hyH : y ∈ bar M Q (H0 M Z) :=
    (bar M Q (H0 M Z)).mul_mem (hAleH hxA) ((bar M Q (H0 M Z)).inv_mem (hLleH hlL))
  have hycomm : ∀ z ∈ L, y * z = z * y := by
    intro z hz
    have hz' : l⁻¹ * z * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hlL) hz) hlL
    have hcj : y * z * y⁻¹ = z := by
      calc y * z * y⁻¹ = x * (l⁻¹ * z * l) * x⁻¹ := by simp [y, mul_assoc]
        _ = l * (l⁻¹ * z * l) * l⁻¹ := hconj _ hz'
        _ = z := by group
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hcj]
  have hy1 : y = 1 := hc.eq_one_of_centralizes_layer h44 H.width H.n_gt H.noA2 H.gen hyH hycomm
  have hxeq : x = l := by
    rw [hydef] at hy1
    exact mul_inv_eq_one.mp hy1
  have hxL : x ∈ L := by rw [hxeq]; exact hlL
  have hxU : x ∈ bar M Q (hc.CN t) ⊓ L := ⟨hAleNbar hxA, hxL⟩
  rw [hU] at hxU
  exact Subgroup.mem_bot.mp hxU

private theorem false_of_bar_CN_inf_layer_eq_bot [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : t ∈ LB M Q B)
    (htQ : t ∉ Q) {m : ℕ} (hm2 : 2 ≤ m) (hm : SLMNat hc t m)
    (hout : OutCyc ↥(layer (Mbar M Q)))
    (hU : bar M Q (hc.CN t) ⊓ layer (Mbar M Q) = ⊥) : False := by
  set A : Subgroup (Mbar M Q) := bar M Q (LB M Q B ⊓ hc.CN t) with hAdef
  have hswap := hc.swapHyp H.width H.n_gt H.noA2
  have hA2 : ∀ x : ↥A, x * x = 1 := by
    intro x
    have hmem : (x : Mbar M Q) ∈ bar M Q (LB M Q B) :=
      (Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_left)) x.2
    exact Subtype.ext (by simpa [pow_two] using hswap.sq (x : Mbar M Q) hmem)
  haveI hLc : (layer (Mbar M Q)).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLn : (layer (Mbar M Q)).Normal := inferInstance
  have hnormalA : ∀ k ∈ A, ∀ l ∈ layer (Mbar M Q), k * l * k⁻¹ ∈ layer (Mbar M Q) :=
    fun k _ l hl => hLn.conj_mem l hl k
  let f : ↥A →* Outer ↥(layer (Mbar M Q)) :=
    endgOuterHom (layer (Mbar M Q)) A hnormalA
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨l, hlL, hl⟩ :=
      (endg_outerHom_eq_one_iff (layer (Mbar M Q)) A hnormalA x).mp hx
    exact Subtype.ext (eq_of_mem_bar_LB_inf_CN_of_conj_eq h34 h44 hc H ht hU x.2 hlL hl)
  have h2 : Nat.card ↥A ≤ 2 := by
    have h := card_range_le_two_of_outCyc hout hA2 f
    rwa [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv] at h
  have h16 : 16 ≤ Nat.card ↥A := by
    have hpow : Nat.card Z ^ m ≤ Nat.card ↥A :=
      H.pow_le_card_bar_LB_inf_CN h34 ht htQ hm2 hm
    have h4m : 16 ≤ Nat.card Z ^ m := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ Nat.card Z ^ 2 := Nat.pow_le_pow_left hc.hyp.q4 2
        _ ≤ Nat.card Z ^ m := Nat.pow_le_pow_right (by have := hc.hyp.q4; omega) hm2
    exact h4m.trans hpow
  omega

private theorem le_normalizer_bar_CN_inf_layer [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {P : Subgroup (Mbar M Q)}
    (hPR : P ≤ bar M Q (Rt M (LB M Q B) t)) (hPL : P ≤ layer (Mbar M Q)) :
    P ≤ Subgroup.normalizer
      ((bar M Q (hc.CN t) ⊓ layer (Mbar M Q) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
  haveI hLn : (layer (Mbar M Q)).Normal := by
    haveI : (layer (Mbar M Q)).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact ⟨hc.bar_CN_conj_mem ht (hPR hp) hu.1, hLn.conj_mem u hu.2 p⟩
  · intro hu
    have hp' : p⁻¹ ∈ P := P.inv_mem hp
    have hconj : p⁻¹ * (p * u * p⁻¹) * (p⁻¹)⁻¹ ∈
        bar M Q (hc.CN t) ⊓ layer (Mbar M Q) :=
      ⟨hc.bar_CN_conj_mem ht (hPR hp') hu.1, hLn.conj_mem (p * u * p⁻¹) hu.2 p⁻¹⟩
    simpa [mul_assoc] using hconj

private theorem isSolvable_of_le_normalizer_bar_CN_inf_layer [(Q.subgroupOf M).Normal]
    (hB : fusionIsBenderGroup ↥(layer (Mbar M Q)))
    (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {P : Subgroup (Mbar M Q)}
    (hPR : P ≤ bar M Q (Rt M (LB M Q B) t)) (hPL : P ≤ layer (Mbar M Q))
    (hU2 : IsPGroup 2 ↥(bar M Q (hc.CN t) ⊓ layer (Mbar M Q)))
    (hU : bar M Q (hc.CN t) ⊓ layer (Mbar M Q) ≠ ⊥) : Group.IsSolvable ↥P := by
  have hPnormU := le_normalizer_bar_CN_inf_layer hc ht hPR hPL
  have hUL : bar M Q (hc.CN t) ⊓ layer (Mbar M Q) ≤ layer (Mbar M Q) := inf_le_right
  have hΛ : P.subgroupOf (layer (Mbar M Q)) ≤ Subgroup.normalizer
      ((bar M Q (hc.CN t) ⊓ layer (Mbar M Q)).subgroupOf (layer (Mbar M Q)) :
        Set ↥(layer (Mbar M Q))) := by
    have h := Subgroup.subgroupOf_mono (layer (Mbar M Q)) hPnormU
    rwa [Subgroup.subgroupOf_normalizer_eq hUL] at h
  have hU2' : IsPGroup 2
      ↥((bar M Q (hc.CN t) ⊓ layer (Mbar M Q)).subgroupOf (layer (Mbar M Q))) :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm
  have hU1' : (bar M Q (hc.CN t) ⊓ layer (Mbar M Q)).subgroupOf
      (layer (Mbar M Q)) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff_inf_le, inf_eq_left.mpr hUL, le_bot_iff] at hbot
    exact hU hbot
  haveI : Group.IsSolvable
      ↥(P.subgroupOf (layer (Mbar M Q))) :=
    CFSG.QuasithinUnique.A5.C25.solvable_of_bender hB hU2' hU1' hΛ
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hPL).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hPL).symm.injective

private theorem false_of_bar_CN_inf_layer_ne_bot [(Q.subgroupOf M).Normal]
    (hNt : StrothNtStatement)
    (hB : fusionIsBenderGroup ↥(layer (Mbar M Q))) (hc : Ctx M Q Z B) {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q)
    {P : Subgroup (Mbar M Q)} (hPR : P ≤ bar M Q (Rt M (LB M Q B) t))
    (hPL : P ≤ layer (Mbar M Q)) (hPperf : ⁅P, P⁆ = P) (hPne : P ≠ ⊥)
    (hU : bar M Q (hc.CN t) ⊓ layer (Mbar M Q) ≠ ⊥) : False := by
  haveI hPsolv : Group.IsSolvable ↥P :=
    isSolvable_of_le_normalizer_bar_CN_inf_layer hB hc ht hPR hPL
      (isPGroup_bar_CN_inf_layer hNt hc H ht htQ) hU
  haveI hPperfI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPperf
  haveI hPnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  exact Group.IsPerfect.not_isSolvable ↥P hPsolv

theorem Sec10Hyp.false_of_bender_layer [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement) (hNt : StrothNtStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    (hB : fusionIsBenderGroup ↥(layer (Mbar M Q))) (hout : OutCyc ↥(layer (Mbar M Q))) :
    False := by
  obtain ⟨t, ht, htQ, hsl⟩ := H.ex
  obtain ⟨m, hm2, hm⟩ := hsl.exists_SLMNat
  obtain ⟨P, hPR, hPperf, hPne⟩ := hc.exists_perfect_le_bar_Rt ht hm2 hm
  have hRleH : bar M Q (Rt M (LB M Q B) t) ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr
        (hc.Lgen_le_H0_sec4x ((Rt_le_Lgen' M (LB M Q B) t) (Subgroup.mem_subgroupOf.mp hx)))
  have hPL : P ≤ layer (Mbar M Q) :=
    hc.le_layer_of_perfect h34 h44 H.width H.n_gt H.noA2 H.gen hB (hPR.trans hRleH) hPperf
  by_cases hU : bar M Q (hc.CN t) ⊓ layer (Mbar M Q) = ⊥
  · exact false_of_bar_CN_inf_layer_eq_bot h34 h44 hc H ht htQ hm2 hm hout hU
  · exact false_of_bar_CN_inf_layer_ne_bot hNt hB hc H ht htQ hPR hPL hPperf hPne hU

end CFSG.RankThree.GF2n.Stroth80
