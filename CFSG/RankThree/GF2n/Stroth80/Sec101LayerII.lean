module

public import CFSG.RankThree.GF2n.Stroth80.Sec101LayerIII
public import CFSG.RankThree.GF2n.Stroth80.Sec101Cent
public import CFSG.RankThree.GF2n.Stroth80.Sec101SL2Aut
public import CFSG.RankThree.GF2n.Stroth80.Sec101SatRoots
public import CFSG.RankThree.GF2n.Stroth80.Sec45

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem le_normalizer_of_le_normalizer_of_sup_eq_layer {Γ : Type} [Group Γ]
    [Finite Γ] {Λ X Y : Subgroup Γ}
    (hN : Λ ≤ Subgroup.normalizer (Y : Set Γ)) (hXY : X ⊔ Y = layer Γ)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXc : IsComponent X) (hYc : IsComponent Y) (hXYne : X ≠ Y) :
    Λ ≤ Subgroup.normalizer (X : Set Γ) := by
  intro e he
  have hconj : conjSubgroup e X = X := by
    rcases eq_or_eq_of_sup_eq_layer hXY hcomm hXc hYc
      (isComponent_conjSubgroup e hXc) with h | h
    · exact h
    · exfalso
      have hYconj : conjSubgroup e Y = Y := conjSubgroup_eq_self_iff.mpr (hN he)
      have h1 : conjSubgroup e X = conjSubgroup e Y := by rw [h, hYconj]
      have h2 := congrArg (conjSubgroup e⁻¹) h1
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, ← conjSubgroup_mul,
        inv_mul_cancel, conjSubgroup_one] at h2
      exact hXYne h2
  exact conjSubgroup_eq_self_iff.mp hconj

private theorem inf_normalizer_le_normalizer_of_conj_eq {Γ : Type} [Group Γ]
    {Λ X Y : Subgroup Γ} {s : Γ} (hΛ : SwapHyp Γ Λ) (hs : s ∈ Λ)
    (hYX : conjSubgroup s Y = X) :
    Λ ⊓ Subgroup.normalizer (Y : Set Γ) ≤ Subgroup.normalizer (X : Set Γ) := by
  intro e he
  have hconj : conjSubgroup e X = X := by
    calc conjSubgroup e X = conjSubgroup e (conjSubgroup s Y) := by rw [← hYX]
      _ = conjSubgroup (e * s) Y := (conjSubgroup_mul e s Y).symm
      _ = conjSubgroup (s * e) Y := by rw [hΛ.comm e he.1 s hs]
      _ = conjSubgroup s (conjSubgroup e Y) := conjSubgroup_mul s e Y
      _ = conjSubgroup s Y := by rw [conjSubgroup_eq_self_iff.mpr he.2]
      _ = X := hYX
  exact conjSubgroup_eq_self_iff.mp hconj

private theorem bar_inf_CN_comm_of_component [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : t ∈ LB M Q B) (hcs : CompSimple (Mbar M Q))
    {X : Subgroup (Mbar M Q)} (hXc : IsComponent X)
    (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hNX : bar M Q (LB M Q B) ≤ Subgroup.normalizer (X : Set (Mbar M Q))) :
    ∀ e ∈ bar M Q (LB M Q B ⊓ hc.CN t), ∀ x ∈ X, e * x = x * e := by
  intro e he x hx
  have heΛ : e ∈ bar M Q (LB M Q B) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_left) he
  have heCN : e ∈ bar M Q (hc.CN t) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_right) he
  have hXmem : ⁅e, x⁆ ∈ X := by
    rw [commutatorElement_def]
    have hex : e * x * e⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hNX heΛ) x).mp hx
    exact X.mul_mem hex (X.inv_mem hx)
  have hCNmem : ⁅e, x⁆ ∈ bar M Q (hc.CN t) := by
    have h1 : x * e * x⁻¹ ∈ bar M Q (hc.CN t) :=
      hc.bar_CN_conj_mem ht (hXR hx) heCN
    have h2 : x * e⁻¹ * x⁻¹ ∈ bar M Q (hc.CN t) := by
      have := (bar M Q (hc.CN t)).inv_mem h1
      simpa [mul_inv_rev, mul_assoc] using this
    have h3 := (bar M Q (hc.CN t)).mul_mem heCN h2
    simpa [commutatorElement_def, mul_assoc] using h3
  have hmem : ⁅e, x⁆ ∈ X ⊓ bar M Q (hc.CN t) := ⟨hXmem, hCNmem⟩
  rw [hc.component_inf_CN_eq_bot h34 H.width H.n_gt H.noA2 H.gen hcs ht hXc hXR] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

private theorem inf_centralizer_eq_bot_of_le_bar_LB [(Q.subgroupOf M).Normal]
    (h44 : Stroth44Statement) (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    {E X Y : Subgroup (Mbar M Q)} (hE : E ≤ bar M Q (LB M Q B))
    (hXY : X ⊔ Y = layer (Mbar M Q)) :
    E ⊓ Subgroup.centralizer (Y : Set (Mbar M Q)) ⊓
      Subgroup.centralizer (X : Set (Mbar M Q)) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨⟨hzE, hzY⟩, hzX⟩
  refine hc.eq_one_of_centralizes_layer h44 H.width H.n_gt H.noA2 H.gen ?_ ?_
  · exact (hc.bar_LB_le_bar_Lgen.trans hc.bar_Lgen_le_bar_H0) (hE hzE)
  · intro y hy
    have hXle : X ≤ Subgroup.centralizer ({z} : Set (Mbar M Q)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzX x hx
    have hYle : Y ≤ Subgroup.centralizer ({z} : Set (Mbar M Q)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzY y hy
    rw [← hXY] at hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hXle hYle hy)).symm

private theorem false_of_bar_inf_CN_of_normal [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n) {X Y : Subgroup (Mbar M Q)}
    (hXY : X ⊔ Y = layer (Mbar M Q))
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXc : IsComponent X) (hYc : IsComponent Y) (hXYne : X ≠ Y)
    (hYSL : IsSLModel 2 (Nat.card Z) ↥Y)
    (hN : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Y : Set (Mbar M Q)))
    {r : ℕ} (hr : 2 ≤ r) (hZr : Nat.card Z = 2 ^ r) {t : G} (htLB : t ∈ LB M Q B)
    (htQ : t ∉ Q) {m : ℕ} (hm2 : 2 ≤ m) (hm : SLMNat hc t m)
    (hXR : X ≤ bar M Q (Rt M (LB M Q B) t)) : False := by
  have hcs : CompSimple (Mbar M Q) := hc.compSimple h34 h44 H.width H.n_gt H.noA2 H.gen
  have hΛ : SwapHyp (Mbar M Q) (bar M Q (LB M Q B)) :=
    hc.swapHyp H.width H.n_gt H.noA2
  set E : Subgroup (Mbar M Q) := bar M Q (LB M Q B ⊓ hc.CN t) with hEdef
  have hEΛ : E ≤ bar M Q (LB M Q B) := by
    rw [hEdef]; exact Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_left)
  have hE2 : ∀ x ∈ E, x * x = 1 :=
    fun x hx => by simpa [pow_two] using hΛ.sq x (hEΛ hx)
  have hpow : Nat.card Z ^ m ≤ Nat.card ↥E := by
    rw [hEdef]
    exact H.pow_le_card_bar_LB_inf_CN h34 htLB htQ hm2 hm
  have hNX : bar M Q (LB M Q B) ≤ Subgroup.normalizer (X : Set (Mbar M Q)) :=
    le_normalizer_of_le_normalizer_of_sup_eq_layer hN hXY hcomm hXc hYc hXYne
  have hEX : ∀ e ∈ E, ∀ x ∈ X, e * x = x * e := by
    rw [hEdef]
    exact bar_inf_CN_comm_of_component h34 hc H htLB hcs hXc hXR hNX
  have hbot3 : E ⊓ Subgroup.centralizer (Y : Set (Mbar M Q)) ⊓
      Subgroup.centralizer (X : Set (Mbar M Q)) = ⊥ :=
    inf_centralizer_eq_bot_of_le_bar_LB h44 hc H hEΛ hXY
  have hbot : E ⊓ Subgroup.centralizer (Y : Set (Mbar M Q)) = ⊥ := by
    rw [eq_bot_iff] at hbot3 ⊢
    intro z hz
    exact hbot3 ⟨hz, fun x hx => (hEX z hz.1 x hx).symm⟩
  have hcard : Nat.card ↥E ≤
      2 ^ r * Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set (Mbar M Q))) :=
    card_le_mul_card_inf_centralizer_of_sl2 hr (hZr ▸ hYSL) (hEΛ.trans hN) hE2
  rw [hbot, Subgroup.card_bot, mul_one] at hcard
  have hcardZ : Nat.card ↥E ≤ Nat.card Z := by simpa [hZr] using hcard
  have hqm : Nat.card Z ^ m ≤ Nat.card Z := hpow.trans hcardZ
  have hq4 := hc.hyp.q4
  have hpow2 : Nat.card Z ^ 2 ≤ Nat.card Z ^ m :=
    Nat.pow_le_pow_right (by omega) hm2
  have h22 : Nat.card Z ^ 2 ≤ Nat.card Z := hpow2.trans hqm
  nlinarith

theorem Sec10Hyp.false_of_sl2_factor_normal [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X Y : Subgroup (Mbar M Q)} (hXY : X ⊔ Y = layer (Mbar M Q))
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (hXq : CFSG.IsQuasisimple ↥X)
    (hYSL : IsSLModel 2 (Nat.card Z) ↥Y)
    (hN : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Y : Set (Mbar M Q))) : False := by
  obtain ⟨r, -, hZr, -⟩ := hc.hyp.cp
  have h4q : 4 ≤ 2 ^ r := by rw [← hZr]; exact hc.hyp.q4
  have hr : 2 ≤ r := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by
    calc 2 ^ 2 = 4 := by norm_num
      _ ≤ 2 ^ r := h4q)
  obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hZr ▸ hYSL
  have hYq : CFSG.IsQuasisimple ↥Y :=
    CFSG.IsQuasisimple.of_mulEquiv e
      (@statedSL_quasisimple_of_card 2 K hF hFin le_rfl (by rw [hK]; exact h4q))
  have hcomm' : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x :=
    fun x hx y hy => (hcomm x hx y hy).eq
  have hXc : IsComponent X := isComponent_of_sup_eq_layer hXY hcomm' hXq
  have hYc : IsComponent Y :=
    isComponent_of_sup_eq_layer (by rw [sup_comm]; exact hXY)
      (fun y hy x hx => (hcomm' x hx y hy).symm) hYq
  have hXYne : X ≠ Y := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hXc
    exact hab (Subtype.ext (hcomm' a.1 a.2 b.1 b.2))
  have hcs : CompSimple (Mbar M Q) := hc.compSimple h34 h44 H.width H.n_gt H.noA2 H.gen
  have hΛ : SwapHyp (Mbar M Q) (bar M Q (LB M Q B)) :=
    hc.swapHyp H.width H.n_gt H.noA2
  have hne : bar M Q (LB M Q B) ⊓ Y ≠ ⊥ :=
    hc.inter_bar_LB_ne_bot h34 H.width H.n_gt H.noA2 H.gen hYq hN
  obtain ⟨tbar, htbar1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have htbarΛ : (tbar : Mbar M Q) ∈ bar M Q (LB M Q B) := tbar.2.1
  have htbar1' : (tbar : Mbar M Q) ≠ 1 := fun h => htbar1 (Subtype.ext h)
  obtain ⟨t, htLB, htQ, htx⟩ := hc.exists_lift_ne_one htbarΛ htbar1'
  have hcentX : ∀ x ∈ X, x * (QuotientGroup.mk t : Mbar M Q) =
      (QuotientGroup.mk t : Mbar M Q) * x := by
    intro x hx
    rw [htx]
    exact hcomm' x hx (tbar : Mbar M Q) tbar.2.2
  have hXR : X ≤ bar M Q (Rt M (LB M Q B) (t : G)) :=
    hc.component_le_bar_Rt h34 H.width H.n_gt H.noA2 H.gen hcs hXc htLB hcentX
  obtain ⟨m, hm2, hm⟩ :=
    H.exists_SLMNat_of_le_bar_Rt htLB htQ hXR (exists_noncomm_of_isComponent hXc)
  exact false_of_bar_inf_CN_of_normal h34 h44 hc H hXY hcomm' hXc hYc hXYne hYSL hN
    hr hZr htLB htQ hm2 hm hXR

private theorem false_of_inf_normalizer_of_swap [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    (hc : Ctx M Q Z B)
    {n : ℕ} (H : Sec10Hyp hc n) {X Y : Subgroup (Mbar M Q)}
    (hXY : X ⊔ Y = layer (Mbar M Q))
    (hYc : IsComponent Y)
    (hYSL : IsSLModel 2 (Nat.card Z) ↥Y) {r : ℕ}
    (hXSL : IsSLModel 2 (2 ^ r) ↥X)
    (hΛ : SwapHyp (Mbar M Q) (bar M Q (LB M Q B)))
    (hcs : CompSimple (Mbar M Q)) {s : Mbar M Q}
    (hsΛ : s ∈ bar M Q (LB M Q B)) (hne : conjSubgroup s Y ≠ Y)
    (hYX : conjSubgroup s Y = X) (hr : 2 ≤ r) (hZr : Nat.card Z = 2 ^ r) : False := by
  set E : Subgroup (Mbar M Q) :=
    bar M Q (LB M Q B) ⊓ Subgroup.normalizer (Y : Set (Mbar M Q)) with hEdef
  have hEΛ : E ≤ bar M Q (LB M Q B) := by rw [hEdef]; exact inf_le_left
  have hENY : E ≤ Subgroup.normalizer (Y : Set (Mbar M Q)) := by
    rw [hEdef]; exact inf_le_right
  have hE2 : ∀ x ∈ E, x * x = 1 :=
    fun x hx => by simpa [pow_two] using hΛ.sq x (hEΛ hx)
  have hcardΛ : Nat.card ↥(bar M Q (LB M Q B)) = 2 * Nat.card ↥E := by
    simpa [hEdef] using swap_card_eq_two_mul hΛ hcs hYc hsΛ hne
  have hbar : Nat.card ↥(bar M Q (LB M Q B)) = Nat.card Z ^ (n - 1) :=
    hc.card_bar_LB_of_34 h34 H.width H.n_gt H.noA2 H.gen
  have hNX : E ≤ Subgroup.normalizer (X : Set (Mbar M Q)) :=
    inf_normalizer_le_normalizer_of_conj_eq hΛ hsΛ hYX
  set E₁ : Subgroup (Mbar M Q) :=
    E ⊓ Subgroup.centralizer (Y : Set (Mbar M Q)) with hE₁def
  have hE₁E : E₁ ≤ E := by rw [hE₁def]; exact inf_le_left
  have hE₁2 : ∀ x ∈ E₁, x * x = 1 := fun x hx => hE2 x (hE₁E hx)
  have hE₁NX : E₁ ≤ Subgroup.normalizer (X : Set (Mbar M Q)) :=
    hE₁E.trans hNX
  have hcardY : Nat.card ↥E ≤ 2 ^ r * Nat.card ↥E₁ := by
    rw [hE₁def]
    exact card_le_mul_card_inf_centralizer_of_sl2 hr (hZr ▸ hYSL) hENY hE2
  have hcardX : Nat.card ↥E₁ ≤ 2 ^ r *
      Nat.card ↥(E₁ ⊓ Subgroup.centralizer (X : Set (Mbar M Q))) :=
    card_le_mul_card_inf_centralizer_of_sl2 hr hXSL hE₁NX hE₁2
  have hbot : E₁ ⊓ Subgroup.centralizer (X : Set (Mbar M Q)) = ⊥ := by
    rw [hE₁def]
    exact inf_centralizer_eq_bot_of_le_bar_LB h44 hc H hEΛ hXY
  rw [hbot, Subgroup.card_bot, mul_one] at hcardX
  have hcardE : Nat.card ↥E ≤ 2 ^ r * 2 ^ r := by
    calc Nat.card ↥E ≤ 2 ^ r * Nat.card ↥E₁ := hcardY
      _ ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul_left _ hcardX
  have hn1 : 3 ≤ n - 1 := by have := H.four_le h34; omega
  have hle : Nat.card Z ^ 3 ≤ 2 * (2 ^ r * 2 ^ r) := by
    calc Nat.card Z ^ 3 ≤ Nat.card Z ^ (n - 1) :=
          Nat.pow_le_pow_right (by rw [hZr]; positivity) hn1
      _ = Nat.card ↥(bar M Q (LB M Q B)) := hbar.symm
      _ = 2 * Nat.card ↥E := hcardΛ
      _ ≤ 2 * (2 ^ r * 2 ^ r) := Nat.mul_le_mul_left 2 hcardE
  rw [← hZr] at hle
  have hq4 := hc.hyp.q4
  nlinarith

theorem Sec10Hyp.false_of_sl2_factor_swap [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X Y : Subgroup (Mbar M Q)} (hXY : X ⊔ Y = layer (Mbar M Q))
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (hXq : CFSG.IsQuasisimple ↥X)
    (hYSL : IsSLModel 2 (Nat.card Z) ↥Y)
    (hN : ¬ bar M Q (LB M Q B) ≤ Subgroup.normalizer (Y : Set (Mbar M Q))) : False := by
  obtain ⟨r, -, hZr, -⟩ := hc.hyp.cp
  have h4q : 4 ≤ 2 ^ r := by rw [← hZr]; exact hc.hyp.q4
  have hr : 2 ≤ r := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by
    calc 2 ^ 2 = 4 := by norm_num
      _ ≤ 2 ^ r := h4q)
  obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hZr ▸ hYSL
  have hYq : CFSG.IsQuasisimple ↥Y :=
    CFSG.IsQuasisimple.of_mulEquiv e
      (@statedSL_quasisimple_of_card 2 K hF hFin le_rfl (by rw [hK]; exact h4q))
  have hcomm' : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x :=
    fun x hx y hy => (hcomm x hx y hy).eq
  have hXc : IsComponent X := isComponent_of_sup_eq_layer hXY hcomm' hXq
  have hYc : IsComponent Y :=
    isComponent_of_sup_eq_layer (by rw [sup_comm]; exact hXY)
      (fun y hy x hx => (hcomm' x hx y hy).symm) hYq
  have hXYne : X ≠ Y := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hXc
    exact hab (Subtype.ext (hcomm' a.1 a.2 b.1 b.2))
  have hcs : CompSimple (Mbar M Q) := hc.compSimple h34 h44 H.width H.n_gt H.noA2 H.gen
  have hΛ : SwapHyp (Mbar M Q) (bar M Q (LB M Q B)) :=
    hc.swapHyp H.width H.n_gt H.noA2
  obtain ⟨s, hsΛ, hsN⟩ := Set.not_subset.mp hN
  have hne : conjSubgroup s Y ≠ Y := fun h => hsN (conjSubgroup_eq_self_iff.mp h)
  have hYX : conjSubgroup s Y = X := by
    rcases eq_or_eq_of_sup_eq_layer hXY hcomm' hXc hYc
      (isComponent_conjSubgroup s hYc) with h | h
    · exact h
    · exact (hne h).elim
  have hXSL : IsSLModel 2 (2 ^ r) ↥X :=
    hYX ▸ isSLModel_conjSubgroup (hZr ▸ hYSL) s
  exact false_of_inf_normalizer_of_swap h34 h44 hc H hXY hYc hYSL hXSL hΛ hcs hsΛ
    hne hYX hr hZr

theorem Sec10Hyp.isQuasisimple_layer [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (h44 : Stroth44Statement) (h45 : Stroth45Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) :
    CFSG.IsQuasisimple ↥(layer (Mbar M Q)) := by
  obtain ⟨-, hq | ⟨X, Y, hXY, -, hcomm, hXq, hYSL⟩ |
      ⟨X₁, X₂, X₃, -, -, -, hc12, hc3, -, -, -, h1, h2, h3⟩⟩ :=
    h45 G M Q Z B hc n H.width H.n_gt H.noA2 H.gen
  · exact hq
  · by_cases hN : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Y : Set (Mbar M Q))
    · exact (H.false_of_sl2_factor_normal h34 h44 hXY hcomm hXq hYSL hN).elim
    · exact (H.false_of_sl2_factor_swap h34 h44 hXY hcomm hXq hYSL hN).elim
  · exact (H.false_of_three_factors h34 h44 hc12 hc3 h1 h2 h3).elim

end CFSG.RankThree.GF2n.Stroth80
