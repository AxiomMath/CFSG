module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma4
public import CFSG.Quasithin.Background.G2L2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

section TwoGroup

variable {G : Type*} [Group G] [Finite G]

theorem zpowers_eq_of_card_eq_two {D : Subgroup G} (hD : Nat.card D = 2) {d : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) : Subgroup.zpowers d = D := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd) ?_
  rw [hD, Nat.card_zpowers]
  have h2 : orderOf d ∣ 2 := by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : D)
    rwa [hD, Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hd1
  · exact h.ge

theorem le_centralizer_normalizer_of_card_eq_two {D : Subgroup G} (hD : Nat.card D = 2) :
    D ≤ Subgroup.centralizer (Subgroup.normalizer (D : Set G) : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hd1 : d = 1
  · rw [hd1, one_mul, mul_one]
  · have h1 : g * d * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hg d).1 hd
    have h2 : g * d * g⁻¹ ≠ 1 := fun h => hd1 (by
      have := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using this)
    have e := SteinbergBS.eq_of_card_le_two hD.le h1 hd h2 hd1
    calc g * d = (g * d * g⁻¹) * g := by group
      _ = d * g := by rw [e]

theorem exists_extraspecial_sup_centerOf {U D : Subgroup G} (hU : IsPGroup 2 U) (hDU : D ≤ U)
    (hD2 : Nat.card D = 2) (hDc : D ≤ Subgroup.centralizer (U : Set G))
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ D) (hsq : ∀ x ∈ U, x ^ 2 ∈ D)
    (hnab : ∃ x ∈ U, ∃ y ∈ U, x * y ≠ y * x) :
    ∃ U₀ : Subgroup G, U₀ ≤ U ∧ IsExtraspecialPGroup 2 ↥U₀ ∧ frattiniOf U₀ = D ∧
      U₀ ⊔ centerOf U = U ∧ U₀ ⊓ centerOf U = D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZU : centerOf U ≤ U := inf_le_left
  have hUZ : U ≤ Subgroup.normalizer (centerOf U : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hc : u * z = z * u := Subgroup.mem_centralizer_iff.1 hz.2 u hu
      rw [show u * z * u⁻¹ = z by rw [hc]; group]
      exact hz
    · intro hz
      have hc : u * (u * z * u⁻¹) = (u * z * u⁻¹) * u := Subgroup.mem_centralizer_iff.1 hz.2 u hu
      have e : u * z * u⁻¹ = z := by
        calc u * z * u⁻¹ = u⁻¹ * (u * (u * z * u⁻¹)) := by group
          _ = u⁻¹ * ((u * z * u⁻¹) * u) := by rw [hc]
          _ = z := by group
      rw [e] at hz
      exact hz
  obtain ⟨U₀, ⟨hU₀U, hU₀sup⟩, hmin⟩ := Set.exists_min_image
    {K : Subgroup G | K ≤ U ∧ K ⊔ centerOf U = U} (fun K => Nat.card K) (Set.toFinite _)
    ⟨U, le_rfl, sup_eq_left.2 hZU⟩
  have hdec : ∀ x ∈ U, ∃ k ∈ U₀, ∃ z ∈ centerOf U, k * z = x := by
    intro x hx
    have hx' : x ∈ ((U₀ ⊔ centerOf U : Subgroup G) : Set G) := by
      rw [hU₀sup]
      exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hU₀U.trans hUZ)] at hx'
    exact Set.mem_mul.1 hx'
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ U₀, ∃ b ∈ U₀, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    obtain ⟨k, hk, z, hz, rfl⟩ := hdec x hx
    obtain ⟨k', hk', z', hz', rfl⟩ := hdec y hy
    refine ⟨k, hk, k', hk', fun h => hxy ?_⟩
    have hz1 : ∀ g ∈ U, g * z = z * g := fun g hg => Subgroup.mem_centralizer_iff.1 hz.2 g hg
    have hz2 : ∀ g ∈ U, g * z' = z' * g := fun g hg => Subgroup.mem_centralizer_iff.1 hz'.2 g hg
    have e1 : k * z * (k' * z') = k * k' * (z * z') := by
      calc k * z * (k' * z') = k * (z * k') * z' := by group
        _ = k * (k' * z) * z' := by rw [← hz1 k' (hU₀U hk')]
        _ = k * k' * (z * z') := by group
    have e2 : k' * z' * (k * z) = k' * k * (z * z') := by
      calc k' * z' * (k * z) = k' * (z' * k) * z := by group
        _ = k' * (k * z') * z := by rw [← hz2 k (hU₀U hk)]
        _ = k' * k * (z' * z) := by group
        _ = k' * k * (z * z') := by rw [hz1 z' hz'.1]
    rw [e1, e2, h]
  have hd1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := fun h => hab (by
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h, one_mul])
  have hDU₀ : D ≤ U₀ := by
    rw [← zpowers_eq_of_card_eq_two hD2 (hcomm a (hU₀U ha) b (hU₀U hb)) hd1,
      Subgroup.zpowers_le]
    exact U₀.mul_mem (U₀.mul_mem (U₀.mul_mem ha hb) (U₀.inv_mem ha)) (U₀.inv_mem hb)
  have hU₀p : IsPGroup 2 ↥U₀ := hU.to_le hU₀U
  have : Fact (IsPGroup 2 ↥U₀) := ⟨hU₀p⟩
  have hcommU₀ : ∀ x y : ↥U₀, ((⁅x, y⁆ : ↥U₀) : G) ∈ D := by
    intro x y
    have e : ((⁅x, y⁆ : ↥U₀) : G) = (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ := by
      simp [commutatorElement_def]
    rw [e]
    exact hcomm _ (hU₀U x.2) _ (hU₀U y.2)
  have hΦD : frattini ↥U₀ ≤ D.subgroupOf U₀ := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (hx | ⟨y, rfl⟩)
    · have hle : commutator ↥U₀ ≤ D.subgroupOf U₀ := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro x _ y _
        exact Subgroup.mem_subgroupOf.2 (hcommU₀ x y)
      exact hle hx
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact hsq _ (hU₀U y.2)
  have hKΦ : (centerOf U).subgroupOf U₀ ≤ frattini ↥U₀ := by
    show _ ≤ ⨅ a ∈ {H : Subgroup ↥U₀ | IsCoatom H}, a
    refine le_iInf₂ fun M hM => ?_
    by_contra hKM
    have hsup : M ⊔ (centerOf U).subgroupOf U₀ = ⊤ :=
      hM.2 _ (lt_of_le_of_ne le_sup_left fun h => hKM (h ▸ le_sup_right))
    have hM'U : M.map U₀.subtype ≤ U := (Subgroup.map_subtype_le M).trans hU₀U
    have hU₀le : U₀ ≤ M.map U₀.subtype ⊔ centerOf U := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥U₀) ∈ M ⊔ (centerOf U).subgroupOf U₀ := hsup ▸ Subgroup.mem_top _
      have h1 := Subgroup.mem_map_of_mem U₀.subtype hx'
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype] at h1
      have hle : M.map U₀.subtype ⊔ centerOf U ⊓ U₀ ≤ M.map U₀.subtype ⊔ centerOf U :=
        sup_le_sup_left inf_le_left _
      exact hle h1
    have hM' : M.map U₀.subtype ⊔ centerOf U = U := by
      refine le_antisymm (sup_le hM'U hZU) ?_
      calc U = U₀ ⊔ centerOf U := hU₀sup.symm
        _ ≤ M.map U₀.subtype ⊔ centerOf U := sup_le hU₀le le_sup_right
    have h1 := hmin _ ⟨hM'U, hM'⟩
    rw [Subgroup.card_map_of_injective U₀.subtype_injective] at h1
    have h2 : Nat.card M < Nat.card ↥U₀ := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hM.1)
      rwa [Subgroup.card_top] at this
    exact absurd h1 (not_le.2 h2)
  have hinf : U₀ ⊓ centerOf U = D := by
    refine le_antisymm (fun x hx => ?_) (le_inf hDU₀ (le_inf hDU hDc))
    have h1 : (⟨x, hx.1⟩ : ↥U₀) ∈ (centerOf U).subgroupOf U₀ := Subgroup.mem_subgroupOf.2 hx.2
    exact Subgroup.mem_subgroupOf.1 (hΦD (hKΦ h1))
  have hZc' : D.subgroupOf U₀ ≤ Subgroup.center ↥U₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.1 (hDc (Subgroup.mem_subgroupOf.1 hx)) y (hU₀U y.2)
  have hext : IsExtraspecialPGroup 2 ↥U₀ :=
    CFSG.RankThree.PartOne.PlaneCommuting.isExtraspecialPGroup_of_pairing hU₀p
      (Z := D.subgroupOf U₀) ?_ hZc' ?_ ?_ ?_ ?_
  · refine ⟨U₀, hU₀U, hext, ?_, hU₀sup, hinf⟩
    have hΦ : frattini ↥U₀ = D.subgroupOf U₀ := le_antisymm hΦD (hext.2.2.1 ▸ hZc')
    show (frattini ↥U₀).map U₀.subtype = D
    rw [hΦ, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hDU₀]
  · rw [← hD2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDU₀).toEquiv
  · intro x y
    exact Subgroup.mem_subgroupOf.2 (hcommU₀ x y)
  · intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hsq _ (hU₀U x.2)
  · intro x hx
    rw [Subgroup.mem_subgroupOf, ← hinf]
    refine ⟨x.2, hU₀U x.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨k, hk, z, hz, rfl⟩ := hdec y hy
    have h1 := congrArg Subtype.val (hx ⟨k, hk⟩)
    simp only [Subgroup.coe_mul] at h1
    have hz' : (x : G) * z = z * x := Subgroup.mem_centralizer_iff.1 hz.2 _ (hU₀U x.2)
    calc k * z * (x : G) = k * (z * x) := by group
      _ = k * (x * z) := by rw [hz']
      _ = k * x * z := by group
      _ = x * k * z := by rw [h1]
      _ = x * (k * z) := by group
  · refine ⟨⟨a, ha⟩, fun h => hab ?_⟩
    have := Subgroup.mem_centralizer_iff.1 (hDc (Subgroup.mem_subgroupOf.1 h)) b (hU₀U hb)
    exact this.symm

end TwoGroup

section Lemma8

variable {G : Type} [Group G] [Finite G]

theorem isHzOne_normalizer (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    IsHzOne T L V₁ (Subgroup.normalizer (V₁ : Set G)) := by
  have hlOne : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  refine ⟨⟨sup_le (hlOne.trans inf_le_right) hV₁.2.2, fun hb => ?_⟩, le_rfl,
    lemma12_8_3_four h12213 h hV₁⟩
  have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ (IsPGroup.of_card hV₁.2.1)
  rw [hb, le_bot_iff] at h1
  have h2 := hV₁.2.1
  rw [h1, Subgroup.card_bot] at h2
  norm_num at h2

theorem Setting1282One.almostSpecial (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    AlmostSpecialHyp V V₁ L T (Subgroup.normalizer (V₁ : Set G)) :=
  lemma12_8_4_one h1222 hs.hyp hs.v1 (isHzOne_normalizer h12213 hs.hyp hs.v1)

theorem Setting1282One.exists_mul_ne {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) :
    ∃ x ∈ u128 V V₁, ∃ y ∈ u128 V V₁, x * y ≠ y * x := by
  by_contra hall
  push Not at hall
  exact hs.nonabelian ⟨⟨fun a b => Subtype.ext (hall a a.2 b b.2)⟩⟩

theorem Setting1282One.le_centerOf (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    V₁ ≤ zU128 V V₁ := by
  have hA := hs.almostSpecial h1222 h12213
  refine le_inf (hs.v1.1.trans (le_conjClosure V _)) ?_
  exact (le_centralizer_normalizer_of_card_eq_two (by simpa using hs.v1.2.1)).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hA.conjClosure_le_N))

theorem display12_8_frattini (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
      Setting1282One G T L V n V₁ V₂ → frattiniOf (u128 V V₁) = V₁ := by
  intro G _ _ T L V n V₁ V₂ hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hs.almostSpecial h1222 h12213
  have : Fact (IsPGroup 2 ↥(u128 V V₁)) := ⟨hs.hyp.hyp.sylow.1.to_le hA.G22_three.1⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hs.exists_mul_ne
  have hc1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := fun h => hxy (by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h, one_mul])
  have hc : x * y * x⁻¹ * y⁻¹ ∈ frattiniOf (u128 V V₁) := by
    refine ⟨⁅(⟨x, hx⟩ : ↥(u128 V V₁)), ⟨y, hy⟩⁆, ?_, by simp [commutatorElement_def]⟩
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine Subgroup.subset_closure (Or.inl ?_)
    rw [SetLike.mem_coe, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine le_antisymm hA.G22_two ?_
  calc V₁ = Subgroup.zpowers (x * y * x⁻¹ * y⁻¹) :=
        (zpowers_eq_of_card_eq_two (by simpa using hs.v1.2.1) (hA.G22_two hc) hc1).symm
    _ ≤ frattiniOf (u128 V V₁) := Subgroup.zpowers_le.2 hc

theorem lemma12_8_8_one (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    ∃ U₀ : Subgroup G, U₀ ≤ u128 V V₁ ∧ CFSG.IsExtraspecialPGroup 2 ↥U₀ ∧
      frattiniOf U₀ = V₁ ∧ U₀ ⊔ zU128 V V₁ = u128 V V₁ := by
  have hA := hs.almostSpecial h1222 h12213
  have hZ := hs.le_centerOf h1222 h12213
  obtain ⟨U₀, hU₀U, hext, hΦ, hsup, -⟩ := exists_extraspecial_sup_centerOf
    (hs.hyp.hyp.sylow.1.to_le hA.G22_three.1) (hZ.trans inf_le_left)
    (by simpa using hs.v1.2.1) (hZ.trans inf_le_right)
    (fun x hx y hy => hA.G22_commutator_mem hx hy) (fun x hx => hA.G22_sq_mem hx)
    hs.exists_mul_ne
  exact ⟨U₀, hU₀U, hext, hΦ, hsup⟩

theorem lemma12_8_8_three (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    V ⊓ zU128 V V₁ = V₁ := by
  have hirr := irred_lOne h1222 hs.hyp hs.v1
  have hG₁Z : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    (le_normalizer_conjClosure V _).trans (normalizer_le_normalizer_centerOf _)
  rcases hirr.2.2.2 (V ⊓ zU128 V V₁) (le_inf hs.v1.1 (hs.le_centerOf h1222 h12213)) inf_le_left
    ((le_inf hirr.2.1 (hirr.2.2.1.trans hG₁Z)).trans Subgroup.inf_normalizer_le_normalizer_inf)
    with h | h
  · exact h
  · exfalso
    have hVZ : V ≤ zU128 V V₁ := inf_eq_left.1 h
    have hUZ : u128 V V₁ ≤ zU128 V V₁ := conjClosure_le fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.1 (hG₁Z hg) z).1 (hVZ hz)
    exact hs.nonabelian ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 (hUZ b.2).2 a a.2)⟩⟩

theorem lemma12_8_8_six (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    u128 V V₁ = conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)) := by
  have hirr := irred_lOne h1222 hs.hyp hs.v1
  have hG₁U₂ := le_normalizer_conjClosure V₂ (Subgroup.normalizer (V₁ : Set G))
  refine le_antisymm ?_ (conjClosure_mono hs.v2.1 le_rfl)
  rcases hirr.2.2.2 (V ⊓ conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)))
    (le_inf hs.v1.1 (hs.le.trans (le_conjClosure V₂ _))) inf_le_left
    ((le_inf hirr.2.1 (hirr.2.2.1.trans hG₁U₂)).trans Subgroup.inf_normalizer_le_normalizer_inf)
    with h | h
  · exfalso
    have h1 := Subgroup.card_le_of_le ((le_inf hs.v2.1 (le_conjClosure V₂ _)).trans h.le)
    rw [hs.v2.2.1, hs.v1.2.1] at h1
    norm_num at h1
  · have hVU₂ := inf_eq_left.1 h
    exact conjClosure_le fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.1 (hG₁U₂ hg) z).1 (hVU₂ hz)

@[expose] def Lemma12_8_8_five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ →
      Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lOne L V₁ : Set G) → n ≤ 3

theorem lemma12_8_8_of_five (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h5 : Lemma12_8_8_five) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
      Setting1282One G T L V n V₁ V₂ →
        (∃ U₀ : Subgroup G, U₀ ≤ u128 V V₁ ∧ CFSG.IsExtraspecialPGroup 2 ↥U₀ ∧
          frattiniOf U₀ = V₁ ∧ U₀ ⊔ zU128 V V₁ = u128 V V₁) ∧
        V ⊓ zU128 V V₁ = V₁ ∧
        (Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lOne L V₁ : Set G) → n ≤ 3) ∧
        u128 V V₁ = conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)) := by
  intro G _ _ T L V n V₁ V₂ hs
  exact ⟨lemma12_8_8_one h1222 h12213 hs, lemma12_8_8_three h1222 h12213 hs,
    h5 G T L V n V₁ V₂ hs, lemma12_8_8_six h1222 hs⟩

theorem lemma12_8_8_n3 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 3 V₁ V₂) :
    (∃ U₀ : Subgroup G, U₀ ≤ u128 V V₁ ∧ CFSG.IsExtraspecialPGroup 2 ↥U₀ ∧
        frattiniOf U₀ = V₁ ∧ U₀ ⊔ zU128 V V₁ = u128 V V₁) ∧
      V ⊓ zU128 V V₁ = V₁ ∧
      (Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lOne L V₁ : Set G) → 3 ≤ 3) ∧
      u128 V V₁ = conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)) :=
  ⟨lemma12_8_8_one h1222 h12213 hs, lemma12_8_8_three h1222 h12213 hs, fun _ => le_rfl,
    lemma12_8_8_six h1222 hs⟩

end Lemma8

end CFSG.Quasithin.H13
