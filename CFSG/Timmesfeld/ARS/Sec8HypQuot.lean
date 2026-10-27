module

public import CFSG.Timmesfeld.ARS.Sec8Restrict
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.ARS.Sec3PlaneGroup
public import CFSG.Timmesfeld.ARS.Sec8Regular

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem commutatorElement_mul_left_of_mem_center {H : Type*} [Group H] {a b z : H}
    (hz : z ∈ Subgroup.center H) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.1 hz b
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * z * b * (z⁻¹ * a⁻¹) * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_right_of_mem_center {H : Type*} [Group H] {a b z : H}
    (hz : z ∈ Subgroup.center H) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.1 hz a⁻¹
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * (b * z) * a⁻¹ * (z⁻¹ * b⁻¹) = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem center_quotient_center_eq_bot {H : Type*} [Group H]
    (hH : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤) :
    Subgroup.center (H ⧸ Subgroup.center H) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun q hq => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) q
  have hc : ∀ g : H, ⁅x, g⁆ ∈ Subgroup.center H := fun g => by
    have h1 := Subgroup.mem_center_iff.1 hq (QuotientGroup.mk' _ g)
    have h2 : (QuotientGroup.mk' (Subgroup.center H) ⁅x, g⁆) = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    exact (QuotientGroup.eq_one_iff _).1 h2
  let φ : H →* Subgroup.center H :=
    { toFun := fun g => ⟨⁅x, g⁆, hc g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g k => Subtype.ext (by
        change ⁅x, g * k⁆ = ⁅x, g⁆ * ⁅x, k⁆
        have hk := Subgroup.mem_center_iff.1 (hc k) g
        calc ⁅x, g * k⁆ = ⁅x, g⁆ * (g * ⁅x, k⁆ * g⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = ⁅x, g⁆ * ⁅x, k⁆ := by rw [hk, mul_inv_cancel_right]) }
  have hker : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hH] at hker
  have hx : x ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun g => by
    have h1 : ⁅x, g⁆ = 1 := congrArg Subtype.val (hker (Subgroup.mem_top g))
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  exact (QuotientGroup.eq_one_iff _).2 hx

theorem eq_top_of_forall_mul_center {H : Type*} [Group H]
    (hH : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤)
    {K : Subgroup H} (hK : ∀ v : H, ∃ k ∈ K, ∃ z ∈ Subgroup.center H, v = k * z) : K = ⊤ := by
  rw [eq_top_iff, ← hH, Subgroup.commutator_le]
  intro v _ w _
  obtain ⟨k, hk, z, hz, rfl⟩ := hK v
  obtain ⟨k', hk', z', hz', rfl⟩ := hK w
  rw [commutatorElement_mul_left_of_mem_center hz, commutatorElement_mul_right_of_mem_center hz',
    commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')

@[expose] def quotMap (V X : Subgroup G) : Subgroup (↥V ⧸ Subgroup.center ↥V) :=
  (X.subgroupOf V).map (QuotientGroup.mk' (Subgroup.center ↥V))

@[expose] def quotClass (V : Subgroup G) (Δ : Set (Subgroup G)) :
    Set (Subgroup (↥V ⧸ Subgroup.center ↥V)) :=
  quotMap V '' Δ

namespace LeviQuot

variable {V : Subgroup G}

theorem mk_mem_quotMap {X : Subgroup G} {x : ↥V} (hx : (x : G) ∈ X) :
    QuotientGroup.mk' (Subgroup.center ↥V) x ∈ quotMap V X :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)

theorem exists_of_mem_quotMap {X : Subgroup G} {a : ↥V ⧸ Subgroup.center ↥V}
    (h : a ∈ quotMap V X) :
    ∃ x : ↥V, (x : G) ∈ X ∧ QuotientGroup.mk' (Subgroup.center ↥V) x = a := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 h
  exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩

theorem eq_one_of_mem_center {X Y : Subgroup G} (hXY : Opposite X Y) (hYV : Y ≤ V) {x : ↥V}
    (hx : (x : G) ∈ X) (hxc : x ∈ Subgroup.center ↥V) : x = 1 := by
  by_contra hx1
  have hx1' : (x : G) ≠ 1 := fun e => hx1 (Subtype.ext e)
  refine hXY.not_commute_of_mem hx hx1' fun y hy => ?_
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hxc ⟨y, hYV hy⟩)).symm

theorem eq_one_of_mk_eq_one {X Y : Subgroup G} (hXY : Opposite X Y) (hYV : Y ≤ V) {x : ↥V}
    (hx : (x : G) ∈ X) (h1 : QuotientGroup.mk' (Subgroup.center ↥V) x = 1) : x = 1 :=
  eq_one_of_mem_center hXY hYV hx ((QuotientGroup.eq_one_iff x).1 h1)

theorem quotMap_ne_bot (hR : IsRootClass R) {X Y : Subgroup G} (hX : X ∈ R) (hXV : X ≤ V)
    (hXY : Opposite X Y) (hYV : Y ≤ V) : quotMap V X ≠ ⊥ := by
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
  intro hbot
  have hmem := mk_mem_quotMap (V := V) (x := ⟨x, hXV hx⟩) hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hx1 (congrArg Subtype.val (eq_one_of_mk_eq_one hXY hYV hx hmem))

theorem quotMap_commutator {X Y : Subgroup G} (hX : X ≤ V) (hY : Y ≤ V) :
    quotMap V ⁅X, Y⁆ = ⁅quotMap V X, quotMap V Y⁆ := by
  rw [quotMap, ← Restrict.commutator_subgroupOf hX hY, Subgroup.map_commutator]
  rfl

theorem quotMap_conjSub (X : Subgroup G) {g : G} (hg : g ∈ V) :
    quotMap V (conjSub X g) =
      conjSub (quotMap V X) (QuotientGroup.mk' (Subgroup.center ↥V) ⟨g, hg⟩) := by
  rw [quotMap, quotMap, ← map_conj_subgroupOf_mk hg, Subgroup.map_map]
  show _ = Subgroup.map _ (Subgroup.map _ _)
  rw [Subgroup.map_map]
  congr 1

theorem mul_self_of_mem_quotMap (hR : IsRootClass R) {X : Subgroup G} (hX : X ∈ R)
    {a : ↥V ⧸ Subgroup.center ↥V} (ha : a ∈ quotMap V X) : a * a = 1 := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_quotMap ha
  rw [← map_mul, show x * x = 1 from Subtype.ext (hR.mul_self X hX x hx), map_one]

theorem commuting_quotMap {X Y : Subgroup G} (h : Commuting X Y) :
    Commuting (quotMap V X) (quotMap V Y) := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_quotMap ha
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_quotMap hb
  exact Commute.map (Subtype.ext (h x hx y hy) : Commute x y) _

theorem opposite_quotMap {X Y : Subgroup G} (hXV : X ≤ V) (hYV : Y ≤ V) (h : Opposite X Y)
    (hne : quotMap V X ≠ quotMap V Y) : Opposite (quotMap V X) (quotMap V Y) := by
  refine ⟨hne, fun a ha ha1 => ?_, fun b hb hb1 => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := exists_of_mem_quotMap ha
    have hx1 : (x : G) ≠ 1 := fun e => ha1 (by rw [show x = 1 from Subtype.ext e, map_one])
    obtain ⟨b, hb, hb1, hXb⟩ := h.2.1 x hx hx1
    refine ⟨QuotientGroup.mk' _ ⟨b, hYV hb⟩, mk_mem_quotMap hb, fun e => hb1 ?_, ?_⟩
    · exact congrArg Subtype.val (eq_one_of_mk_eq_one h.symm hXV hb e)
    · rw [← quotMap_conjSub X (hYV hb), hXb, quotMap_conjSub Y x.2]
  · obtain ⟨y, hy, rfl⟩ := exists_of_mem_quotMap hb
    have hy1 : (y : G) ≠ 1 := fun e => hb1 (by rw [show y = 1 from Subtype.ext e, map_one])
    obtain ⟨a, ha, ha1, hYa⟩ := h.2.2 y hy hy1
    refine ⟨QuotientGroup.mk' _ ⟨a, hXV ha⟩, mk_mem_quotMap ha, fun e => ha1 ?_, ?_⟩
    · exact congrArg Subtype.val (eq_one_of_mk_eq_one h hYV ha e)
    · rw [← quotMap_conjSub Y (hXV ha), hYa, quotMap_conjSub X y.2]

theorem special_quotMap {Δ : Set (Subgroup G)} (hΔV : ∀ X ∈ Δ, X ≤ V) {X Y : Subgroup G}
    (hX : X ∈ Δ) (hY : Y ∈ Δ) (h : Special R X Y) (hW : ⁅X, Y⁆ ∈ Δ) :
    Special (quotClass V Δ) (quotMap V X) (quotMap V Y) := by
  rw [Special, ← quotMap_commutator (hΔV X hX) (hΔV Y hY)]
  exact ⟨⟨_, hW, rfl⟩, commuting_quotMap h.2.1, commuting_quotMap h.2.2⟩

theorem pow_eq_self_of_mul_self_of_odd {H : Type*} [Monoid H] {n : H} (hn : n * n = 1) {k : ℕ}
    (hk : Odd k) : n ^ k = n := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, sq, hn, one_pow, one_mul]

theorem injOn_quotMap [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {Δ : Set (Subgroup G)} (hΔR : Δ ⊆ R) (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔopp : ∀ X ∈ Δ, ∃ Y ∈ Δ, Opposite X Y) : Set.InjOn (quotMap V) Δ := by
  intro X hX Y hY hXY
  by_contra hne
  have hXR := hΔR hX
  have hYR := hΔR hY
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hXR
  obtain ⟨Z, hZ, hXZ⟩ := hΔopp X hX
  have hZR := hΔR hZ
  have hZV := hΔV Z hZ
  have hmem : QuotientGroup.mk' (Subgroup.center ↥V) ⟨x, hΔV X hX hx⟩ ∈ quotMap V Y :=
    hXY ▸ mk_mem_quotMap hx
  obtain ⟨y, hy, hyx⟩ := exists_of_mem_quotMap hmem
  have hnc : (⟨x, hΔV X hX hx⟩ : ↥V)⁻¹ * y ∈ Subgroup.center ↥V := QuotientGroup.eq.1 hyx.symm
  set n : G := x⁻¹ * y with hn
  have hcen : ∀ v ∈ V, v * n = n * v := fun v hv =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hnc ⟨v, hv⟩)
  have hyxn : (y : G) = x * n := by rw [hn, mul_inv_cancel_left]
  have hxx := hR.mul_self X hXR x hx
  have hyy := hR.mul_self Y hYR y hy
  have hnn : n * n = 1 := by
    have h1 : (x * n) * (x * n) = 1 := by rw [← hyxn]; exact hyy
    rw [mul_assoc, ← mul_assoc n x n, ← hcen x (hΔV X hX hx), mul_assoc, ← mul_assoc x x,
      hxx, one_mul] at h1
    exact h1
  have hn1 : n ≠ 1 := by
    intro e
    rw [e, mul_one] at hyxn
    exact hne (Sec3.eq_of_mem_of_mem hR hiso hXR hYR hx (hyxn ▸ hy) hx1)
  have hZn : conjSub Z n = Z := conjSub_of_forall_commute fun z hz => (hcen z (hZV hz)).symm
  have hZy : conjSub Z y = conjSub Z x := by rw [hyxn, conjSub_mul, hZn]
  have hZx : conjSub Z x ≠ Z := fun e => hx1 (hXZ.eq_one_of_conjSub_eq hx e)
  have hZxo : Opposite Z (conjSub Z x) := opposite_conjSub_of_opposite hR hXR hZR hXZ hx hx1
  have hYZ : Opposite Y Z := by
    have hne' : Y ≠ Z := fun e => hZx (by rw [← hZy, conjSub_of_mem (e ▸ hy)])
    rcases hR.rel Y hYR Z hZR hne' with hc | ho | hs
    · exact absurd (by rw [← hZy]; exact conjSub_of_forall_commute fun z hz =>
        (hc y hy z hz)) hZx
    · exact ho
    · exact absurd (hZy ▸ commuting_conjSub_of_special hR hZR hs.symm hy)
        (hZxo.not_commuting (hR.ne_bot Z hZR))
  obtain ⟨z, hz, hz1⟩ := hR.exists_ne_one hZR
  have hy1 : (y : G) ≠ 1 := by
    intro e
    have : x * n = 1 := by rw [← hyxn, e]
    have hxinv : n = x⁻¹ := eq_inv_of_mul_eq_one_right this
    apply hx1
    have hxc : (⟨x, hΔV X hX hx⟩ : ↥V) ∈ Subgroup.center ↥V := by
      refine Subgroup.mem_center_iff.2 fun v => Subtype.ext ?_
      have := hcen v v.2
      rw [hxinv] at this
      change (v : G) * x = x * v
      have h2 : (v : G) * x⁻¹ = x⁻¹ * v := this
      calc (v : G) * x = x * (x⁻¹ * v) * x := by group
        _ = x * ((v : G) * x⁻¹) * x := by rw [h2]
        _ = x * v := by group
    exact congrArg Subtype.val (eq_one_of_mem_center hXZ hZV hx hxc)
  have ho₁ := hXZ.odd_orderOf_mul (hR.mul_self X hXR) hx hx1 hz hz1
  have ho₂ := hYZ.odd_orderOf_mul (hR.mul_self Y hYR) hy hy1 hz hz1
  have hcomm : Commute (x * z) n := hcen _ (Subgroup.mul_mem _ (hΔV X hX hx) (hZV hz))
  have hyz : (y : G) * z = x * z * n := by
    rw [hyxn, mul_assoc, (hcen z (hZV hz)).symm, ← mul_assoc]
  set o₂ := orderOf ((y : G) * z) with ho₂def
  have h2 : (x * z) ^ o₂ = n := by
    have h3 : ((y : G) * z) ^ o₂ = 1 := pow_orderOf_eq_one _
    rw [hyz, hcomm.mul_pow, pow_eq_self_of_mul_self_of_odd hnn ho₂] at h3
    calc (x * z) ^ o₂ = (x * z) ^ o₂ * n * n := by rw [mul_assoc, hnn, mul_one]
      _ = n := by rw [h3, one_mul]
  apply hn1
  rw [← pow_eq_self_of_mul_self_of_odd hnn ho₁, ← h2, ← pow_mul, mul_comm, pow_mul,
    pow_orderOf_eq_one, one_pow]

theorem commuting_of_commuting_quotMap [Finite G] (hR : IsRootClass R)
    {Δ : Set (Subgroup G)} (hΔR : Δ ⊆ R) (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔopp : ∀ X ∈ Δ, ∃ Y ∈ Δ, Opposite X Y)
    (hΔcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ) {X Y : Subgroup G} (hX : X ∈ Δ)
    (hY : Y ∈ Δ) (h : Commuting (quotMap V X) (quotMap V Y)) : Commuting X Y := by
  have hXR := hΔR hX
  have hYR := hΔR hY
  have hXV := hΔV X hX
  have hYV := hΔV Y hY
  have hcen : ∀ x ∈ X, ∀ y ∈ Y, ∀ v ∈ V, v * ⁅x, y⁆ = ⁅x, y⁆ * v := by
    intro x hx y hy v hv
    have h1 := h _ (mk_mem_quotMap (V := V) (x := ⟨x, hXV hx⟩) hx) _
      (mk_mem_quotMap (V := V) (x := ⟨y, hYV hy⟩) hy)
    have h2 : QuotientGroup.mk' (Subgroup.center ↥V) ⁅(⟨x, hXV hx⟩ : ↥V), ⟨y, hYV hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff _).1 h2)
      ⟨v, hv⟩)
  by_cases hXY : X = Y
  · rw [hXY]
    exact hR.commuting_self hYR
  rcases hR.rel X hXR Y hYR hXY with hc | ho | hs
  · exact hc
  ·
    exfalso
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hXR
    obtain ⟨y, hy, hy1⟩ := hR.exists_ne_one hYR
    have hodd := ho.odd_orderOf_mul (hR.mul_self X hXR) hx hx1 hy hy1
    have hxx := hR.mul_self X hXR x hx
    have hyy := hR.mul_self Y hYR y hy
    have hc2 : ⁅x, y⁆ = (x * y) ^ 2 := by
      rw [commutatorElement_def, sq, hR.inv_eq hXR hx, hR.inv_eq hYR hy]
      group
    obtain ⟨k, hk⟩ := hodd
    have hxy : x * y = ((x * y) ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf (x * y) + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hxyc : ∀ v ∈ V, v * (x * y) = x * y * v := fun v hv => by
      rw [hxy, ← hc2]
      exact ((Commute.pow_right (hcen x hx y hy v hv) (k + 1)))
    have hcxy : x * y = y * x := by
      have h1 := hxyc x (hXV hx)
      calc x * y = x * (x * y) * x := by rw [h1, mul_assoc, hxx, mul_one]
        _ = y * x := by rw [← mul_assoc, hxx, one_mul]
    have h1 : (x * y) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc y x y, ← hcxy, mul_assoc, hyy, mul_one, hxx]
    have hdvd : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    have hxy1 : x * y = 1 := by
      have : orderOf (x * y) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
        · exact h
        · omega
      exact orderOf_eq_one_iff.1 this
    have hyx : y = x := by
      rw [← hR.inv_eq hXR hx]
      exact eq_inv_of_mul_eq_one_right hxy1
    have hmem : x ∈ X ⊓ Y := ⟨hx, hyx ▸ hy⟩
    rw [ho.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  ·
    exfalso
    have hW := hΔcl X hX Y hY hs
    obtain ⟨U, hU, hWU⟩ := hΔopp _ hW
    obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hs.1
    have hWc : ⁅X, Y⁆ ≤ (Subgroup.center ↥V).map V.subtype := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hxyV : ⁅x, y⁆ ∈ V := by
        rw [commutatorElement_def]
        exact V.mul_mem (V.mul_mem (V.mul_mem (hXV hx) (hYV hy)) (V.inv_mem (hXV hx)))
          (V.inv_mem (hYV hy))
      exact ⟨⟨⁅x, y⁆, hxyV⟩, Subgroup.mem_center_iff.2 fun v =>
        Subtype.ext (hcen x hx y hy v v.2), rfl⟩
    obtain ⟨w', hw'c, rfl⟩ := hWc hw
    exact hw1 (congrArg Subtype.val (eq_one_of_mem_center hWU (hΔV U hU) hw hw'c))

theorem isRootClass_quotClass [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {Δ : Set (Subgroup G)} {E₀ : Subgroup G} (hΔR : Δ ⊆ R) (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔopp : ∀ X ∈ Δ, ∃ Y ∈ Δ, Opposite X Y) (hE₀ : E₀ ∈ Δ)
    (hΔconj : ∀ X ∈ Δ, ∀ g ∈ V, conjSub X g ∈ Δ) (hΔtrans : ∀ X ∈ Δ, ∃ g ∈ V, conjSub E₀ g = X)
    (hΔcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ) (hgen : gen Δ = V) :
    IsRootClass (quotClass V Δ) := by
  have hinj := injOn_quotMap hR hiso hΔR hΔV hΔopp (V := V)
  refine ⟨⟨quotMap V E₀, Set.Subset.antisymm ?_ ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, hX, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hΔtrans X hX
    exact ⟨_, (quotMap_conjSub E₀ hg).symm⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥V) a
    exact ⟨_, hΔconj E₀ hE₀ g g.2, quotMap_conjSub E₀ g.2⟩
  · rintro _ ⟨X, hX, rfl⟩
    obtain ⟨Y, hY, hXY⟩ := hΔopp X hX
    exact quotMap_ne_bot hR (hΔR hX) (hΔV X hX) hXY (hΔV Y hY)
  · rintro _ ⟨X, hX, rfl⟩ a ha
    exact mul_self_of_mem_quotMap hR (hΔR hX) ha
  · rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩ hne
    have hXY : X ≠ Y := fun e => hne (by rw [e])
    rcases hR.rel X (hΔR hX) Y (hΔR hY) hXY with hc | ho | hs
    · exact Or.inl (commuting_quotMap hc)
    · exact Or.inr (Or.inl (opposite_quotMap (hΔV X hX) (hΔV Y hY) ho hne))
    · exact Or.inr (Or.inr (special_quotMap hΔV hX hY hs (hΔcl X hX Y hY hs)))
  · refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥V) a
    have hv : (v : G) ∈ gen Δ := hgen ▸ v.2
    obtain ⟨hvV, hmem⟩ := gen_induction (Δ := Δ)
      (p := fun y => ∃ hy : y ∈ V, QuotientGroup.mk' (Subgroup.center ↥V) ⟨y, hy⟩ ∈
        ⨆ A ∈ quotClass V Δ, A) hv
      (fun B hB z hz => ⟨hΔV B hB hz, le_iSup₂ (f := fun A (_ : A ∈ quotClass V Δ) => A)
        (quotMap V B) ⟨B, hB, rfl⟩ (mk_mem_quotMap hz)⟩)
      ⟨V.one_mem, by
        rw [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, map_one]
        exact Subgroup.one_mem _⟩
      fun y z ⟨hyV, hy⟩ ⟨hzV, hz⟩ => ⟨V.mul_mem hyV hzV, by
        rw [show (⟨y * z, V.mul_mem hyV hzV⟩ : ↥V) = ⟨y, hyV⟩ * ⟨z, hzV⟩ from rfl, map_mul]
        exact Subgroup.mul_mem _ hy hz⟩
    exact hmem

theorem noIsolated_quotClass [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {Δ : Set (Subgroup G)} (hΔR : Δ ⊆ R) (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔopp : ∀ X ∈ Δ, ∃ Y ∈ Δ, Opposite X Y) : NoIsolated (quotClass V Δ) := by
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨Y, hY, hXY⟩ := hΔopp X hX
  exact ⟨quotMap V Y, ⟨Y, hY, rfl⟩, opposite_quotMap (hΔV X hX) (hΔV Y hY) hXY
    fun e => hXY.1 (injOn_quotMap hR hiso hΔR hΔV hΔopp hX hY e)⟩

theorem isNondegenerate_quotClass {Δ : Set (Subgroup G)} (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ)
    (hnd : ∃ X ∈ Δ, ∃ Y ∈ Δ, Special R X Y) : IsNondegenerate (quotClass V Δ) := by
  obtain ⟨X, hX, Y, hY, hs⟩ := hnd
  exact ⟨_, ⟨X, hX, rfl⟩, _, ⟨Y, hY, rfl⟩, special_quotMap hΔV hX hY hs (hΔcl X hX Y hY hs)⟩

theorem opposite_of_opposite_quotMap [Finite G] (hR : IsRootClass R) {Δ : Set (Subgroup G)}
    (hΔR : Δ ⊆ R) (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔopp : ∀ X ∈ Δ, ∃ Y ∈ Δ, Opposite X Y) {X Y : Subgroup G} (hX : X ∈ Δ) (hY : Y ∈ Δ)
    (h : Opposite (quotMap V X) (quotMap V Y)) : Opposite X Y := by
  have hXR := hΔR hX
  have hYR := hΔR hY
  have hXV := hΔV X hX
  have hYV := hΔV Y hY
  have hXY : X ≠ Y := fun e => h.1 (by rw [e])
  obtain ⟨X', hX', hXX'⟩ := hΔopp X hX
  obtain ⟨Y', hY', hYY'⟩ := hΔopp Y hY
  rcases hR.rel X hXR Y hYR hXY with hc | ho | hs
  · exact absurd (commuting_quotMap hc)
      (h.not_commuting (quotMap_ne_bot hR hXR hXV hXX' (hΔV X' hX')))
  · exact ho
  ·
    exfalso
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hXR
    obtain ⟨y, hy, hy1⟩ := hR.exists_ne_one hYR
    set a := QuotientGroup.mk' (Subgroup.center ↥V) ⟨x, hXV hx⟩ with ha
    set b := QuotientGroup.mk' (Subgroup.center ↥V) ⟨y, hYV hy⟩ with hb
    have ha1 : a ≠ 1 := fun e => hx1 (congrArg Subtype.val (eq_one_of_mk_eq_one hXX'
      (hΔV X' hX') hx e))
    have hb1 : b ≠ 1 := fun e => hy1 (congrArg Subtype.val (eq_one_of_mk_eq_one hYY'
      (hΔV Y' hY') hy e))
    have hodd := h.odd_orderOf_mul (fun c hc => mul_self_of_mem_quotMap hR hXR hc)
      (mk_mem_quotMap hx) ha1 (mk_mem_quotMap hy) hb1
    obtain ⟨k, hk⟩ := Special.isPGroup_sup hR hXR hYR hs
      ⟨x * y, Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)⟩
    have hpow : (a * b) ^ 2 ^ k = 1 := by
      have h1 : (x * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [ha, hb, ← map_mul, ← map_pow]
      rw [show (⟨x, hXV hx⟩ * ⟨y, hYV hy⟩ : ↥V) ^ 2 ^ k = 1 from Subtype.ext h1, map_one]
    have hdvd : orderOf (a * b) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj0 : j = 0 := by
      rcases j with _ | j
      · rfl
      · rw [hj, pow_succ] at hodd
        exact absurd hodd (by simp)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    have hab : a = b⁻¹ := eq_inv_of_mul_eq_one_left hj
    have hmem : a ∈ quotMap V X ⊓ quotMap V Y :=
      ⟨mk_mem_quotMap hx, hab ▸ Subgroup.inv_mem _ (mk_mem_quotMap hy)⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact ha1 hmem

theorem special_of_special_quotMap [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {Δ : Set (Subgroup G)} (hΔR : Δ ⊆ R) (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔopp : ∀ X ∈ Δ, ∃ Y ∈ Δ, Opposite X Y) (hR' : IsRootClass (quotClass V Δ))
    {X Y : Subgroup G} (hX : X ∈ Δ) (hY : Y ∈ Δ)
    (h : Special (quotClass V Δ) (quotMap V X) (quotMap V Y)) : Special R X Y := by
  have hXR := hΔR hX
  have hYR := hΔR hY
  have hXV := hΔV X hX
  have hYV := hΔV Y hY
  have hX' : quotMap V X ∈ quotClass V Δ := ⟨X, hX, rfl⟩
  have hXY : X ≠ Y := by
    rintro rfl
    exact h.commutator_ne_bot hR' (hR'.commutator_self_eq_bot hX')
  rcases hR.rel X hXR Y hYR hXY with hc | ho | hs
  · exact absurd (commuting_quotMap hc) (h.not_commuting hR')
  · exact absurd (opposite_quotMap hXV hYV ho
      fun e => hXY (injOn_quotMap hR hiso hΔR hΔV hΔopp hX hY e)) (h.not_opposite hR' hX')
  · exact hs

theorem commutator_mem_and_quotMap {Δ : Set (Subgroup G)} (hΔV : ∀ X ∈ Δ, X ≤ V)
    (hΔcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ) {X Y : Subgroup G} (hX : X ∈ Δ)
    (hY : Y ∈ Δ) (hs : Special R X Y) :
    ⁅X, Y⁆ ∈ Δ ∧ quotMap V ⁅X, Y⁆ = ⁅quotMap V X, quotMap V Y⁆ :=
  ⟨hΔcl X hX Y hY hs, quotMap_commutator (hΔV X hX) (hΔV Y hY)⟩

theorem commutator_eq_of_special {Δ : Set (Subgroup G)} {E₀ : Subgroup G}
    (hΔV : ∀ X ∈ Δ, X ≤ V) (hΔtrans : ∀ X ∈ Δ, ∃ g ∈ V, conjSub E₀ g = X)
    (hΔcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ) (hgen : gen Δ = V)
    (hnd : ∃ X ∈ Δ, ∃ Y ∈ Δ, Special R X Y) : ⁅V, V⁆ = V := by
  obtain ⟨X₁, hX₁, Y₁, hY₁, hs⟩ := hnd
  have hW := hΔcl X₁ hX₁ Y₁ hY₁ hs
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact V.mul_mem (V.mul_mem (V.mul_mem hx hy) (V.inv_mem hx)) (V.inv_mem hy)
  ·
    calc V = gen Δ := hgen.symm
      _ ≤ ⁅V, V⁆ := gen_le fun X hX => by
        obtain ⟨g₁, hg₁, rfl⟩ := hΔtrans X hX
        obtain ⟨g₂, hg₂, hW₂⟩ := hΔtrans _ hW
        have hE₀ : E₀ = conjSub ⁅X₁, Y₁⁆ g₂⁻¹ := by
          rw [← hW₂, Plane.conjSub_conjSub_inv]
        have hnorm : conjSub ⁅V, V⁆ (g₁ * g₂⁻¹) = ⁅V, V⁆ := by
          rw [conjSub, Subgroup.map_commutator, ← conjSub,
            conjSub_of_mem (V.mul_mem hg₁ (V.inv_mem hg₂))]
        rw [hE₀, ← conjSub_mul, ← hnorm]
        exact Subgroup.map_mono (Subgroup.commutator_mono (hΔV X₁ hX₁) (hΔV Y₁ hY₁))

theorem commutator_top_eq_top (hV : ⁅V, V⁆ = V) :
    ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⊤ := by
  apply Subgroup.map_injective V.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hV]

theorem center_eq_bot {Δ : Set (Subgroup G)} {E₀ : Subgroup G}
    (hΔV : ∀ X ∈ Δ, X ≤ V) (hΔtrans : ∀ X ∈ Δ, ∃ g ∈ V, conjSub E₀ g = X)
    (hΔcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ) (hgen : gen Δ = V)
    (hnd : ∃ X ∈ Δ, ∃ Y ∈ Δ, Special R X Y) :
    Subgroup.center (↥V ⧸ Subgroup.center ↥V) = ⊥ :=
  center_quotient_center_eq_bot
    (commutator_top_eq_top (commutator_eq_of_special hΔV hΔtrans hΔcl hgen hnd))

theorem card_lt [Finite G] (hV : V ≠ ⊤) : Nat.card (↥V ⧸ Subgroup.center ↥V) < Nat.card G := by
  have h1 : Nat.card (↥V ⧸ Subgroup.center ↥V) ≤ Nat.card ↥V :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h2 : Nat.card ↥V < Nat.card ↥(⊤ : Subgroup G) :=
    Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hV)
  rw [Subgroup.card_top] at h2
  exact h1.trans_lt h2

theorem iSup_eq_of_iSup_quotMap_eq_top {ι : Type*} (hV : ⁅V, V⁆ = V) {A B : ι → Subgroup G}
    (hA : ∀ k, A k ≤ V) (hB : ∀ k, B k ≤ V)
    (h : ⨆ k, (quotMap V (A k) ⊔ quotMap V (B k)) = ⊤) : ⨆ k, (A k ⊔ B k) = V := by
  set H := ⨆ k, (A k ⊔ B k) with hH
  have hHV : H ≤ V := iSup_le fun k => sup_le (hA k) (hB k)
  set K : Subgroup ↥V := ⨆ k, ((A k).subgroupOf V ⊔ (B k).subgroupOf V) with hK
  have hKH : K ≤ H.subgroupOf V := iSup_le fun k => sup_le
    (Subgroup.comap_mono (le_sup_left.trans (le_iSup (fun k => A k ⊔ B k) k)))
    (Subgroup.comap_mono (le_sup_right.trans (le_iSup (fun k => A k ⊔ B k) k)))
  have hKmap : K.map (QuotientGroup.mk' (Subgroup.center ↥V)) = ⊤ := by
    rw [hK, Subgroup.map_iSup]
    simp only [Subgroup.map_sup]
    exact h
  have htop : H.subgroupOf V = ⊤ := by
    refine eq_top_of_forall_mul_center (commutator_top_eq_top hV) fun v => ?_
    obtain ⟨k, hk, hkv⟩ := Subgroup.mem_map.1 (hKmap ▸ Subgroup.mem_top
      (QuotientGroup.mk' (Subgroup.center ↥V) v))
    exact ⟨k, hKH hk, k⁻¹ * v, QuotientGroup.eq.1 hkv, by rw [mul_inv_cancel_left]⟩
  exact le_antisymm hHV ((Subgroup.subgroupOf_eq_top).1 htop)

theorem mem_rootClosure_quotMap_iff [Finite G] (hR : IsRootClass R) {Δ : Set (Subgroup G)}
    (hΔR : Δ ⊆ R) (hΔV : ∀ X ∈ Δ, X ≤ V) (hΔopp : ∀ X ∈ Δ, ∃ Y ∈ Δ, Opposite X Y)
    (hΔcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ) {X Y : Subgroup G} (hX : X ∈ Δ)
    (hY : Y ∈ Δ) :
    quotMap V Y ∈ rootClosure (quotClass V Δ) (quotMap V X) ↔
      ∀ Z ∈ Δ, (Commuting X Z ↔ Commuting Y Z) := by
  have hc : ∀ {X Z : Subgroup G}, X ∈ Δ → Z ∈ Δ →
      (Commuting (quotMap V X) (quotMap V Z) ↔ Commuting X Z) := fun hX hZ =>
    ⟨commuting_of_commuting_quotMap hR hΔR hΔV hΔopp hΔcl hX hZ, commuting_quotMap⟩
  constructor
  · rintro ⟨-, h⟩ Z hZ
    have h1 : quotMap V Z ∈ centralSet (quotClass V Δ) (quotMap V Y) ↔
        quotMap V Z ∈ centralSet (quotClass V Δ) (quotMap V X) := by rw [h]
    simp only [centralSet, Set.mem_ofPred_eq] at h1
    rw [← hc hX hZ, ← hc hY hZ]
    exact ⟨fun h2 => (h1.2 ⟨⟨Z, hZ, rfl⟩, h2⟩).2, fun h2 => (h1.1 ⟨⟨Z, hZ, rfl⟩, h2⟩).2⟩
  · intro h
    refine ⟨⟨Y, hY, rfl⟩, Set.ext fun B => ?_⟩
    constructor
    · rintro ⟨⟨Z, hZ, rfl⟩, hYZ⟩
      exact ⟨⟨Z, hZ, rfl⟩, (hc hX hZ).2 ((h Z hZ).2 ((hc hY hZ).1 hYZ))⟩
    · rintro ⟨⟨Z, hZ, rfl⟩, hXZ⟩
      exact ⟨⟨Z, hZ, rfl⟩, (hc hY hZ).2 ((h Z hZ).1 ((hc hX hZ).1 hXZ))⟩

end LeviQuot

end CFSG.Timmesfeld.ARS
