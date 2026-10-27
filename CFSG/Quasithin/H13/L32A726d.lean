module

public import CFSG.Quasithin.H13.L32A726c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem injective_noncommCoprod_726 {A B : Subgroup G}
    (comm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b)) (hinf : A ⊓ B = ⊥) :
    Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype comm) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  change (a : G) * (b : G) = 1 at h
  have hb : (b : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hbA : (b : G) ∈ A ⊓ B := ⟨hb ▸ A.inv_mem a.2, b.2⟩
  rw [hinf, Subgroup.mem_bot] at hbA
  have ha : (a : G) = 1 := by
    rw [hbA] at hb
    exact inv_eq_one.mp hb.symm
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hbA)

theorem inf_zpowers_eq_bot_726 {E : Subgroup G} {c : G} {p : ℕ} (hp : p.Prime)
    (hc : orderOf c = p) (hcE : c ∉ E) : E ⊓ Subgroup.zpowers c = ⊥ := by
  have hle : E ⊓ Subgroup.zpowers c ≤ Subgroup.zpowers c := inf_le_right
  have hdvd : Nat.card (E ⊓ Subgroup.zpowers c : Subgroup G) ∣ p := by
    rw [← hc, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exfalso
    have heq : E ⊓ Subgroup.zpowers c = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h, Nat.card_zpowers, hc])
    have hmem : c ∈ E ⊓ Subgroup.zpowers c := by
      rw [heq]
      exact Subgroup.mem_zpowers c
    exact hcE hmem.1

omit [Finite G] in
theorem commute_of_mem_zpowers_726 {c a b : G} (ha : a ∈ Subgroup.zpowers c)
    (hb : b ∈ Subgroup.zpowers c) : a * b = b * a := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow_self c i j).eq

omit [Finite G] in
theorem commute_zpowers_726 {c c' a : G} (hcc : c * c' = c' * c)
    (ha : a ∈ Subgroup.zpowers c') : c * a = a * c := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ((Commute.zpow_right (show Commute c c' from hcc) i)).eq

theorem le_pRank_of_commute_726 {X E : Subgroup G} (hEX : E ≤ X) (hE : IsElemAbelian 3 E)
    {k : ℕ} (hEk : Nat.card E = 3 ^ k) {c : G} (hcX : c ∈ X) (hc3 : orderOf c = 3)
    (hcE : c ∉ E) (hcomm : ∀ e ∈ E, c * e = e * c) : k + 1 ≤ CFSG.Open.pRank 3 X := by
  have comm : ∀ (a : ↥E) (b : ↥(Subgroup.zpowers c)),
      Commute (E.subtype a) ((Subgroup.zpowers c).subtype b) := fun a b =>
    commute_zpowers_726 (hcomm a a.2).symm b.2
  have hinf := inf_zpowers_eq_bot_726 Nat.prime_three hc3 hcE
  have hEc := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => ?_)
    (fun a => ?_) ?_ _ (injective_noncommCoprod_726 comm hinf) ?_
  · refine Prod.ext (mul_comm' a.1 b.1) (Subtype.ext ?_)
    exact commute_of_mem_zpowers_726 a.2.2 b.2.2
  · refine Prod.ext (Subtype.ext (hE.2 _ a.1.2)) (Subtype.ext ?_)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    show ((a.2 : G)) ^ 3 = 1
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc3,
      pow_orderOf_eq_one, one_zpow]
  · rw [Nat.card_prod, hEk, Nat.card_zpowers, hc3, pow_succ]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    simp only [MonoidHom.noncommCoprod_apply, Subgroup.coe_subtype]
    exact X.mul_mem (hEX a.2) ((Subgroup.zpowers_le.mpr hcX) b.2)

theorem mem_of_commute_of_pRank_726 {X E : Subgroup G} (hr : CFSG.Open.pRank 3 X ≤ 2)
    (hEX : E ≤ X)
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {c : G} (hcX : c ∈ X) (hc3 : orderOf c = 3)
    (hcomm : ∀ e ∈ E, c * e = e * c) : c ∈ E := by
  by_contra hcE
  have := le_pRank_of_commute_726 hEX hE (k := 2) (by rw [hE9]; norm_num) hcX hc3 hcE hcomm
  omega

theorem isElemAbelian_sup_726 {x y : G} (hxy : x * y = y * x) (hx3 : orderOf x = 3)
    (hy3 : orderOf y = 3) (hy : y ∉ Subgroup.zpowers x) :
    IsElemAbelian 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∧
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = 9 := by
  have hAB : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a :=
    fun a ha b hb => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((show Commute x y from hxy).zpow_zpow i j).eq
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [inf_comm]
    exact inf_zpowers_eq_bot_726 Nat.prime_three hx3
      (fun h => hy (by
        have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr h
        have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx3, hy3])
        rw [heq]
        exact Subgroup.mem_zpowers y))
  have comm : ∀ (a : ↥(Subgroup.zpowers x)) (b : ↥(Subgroup.zpowers y)),
      Commute ((Subgroup.zpowers x).subtype a) ((Subgroup.zpowers y).subtype b) := fun a b =>
    hAB a a.2 b b.2
  set f := MonoidHom.noncommCoprod (Subgroup.zpowers x).subtype (Subgroup.zpowers y).subtype
    comm with hf
  have hinj : Function.Injective f := injective_noncommCoprod_726 comm hinf
  have hrange : f.range = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [hf, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange]
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hu, ← hv, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact commute_of_mem_zpowers_726 u.1.2 v.1.2
    · exact commute_of_mem_zpowers_726 u.2.2 v.2.2
  · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hz
    rw [← map_pow]
    have h1 : u ^ 3 = 1 := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.1.2
        show ((u.1 : G)) ^ 3 = 1
        rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx3,
          pow_orderOf_eq_one, one_zpow]
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2.2
        show ((u.2 : G)) ^ 3 = 1
        rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy3,
          pow_orderOf_eq_one, one_zpow]
    rw [h1, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hx3, hy3]

theorem exists_mem_inf_center_726 {p : ℕ} [Fact p.Prime] {W N : Subgroup G} (hW : IsPGroup p W)
    (hNW : N ≤ W) (hn : W ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) :
    ∃ c ∈ N, c ≠ 1 ∧ ∀ w ∈ W, c * w = w * c := by
  have : Group.IsNilpotent W := hW.isNilpotent
  have hnormal : (N.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hne : N.subgroupOf W ≠ ⊥ := by
    intro h
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNW, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h => hy1 (Subtype.ext (Subtype.ext h)), fun w hw => ?_⟩
  have := Subgroup.mem_center_iff.mp hy.2 ⟨w, hw⟩
  exact (congrArg Subtype.val this).symm

theorem exists_pow_orderOf_three_726 {W : Subgroup G} (hW : IsPGroup 3 W) {c : G} (hcW : c ∈ W)
    (hc1 : c ≠ 1) : ∃ c' ∈ Subgroup.zpowers c, orderOf c' = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers c) := hW.to_le (Subgroup.zpowers_le.mpr hcW)
  have h3 : 3 ∣ Nat.card (Subgroup.zpowers c) := by
    rcases hp.card_eq_or_dvd with h | h
    · exfalso
      apply hc1
      have : Subgroup.zpowers c = ⊥ := Subgroup.card_eq_one.mp h
      rw [← Subgroup.zpowers_eq_bot]
      exact this
    · exact h
  obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨c', c'.2, by rw [Subgroup.orderOf_coe]; exact hc'⟩

theorem iLemma_726 {G0 Y E₁ E₂ I : Subgroup G} {x : G} (hr : CFSG.Open.pRank 3 G0 ≤ 2)
    (hYG0 : Y ≤ G0)
    (hY : IsPGroup 3 Y) (hE₁ : E₁ ≤ Y) (hE₂ : E₂ ≤ Y) (he₁ : IsElemAbelian 3 E₁)
    (he₂ : IsElemAbelian 3 E₂) (hc₁ : Nat.card E₁ = 9) (hc₂ : Nat.card E₂ = 9)
    (hx3 : orderOf x = 3) (hE : E₁ ⊓ E₂ ≤ Subgroup.zpowers x) (hIG0 : I ≤ G0)
    (hYI : Y ≤ Subgroup.normalizer (I : Set G)) (h3 : 3 ∣ Nat.card I) :
    ∃ W : Subgroup G, IsSylowOf 3 W (I ⊔ Y) ∧ Y ≤ W ∧ IsSylowOf 3 (W ⊓ I) I ∧ x ∈ W ⊓ I ∧
      ∀ w ∈ W, x * w = w * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYp : IsPGroup 3 (Y.subgroupOf (I ⊔ Y)) := hY.comap_subtype
  obtain ⟨Q, hQ⟩ := hYp.exists_le_sylow
  set W := (Q : Subgroup ↥(I ⊔ Y)).map (I ⊔ Y).subtype with hWdef
  have hWsyl : IsSylowOf 3 W (I ⊔ Y) := ⟨Q, rfl⟩
  have hYW : Y ≤ W := fun y hy =>
    ⟨⟨y, (le_sup_right : Y ≤ I ⊔ Y) hy⟩,
      hQ (show (⟨y, (le_sup_right : Y ≤ I ⊔ Y) hy⟩ : ↥(I ⊔ Y)) ∈ Y.subgroupOf (I ⊔ Y) from hy),
      rfl⟩
  have hWp : IsPGroup 3 W := hWsyl.isPGroup
  have hIYn : I ⊔ Y ≤ Subgroup.normalizer (I : Set G) := sup_le Subgroup.le_normalizer hYI
  have hWG0 : W ≤ G0 := hWsyl.le.trans (sup_le hIG0 hYG0)
  have hNsyl : IsSylowOf 3 (W ⊓ I) I := hWsyl.inf_of_le_normalizer le_sup_left hIYn
  have key : ∀ c ∈ W, (∀ w ∈ W, c * w = w * c) → orderOf c = 3 →
      Subgroup.zpowers c = Subgroup.zpowers x := by
    intro c hcW hcc hc3
    have h₁ := mem_of_commute_of_pRank_726 hr ((hE₁.trans hYW).trans hWG0) he₁ hc₁ (hWG0 hcW)
      hc3 fun e he => hcc e ((hE₁.trans hYW) he)
    have h₂ := mem_of_commute_of_pRank_726 hr ((hE₂.trans hYW).trans hWG0) he₂ hc₂ (hWG0 hcW)
      hc3 fun e he => hcc e ((hE₂.trans hYW) he)
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hE ⟨h₁, h₂⟩))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hx3])
  have hN1 : W ⊓ I ≠ ⊥ := by
    intro h
    have hcard := hNsyl.card_eq
    rw [h, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card I).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
    have : 1 < 3 ^ (Nat.card I).factorization 3 := Nat.one_lt_pow hpos.ne' (by norm_num)
    omega
  have hWN : W ≤ Subgroup.normalizer ((W ⊓ I : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hw) n
    have h2 := Subgroup.mem_normalizer_iff.mp (hIYn (hWsyl.le hw)) n
    exact ⟨fun hn => ⟨h1.mp hn.1, h2.mp hn.2⟩, fun hn => ⟨h1.mpr hn.1, h2.mpr hn.2⟩⟩
  obtain ⟨c', hc'N, hc'1, hc'c⟩ := exists_mem_inf_center_726 hWp inf_le_left hWN hN1
  obtain ⟨c, hcc', hc3⟩ := exists_pow_orderOf_three_726 hWp hc'N.1 hc'1
  have hcN : c ∈ W ⊓ I := (Subgroup.zpowers_le.mpr hc'N) hcc'
  have hcc : ∀ w ∈ W, c * w = w * c := fun w hw =>
    (commute_zpowers_726 (hc'c w hw).symm hcc').symm
  have hcx := key c hcN.1 hcc hc3
  have hxc : x ∈ Subgroup.zpowers c := by
    rw [hcx]
    exact Subgroup.mem_zpowers x
  refine ⟨W, hWsyl, hYW, hNsyl, (Subgroup.zpowers_le.mpr hcN) hxc, fun w hw => ?_⟩
  exact (commute_zpowers_726 (hcc w hw).symm hxc).symm

structure XData726 (K L₁ : Subgroup G) (x : G) (Y E₁ E₂ : Subgroup G) : Prop where
  x_mem : x ∈ L₁
  x_order : orderOf x = 3
  y_le : Y ≤ K
  y_pgroup : IsPGroup 3 Y
  y_card : Nat.card Y = 27
  x_mem_y : x ∈ Y
  x_comm : ∀ y ∈ Y, x * y = y * x
  e₁_le : E₁ ≤ Y
  e₂_le : E₂ ≤ Y
  e₁_elem : IsElemAbelian 3 E₁
  e₂_elem : IsElemAbelian 3 E₂
  e₁_card : Nat.card E₁ = 9
  e₂_card : Nat.card E₂ = 9
  inf_le : E₁ ⊓ E₂ ≤ Subgroup.zpowers x

section Ctx

variable {T L V H D : Subgroup G}

theorem relIndex_l1_726 (hc : Ctx726 G T L V H D) :
    (pCoreOf 2 (L32A.l1 T L V)).relIndex (L32A.l1 T L V) = 3 := by
  have hP := isPOnePlusTwo_K hc.three
  have hQZ : pCoreOf 2 (oTwoUpper H) ≤ o2z (oTwoUpper H) := by
    rw [← commutator_sup_pCoreOf_eq_o2z_726 hP]
    exact le_sup_right
  have hZ3 : ∀ z ∈ o2z (oTwoUpper H), z ^ 3 ∈ pCoreOf 2 (oTwoUpper H) := fun z hz =>
    pow_three_mem_K hc.three z (o2z_le _ hz)
  have h := relIndex_oTwoUpper_eq hQZ (o2z_le _) hZ3
  rw [relIndex_o2z hP, ← hc.l1_eq] at h
  exact h

theorem card_l1_726 (hc : Ctx726 G T L V H D) :
    Nat.card (L32A.l1 T L V) = 3 * Nat.card (pCoreOf 2 (L32A.l1 T L V)) := by
  have h := Subgroup.relIndex_mul_card (pCoreOf 2 (L32A.l1 T L V)) (L32A.l1 T L V)
  rw [relIndex_l1_726 hc, inf_eq_left.mpr (pCoreOf_le 2 _)] at h
  exact h.symm

theorem commute_x_726 (hc : Ctx726 G T L V H D) {x : G} (hxL : x ∈ L32A.l1 T L V)
    {Y : Subgroup G} (hYK : Y ≤ oTwoUpper H) (hY : IsPGroup 3 Y) (hxY : x ∈ Y) :
    ∀ y ∈ Y, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y hy
  have hxz : x ∈ o2z (oTwoUpper H) := by
    rw [hc.l1_eq] at hxL
    exact oTwoUpper_le _ hxL
  have h1 := (mem_o2z_iff.mp hxz).2 y (hYK hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem hxY hy) (Y.inv_mem hxY)) (Y.inv_mem hy)
  have hbot : Y ⊓ pCoreOf 2 (oTwoUpper H) = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y _ hY (pCoreOf_isPGroup 2 _))
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ Y ⊓ pCoreOf 2 (oTwoUpper H) := ⟨h2, h1⟩
  rw [hbot, Subgroup.mem_bot] at h3
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem pow_three_eq_one_726 (hc : Ctx726 G T L V H D) {Y : Subgroup G}
    (hYK : Y ≤ oTwoUpper H) (hY : IsPGroup 3 Y) : ∀ y ∈ Y, y ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y hy
  have hbot : Y ⊓ pCoreOf 2 (oTwoUpper H) = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y _ hY (pCoreOf_isPGroup 2 _))
  have h : y ^ 3 ∈ Y ⊓ pCoreOf 2 (oTwoUpper H) :=
    ⟨Y.pow_mem hy 3, pow_three_mem_K hc.three y (hYK hy)⟩
  rw [hbot, Subgroup.mem_bot] at h
  exact h

omit [Finite G] in
theorem orderOf_eq_three_726 {y : G} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) : orderOf y = 3 :=
  orderOf_eq_prime hy3 hy1

theorem exists_xData_726 (hc : Ctx726 G T L V H D) :
    ∃ (x : G) (Y E₁ E₂ : Subgroup G), XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (L32A.l1 T L V) := ⟨_, card_l1_726 hc⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set x : G := (x' : G) with hxdef
  have hxL : x ∈ L32A.l1 T L V := x'.2
  have hx3 : orderOf x = 3 := by rw [hxdef, Subgroup.orderOf_coe]; exact hx'
  have hxK : x ∈ oTwoUpper H := l1_le_k_726 hc hxL
  have hzp : IsPGroup 3 (Subgroup.zpowers (⟨x, hxK⟩ : ↥(oTwoUpper H))) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
    exact hx3
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  set Y := (S : Subgroup ↥(oTwoUpper H)).map (oTwoUpper H).subtype with hYdef
  have hYK : Y ≤ oTwoUpper H := Subgroup.map_subtype_le _
  have hYp : IsPGroup 3 Y := (S.isPGroup').map _
  have hY27 : Nat.card Y = 27 := by
    rw [hYdef, Subgroup.card_map_of_injective (oTwoUpper H).subtype_injective]
    exact card_sylow_three_k_726 hc S
  have hxY : x ∈ Y := ⟨⟨x, hxK⟩, hS (Subgroup.mem_zpowers _), rfl⟩
  have hxc := commute_x_726 hc hxL hYK hYp hxY
  have hpow := pow_three_eq_one_726 hc hYK hYp
  have hzx : Subgroup.zpowers x ≤ Y := Subgroup.zpowers_le.mpr hxY
  obtain ⟨y₁, hy₁Y, hy₁x⟩ : ∃ y₁ ∈ Y, y₁ ∉ Subgroup.zpowers x := by
    by_contra hno
    push Not at hno
    have hle : Nat.card Y ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hno
    rw [hY27, Nat.card_zpowers, hx3] at hle
    omega
  have hy₁1 : y₁ ≠ 1 := fun h => hy₁x (h ▸ Subgroup.one_mem _)
  obtain ⟨he₁, hc₁⟩ := isElemAbelian_sup_726 (hxc y₁ hy₁Y) hx3
    (orderOf_eq_three_726 (hpow y₁ hy₁Y) hy₁1) hy₁x
  set E₁ := Subgroup.zpowers x ⊔ Subgroup.zpowers y₁ with hE₁def
  have hE₁Y : E₁ ≤ Y := sup_le hzx (Subgroup.zpowers_le.mpr hy₁Y)
  obtain ⟨y₂, hy₂Y, hy₂E⟩ : ∃ y₂ ∈ Y, y₂ ∉ E₁ := by
    by_contra hno
    push Not at hno
    have hle : Nat.card Y ≤ Nat.card E₁ := Subgroup.card_le_of_le hno
    rw [hY27, hc₁] at hle
    omega
  have hy₂x : y₂ ∉ Subgroup.zpowers x := fun h => hy₂E (le_sup_left (a := Subgroup.zpowers x) h)
  have hy₂1 : y₂ ≠ 1 := fun h => hy₂x (h ▸ Subgroup.one_mem _)
  obtain ⟨he₂, hc₂⟩ := isElemAbelian_sup_726 (hxc y₂ hy₂Y) hx3
    (orderOf_eq_three_726 (hpow y₂ hy₂Y) hy₂1) hy₂x
  set E₂ := Subgroup.zpowers x ⊔ Subgroup.zpowers y₂ with hE₂def
  have hE₂Y : E₂ ≤ Y := sup_le hzx (Subgroup.zpowers_le.mpr hy₂Y)
  have hinf : E₁ ⊓ E₂ ≤ Subgroup.zpowers x := by
    have hxle : Subgroup.zpowers x ≤ E₁ ⊓ E₂ := le_inf le_sup_left le_sup_left
    have hd9 : Nat.card (E₁ ⊓ E₂ : Subgroup G) ∣ 9 := hc₁ ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd3 : 3 ∣ Nat.card (E₁ ⊓ E₂ : Subgroup G) := by
      have := Subgroup.card_dvd_of_le hxle
      rwa [Nat.card_zpowers, hx3] at this
    have hcases : Nat.card (E₁ ⊓ E₂ : Subgroup G) = 3 ∨
        Nat.card (E₁ ⊓ E₂ : Subgroup G) = 9 := by
      have hpos : 0 < Nat.card (E₁ ⊓ E₂ : Subgroup G) := Nat.card_pos
      have hle : Nat.card (E₁ ⊓ E₂ : Subgroup G) ≤ 9 := Nat.le_of_dvd (by norm_num) hd9
      interval_cases h : Nat.card (E₁ ⊓ E₂ : Subgroup G) <;> omega
    rcases hcases with h | h
    · exact (Subgroup.eq_of_le_of_card_ge hxle (by rw [h, Nat.card_zpowers, hx3])).symm.le
    · exfalso
      have heq : E₁ ⊓ E₂ = E₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hc₁])
      have hE12 : E₁ ≤ E₂ := heq ▸ inf_le_right
      have heq2 : E₁ = E₂ := Subgroup.eq_of_le_of_card_ge hE12 (by rw [hc₁, hc₂])
      apply hy₂E
      rw [heq2]
      exact le_sup_right (a := Subgroup.zpowers x) (Subgroup.mem_zpowers y₂)
  exact ⟨x, Y, E₁, E₂, hxL, hx3, hYK, hYp, hY27, hxY, hxc, hE₁Y, hE₂Y, he₁, he₂, hc₁, hc₂, hinf⟩

theorem l1_le_conjClosure_726 (hc : Ctx726 G T L V H D) {x : G} (hxL : x ∈ L32A.l1 T L V)
    (hx3 : orderOf x = 3) :
    L32A.l1 T L V ≤ conjClosure (Subgroup.zpowers x) (pCoreOf 2 (L32A.l1 T L V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (L32A.l1 T L V) with hPdef
  set N := conjClosure (Subgroup.zpowers x) P with hNdef
  have hPL : P ≤ L32A.l1 T L V := pCoreOf_le 2 _
  have hxP : Subgroup.zpowers x ⊔ P = L32A.l1 T L V := by
    have hle : Subgroup.zpowers x ⊔ P ≤ L32A.l1 T L V := sup_le (Subgroup.zpowers_le.mpr hxL) hPL
    have hmul := Subgroup.relIndex_mul_relIndex P (Subgroup.zpowers x ⊔ P) (L32A.l1 T L V)
      le_sup_right hle
    rw [relIndex_l1_726 hc] at hmul
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hmul) with h | h
    · exfalso
      have hx : x ∈ P := Subgroup.relIndex_eq_one.mp h (le_sup_left (a := Subgroup.zpowers x)
        (Subgroup.mem_zpowers x))
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (L32A.l1 T L V)) ⟨x, hx⟩
      have hk' : x ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hdvd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one hk'
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
    · rw [h] at hmul
      have h1 : (Subgroup.zpowers x ⊔ P).relIndex (L32A.l1 T L V) = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
  have hl1 : oTwoUpper (L32A.l1 T L V) = L32A.l1 T L V := by
    rw [hc.l1_eq]
    exact A4.oTwoUpper_oTwoUpper _
  rw [← hl1]
  refine oTwoUpper_le_of_pow_mem fun g hg => E1.exists_pow_mem_of_mem_sup
    (pCoreOf_isPGroup 2 (L32A.l1 T L V)) (le_normalizer_conjClosure _ _) ?_
  rw [← hxP] at hg
  exact sup_le_sup_right (le_conjClosure _ _) P hg

end Ctx

end CFSG.Quasithin.H13.L32A
