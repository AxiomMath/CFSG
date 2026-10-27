module

public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.ThinCatalog.OuterThreeFree

public section

namespace CFSG.RankThree.ThetaFree

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem center_eq_bot_of_pCore_eq_bot (hθ : aschbacherSolvableCore 3 G = ⊥)
    (h3 : pCore 3 G = ⊥) {K : Subgroup G} (hK : IsComponent K) : center K = ⊥ := by
  have h := Theta.center_map_le_pCore_three hθ hK
  rw [h3, le_bot_iff] at h
  exact (map_eq_bot_iff_of_injective _ K.subtype_injective).1 h

omit [Finite G] in
theorem eq_one_of_mem_centralizer_of_center_eq_bot {K : Subgroup G} (hZ : center K = ⊥) :
    ∀ y ∈ K, y ∈ centralizer (K : Set G) → y = 1 := fun y hy hyc => by
  have h : (⟨y, hy⟩ : K) ∈ center K := mem_center_iff_coe_mem_centralizer.2 hyc
  rw [hZ, mem_bot] at h
  exact congrArg Subtype.val h

omit [Finite G] in
theorem isSimpleGroup_of_center_eq_bot {K : Subgroup G} (hK : IsComponent K)
    (hZ : center K = ⊥) : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hK.1
  have : IsSimpleGroup (K ⧸ center K) := hs
  let e : K ⧸ center K ≃* K := (QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem exists_triple_of_not_le_normalizer {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G}
    (hLA : ¬ A ≤ normalizer (L : Set G)) :
    ∃ g₁ ∈ A, ∃ g₂ ∈ A, L ≠ L.map (MulAut.conj g₁).toMonoidHom ∧
      L ≠ L.map (MulAut.conj g₂).toMonoidHom ∧
      L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom := by
  let := Theta.conjAction A
  have hstab : MulAction.stabilizer A L = (normalizer (L : Set G)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf]
    exact ⟨fun h => Theta.mem_normalizer_of_map_conj_eq_self h,
      fun h => Theta.map_conj_eq_of_mem_normalizer h⟩
  have hidx := MulAction.index_stabilizer A L
  obtain ⟨j, hj⟩ := hA.index (MulAction.stabilizer A L)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, index_eq_one, hstab] at hj
    apply hLA
    intro a ha
    have h : (⟨a, ha⟩ : A) ∈ (normalizer (L : Set G)).subgroupOf A := hj ▸ mem_top _
    exact mem_subgroupOf.1 h
  have h3 : 3 ≤ (MulAction.orbit A L).ncard := by
    rw [← hidx, hj]
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hj0)
  have h2 : 1 < (MulAction.orbit A L \ {L}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem (MulAction.mem_orbit_self L)]
    omega
  obtain ⟨K₁, K₂, hK₁, hK₂, hK₁₂⟩ := (Set.one_lt_ncard_iff).1 h2
  obtain ⟨a₁, ha₁⟩ := hK₁.1
  obtain ⟨a₂, ha₂⟩ := hK₂.1
  have e₁ : L.map (MulAut.conj (a₁ : G)).toMonoidHom = K₁ := ha₁
  have e₂ : L.map (MulAut.conj (a₂ : G)).toMonoidHom = K₂ := ha₂
  refine ⟨a₁, a₁.2, a₂, a₂.2, ?_, ?_, ?_⟩
  · rw [e₁]
    exact fun h => hK₁.2 h.symm
  · rw [e₂]
    exact fun h => hK₂.2 h.symm
  · rw [e₁, e₂]
    exact hK₁₂

section Triple

variable {L : Subgroup G} {g₁ g₂ : G}

theorem prime_dvd_card_normalizer_of_triple (hL : IsComponent L) (hZ : center L = ⊥)
    (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom) (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) {U : Subgroup L} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ Nat.card (normalizer (U : Set L))) : r = 2 ∨ r = 3 := by
  by_contra hne
  push Not at hne
  have hr3 : 3 < r := by
    have := hr.two_le
    omega
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrd
  refine (orderOf_ne_of_conjugate_components hL h01 h02 h12 hr hr3 (hq r hr hr3)
    (fun w hwL hwc => ⟨0, by
      rw [eq_one_of_mem_centralizer_of_center_eq_bot hZ w hwL hwc, pow_zero, one_pow]⟩)
    (U := U.map L.subtype) ?_ (hU2.map _) (map_subtype_le U) (y : L).2
    (coe_mem_normalizer_map y.2)) ?_
  · exact fun hb => hU ((map_eq_bot_iff_of_injective _ L.subtype_injective).1 hb)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]

theorem exists_two_subgroup_three_normalizer_of_triple (hL : IsComponent L) (hZ : center L = ⊥)
    (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom) (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) :
    ∃ U : Subgroup L, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∃ v ∈ normalizer (U : Set L), orderOf v = 3 := by
  have hLns : ¬ Group.IsSolvable L := by
    have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect L := hL.1.1
    exact Group.IsPerfect.not_isSolvable L
  obtain ⟨U, hU, hU2, q, hq', hq2, v, hvN, hv⟩ :=
    Theta.exists_two_subgroup_odd_prime_normalizer hLns
  have hdvd : q ∣ Nat.card (normalizer (U : Set L)) := hv ▸ Subgroup.orderOf_dvd_natCard _ hvN
  rcases prime_dvd_card_normalizer_of_triple hL hZ h01 h02 h12 hq hU hU2 hq' hdvd with h | h
  · exact absurd h hq2
  · exact ⟨U, hU, hU2, v, hvN, h ▸ hv⟩

omit [Finite G] in
theorem isMulCommutative_sup_and_pow_eq_one {r : ℕ} {E₁ E₂ : Subgroup G}
    (h1c : IsMulCommutative E₁) (h2c : IsMulCommutative E₂)
    (h12 : E₂ ≤ centralizer (E₁ : Set G)) (h1q : ∀ x ∈ E₁, x ^ r = 1)
    (h2q : ∀ x ∈ E₂, x ^ r = 1) :
    IsMulCommutative (E₁ ⊔ E₂ : Subgroup G) ∧ ∀ w ∈ E₁ ⊔ E₂, w ^ r = 1 := by
  have hle : E₂ ≤ normalizer (E₁ : Set G) := h12.trans (centralizer_le_normalizer _)
  have hmem : ∀ w ∈ E₁ ⊔ E₂, ∃ a ∈ E₁, ∃ b ∈ E₂, a * b = w := fun w hw => by
    have hw' : w ∈ (E₁ : Set G) * (E₂ : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left E₁ _ hle]
      exact hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw'
    exact ⟨a, ha, b, hb, rfl⟩
  have hc1 : ∀ a ∈ E₁, ∀ a' ∈ E₁, Commute a a' := fun a ha a' ha' =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E₁) ⟨a', ha'⟩)
  have hc2 : ∀ b ∈ E₂, ∀ b' ∈ E₂, Commute b b' := fun b hb b' hb' =>
    congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : E₂) ⟨b', hb'⟩)
  have hc12 : ∀ a ∈ E₁, ∀ b ∈ E₂, Commute a b := fun a ha b hb =>
    (mem_centralizer_iff.1 (h12 hb) a ha)
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun w hw => ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := hmem x x.2
    obtain ⟨a', ha', b', hb', hy⟩ := hmem y y.2
    change (x : G) * y = y * x
    rw [← hx, ← hy]
    exact ((((hc1 a ha a' ha').mul_right (hc12 a ha b' hb')).mul_left
      (((hc12 a' ha' b hb).symm).mul_right (hc2 b hb b' hb'))) : _)
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem w hw
    rw [(hc12 a ha b hb).mul_pow, h1q a ha, h2q b hb, one_mul]

theorem pRank_le_one_of_triple (hL : IsComponent L) (hZ : center L = ⊥)
    (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom) (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom) {r : ℕ}
    (hr : r.Prime) (hrank : localRank r G ≤ 3) (hrank' : 3 < r → localRank r G ≤ 2)
    (hr3 : r = 3 ∨ 3 < r) : Assembly.pRank r L ≤ 1 := by
  obtain ⟨c01, c02, c12⟩ := conjugate_components_commute hL h01 h02 h12
  set L₁ := L.map (MulAut.conj g₁).toMonoidHom with hL₁def
  set L₂ := L.map (MulAut.conj g₂).toMonoidHom with hL₂def
  have hc0 := eq_one_of_mem_centralizer_of_center_eq_bot hZ
  have hc1 := Theta.eq_one_of_mem_map_conj hc0 g₁
  obtain ⟨E, hEL, hE, hEcard⟩ := SectionRank.exists_pRank hr.one_lt L
  set E₁ := E.map (MulAut.conj g₁).toMonoidHom with hE₁def
  set E₂ := E.map (MulAut.conj g₂).toMonoidHom with hE₂def
  have hE₁L : E₁ ≤ L₁ := map_mono hEL
  have hE₂L : E₂ ≤ L₂ := map_mono hEL
  have hE₁ : Assembly.IsElemAbelian r E₁ := SectionRank.isElemAbelian_map hE _
  have hE₂ : Assembly.IsElemAbelian r E₂ := SectionRank.isElemAbelian_map hE _
  have h21 : E₂ ≤ centralizer (E₁ : Set G) :=
    (hE₂L.trans (le_centralizer_iff.1 c12)).trans (centralizer_le hE₁L)
  have hdisj : E₁ ⊓ E₂ = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    rw [mem_bot]
    exact hc1 y (hE₁L hy.1) (le_centralizer_iff.1 c12 (hE₂L hy.2))
  have hcard : Nat.card (E₁ ⊔ E₂ : Subgroup G) = r ^ (Assembly.pRank r L + Assembly.pRank r L) := by
    rw [CentralCover.card_sup_eq_mul_of_le_normalizer (h21.trans (centralizer_le_normalizer _))
      hdisj, card_map_of_injective (MulAut.conj g₁).injective,
      card_map_of_injective (MulAut.conj g₂).injective, hEcard, pow_add]
  obtain ⟨hWc, hWq⟩ := isMulCommutative_sup_and_pow_eq_one hE₁.1 hE₂.1 h21 hE₁.2 hE₂.2
  have hLns : ¬ Group.IsSolvable L := by
    have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect L := hL.1.1
    exact Group.IsPerfect.not_isSolvable L
  obtain ⟨u, hu⟩ := Theta.exists_orderOf_eq_two_of_not_isSolvable hLns
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
  obtain ⟨hU, hU2⟩ := zpowers_ne_bot_and_isPGroup_two hu'
  have hWU : E₁ ⊔ E₂ ≤ normalizer (zpowers (u : G) : Set G) := by
    refine le_trans ?_ ((centralizer_le (zpowers_le.2 u.2)).trans (centralizer_le_normalizer _))
    exact sup_le (hE₁L.trans (le_centralizer_iff.1 c01)) (hE₂L.trans (le_centralizer_iff.1 c02))
  have h2k := Theta.le_localRank_of_le_normalizer hr.one_lt hU hU2 hWc hWq hcard hWU
  rcases hr3 with rfl | hr3
  · omega
  · have := hrank' hr3
    omega

omit [Finite G] in
theorem mem_centralizer_map_conj_of_commute {c : G} (hcg : c * g₁ = g₁ * c)
    (hc : c ∈ centralizer (L : Set G)) :
    c ∈ centralizer ((L.map (MulAut.conj g₁).toMonoidHom : Subgroup G) : Set G) := by
  have h : g₁ * c * g₁⁻¹ = c := by rw [← hcg, mul_inv_cancel_right]
  have h' := conj_mem_centralizer_map_conj_iff (L := L) (g := g₁) (x := c) |>.2 hc
  rwa [h] at h'

theorem four_le_localRank_three_of_triple (hL : IsComponent L) (hZ : center L = ⊥)
    (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom) (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom) {c : G}
    (hc0 : c ∈ centralizer (L : Set G))
    (hc1 : c ∈ centralizer ((L.map (MulAut.conj g₁).toMonoidHom : Subgroup G) : Set G))
    (hc2 : c ∈ centralizer ((L.map (MulAut.conj g₂).toMonoidHom : Subgroup G) : Set G))
    (hco : orderOf c = 3) {U : Subgroup L} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) {x : L}
    (hxN : x ∈ normalizer (U : Set L)) (hxo : orderOf x = 3) : 4 ≤ localRank 3 G := by
  obtain ⟨c01, c02, c12⟩ := conjugate_components_commute hL h01 h02 h12
  set L₁ := L.map (MulAut.conj g₁).toMonoidHom with hL₁def
  set L₂ := L.map (MulAut.conj g₂).toMonoidHom with hL₂def
  have c10 : L₁ ≤ centralizer (L : Set G) := le_centralizer_iff.1 c01
  have c20 : L₂ ≤ centralizer (L : Set G) := le_centralizer_iff.1 c02
  have hc0' := eq_one_of_mem_centralizer_of_center_eq_bot hZ
  have hc1' := Theta.eq_one_of_mem_map_conj hc0' g₁
  have hc2' := Theta.eq_one_of_mem_map_conj hc0' g₂
  set U' : Subgroup G := U.map L.subtype with hU'def
  have hU' : U' ≠ ⊥ := fun h => hU ((map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)
  have hU'2 : IsPGroup 2 U' := hU2.map L.subtype
  have hUL : U' ≤ L := map_subtype_le U
  set v₀ : G := (x : G) with hv₀def
  have hv₀L : v₀ ∈ L := x.2
  have hv₀N : v₀ ∈ normalizer (U' : Set G) := coe_mem_normalizer_map hxN
  have hv₀ : orderOf v₀ = 3 := by rw [hv₀def, Subgroup.orderOf_coe, hxo]
  have hCU : centralizer (L : Set G) ≤ normalizer (U' : Set G) :=
    (centralizer_le hUL).trans (centralizer_le_normalizer _)
  set v₁ : G := (MulAut.conj g₁).toMonoidHom v₀ with hv₁def
  set v₂ : G := (MulAut.conj g₂).toMonoidHom v₀ with hv₂def
  have hv₁L : v₁ ∈ L₁ := mem_map_of_mem _ hv₀L
  have hv₂L : v₂ ∈ L₂ := mem_map_of_mem _ hv₀L
  have hv₁ : orderOf v₁ = 3 := by rw [← hv₀]; exact MulEquiv.orderOf_eq _ v₀
  have hv₂ : orderOf v₂ = 3 := by rw [← hv₀]; exact MulEquiv.orderOf_eq _ v₀
  have hW₀c : ∀ w ∈ zpowers c, w ^ 3 = 1 := fun w hw => Theta.pow_eq_one_of_mem_zpowers hco hw
  obtain ⟨hW₁card, hW₁c, hW₁q⟩ := Theta.card_sup_zpowers_of_le_centralizer hc0'
    (zpowers_le.2 hc0) inferInstance hW₀c hv₀L hv₀
  obtain ⟨hW₂card, hW₂c, hW₂q⟩ := Theta.card_sup_zpowers_of_le_centralizer hc1'
    (sup_le (zpowers_le.2 hc1) ((zpowers_le.2 hv₀L).trans c01)) hW₁c hW₁q hv₁L hv₁
  obtain ⟨hW₃card, hW₃c, hW₃q⟩ := Theta.card_sup_zpowers_of_le_centralizer hc2'
    (sup_le (sup_le (zpowers_le.2 hc2) ((zpowers_le.2 hv₀L).trans c02))
      ((zpowers_le.2 hv₁L).trans c12)) hW₂c hW₂q hv₂L hv₂
  have hcard : Nat.card (zpowers c ⊔ zpowers v₀ ⊔ zpowers v₁ ⊔ zpowers v₂ : Subgroup G) =
      3 ^ 4 := by
    rw [hW₃card, hW₂card, hW₁card, Nat.card_zpowers, hco]
    norm_num
  have hWU : zpowers c ⊔ zpowers v₀ ⊔ zpowers v₁ ⊔ zpowers v₂ ≤ normalizer (U' : Set G) :=
    sup_le (sup_le (sup_le (zpowers_le.2 (hCU hc0)) (zpowers_le.2 hv₀N))
      (zpowers_le.2 (hCU (c10 hv₁L)))) (zpowers_le.2 (hCU (c20 hv₂L)))
  exact Theta.le_localRank_of_le_normalizer (by norm_num) hU' hU'2 hW₃c hW₃q hcard hWU

end Triple

omit [Finite G] in
theorem stabilizer_conjAction_eq (A L : Subgroup G) :
    letI := Theta.conjAction A
    MulAction.stabilizer A L = (normalizer (L : Set G)).subgroupOf A := by
  let := Theta.conjAction A
  ext a
  rw [MulAction.mem_stabilizer_iff, mem_subgroupOf]
  exact ⟨fun h => Theta.mem_normalizer_of_map_conj_eq_self h,
    fun h => Theta.map_conj_eq_of_mem_normalizer h⟩

theorem orbit_ncard_eq_three_of_center_free {A : Subgroup G} (hA : IsPGroup 3 A)
    {L : Subgroup G} (hL : IsComponent L) (hLA : ¬ A ≤ normalizer (L : Set G))
    (hZ : ∀ K : Subgroup G, IsComponent K → center K = ⊥) (hrank3 : localRank 3 G ≤ 3)
    (h3L : 3 ∣ Nat.card L) :
    letI := Theta.conjAction A
    (MulAction.orbit A L).ncard = 3 := by
  let := Theta.conjAction A
  have hstab := stabilizer_conjAction_eq A L
  have hidx := MulAction.index_stabilizer A L
  obtain ⟨j, hj⟩ := hA.index (MulAction.stabilizer A L)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, index_eq_one, hstab] at hj
    apply hLA
    intro a ha
    have h : (⟨a, ha⟩ : A) ∈ (normalizer (L : Set G)).subgroupOf A := hj ▸ mem_top _
    exact mem_subgroupOf.1 h
  have hOK : ∀ K ∈ MulAction.orbit A L, IsComponent K ∧ 3 ∣ Nat.card (K ⧸ center K) := by
    rintro _ ⟨a, rfl⟩
    change IsComponent (L.map (MulAut.conj (a : G)).toMonoidHom) ∧
      3 ∣ Nat.card ((L.map (MulAut.conj (a : G)).toMonoidHom) ⧸
        center (L.map (MulAut.conj (a : G)).toMonoidHom))
    have hKc : IsComponent (L.map (MulAut.conj (a : G)).toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv _ hL
    refine ⟨hKc, ?_⟩
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (L.map (MulAut.conj (a : G)).toMonoidHom))
    have h1 : Nat.card (center (L.map (MulAut.conj (a : G)).toMonoidHom)) = 1 := by
      rw [hZ _ hKc]
      exact Subgroup.card_bot
    rw [h1, mul_one, card_map_of_injective (MulAut.conj (a : G)).injective] at hcard
    rw [← hcard]
    exact h3L
  have hle : (MulAction.orbit A L).ncard ≤ 4 := by
    classical
    have hLns : ¬ Group.IsSolvable L := by
      have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
      have : Group.IsPerfect L := hL.1.1
      exact Group.IsPerfect.not_isSolvable L
    obtain ⟨u, hu⟩ := Theta.exists_orderOf_eq_two_of_not_isSolvable hLns
    let ι := ↥(MulAction.orbit A L \ {L})
    let : Fintype ι := Fintype.ofFinite ι
    have hι : ∀ i : ι, (i : Subgroup G) ∈ MulAction.orbit A L ∧ (i : Subgroup G) ≠ L :=
      fun i => ⟨i.2.1, i.2.2⟩
    have hcomm : ∀ i j : ι, i ≠ j → (j : Subgroup G) ≤ centralizer ((i : Subgroup G) : Set G) := by
      intro i j hij
      have hne : (j : Subgroup G) ≠ i := fun h => hij (Subtype.ext h.symm)
      exact commutator_eq_bot_iff_le_centralizer.1
        ((LocalCores.distinct_components_commute (hOK _ (hι j).1).1 (hOK _ (hι i).1).1).resolve_left
          hne)
    have hiL : ∀ i : ι, (i : Subgroup G) ≤ centralizer (L : Set G) := fun i =>
      commutator_eq_bot_iff_le_centralizer.1
        ((LocalCores.distinct_components_commute (hOK _ (hι i).1).1 hL).resolve_left (hι i).2)
    have hex : ∀ i : ι, ∃ y ∈ (i : Subgroup G), y ∉ centralizer ((i : Subgroup G) : Set G) ∧
        y ^ 3 ∈ centralizer ((i : Subgroup G) : Set G) := fun i =>
      Theta.exists_mem_not_centralizer_cube (hOK _ (hι i).1).2
    choose y hyK hy hy3 using hex
    have hyu : ∀ i, y i ∈ centralizer ({(u : G)} : Set G) := fun i =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hiL i (hyK i)) u u.2).symm
    have hcard := Theta.card_le_localRank_three (fun i : ι => (i : Subgroup G)) hcomm y hyK hy hy3
      (by rw [Subgroup.orderOf_coe, hu]) hyu
    have hι' : Fintype.card ι = (MulAction.orbit A L).ncard - 1 := by
      rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq,
        Set.ncard_sdiff_singleton_of_mem (MulAction.mem_orbit_self L)]
    omega
  rw [← hidx, hj] at hle ⊢
  rcases j with _ | _ | j
  · exact absurd rfl hj0
  · norm_num
  · exfalso
    have : 9 ≤ 3 ^ (j + 1 + 1) := by
      rw [pow_succ, pow_succ]
      have : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
      omega
    omega

omit [Finite G] in
theorem exists_ne_one_mem_centralizer_of_index_three {A : Subgroup G}
    (hAe : Assembly.IsElemAbelian 3 A) {n : ℕ} (hn : 3 ≤ n) (hAc : Nat.card A = 3 ^ n)
    {L : Subgroup G} (hidx : ((normalizer (L : Set G)).subgroupOf A).index = 3)
    (hAut : ∀ E : Subgroup (MulAut L), IsElementaryAbelian 3 E → Nat.card E ≤ 3) :
    ∃ c ∈ A, c ≠ 1 ∧ c ∈ centralizer (L : Set G) := by
  set H := (normalizer (L : Set G)).subgroupOf A with hHdef
  have hHcard : Nat.card H = 3 ^ (n - 1) := by
    have h := Subgroup.card_mul_index H
    rw [hidx, hAc] at h
    have h' : Nat.card H * 3 = 3 ^ (n - 1) * 3 := by
      rw [h, ← pow_succ, Nat.sub_add_cancel (by omega)]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  let ι : H →* normalizer (L : Set G) :=
    { toFun := fun h => ⟨((h : A) : G), mem_subgroupOf.1 h.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ψ : H →* MulAut L := L.normalizerMonoidHom.comp ι
  have : IsMulCommutative A := hAe.1
  have hcomm : ∀ a b : H, a * b = b * a := fun a b => Subtype.ext (mul_comm' (a : A) b)
  have hpow : ∀ a : H, a ^ 3 = 1 := fun a => Subtype.ext (Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    exact hAe.2 _ (a : A).2))
  have hR : IsElementaryAbelian 3 ψ.range := by
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      change (x : MulAut L) * y = y * x
      rw [← ha, ← hb, ← map_mul, ← map_mul, hcomm]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨a, ha⟩ := x.2
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← ha, ← map_pow, hpow, map_one, OneMemClass.coe_one]
  have hker : ψ.ker ≠ ⊥ := by
    intro hb
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hb
    have h1 : Nat.card ψ.range = Nat.card H :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have h2 := hAut _ hR
    rw [h1, hHcard] at h2
    have : 9 ≤ 3 ^ (n - 1) :=
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨c', hc'K⟩, hc'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  refine ⟨((c' : A) : G), (c' : A).2, fun h => hc'1 (Subtype.ext (Subtype.ext
    (Subtype.ext h))), ?_⟩
  have hmem : ι c' ∈ L.normalizerMonoidHom.ker := hc'K
  rw [Subgroup.normalizerMonoidHom_ker, mem_subgroupOf] at hmem
  exact hmem

theorem elementary_card_le_three_of_triple {G : Type} [Group G] [Finite G]
    (hK : SectionRank.IsKGroupCat G) {L : Subgroup G} (hL : IsComponent L) (hZ : center L = ⊥)
    {g₁ g₂ : G} (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom)
    (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) (hrank3 : localRank 3 G ≤ 3)
    {x₀ : G} (hx₀L : x₀ ∈ L) (hx₀ : orderOf x₀ = 3) :
    ∀ E : Subgroup (MulAut L), IsElementaryAbelian 3 E → Nat.card E ≤ 3 := by
  obtain ⟨hs, hnab⟩ := isSimpleGroup_of_center_eq_bot hL hZ
  have hcat : Blueprint.Catalog L := by
    have : IsSimpleGroup (L ⧸ (⊥ : Subgroup L)) := QuotientGroup.quotientBot.isSimpleGroup
    exact SectionRank.catalog_of_mulEquiv QuotientGroup.quotientBot.symm (hK L ⊥ this)
  have hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r L ≤ 1 := fun r hr hr2 => by
    rw [pRank_coe_eq_assembly_pRank]
    have hr3 : r = 3 ∨ 3 < r := by
      have := hr.two_le
      omega
    rcases hr3 with rfl | hr3'
    · exact pRank_le_one_of_triple hL hZ h01 h02 h12 hr hrank3 (fun h => absurd h (lt_irrefl 3))
        (Or.inl rfl)
    · exact pRank_le_one_of_triple hL hZ h01 h02 h12 hr ((hq r hr hr3').trans (by norm_num))
        (fun _ => hq r hr hr3') (Or.inr hr3')
  have h3 : CFSG.pRank 3 L = 1 := by
    refine le_antisymm (hodd 3 Nat.prime_three (by norm_num)) ?_
    rw [pRank_coe_eq_assembly_pRank]
    exact SectionRank.le_pRank (by norm_num) (zpowers_le.2 hx₀L)
      ⟨inferInstance, fun w hw => hx₀ ▸ pow_orderOf_eq_one_of_mem_zpowers hw⟩
      (by rw [Nat.card_zpowers, hx₀, pow_one])
  exact (ThinCatalog.thin_catalog_two_local_prime_support_outer_three_free L hnab hcat hodd h3
    fun V hV hV2 r hr hrd => prime_dvd_card_normalizer_of_triple hL hZ h01 h02 h12 hq hV hV2 hr
      hrd).2

theorem normalizes_of_isElemAbelian_of_pCore_eq_bot {G : Type} [Group G] [Finite G]
    (hK : SectionRank.IsKGroupCat G) (hθ : aschbacherSolvableCore 3 G = ⊥)
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2)
    (h3 : pCore 3 G = ⊥) {A : Subgroup G} (hAe : Assembly.IsElemAbelian 3 A) {n : ℕ}
    (hn : 3 ≤ n) (hAc : Nat.card A = 3 ^ n) {L : Subgroup G} (hL : IsComponent L) :
    A ≤ normalizer (L : Set G) := by
  by_contra hLA
  have hA : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hAe.2 _ a.2, Subgroup.coe_one])⟩
  have hZ := center_eq_bot_of_pCore_eq_bot hθ h3 hL
  obtain ⟨g₁, hg₁, g₂, hg₂, h01, h02, h12⟩ := exists_triple_of_not_le_normalizer hA hLA
  obtain ⟨U, hU, hU2, x, hxN, hxo⟩ :=
    exists_two_subgroup_three_normalizer_of_triple hL hZ h01 h02 h12 hq
  have hxo' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hxo]
  have h3L : 3 ∣ Nat.card L := hxo ▸ orderOf_dvd_natCard x
  have h3G : 3 ∣ Nat.card G := h3L.trans (Subgroup.card_subgroup_dvd_card L)
  have hrank3 : localRank 3 G ≤ 3 :=
    (Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num) h3G).trans he
  have hd := orbit_ncard_eq_three_of_center_free hA hL hLA
    (fun K hK' => center_eq_bot_of_pCore_eq_bot hθ h3 hK') hrank3 h3L
  have hidx : ((normalizer (L : Set G)).subgroupOf A).index = 3 := by
    let := Theta.conjAction A
    rw [← stabilizer_conjAction_eq A L, MulAction.index_stabilizer]
    exact hd
  have hAut := elementary_card_le_three_of_triple hK hL hZ h01 h02 h12 hq hrank3 x.2 hxo'
  obtain ⟨c, hcA, hc1, hcL⟩ := exists_ne_one_mem_centralizer_of_index_three hAe hn hAc hidx hAut
  have : IsMulCommutative A := hAe.1
  have hcomm : ∀ g ∈ A, c * g = g * c := fun g hg =>
    congrArg Subtype.val (mul_comm' (⟨c, hcA⟩ : A) ⟨g, hg⟩)
  have hco : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have h4 := four_le_localRank_three_of_triple hL hZ h01 h02 h12 hcL
    (mem_centralizer_map_conj_of_commute (hcomm g₁ hg₁) hcL)
    (mem_centralizer_map_conj_of_commute (hcomm g₂ hg₂) hcL) hco hU hU2 hxN hxo
  omega

end CFSG.RankThree.ThetaFree
