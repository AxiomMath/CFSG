module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.RankThree.PGroups.ZJCenterIntersection

public section

namespace CFSG.RankThree.Theta

open Subgroup
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_normalizer_of_map_conj_eq {L : Subgroup G} {g h : G}
    (heq : L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj h).toMonoidHom) :
    h⁻¹ * g ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨y', hy', hyy'⟩ : (MulAut.conj g).toMonoidHom y ∈ L.map (MulAut.conj h).toMonoidHom :=
      heq ▸ mem_map_of_mem _ hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy'
    have e : h⁻¹ * g * y * (h⁻¹ * g)⁻¹ = y' := by
      rw [show y' = h⁻¹ * (h * y' * h⁻¹) * h by group, hyy']
      group
    rw [e]
    exact hy'
  · intro hy
    obtain ⟨y', hy', hyy'⟩ : (MulAut.conj h).toMonoidHom (h⁻¹ * g * y * (h⁻¹ * g)⁻¹) ∈
        L.map (MulAut.conj g).toMonoidHom :=
      heq ▸ mem_map_of_mem _ hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy'
    have e : y' = y := by
      have h2 : g * y' * g⁻¹ = g * y * g⁻¹ := by
        rw [hyy']
        group
      simpa using h2
    rw [← e]
    exact hy'

theorem mem_normalizer_of_map_conj_eq_self {L : Subgroup G} {g : G}
    (heq : L.map (MulAut.conj g).toMonoidHom = L) : g ∈ normalizer (L : Set G) := by
  have h := mem_normalizer_of_map_conj_eq (L := L) (g := g) (h := 1) (by
    rw [heq]
    ext y
    simp)
  rwa [inv_one, one_mul] at h

theorem eq_one_of_mem_map_conj {L : Subgroup G}
    (hc : ∀ y ∈ L, y ∈ centralizer (L : Set G) → y = 1) (g : G) :
    ∀ y ∈ L.map (MulAut.conj g).toMonoidHom,
      y ∈ centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → y = 1 := by
  rintro _ ⟨y, hy, rfl⟩ hyc
  have hyL : y ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h := mem_centralizer_iff.1 hyc _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hl)
    rw [← map_mul, ← map_mul] at h
    exact (MulAut.conj g).injective h
  rw [hc y hy hyL, map_one]

theorem pow_eq_one_of_mem_zpowers {q : ℕ} {v w : G} (hv : orderOf v = q) (hw : w ∈ zpowers v) :
    w ^ q = 1 := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hv, pow_orderOf_eq_one,
    one_zpow]

theorem card_sup_zpowers_of_le_centralizer {q : ℕ} {W K : Subgroup G}
    (hK : ∀ y ∈ K, y ∈ centralizer (K : Set G) → y = 1) (hWK : W ≤ centralizer (K : Set G))
    (hWc : IsMulCommutative W) (hWq : ∀ w ∈ W, w ^ q = 1) {v : G} (hvK : v ∈ K)
    (hv : orderOf v = q) :
    Nat.card (W ⊔ zpowers v : Subgroup G) = Nat.card W * q ∧
      IsMulCommutative (W ⊔ zpowers v : Subgroup G) ∧ ∀ w ∈ W ⊔ zpowers v, w ^ q = 1 := by
  have hvc : v ∈ centralizer (W : Set G) :=
    mem_centralizer_iff.2 fun w hw => (mem_centralizer_iff.1 (hWK hw) v hvK).symm
  have hle : zpowers v ≤ normalizer (W : Set G) := zpowers_le.2 (centralizer_le_normalizer _ hvc)
  have hdisj : W ⊓ zpowers v = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    rw [mem_bot]
    exact hK y (zpowers_le.2 hvK hy.2) (hWK hy.1)
  refine ⟨?_, PGroups.isMulCommutative_sup_zpowers hWc hvc, fun w hw => ?_⟩
  · rw [CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj, Nat.card_zpowers, hv]
  · have hw' : w ∈ (W : Set G) * (zpowers v : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left W _ hle]
      exact hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    have hcomm : Commute a (v ^ n) :=
      (show Commute a v from mem_centralizer_iff.1 hvc a ha).zpow_right n
    rw [hcomm.mul_pow, hWq a ha, one_mul]
    exact pow_eq_one_of_mem_zpowers hv (zpow_mem (mem_zpowers v) n)

variable [Finite G]

theorem le_localRank_of_le_normalizer {q : ℕ} (hq : 1 < q) {U W : Subgroup G} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hWc : IsMulCommutative W) (hWq : ∀ w ∈ W, w ^ q = 1) {k : ℕ}
    (hWk : Nat.card W = q ^ k) (hWU : W ≤ normalizer (U : Set G)) : k ≤ localRank q G := by
  have hbdd : BddAbove
      {k | ∃ H : Subgroup G, Assembly.IsTwoLocal H ∧ Assembly.pRank q H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := SectionRank.exists_pRank hq H
    have h1 : Open.pRank q H < q ^ Open.pRank q H := Nat.lt_pow_self hq
    have h2 : Nat.card E ≤ Nat.card G := card_le_card_group E
    change Open.pRank q H ≤ Nat.card G
    omega
  exact (SectionRank.le_pRank hq hWU ⟨hWc, hWq⟩ hWk).trans
    (le_csSup hbdd ⟨_, ⟨U, hU, hU2, rfl⟩, rfl⟩)

theorem exists_two_subgroup_odd_prime_normalizer {K : Type*} [Group K] [Finite K]
    (hK : ¬ Group.IsSolvable K) :
    ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      ∃ v ∈ normalizer (U : Set K), orderOf v = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hnorm : ∀ U : Subgroup K, U ≠ ⊥ → IsPGroup 2 U → IsPGroup 2 (normalizer (U : Set K)) := by
    intro U hU hU2
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun {d} hd hdN => ?_)
    by_contra hd2
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' d hdN
    exact hcon U hU hU2 d hd hd2 v v.2 (by rw [orderOf_coe, hv])
  obtain ⟨R, hRn, hRc, k, hk⟩ := (GroupTheory.frobenius_normal_p_complement (G := K) 2).1.2
    fun Q hQ => by
      by_cases hQb : Q = ⊥
      · subst hQb
        refine IsPGroup.of_card (n := 0) ?_
        rw [pow_zero, ← index_eq_card, index_eq_one, subgroupOf_eq_top]
        exact fun g _ => mem_centralizer_iff.2 fun h hh => by
          rw [show h = 1 from mem_bot.1 hh, one_mul, mul_one]
      · exact (hnorm Q hQb hQ).to_quotient _
  apply hK
  have : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_right.1 hRc)
  have : Group.IsSolvable (K ⧸ R) := by
    have hp : IsPGroup 2 (K ⧸ R) := IsPGroup.of_card (n := k) (by rw [← index_eq_card]; exact hk)
    have := hp.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', range_subtype])

theorem normal_three_core_forces_center_free_component_normalization
    (h3 : pCore 3 G ≠ ⊥) (hrank3 : localRank 3 G ≤ 3)
    (hrankq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) {A : Subgroup G}
    (hA : IsPGroup 3 A) {L : Subgroup G} (hL : IsComponent L) (hZ : center L = ⊥) :
    A ≤ normalizer (L : Set G) := by
  intro x hxA
  by_contra hxL
  obtain ⟨k, hk⟩ := hA ⟨x, hxA⟩
  have hx3 : x ^ 3 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    rwa [coe_pow, coe_one] at h
  have hsq : x ^ 2 ∈ normalizer (L : Set G) → x ∈ normalizer (L : Set G) := by
    intro h
    obtain ⟨c, hc⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have e : (x ^ 2) ^ (c + 1) = x := by
      rw [← pow_mul, show 2 * (c + 1) = 3 ^ k + 1 by rw [hc]; ring, pow_succ, hx3, one_mul]
    rw [← e]
    exact pow_mem h _
  set L₁ := L.map (MulAut.conj x).toMonoidHom with hL₁def
  set L₂ := L.map (MulAut.conj (x ^ 2)).toMonoidHom with hL₂def
  have hL₁ : IsComponent L₁ := LocalCores.isComponent_map_mulEquiv _ hL
  have hL₂ : IsComponent L₂ := LocalCores.isComponent_map_mulEquiv _ hL
  have h01 : L ≠ L₁ := fun h => hxL (mem_normalizer_of_map_conj_eq_self h.symm)
  have h02 : L ≠ L₂ := fun h => hxL (hsq (mem_normalizer_of_map_conj_eq_self h.symm))
  have h12 : L₁ ≠ L₂ := fun h => hxL (by
    have h' := mem_normalizer_of_map_conj_eq h.symm
    rwa [pow_two, inv_mul_cancel_left] at h')
  have c01 : L ≤ centralizer (L₁ : Set G) := commutator_eq_bot_iff_le_centralizer.1
    ((LocalCores.distinct_components_commute hL hL₁).resolve_left h01)
  have c02 : L ≤ centralizer (L₂ : Set G) := commutator_eq_bot_iff_le_centralizer.1
    ((LocalCores.distinct_components_commute hL hL₂).resolve_left h02)
  have c12 : L₁ ≤ centralizer (L₂ : Set G) := commutator_eq_bot_iff_le_centralizer.1
    ((LocalCores.distinct_components_commute hL₁ hL₂).resolve_left h12)
  have c10 : L₁ ≤ centralizer (L : Set G) := le_centralizer_iff.1 c01
  have c20 : L₂ ≤ centralizer (L : Set G) := le_centralizer_iff.1 c02
  have hc0 : ∀ y ∈ L, y ∈ centralizer (L : Set G) → y = 1 := fun y hy hyc => by
    have h : (⟨y, hy⟩ : L) ∈ center L :=
      mem_center_iff.2 fun l => Subtype.ext (mem_centralizer_iff.1 hyc l l.2)
    rw [hZ, mem_bot] at h
    exact congrArg Subtype.val h
  have hc1 := eq_one_of_mem_map_conj hc0 x
  have hc2 := eq_one_of_mem_map_conj hc0 (x ^ 2)
  have hLns : ¬ Group.IsSolvable L := by
    have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect L := hL.1.1
    exact Group.IsPerfect.not_isSolvable L
  obtain ⟨U', hU'ne, hU'2, q, hq, hq2, v', hv'N, hv'⟩ :=
    exists_two_subgroup_odd_prime_normalizer hLns
  set U : Subgroup G := U'.map L.subtype with hUdef
  have hU : U ≠ ⊥ := fun h => hU'ne ((map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)
  have hU2 : IsPGroup 2 U := hU'2.map L.subtype
  have hUL : U ≤ L := map_subtype_le U'
  set v₀ : G := (v' : G)
  have hv₀L : v₀ ∈ L := v'.2
  have hv₀N : v₀ ∈ normalizer (U : Set G) := le_normalizer_map L.subtype (mem_map_of_mem _ hv'N)
  have hv₀ : orderOf v₀ = q := by rw [orderOf_coe, hv']
  have hCU : centralizer (L : Set G) ≤ normalizer (U : Set G) :=
    (centralizer_le hUL).trans (centralizer_le_normalizer _)
  set v₁ : G := (MulAut.conj x).toMonoidHom v₀
  set v₂ : G := (MulAut.conj (x ^ 2)).toMonoidHom v₀
  have hv₁L : v₁ ∈ L₁ := mem_map_of_mem _ hv₀L
  have hv₂L : v₂ ∈ L₂ := mem_map_of_mem _ hv₀L
  have hv₁ : orderOf v₁ = q := by rw [← hv₀]; exact MulEquiv.orderOf_eq _ v₀
  have hv₂ : orderOf v₂ = q := by rw [← hv₀]; exact MulEquiv.orderOf_eq _ v₀
  have hv₀c : ∀ w ∈ zpowers v₀, w ^ q = 1 := fun w hw => pow_eq_one_of_mem_zpowers hv₀ hw
  by_cases hq3 : q = 3
  ·
    subst hq3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hP3 : IsPGroup 3 (pCore 3 G) := pCore_isPGroup
    obtain ⟨z, hz⟩ : ∃ z : pCore 3 G, orderOf z = 3 := by
      obtain ⟨n, hn⟩ := hP3.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero, card_eq_one] at hn
        exact h3 hn
      exact exists_prime_orderOf_dvd_card' 3 (by rw [hn]; exact dvd_pow_self 3 hn0)
    have hPs : Group.IsSolvable (pCore 3 G) := by
      have := hP3.isNilpotent
      infer_instance
    have hPcen : ∀ K : Subgroup G, IsComponent K → pCore 3 G ≤ centralizer (K : Set G) :=
      fun K hK => le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1
        ((LocalCores.component_solvable_centralizer hPs
          (inferInstance : (pCore 3 G).Normal).isSubnormal).1 K hK))
    have hzP : (z : G) ∈ pCore 3 G := z.2
    have hz' : orderOf (z : G) = 3 := by rw [orderOf_coe, hz]
    have hW₀c : ∀ w ∈ zpowers (z : G), w ^ 3 = 1 := fun w hw => pow_eq_one_of_mem_zpowers hz' hw
    have hzL : zpowers (z : G) ≤ centralizer (L : Set G) := zpowers_le.2 (hPcen L hL hzP)
    obtain ⟨hW₁card, hW₁c, hW₁q⟩ := card_sup_zpowers_of_le_centralizer hc0 hzL inferInstance
      hW₀c hv₀L hv₀
    obtain ⟨hW₂card, hW₂c, hW₂q⟩ := card_sup_zpowers_of_le_centralizer hc1
      (sup_le (zpowers_le.2 (hPcen L₁ hL₁ hzP)) ((zpowers_le.2 hv₀L).trans c01)) hW₁c hW₁q
      hv₁L hv₁
    obtain ⟨hW₃card, hW₃c, hW₃q⟩ := card_sup_zpowers_of_le_centralizer hc2
      (sup_le (sup_le (zpowers_le.2 (hPcen L₂ hL₂ hzP)) ((zpowers_le.2 hv₀L).trans c02))
        ((zpowers_le.2 hv₁L).trans c12)) hW₂c hW₂q hv₂L hv₂
    have hWU : zpowers (z : G) ⊔ zpowers v₀ ⊔ zpowers v₁ ⊔ zpowers v₂ ≤ normalizer (U : Set G) :=
      sup_le (sup_le (sup_le (hzL.trans hCU) (zpowers_le.2 hv₀N))
        ((zpowers_le.2 hv₁L).trans (c10.trans hCU))) ((zpowers_le.2 hv₂L).trans (c20.trans hCU))
    have h4 := le_localRank_of_le_normalizer (k := 4) (by norm_num) hU hU2 hW₃c hW₃q
      (by rw [hW₃card, hW₂card, hW₁card, Nat.card_zpowers, hz']; norm_num) hWU
    omega
  ·
    have hq3' : 3 < q := by
      have := hq.two_le
      omega
    obtain ⟨hW₁card, hW₁c, hW₁q⟩ := card_sup_zpowers_of_le_centralizer hc1
      ((zpowers_le.2 hv₀L).trans c01) inferInstance hv₀c hv₁L hv₁
    obtain ⟨hW₂card, hW₂c, hW₂q⟩ := card_sup_zpowers_of_le_centralizer hc2
      (sup_le ((zpowers_le.2 hv₀L).trans c02) ((zpowers_le.2 hv₁L).trans c12)) hW₁c hW₁q hv₂L
      hv₂
    have hWU : zpowers v₀ ⊔ zpowers v₁ ⊔ zpowers v₂ ≤ normalizer (U : Set G) :=
      sup_le (sup_le (zpowers_le.2 hv₀N) ((zpowers_le.2 hv₁L).trans (c10.trans hCU)))
        ((zpowers_le.2 hv₂L).trans (c20.trans hCU))
    have h3' := le_localRank_of_le_normalizer (k := 3) hq.one_lt hU hU2 hW₂c hW₂q
      (by rw [hW₂card, hW₁card, Nat.card_zpowers, hv₀]; ring) hWU
    have := hrankq q hq hq3'
    omega

end CFSG.RankThree.Theta
