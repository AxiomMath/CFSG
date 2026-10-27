module

public import CFSG.RankThree.PartOne.KF.F128Order
public import CFSG.RankThree.PartOne.S11d.FieldTransfer
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.RankThree.PartOne.S12K (charTwoOrder)

variable {T : Type} [Group T]

theorem fixRes_centralizer_trivial {p : ℕ} {α : MulAut T} (hF : FixedFacts p α) {g : T}
    (hg : ∀ x ∈ fixRes α, x * g = g * x) : g = 1 := by
  by_contra hg1
  have hsolv : Group.IsSolvable ↥(Subgroup.zpowers g) := by
    have : IsCyclic ↥(Subgroup.zpowers g) := inferInstance
    have : CommGroup ↥(Subgroup.zpowers g) := IsCyclic.commGroup
    infer_instance
  refine hF.nonLocalized (Subgroup.zpowers g) (fun h => hg1 (Subgroup.zpowers_eq_bot.mp h))
    hsolv ?_
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left (show Commute g x from (hg x hx).symm) i).eq

theorem not_pGroup_le_fixSub
    [Finite T] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {α : MulAut T}
    (hF : FixedFacts p α) {P : Subgroup T} (hPp : IsPGroup p P)
    (hPc : Nat.card P = p ^ (Nat.card T).factorization p) (hpT : p ∣ Nat.card T)
    (hPfix : P ≤ fixSub α) : False := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨t, n, f, hf, hM, hX⟩ := hF.fieldAutT
  obtain ⟨hadm', hTcard⟩ := S12K.card_of_lieModel_two hM
  set N : Subgroup T := fixRes α with hN
  have hPN : P ≤ N := by
    intro x hx
    refine hF.pElements x (hPfix hx) ?_
    obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
    have h1 : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  have hZN : Subgroup.center ↥N = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply Subtype.ext
    refine fixRes_centralizer_trivial hF (g := (z : T)) fun x hx => ?_
    have := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hNcard : Nat.card ↥N = Nat.card (↥N ⧸ Subgroup.center ↥N) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥N)
    have hc : Nat.card ↥(Subgroup.center ↥N) = 1 := by rw [hZN]; exact Subgroup.card_bot
    rw [hc, mul_one] at h
    exact h
  have hdvdN : p ^ (Nat.card T).factorization p ∣ Nat.card ↥N := by
    rw [← hPc]
    exact Subgroup.card_dvd_of_le hPN
  have hNpos : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hle : (Nat.card T).factorization p ≤ (Nat.card ↥N).factorization p :=
    (hp.pow_dvd_iff_le_factorization hNpos).mp hdvdN
  rw [hTcard] at hle hpT
  rcases hX with hX | ⟨rfl, rfl, rfl, hX⟩
  · obtain ⟨hadm, hXcard⟩ := S12K.card_of_lieModel_two hX
    rw [hNcard, hXcard] at hle
    exact absurd (charTwoOrder_pval_lt hp h5 hadm hadm' hpT) (not_lt.mpr hle)
  · obtain ⟨-, hXcard⟩ := S12K.card_of_lieModel_two hX
    rw [hNcard, hXcard] at hle
    have hQ : 2 ≤ 2 := le_rfl
    have hpQ : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
    have hpT' : p ∣ ordTwistedF4 (2 ^ p) := by simpa [charTwoOrder] using hpT
    have h1 := ordTwistedF4_lt hp hp2 hp3 hQ hpQ hpT'
    have h2 : ordTwistedF4 2 = 2 * ordTits := by norm_num [ordTwistedF4, ordTits]
    have h3 : (ordTwistedF4 2).factorization p = (ordTits).factorization p := by
      rw [h2, Nat.factorization_mul (by norm_num) (by norm_num [ordTits])]
      simp [Nat.factorization_eq_zero_of_not_dvd hpQ]
    simp only [charTwoOrder, mul_one] at hle
    omega

theorem card_map_eq_of_injOn {C F : Type*} [Group C] [Group F] (θ : C →* F) (S : Subgroup C)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y) : Nat.card (S.map θ) = Nat.card S := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : S => (⟨θ x, x, x.2, rfl⟩ : S.map θ)) ⟨?_, ?_⟩)
  · intro x y hxy
    exact Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem le_pRank_of_card' {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H]
    (E : Subgroup H) (hE : CFSG.IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

variable {G : Type} [Group G]

theorem sylow_moves_of_fixedFacts
    [Finite G] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {J : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hpJ : p ∣ Nat.card J) {a : G}
    (hu : a ∈ Subgroup.normalizer (J : Set G))
    (hF : FixedFacts p (centerQuotientConj J ⟨a, hu⟩)) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S J) : ¬ ∀ s ∈ S, a * s * a⁻¹ = s := by
  intro hcent
  have : Fact p.Prime := ⟨hp⟩
  set α : MulAut (↥J ⧸ Subgroup.center ↥J) := centerQuotientConj J ⟨a, hu⟩ with hα
  have hSJ : S ≤ J := hS.le
  set πJ : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  set S₀ : Subgroup ↥J := S.subgroupOf J with hS₀
  set Sbar : Subgroup (↥J ⧸ Subgroup.center ↥J) := S₀.map πJ with hSbar
  have hS₀p : IsPGroup p S₀ := hS.isPGroup.comap_subtype
  have hinj : ∀ x ∈ S₀, ∀ y ∈ S₀, πJ x = πJ y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ Subgroup.center ↥J := QuotientGroup.eq.mp hxy
    have hxy' : x⁻¹ * y ∈ S₀ := S₀.mul_mem (S₀.inv_mem hx) hy
    obtain ⟨k, hk⟩ := hS₀p ⟨x⁻¹ * y, hxy'⟩
    have hk' : (x⁻¹ * y) ^ (p ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : orderOf (⟨x⁻¹ * y, hz⟩ : Subgroup.center ↥J) ∣
        Nat.card (Subgroup.center ↥J) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero] at hj
      exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp hj)
    · exfalso
      apply hZ
      rw [hj] at hdvd
      exact (dvd_pow_self p hj0).trans hdvd
  have hSbarcard : Nat.card Sbar = Nat.card S := by
    rw [hSbar, card_map_eq_of_injOn πJ S₀ hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSJ).toEquiv
  have hJT : Nat.card ↥J = Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hfact : (Nat.card ↥J).factorization p =
      (Nat.card (↥J ⧸ Subgroup.center ↥J)).factorization p := by
    rw [hJT, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hZ, add_zero]
  have hSbarcard' : Nat.card Sbar =
      p ^ (Nat.card (↥J ⧸ Subgroup.center ↥J)).factorization p := by
    rw [hSbarcard, hS.card_eq, hfact]
  have hpT : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rw [hJT] at hpJ
    exact ((Nat.Prime.dvd_mul hp).mp hpJ).resolve_right hZ
  have hSbarp : IsPGroup p Sbar := hS₀p.map πJ
  have hSbarfix : Sbar ≤ fixSub α := by
    rintro _ ⟨x, hx, rfl⟩
    show α (πJ x) = πJ x
    have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    have h1 : α (πJ x) = πJ ⟨a * (x : G) * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp hu (x : G)).mp x.2⟩ := rfl
    rw [h1]
    congr 1
    exact Subtype.ext (hcent x hxS)
  exact not_pGroup_le_fixSub hp h5 hF hSbarp hSbarcard' hpT hSbarfix

theorem fieldAut_moves_sylow
    [Finite G] (hT : ∀ t, TagFixedFacts t) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {J : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥J) (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (hJ : CFSG.pRank p ↥J ≤ 1) (hpJ : p ∣ Nat.card J) {a : G} (hap : a ^ p = 1)
    (hfa : InducesFieldAut p a J) {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf p S J) :
    ¬ ∀ s ∈ S, a * s * a⁻¹ = s := by
  have : Fact p.Prime := ⟨hp⟩
  have hu : a ∈ Subgroup.normalizer (J : Set G) := hfa.1
  have huJ : a ∉ J ⊔ Subgroup.centralizer (J : Set G) := hfa.2.1
  set α : MulAut (↥J ⧸ Subgroup.center ↥J) := centerQuotientConj J ⟨a, hu⟩ with hα
  have hinn : α ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨q, hq'⟩
    exact huJ (mem_sup_of_inner hq.1 hu hq'.symm)
  have hαp : α ^ p = 1 := centerQuotientConj_pow hu hap
  have hT1 : CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) ≤ 1 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hZ]
    exact hJ
  have hLR2 : LocalRankLeTwo p (↥J ⧸ Subgroup.center ↥J) := by
    intro R hR hRc U _ _ _
    have := le_pRank_of_card' hp.one_lt R hR hRc
    omega
  have hLRA : LocalRankAut p (↥J ⧸ Subgroup.center ↥J) α := by
    intro _ _ R hR hRc _ U _ _ _ _
    have := le_pRank_of_card' hp.one_lt R hR hRc
    omega
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := fieldAutT_of_inducesFieldAut hp hZ hu hap hfa
  have hs1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have : p ∣ 1 := by exact_mod_cast h
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hF : FixedFacts p α :=
    hT t _ p hp h5 hLR2 n f₀ hf₀ hM α hαp hinn hLRA hX α hαp hinn hLRA
      ⟨1, hs1, by rw [zpow_one, mul_inv_cancel]; exact Subgroup.one_mem _⟩
  exact sylow_moves_of_fixedFacts hp h5 hZ hpJ hu hF hS

end CFSG.RankThree.PartOne
