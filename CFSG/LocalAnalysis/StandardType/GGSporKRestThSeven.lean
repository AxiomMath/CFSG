module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestOrderE
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.RankThree.PartOne.CTP.SporadicFusionTh
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
public import CFSG.Sporadic.Bridge.ThSurj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne.CTP.Fus
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
  (card_closure_pair_eq_sq exists_pow_mul_pow_of_mem factorization_pow_mul orderOf_inv_mul_mul)
open scoped Pointwise

theorem sporKRestControlsAt_of_isConj {K : Type} [Group K] {x y : K} {Y : Subgroup K}
    (hY : SporKRestControlsAt x Y) (hxy : IsConj x y) (hyY : y ∈ Y) :
    SporKRestControlsAt y Y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  have hcY : c⁻¹ ∈ Y := hY c⁻¹ (by rw [inv_inv, hc]; exact hyY)
  intro g hg
  have h2 : c⁻¹ * g ∈ Y := hY _ (by
    have : (c⁻¹ * g)⁻¹ * x * (c⁻¹ * g) = g⁻¹ * (c * x * c⁻¹) * g := by group
    rw [this, hc]
    exact hg)
  simpa using Y.mul_mem (Y.inv_mem hcY) h2

theorem sporKRest_generating_of_fusionGeneration {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hfus : FusionGenerationOf K p)
    (hone : ∀ s t : K, orderOf s = p → orderOf t = p → IsConj s t) {x : K} (hx : orderOf x = p) :
    SporKRestGenerating p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, Γ, hE, -, hΓ, hΓE⟩ := hfus
  rintro Y ⟨Q, hQY⟩ hctl
  obtain ⟨Q', hEQ'⟩ := hE.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q Q'
  have hconj : ∀ u ∈ E, k⁻¹ * u * k ∈ Y := by
    intro u hu
    have h1 : u ∈ (Q' : Set K) := hEQ' hu
    have h2 : MulAut.conj k⁻¹ u ∈ (MulAut.conj k⁻¹ • (Q' : Set K)) := Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, ← hk, inv_smul_smul] at h2
    have h3 : k⁻¹ * u * k ∈ Q := by simpa [MulAut.conj_apply] using h2
    exact hQY h3
  have hmem : ∀ g ∈ Γ, k⁻¹ * g * k ∈ Y := by
    intro g hg
    obtain ⟨e, he, he1, hge⟩ := hΓE g hg
    obtain ⟨m, hm⟩ := hE ⟨e, he⟩
    have hepow : e ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hepow)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact he1 (orderOf_eq_one_iff.1 (by simpa using hi))
    have hpd : p ∣ orderOf e := by rw [hi]; exact dvd_pow_self p hi0
    have hord0 : orderOf e ≠ 0 := by rw [hi]; exact pow_ne_zero _ hp.ne_zero
    have he'o : orderOf (e ^ (orderOf e / p)) = p := orderOf_pow_orderOf_div hord0 hpd
    have he'E : e ^ (orderOf e / p) ∈ E := E.pow_mem he _
    have hge' : g * e ^ (orderOf e / p) * g⁻¹ ∈ E := by
      rw [← conj_pow]
      exact E.pow_mem hge _
    have he₁Y : k⁻¹ * e ^ (orderOf e / p) * k ∈ Y := hconj _ he'E
    have he₁o : orderOf (k⁻¹ * e ^ (orderOf e / p) * k) = p := by
      rw [orderOf_inv_mul_mul]; exact he'o
    have hctl₁ := sporKRestControlsAt_of_isConj hctl (hone x _ hx he₁o) he₁Y
    have hg₁ : (k⁻¹ * g * k) * (k⁻¹ * e ^ (orderOf e / p) * k) * (k⁻¹ * g * k)⁻¹ ∈ Y := by
      have h := hconj _ hge'
      have : (k⁻¹ * g * k) * (k⁻¹ * e ^ (orderOf e / p) * k) * (k⁻¹ * g * k)⁻¹ =
          k⁻¹ * (g * e ^ (orderOf e / p) * g⁻¹) * k := by group
      rw [this]
      exact h
    have h3 : (k⁻¹ * g * k)⁻¹ ∈ Y := hctl₁ _ (by rw [inv_inv]; exact hg₁)
    simpa using Y.inv_mem h3
  have hle : (⊤ : Subgroup K) ≤ Subgroup.comap (MulAut.conj k⁻¹).toMonoidHom Y := by
    rw [← hΓ, Subgroup.closure_le]
    intro g hg
    simpa [Subgroup.mem_comap, MulAut.conj_apply] using hmem g hg
  rw [eq_top_iff]
  intro h _
  have := hle (Subgroup.mem_top (k * h * k⁻¹))
  simpa [Subgroup.mem_comap, MulAut.conj_apply, mul_assoc] using this

theorem sporKRest_exists_conj_of_pair {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y z : G} (hcomm : x * y = y * x) (hx : x ^ p = 1) (hy : y ^ p = 1) (hx1 : x ≠ 1)
    (hpow : ∀ k < p, y ≠ x ^ k) (hfac : (Nat.card G).factorization p = 2)
    (hconj : ∀ i j : ℕ, i < p → j < p → i + j ≠ 0 → ∃ m : G, m * (x ^ i * y ^ j) = z * m)
    {s : G} (hs : orderOf s = p) : ∃ m : G, m * s * m⁻¹ = z := by
  have hG : ¬ p ^ 3 ∣ Nat.card G := by
    intro h
    have h0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have := (hp.out.pow_dvd_iff_le_factorization h0).1 h
    omega
  have hQ := card_closure_pair_eq_sq hcomm hx hy hx1 hpow hG
  have hQfull : Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
    rw [hQ, Subgroup.card_top, hfac]
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨i, hi, j, hj, hw⟩ := exists_pow_mul_pow_of_mem hp.out.pos hcomm hx hy hgQ
  have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
  have hij : i + j ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    rw [hi0, hj0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  obtain ⟨m, hm⟩ := hconj i j hi hj hij
  refine ⟨m * g⁻¹, ?_⟩
  rw [← hw] at hm
  calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
    _ = z := by rw [hm]; group

theorem sporKRest_isConj_orderOf_of_pair {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {x y z : G} (hcomm : x * y = y * x) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hx1 : x ≠ 1) (hpow : ∀ k < p, y ≠ x ^ k) (hfac : (Nat.card G).factorization p = 2)
    (hconj : ∀ i j : ℕ, i < p → j < p → i + j ≠ 0 → ∃ m : G, m * (x ^ i * y ^ j) = z * m) :
    orderOf z = p ∧ ∀ s : G, orderOf s = p → IsConj z s := by
  refine ⟨?_, fun s hs => ?_⟩
  · obtain ⟨m, hm⟩ := hconj 1 0 hp.out.one_lt hp.out.pos (by norm_num)
    rw [pow_one, pow_zero, mul_one] at hm
    have hz : z = m * x * m⁻¹ := by rw [hm]; group
    rw [hz, show m * x * m⁻¹ = MulAut.conj m x from rfl, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hx hx1
  · obtain ⟨m, hm⟩ := sporKRest_exists_conj_of_pair hcomm hx hy hx1 hpow hfac hconj hs
    exact isConj_iff.2 ⟨m⁻¹, by rw [← hm]; group⟩

theorem sporKRest_isConj_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a b : G}
    (h : IsConj (e a) (e b)) : IsConj a b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
  simpa using hc

section Th

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

local notation "R7" => slpJ a b prog7

local notation "x7" => R7 24

local notation "y7" => R7 25

local notation "z7" => x7 * y7 ^ 6

theorem thSeven_oneClass_J :
    ∃ z : J, orderOf z = 7 ∧ ∀ s : J, orderOf s = 7 → IsConj z s := by
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine ⟨z7, sporKRest_isConj_orderOf_of_pair (z := z7) (matJ_injective ?_) h7x h7y hx1 hpow ?_
    (fun i j hi hj hij => ?_)⟩
  · simp only [matJ_mul]
    exact hcomm
  · rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
      factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)]
  · obtain ⟨m, hm⟩ := thSeven_conj hi hj hij
    refine ⟨m, matJ_injective ?_⟩
    simp only [matJ_mul, matJ_pow] at hm ⊢
    exact hm

end Th

theorem sporKRest_cover_Th_7_carrier :
    SporKRestCover 7 Blueprint.NativeSporadic.Th := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨z, hz7, hzone⟩ := thSeven_oneClass_J
  haveI : Finite CFSG.Sporadic.Th.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  haveI : Finite Blueprint.NativeSporadic.Th :=
    Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
  have hone : ∀ s t : Blueprint.NativeSporadic.Th, orderOf s = 7 → orderOf t = 7 → IsConj s t := by
    intro s t hs ht
    have hs' : orderOf (CFSG.Sporadic.Th.thEquivJ s) = 7 := by rw [MulEquiv.orderOf_eq]; exact hs
    have ht' : orderOf (CFSG.Sporadic.Th.thEquivJ t) = 7 := by rw [MulEquiv.orderOf_eq]; exact ht
    exact @sporKRest_isConj_of_mulEquiv Blueprint.NativeSporadic.Th ↥CFSG.Sporadic.Th.J
      inferInstance inferInstance CFSG.Sporadic.Th.thEquivJ s t
      ((hzone _ hs').symm.trans (hzone _ ht'))
  have hval : (Nat.card Blueprint.NativeSporadic.Th).factorization 7 = 2 := by
    rw [Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv, CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
      CommutingPair.factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)]
  have hx₀o : orderOf (CFSG.Sporadic.Th.thEquivJ.symm z) = 7 := by
    rw [MulEquiv.orderOf_eq]; exact hz7
  refine sporKRest_cover_of_orderE Nat.prime_seven hval (CFSG.Sporadic.Th.thEquivJ.symm z) ?_ ?_ ?_
  · intro h
    rw [h, orderOf_one] at hx₀o
    exact absurd hx₀o (by norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀o, pow_one])
  · intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    have hxo : orderOf x = 7 := by
      rw [← hc, show c * CFSG.Sporadic.Th.thEquivJ.symm z * c⁻¹ =
        MulAut.conj c (CFSG.Sporadic.Th.thEquivJ.symm z) from rfl, MulEquiv.orderOf_eq]
      exact hx₀o
    exact sporKRest_generating_of_fusionGeneration Nat.prime_seven
      CFSG.RankThree.PartOne.CTP.fusionGenerationOf_Th hone hxo

theorem sporKRest_cover_Th_7 :
    SporKRestCover 7 (TauCeti.CFSGIndex.sporadic .Th).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Th
    (TauCeti.CFSGIndex.sporadic .Th).Group inferInstance inferInstance e 7
    sporKRest_cover_Th_7_carrier

end CFSG.StandardType.SporadicShape
