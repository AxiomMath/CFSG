module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRest
import CFSG.RankThree.PartOne.S11c.PlaneLift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL10
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCOutHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 (Ok69 secondCenterSubgroup OutCase
  NoOk69Order3 ScalarAction D4InnerDatum exists_conj_into_sylow_of_outer
  exists_quadratic_subgroup_of_outerTorusDatum torusType_inner_mem_center
  not_ok69_of_nonabelian_order_27 d4_center_bot d4_innerDatum d4_outCase trialityTarget_holds
  outTrialityInput_holds)


private theorem mem_secondCenter_iff {K : Type} [Group K] (S : Subgroup K) (z : K) :
    z ∈ secondCenterSubgroup S ↔ z ∈ S ∧ ∀ g ∈ S, ∀ h ∈ S,
      h * (z * g * z⁻¹ * g⁻¹) = (z * g * z⁻¹ * g⁻¹) * h := by
  unfold secondCenterSubgroup
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun g hg h hh => ?_⟩
    have h1 := Subgroup.mem_upperCentralSeries_succ_iff.mp hx ⟨g, hg⟩
    rw [Subgroup.upperCentralSeries_one] at h1
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨h, hh⟩)
    simpa [commutatorElement_def] using h2
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr fun y => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    simpa [commutatorElement_def] using h y y.2 w w.2

private theorem isPGroup_zpowers_of_pow_three {K : Type} [Group K] {a : K} (ha3 : a ^ 3 = 1) :
    IsPGroup 3 (zpowers a) := by
  have hd : orderOf a ∣ 3 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one ha3
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

private theorem commute_of_fixes_abelian {K : Type} [Group K] {S : Subgroup K}
    (hS : IsPGroup 3 S) {a z : K} (haS : a ∈ S) (hzS : z ∈ S)
    (hc : ∀ h ∈ S, h * (a * z * a⁻¹ * z⁻¹) = (a * z * a⁻¹ * z⁻¹) * h)
    (hFix : ∀ A : Subgroup K, IsPGroup 3 A → IsMulCommutative A →
      (∀ b ∈ A, MulAut.conj a b ∈ A) → ∀ b ∈ A, MulAut.conj a b = b) :
    a * z = z * a := by
  set c := a * z * a⁻¹ * z⁻¹ with hcdef
  have hcS : c ∈ S := mul_mem (mul_mem (mul_mem haS hzS) (inv_mem haS)) (inv_mem hzS)
  have hzc : z * c = c * z := hc z hzS
  have hac : a * c * a⁻¹ = c := by
    rw [hc a haS]
    group
  have haz : a * z * a⁻¹ = c * z := by
    rw [hcdef]
    group
  have hpair : ({z, c} : Set K).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hzc
    · exact hzc.symm
    · exact Commute.refl _
  have hzA : z ∈ closure ({z, c} : Set K) := subset_closure (Set.mem_insert z _)
  have hcA : c ∈ closure ({z, c} : Set K) := subset_closure (Set.mem_insert_of_mem z rfl)
  have hAS : closure ({z, c} : Set K) ≤ S := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact hzS
    · exact hcS
  have hAinv : ∀ b ∈ closure ({z, c} : Set K), MulAut.conj a b ∈ closure ({z, c} : Set K) := by
    have hle : closure ({z, c} : Set K) ≤
        (closure ({z, c} : Set K)).comap (MulAut.conj a).toMonoidHom := by
      rw [closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        show MulAut.conj a z ∈ closure ({z, c} : Set K)
        rw [MulAut.conj_apply, haz]
        exact mul_mem hcA hzA
      · rw [Set.mem_singleton_iff.1 hx]
        show MulAut.conj a c ∈ closure ({z, c} : Set K)
        rw [MulAut.conj_apply, hac]
        exact hcA
    exact fun b hb => hle hb
  have hfix := hFix _ (hS.to_le hAS) (isMulCommutative_closure hpair) hAinv z hzA
  rw [MulAut.conj_apply] at hfix
  calc a * z = a * z * a⁻¹ * a := by group
    _ = z * a := by rw [hfix]

theorem ok69_of_fixes_abelian {K : Type} [Group K] {a : K} (ha3 : a ^ 3 = 1)
    (hFix : ∀ A : Subgroup K, IsPGroup 3 A → IsMulCommutative A →
      (∀ b ∈ A, MulAut.conj a b ∈ A) → ∀ b ∈ A, MulAut.conj a b = b) : Ok69 a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro R hR haN
  have hS : IsPGroup 3 (R ⊔ zpowers a : Subgroup K) :=
    IsPGroup.to_sup_of_normal_left' hR (isPGroup_zpowers_of_pow_three ha3) (zpowers_le.2 haN)
  have haS : a ∈ R ⊔ zpowers a := mem_sup_right (mem_zpowers a)
  refine ⟨fun z hz => ?_, fun ha2 => ?_⟩
  · obtain ⟨hzS, hzc⟩ := (mem_secondCenter_iff _ z).1 hz
    refine commute_of_fixes_abelian hS haS hzS (fun h hh => ?_) hFix
    have e : a * z * a⁻¹ * z⁻¹ = (z * a * z⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact (Commute.inv_right (show Commute h (z * a * z⁻¹ * a⁻¹) from hzc a haS h hh)).eq
  · obtain ⟨-, hac⟩ := (mem_secondCenter_iff _ a).1 ha2
    refine mem_map.2 ⟨⟨a, haS⟩, mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (commute_of_fixes_abelian hS haS g.2 (hac g g.2) hFix).symm

private theorem three_dvd_card_outer {Y : Type} [Group Y] {α : MulAut Y} (hα3 : α ^ 3 = 1)
    (hα : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ≠ 1 :=
    fun h => hα ((QuotientGroup.eq_one_iff
      (N := CFSG.ComponentClassification.OuterAutomorphisms.inner Y) α).1 h)
  have h3 : (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ^ 3 =
      1 := by
    rw [← QuotientGroup.mk_pow, hα3, QuotientGroup.mk_one]
  rw [← orderOf_eq_prime h3 h1]
  exact orderOf_dvd_natCard _

private theorem scalar_stable {Y : Type} [Group Y] {Q T : Subgroup Y} {y : Y}
    {φ : MulAut Y} {k : ℤ} (hQeq : Q = T ⊔ zpowers y) (hsc : ScalarAction T φ y k) :
    ∀ q ∈ Q, φ q ∈ Q := by
  have hle : T ⊔ zpowers y ≤ (T ⊔ zpowers y).comap φ.toMonoidHom := by
    refine sup_le (fun t ht => ?_) (zpowers_le.2 ?_)
    · show φ t ∈ T ⊔ zpowers y
      rw [hsc.2 t ht]
      exact zpow_mem (mem_sup_left ht) k
    · show φ y ∈ T ⊔ zpowers y
      rw [hsc.1]
      exact mem_sup_right (mem_zpowers y)
  subst hQeq
  exact fun q hq => hle hq

theorem exists_moved_abelian_of_outCase {Y : Type} [Group Y] [Finite Y] (hZ : center Y = ⊥)
    (hO : OutCase Y) {α : MulAut Y} (hα3 : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ A : Subgroup Y, IsPGroup 3 A ∧ IsMulCommutative A ∧
      (∀ a ∈ A, α a ∈ A) ∧ ∃ a ∈ A, α a ≠ a := by
  rcases hO with h3 | ⟨φ, Q, T, V, y, e1, e2, k, hφ3, hOOT, hSD, hsc, hk3, hk⟩
  · exact (h3 (three_dvd_card_outer hα3 hout)).elim
  obtain ⟨g, hg⟩ := hOOT α hout (by rw [hα3]; exact one_mem _)
  have hαg : ∃ (g : Y) (j : ℕ), α = MulAut.conj g * φ ^ j := by
    rcases hg with hg | hg
    · exact ⟨g, 1, by rw [pow_one]; exact hg⟩
    · exact ⟨g, 2, hg⟩
  obtain ⟨hQ3, hQi, -, -, -, -, -, -, hQeq, -⟩ := id hSD
  obtain ⟨l, t, j, htQ, hj3, hconj⟩ := exists_conj_into_sylow_of_outer hZ hQ3 hQi hφ3
    (scalar_stable hQeq hsc) hα3 hαg
  have hj : j = 1 ∨ j = 2 := by
    interval_cases j
    · exfalso
      refine hout ⟨l⁻¹ * t * l, ?_⟩
      have h2 : MulAut.conj l * α * (MulAut.conj l)⁻¹ = MulAut.conj t := by
        rw [hconj, pow_zero, mul_one]
      calc (MulAut.conj : Y →* MulAut Y) (l⁻¹ * t * l)
          = (MulAut.conj l)⁻¹ * (MulAut.conj l * α * (MulAut.conj l)⁻¹) * MulAut.conj l := by
            rw [h2]
            simp [map_mul, map_inv]
        _ = α := by group
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨R, hR3, hRab, hRα, -, hmov⟩ :=
    exists_quadratic_subgroup_of_outerTorusDatum hSD hsc hk3 hk hα3 l t j htQ hj hconj
  exact ⟨R, hR3, hRab, hRα, hmov⟩

theorem eq_one_of_fixes_abelian_of_noOk69 {Y : Type} [Group Y] [Finite Y] (hZ : center Y = ⊥)
    (hNo : NoOk69Order3 Y) (hO : OutCase Y) {α : MulAut Y} (hα3 : α ^ 3 = 1)
    (hFix : ∀ A : Subgroup Y, IsPGroup 3 A → IsMulCommutative A →
      (∀ a ∈ A, α a ∈ A) → ∀ a ∈ A, α a = a) : α = 1 := by
  by_cases hinn : α ∈ (MulAut.conj : Y →* MulAut Y).range
  · obtain ⟨a, rfl⟩ := hinn
    have ha3 : a ^ 3 = 1 := CFSG.RankThree.PartOne.conj_injective_of_center_bot hZ
      (by rw [map_pow, hα3, map_one])
    rw [hNo a ha3 (ok69_of_fixes_abelian ha3 hFix), map_one]
  · obtain ⟨A, hA3, hAab, hAα, a, ha, hmov⟩ := exists_moved_abelian_of_outCase hZ hO hα3 hinn
    exact (hmov (hFix A hA3 hAab hAα a ha)).elim

theorem noOk69Order3_of_d4InnerDatum {Y : Type} [Group Y] [Finite Y] (h : D4InnerDatum Y) :
    NoOk69Order3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro a ha3 hok
  by_contra ha1
  obtain ⟨S, hS⟩ := (isPGroup_zpowers_of_pow_three ha3).exists_le_sylow
  obtain ⟨T, V, y, e1, e2, hSD, hfus⟩ := h S
  obtain ⟨hQ, -, -, hTn, hTab, hVT, hVel, hVmax, hQeq, htransv, -, hout, -, -, -⟩ := hSD
  obtain ⟨haV, hya⟩ := torusType_inner_mem_center hQ hTn hTab hVT hVel hVmax hQeq htransv hout
    (hS (mem_zpowers a)) (orderOf_eq_prime ha3 ha1) hok
  obtain ⟨R, hR, haR, hanz⟩ := hfus a haV ha1 hya
  exact not_ok69_of_nonabelian_order_27 hR haR hanz hok

theorem false_of_trialityD4_three_action
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hY : CFSG.Blueprint.LieModel Y .trialityD4 0 p f) (hp3 : p ≠ 3)
    (α : MulAut Y) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hFix : ∀ A : Subgroup Y, IsPGroup 3 A → IsMulCommutative A →
      (∀ a ∈ A, α a ∈ A) → ∀ a ∈ A, α a = a) : False := by
  exact hα1 (eq_one_of_fixes_abelian_of_noOk69 (d4_center_bot hY)
    (noOk69Order3_of_d4InnerDatum (d4_innerDatum trialityTarget_holds hY hp3))
    (d4_outCase outTrialityInput_holds trialityTarget_holds hY hp3) hα3 hFix)

end CFSG.LocalAnalysis.UniquenessCase.UC22
