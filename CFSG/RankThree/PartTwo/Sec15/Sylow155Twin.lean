module

public import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec15.Sylow155TwinGrp
import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Quasithin.Vol2.Ch11SKFIto

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sylow155T

theorem mem_map_of_mem_centralizer {A M : Subgroup G} (hA : A ∈ partTwoF G) (hAM : A ≤ M)
    {θ : Subgroup ↥M} [θ.Normal] (hθ : ¬ 3 ∣ Nat.card θ) {q : ↥M ⧸ θ}
    (hq : q ∈ Subgroup.centralizer (((A.subgroupOf M).map (QuotientGroup.mk' θ) :
      Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ))) (hq3 : q ^ 3 = 1) :
    q ∈ (A.subgroupOf M).map (QuotientGroup.mk' θ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀3 : IsPGroup 3 (A.subgroupOf M) := fun a =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hA.1.2 _ (Subgroup.mem_subgroupOf.mp a.2)))⟩
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hθ hA₀3] at hq
  obtain ⟨m, hm, rfl⟩ := hq
  obtain ⟨e, r, hr3, hor⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' 3 (by norm_num)
  have hm'e : (m ^ r) ^ 3 ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one]
  have hm'3θ : (m ^ r) ^ 3 ∈ θ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_pow, ← pow_mul,
      mul_comm, pow_mul]
    have h1 : (m : ↥M ⧸ θ) ^ 3 = 1 := hq3
    rw [h1, one_pow]
  have hm'3 : (m ^ r) ^ 3 = 1 := by
    have h1 : orderOf ((m ^ r) ^ 3) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, hm'e, one_pow])
    have h2 : orderOf ((m ^ r) ^ 3) ∣ Nat.card θ := Subgroup.orderOf_dvd_natCard θ hm'3θ
    have hg : Nat.gcd (3 ^ e) (Nat.card θ) = 1 :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ)
    have h3 := Nat.dvd_gcd h1 h2
    rw [hg] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hm'C : m ^ r ∈ Subgroup.centralizer ((A.subgroupOf M : Subgroup ↥M) : Set ↥M) :=
    pow_mem hm r
  have hm'A : ((m ^ r : ↥M) : G) ∈ A := by
    refine mem_of_mem_partTwoF hA (by simpa using congrArg Subtype.val hm'3) fun a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_iff.mp hm'C ⟨a, hAM ha⟩
      (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h1
  have hm'A₀ : m ^ r ∈ A.subgroupOf M := Subgroup.mem_subgroupOf.mpr hm'A
  have hrr : r * r % 3 = 1 := by
    have h1 : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> simp [Nat.mul_mod, h1]
  have hqq : QuotientGroup.mk' θ m = (QuotientGroup.mk' θ m ^ r) ^ r := by
    have h1 : (QuotientGroup.mk' θ m) ^ 3 = 1 := hq3
    rw [← pow_mul, ← Nat.div_add_mod (r * r) 3, hrr, pow_add, pow_mul, h1, one_pow, one_mul,
      pow_one]
  rw [hqq, ← map_pow]
  exact pow_mem (Subgroup.mem_map_of_mem _ hm'A₀) r

theorem card_center_subgroupOf {X M : Subgroup G} (hXM : X ≤ M) :
    Nat.card (Subgroup.center
        (↥(X.subgroupOf M) ⧸ aschbacherSolvableCore 3 ↥(X.subgroupOf M))) =
      Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) := by
  set e : ↥(X.subgroupOf M) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXM
  have he := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  exact Nat.card_congr (Subgroup.centerCongr (QuotientGroup.congr _ _ e he)).toEquiv

theorem map_conj_eq_of_sq {A M X : Subgroup G} (hA : A ∈ partTwoF G) (hAM : A ≤ M)
    (hXM : X ∈ thetaComponentsIn M) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX3 : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1})
    (hZ : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3)
    {d : G} (hdM : d ∈ M) (hdA : d ∈ Subgroup.centralizer (A : Set G))
    (hd2 : X.map (MulAut.conj (d ^ 2)).toMonoidHom = X) :
    X.map (MulAut.conj d).toMonoidHom = X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d₀, rfl⟩ : ∃ d₀ : ↥M, (d₀ : G) = d := ⟨⟨d, hdM⟩, rfl⟩
  by_contra hne
  obtain ⟨hXM', hY'⟩ := mem_thetaComponentsIn_iff.mp hXM
  set Y' := X.subgroupOf M with hY'def
  have hYY' : Y'.map M.subtype = X := by
    rw [hY'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXM']
  have hmapc : ∀ g : ↥M, (Y'.map (MulAut.conj g).toMonoidHom).map M.subtype =
      X.map (MulAut.conj (g : G)).toMonoidHom := by
    intro g
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hY₂ : Y'.map (MulAut.conj d₀).toMonoidHom ∈ thetaComponents 3 ↥M :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj d₀) hY'
  have h12 : Y' ≠ Y'.map (MulAut.conj d₀).toMonoidHom := fun he => hne (by
    rw [← hmapc d₀, ← he, hYY'])
  have hd2' : Y'.map (MulAut.conj (d₀ ^ 2)).toMonoidHom = Y' := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hmapc, Subgroup.coe_pow, hYY', hd2]
  have c12 := commutator_le_of_mem_thetaComponents hY' hY₂ h12
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hθn : (aschbacherSolvableCore 3 ↥M).Normal := @Subgroup.normal_of_characteristic _ _ _ hθc
  set θ := aschbacherSolvableCore 3 ↥M with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hcomm : ∀ w ∈ Y'.map π, ∀ w₂ ∈ (Y'.map (MulAut.conj d₀).toMonoidHom).map π,
      w * w₂ = w₂ * w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : π ⁅a, b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (c12 (Subgroup.commutator_mem_commutator ha hb))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hconj : ∀ (g : ↥M) (K : Subgroup ↥M),
      (K.map π).map (MulAut.conj (π g)).toMonoidHom =
        (K.map (MulAut.conj g).toMonoidHom).map π := by
    intro g K
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hW₂eq : (Y'.map π).map (MulAut.conj (π d₀)).toMonoidHom =
      (Y'.map (MulAut.conj d₀).toMonoidHom).map π := hconj d₀ Y'
  have hWd2 : (Y'.map π).map (MulAut.conj (π d₀ ^ 2)).toMonoidHom = Y'.map π := by
    rw [← map_pow, hconj, hd2']
  have hA₀3 : IsPGroup 3 (A.subgroupOf M) := fun a =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hA.1.2 _ (Subgroup.mem_subgroupOf.mp a.2)))⟩
  have hĀ3 : IsPGroup 3 ((A.subgroupOf M).map π) := hA₀3.map π
  have hdĀ : ∀ a ∈ (A.subgroupOf M).map π, a * π d₀ = π d₀ * a := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (a : G) * d₀ = d₀ * a :=
      Subgroup.mem_centralizer_iff.mp hdA _ (Subgroup.mem_subgroupOf.mp ha)
    rw [← map_mul, ← map_mul, show a * d₀ = d₀ * a from Subtype.ext h1]
  have hL : ∀ q ∈ Subgroup.centralizer (((A.subgroupOf M).map π : Subgroup (↥M ⧸ θ)) :
      Set (↥M ⧸ θ)), q ^ 3 = 1 → π d₀ * q * (π d₀)⁻¹ = q := by
    intro q hq hq3
    have hqĀ := mem_map_of_mem_centralizer hA hAM hθ3 hq hq3
    rw [← hdĀ q hqĀ, mul_inv_cancel_right]
  have hA₀N : A.subgroupOf M ≤ Subgroup.normalizer (Y' : Set ↥M) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hAX (Subgroup.mem_subgroupOf.mp ha)) (y : G)
    simpa [hY'def, Subgroup.mem_subgroupOf] using h1
  have hĀW : (A.subgroupOf M).map π ≤ Subgroup.normalizer ((Y'.map π : Subgroup (↥M ⧸ θ)) :
      Set (↥M ⧸ θ)) :=
    (Subgroup.map_mono hA₀N).trans (Subgroup.le_normalizer_map π)
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hY'.2.1
  have hWq : CFSG.IsQuasisimple ↥(Y'.map π) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv η hY'.2.2
  have hZW : (Subgroup.center ↥(Y'.map π)).map (Y'.map π).subtype =
      Y'.map π ⊓ Subgroup.centralizer ((Y'.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) := by
    ext g
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨h, hh⟩)
    · rintro ⟨hgW, hgC⟩
      exact ⟨⟨g, hgW⟩, Subgroup.mem_center_iff.mpr fun h =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC h h.2), rfl⟩
  have hZcard : Nat.card ↥(Y'.map π ⊓
      Subgroup.centralizer ((Y'.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ))) ≤ 3 := by
    have e1 : Nat.card ↥(Y'.map π ⊓
        Subgroup.centralizer ((Y'.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ))) =
        Nat.card (Subgroup.center ↥(Y'.map π)) := by
      rw [← hZW, Subgroup.card_map_of_injective (Y'.map π).subtype_injective]
    have e2 : Nat.card (Subgroup.center ↥(Y'.map π)) =
        Nat.card (Subgroup.center (↥Y' ⧸ aschbacherSolvableCore 3 ↥Y')) :=
      (Nat.card_congr (Subgroup.centerCongr η).toEquiv).symm
    rw [e1, e2]
    exact (card_center_subgroupOf hXM').trans_le hZ
  have h3W : 3 ∣ Nat.card ↥(Y'.map π) := by
    by_contra h3
    have hcop : Nat.Coprime 3 (Nat.card ↥(Y'.map π)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hXθ : X ≤ θ.map M.subtype := by
      refine hX3.trans ((Subgroup.closure_le _).mpr ?_)
      rintro x ⟨hxX, k, hxk⟩
      have hxM := hXM' hxX
      have hy : π ⟨x, hxM⟩ ∈ Y'.map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxX)
      have hxk' : (⟨x, hxM⟩ : ↥M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hxk)
      have h1 : orderOf (π ⟨x, hxM⟩) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk', map_one])
      have h2 : orderOf (π ⟨x, hxM⟩) ∣ Nat.card ↥(Y'.map π) :=
        Subgroup.orderOf_dvd_natCard _ hy
      have hg : Nat.gcd (3 ^ k) (Nat.card ↥(Y'.map π)) = 1 := Nat.Coprime.pow_left k hcop
      have h3' := Nat.dvd_gcd h1 h2
      rw [hg] at h3'
      have h4 : π ⟨x, hxM⟩ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3')
      exact ⟨⟨x, hxM⟩, (QuotientGroup.eq_one_iff _).mp h4, rfl⟩
    have hWbot : ∀ w ∈ Y'.map π, w = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht, hty⟩ := hXθ (Subgroup.mem_subgroupOf.mp hy)
      rw [← (Subtype.ext hty : t = y)]
      exact (QuotientGroup.eq_one_iff t).mpr ht
    obtain ⟨-, -, a, b, hab⟩ := hWq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a = 1 := Subtype.ext (hWbot _ a.2)
    have hb : b = 1 := Subtype.ext (hWbot _ b.2)
    exact hab (by rw [ha, hb])
  haveI : Group.IsPerfect ↥(Y'.map π) := hWq.1
  obtain ⟨f, hf3, hfc⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center (p := 3) (by norm_num) h3W
  have hfC : (f : ↥M ⧸ θ) ∉
      Subgroup.centralizer ((Y'.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) := by
    intro hfC
    apply hfc
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hfC g g.2)
  have hf3' : (f : ↥M ⧸ θ) ^ 3 = 1 := by simpa using congrArg Subtype.val hf3
  obtain ⟨T, hT, hĀT, hTW, hTWZ⟩ := exists_isPGroup_inf_not_le hĀ3 hĀW f.2 hf3' hfC
  exact false_of_fixed hcomm hW₂eq hWd2 hT hĀT hTW hdĀ hL hZcard hTWZ

end Sylow155T

end CFSG.RankThree.PartTwo.Sec15
