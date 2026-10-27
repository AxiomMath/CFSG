module

public import CFSG.RankThree.PartOne.S11.FivePlusInner
public import CFSG.Assembly.CatalogTransport
import CFSG.RankThree.PartOne.S11.FivePlus
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.S11d.Common

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem map_inSubgroup_theta_subgroupOf {p : ℕ} (hp : p.Prime) {C K : Subgroup G}
    (hKC : K ≤ C) :
    (inSubgroup (aschbacherSolvableCore p) (K.subgroupOf C)).map C.subtype =
      inSubgroup (aschbacherSolvableCore p) K := by
  rw [Sec9A.map_inSubgroup_theta_of_injective hp C.subtype C.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hKC]

theorem exists_zero_of_action
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1)
    {K R : Subgroup G} (hKb : K ∈ thetaComponentsAt p b)
    (hAK : A ≤ normalizer (K : Set G)) (hRb : R ≤ centralizer ({b} : Set G))
    (hRK : R ≤ normalizer (K : Set G)) (hR2 : IsPGroup 2 R) (hAR : A ≤ normalizer (R : Set G))
    (hRA : ⁅R, A⁆ = R)
    (hmove : ∃ r ∈ R, ∃ k ∈ K,
      r * k * r⁻¹ * k⁻¹ ∉ inSubgroup (aschbacherSolvableCore p) K) :
    K ∈ sectionTenZero p A := by
  classical
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id h
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  set C := centralizer ({b} : Set G) with hC
  have hAC : A ≤ C := fun x hx => mem_centralizer_singleton_iff.mpr (hAcomm x hx b hbA)
  obtain ⟨hKC, hK'⟩ := mem_thetaComponentsAt_iff.mp hKb
  set L' : Subgroup C := K.subgroupOf C with hL'
  set A' : Subgroup C := A.subgroupOf C with hA'
  set Q' : Subgroup C := R.subgroupOf C with hQ'
  have hmapA : A'.map C.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAC
  have hmapQ : Q'.map C.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRb
  have hmapL : L'.map C.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKC
  have hA'p : IsPGroup p A' := (IsElementaryAbelian.isPGroup p A).comap_subtype
  have hQ'2 : IsPGroup 2 Q' := hR2.comap_subtype
  have hnormC : ∀ {X : Subgroup G} {Y : Subgroup C} (hXN : X ≤ normalizer (Y.map C.subtype : Set G))
      (hXC : X ≤ C), X.subgroupOf C ≤ normalizer (Y : Set C) := by
    intro X Y hXN hXC x hx
    have hx' : (x : G) ∈ normalizer ((Y.map C.subtype : Subgroup G) : Set G) :=
      hXN (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have this := Subgroup.mem_normalizer_iff.mp hx' (g : G)
    have e : ∀ z : C, z ∈ Y ↔ (z : G) ∈ Y.map C.subtype := fun z =>
      (Subgroup.mem_map_iff_mem C.subtype_injective).symm
    rw [e g, e (x * g * x⁻¹)]
    simpa using this
  have hAL : A' ≤ normalizer (L' : Set C) := hnormC (by rw [hmapL]; exact hAK) hAC
  have hQL : Q' ≤ normalizer (L' : Set C) := hnormC (by rw [hmapL]; exact hRK) hRb
  have hAQ : A' ≤ normalizer (Q' : Set C) := hnormC (by rw [hmapQ]; exact hAR) hAC
  have hQA : ⁅Q', A'⁆ = Q' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hmapQ, hmapA]
    exact hRA
  have hCtop : C ≠ ⊤ := EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hb1
  have hLq : CFSG.IsQuasisimple (L' ⧸ aschbacherSolvableCore p L') := hK'.2.2
  have hcat : Catalog ((L' ⧸ aschbacherSolvableCore p L') ⧸
      Subgroup.center (L' ⧸ aschbacherSolvableCore p L')) := by
    have : IsSimpleGroup ((L' ⧸ aschbacherSolvableCore p L') ⧸
      Subgroup.center (L' ⧸ aschbacherSolvableCore p L')) := hLq.2.1
    exact hbridge _ hLq.2.2 (inCatalog_quotient_center_of_thetaComponent hKP hCtop hLq)
  have hmove' : ∃ q : Q', thetaQuotientAction p hQL q ≠ 1 := by
    obtain ⟨r, hr, k, hk, hrk⟩ := hmove
    have hrC : r ∈ C := hRb hr
    have hkC : k ∈ C := hKC hk
    refine ⟨⟨⟨r, hrC⟩, Subgroup.mem_subgroupOf.mpr hr⟩, ?_⟩
    intro h1
    have h2 : thetaQuotientConj p L' ⟨⟨r, hrC⟩, hQL (Subgroup.mem_subgroupOf.mpr hr)⟩ = 1 := h1
    have h3 := (thetaQuotientConj_eq_one_iff p L' _).mp h2 ⟨k, hkC⟩ (Subgroup.mem_subgroupOf.mpr hk)
    apply hrk
    have h4 := Subgroup.mem_map_of_mem C.subtype h3
    rw [map_inSubgroup_theta_subgroupOf hp hKC] at h4
    simpa using h4
  obtain ⟨T, hTL, hT1, hT2, hAT, hTA⟩ := exists_two_commutator_in_thetaComponent hp hp3 hK hAL hQL
    hA'p hQ'2 hAQ hQA hLq hcat hmove'
  have hKF : K ∈ thetaComponentFamily p A := mem_thetaComponentFamily_iff.mpr ⟨b, hbA, hb1, hKb⟩
  refine ⟨hKF, T.map C.subtype, ?_, ?_, hT2.map _, ?_, ?_⟩
  · rw [← hmapL]
    exact Subgroup.map_mono hTL
  · intro h0
    exact hT1 ((Subgroup.map_eq_bot_iff_of_injective T C.subtype_injective).mp h0)
  · intro x hx
    have hxC : x ∈ C := hAC hx
    have h1 : (⟨x, hxC⟩ : C) ∈ normalizer (T : Set C) := hAT (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.le_normalizer_map C.subtype ⟨⟨x, hxC⟩, h1, rfl⟩
  · conv_lhs => rw [← hTA]
    rw [Subgroup.map_commutator, hmapA]

theorem acts_trivially_of_rel {p : ℕ} (hp : p.Prime) {K K' : Subgroup G} {a' : G}
    (hrel : sectionTenRel p K K') (hK'a : K' ≤ centralizer ({a'} : Set G))
    (ha'N : a' ∈ normalizer (K : Set G)) :
    ∀ k ∈ K, a' * k * a'⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K := by
  intro k hk
  set θ := inSubgroup (aschbacherSolvableCore p) K with hθ
  have hrel' := sectionTenRel_iff.mp hrel
  have hk' : k ∈ ((K ⊓ K' : Subgroup G) : Set G) * (θ : Set G) := by
    rw [← hrel']
    exact hk
  obtain ⟨m, hm, t, ht, rfl⟩ := hk'
  obtain ⟨hθK, hθnormal⟩ := theta_le_and_normal p K
  have hKN : K ≤ normalizer (θ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hθK).mp hθnormal
  have hzN : zpowers a' ≤ normalizer (K : Set G) := Subgroup.zpowers_le.mpr ha'N
  have hθN : a' ∈ normalizer (θ : Set G) :=
    le_normalizer_theta_of_le_normalizer hp hzN (Subgroup.mem_zpowers a')
  have hma : m * a' = a' * m := Subgroup.mem_centralizer_singleton_iff.mp (hK'a (mem_inf.mp hm).2)
  have hm' : a' * m * a'⁻¹ = m := by rw [← hma]; group
  have h1 : a' * t * a'⁻¹ * t⁻¹ ∈ θ := by
    have hta : a' * t * a'⁻¹ ∈ θ := (Subgroup.mem_normalizer_iff.mp hθN t).mp ht
    exact θ.mul_mem hta (θ.inv_mem ht)
  have h2 : m * (a' * t * a'⁻¹ * t⁻¹) * m⁻¹ ∈ θ :=
    (Subgroup.mem_normalizer_iff.mp (hKN (mem_inf.mp hm).1) _).mp h1
  have e : a' * (m * t) * a'⁻¹ * (m * t)⁻¹ = m * (a' * t * a'⁻¹ * t⁻¹) * m⁻¹ := by
    calc a' * (m * t) * a'⁻¹ * (m * t)⁻¹
        = (a' * m * a'⁻¹) * (a' * t * a'⁻¹) * t⁻¹ * m⁻¹ := by group
      _ = m * (a' * t * a'⁻¹ * t⁻¹) * m⁻¹ := by rw [hm']; group
  rw [e]
  exact h2

theorem mem_sectionTenStar_of_cent {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {f : G} (hfA : f ∈ A) (hf1 : f ≠ 1)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt p f) (hAK : A ≤ normalizer (K : Set G))
    (hZ : ∀ y ∈ A, (∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K) →
      y ∈ zpowers f) :
    K ∈ sectionTenStar p A := by
  have hp := sectionTenSetup_prime h
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hKF : K ∈ thetaComponentFamily p A := mem_thetaComponentFamily_iff.mpr ⟨f, hfA, hf1, hK⟩
  refine ⟨hKF, fun K' hK'F hrel => ?_⟩
  obtain ⟨a', ha'A, ha'1, hK'a⟩ := mem_thetaComponentFamily_iff.mp hK'F
  have hK'C : K' ≤ centralizer ({a'} : Set G) := (mem_thetaComponentsAt_iff.mp hK'a).1
  have hact := acts_trivially_of_rel hp hrel hK'C (hAK ha'A)
  have ha'f : a' ∈ zpowers f := hZ a' ha'A hact
  have hfp : f ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) f hfA
  have hcent : centralizer ({a'} : Set G) = centralizer ({f} : Set G) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'f
    have hk' : ¬ (p : ℤ) ∣ k := by
      intro hdiv
      obtain ⟨u, rfl⟩ := hdiv
      apply ha'1
      rw [← hk, zpow_mul, zpow_natCast, hfp, one_zpow]
    rw [← hk]
    exact S11d.centralizer_zpow_eq hp hfp hk'
  have hK'f : K' ∈ thetaComponentsAt p f := by
    have := S11d.thetaComponentsAt_congr (p := p) hcent
    rw [this] at hK'a
    exact hK'a
  by_cases hKK' : K = K'
  · subst hKK'
    exact sectionTenRel_refl p _
  · exfalso
    set θK := inSubgroup (aschbacherSolvableCore p) K with hθK
    have hθeq : θK = K ⊓ inSubgroup (aschbacherSolvableCore p) (centralizer ({f} : Set G)) :=
      theta_eq_inf_of_mem_thetaComponentsAt hp hK
    have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hK
    have hMK : K ⊓ K' ≤ K := inf_le_left
    have hrel' : K = (K ⊓ K') ⊔ θK := hrel
    have hmemθ : ∀ x : ↥K, (x : G) ∈ θK → x ∈ aschbacherSolvableCore p ↥K := fun x hx =>
      (Subgroup.mem_map_iff_mem K.subtype_injective).mp hx
    obtain ⟨hθK_le, -⟩ := theta_le_and_normal p K
    let π : ↥K →* ↥K ⧸ aschbacherSolvableCore p ↥K := QuotientGroup.mk' _
    have hcomm : ∀ m : ↥K, (m : G) ∈ K' → ∀ y : ↥K, π m * π y = π y * π m := by
      intro m hm y
      have hc := S11d.commutator_mem_theta_of_ne hp hK hK'f hKK' (y : G) y.2 (m : G) hm
      have hcK : (y : G) * m * (y : G)⁻¹ * (m : G)⁻¹ ∈ θK := by
        rw [hθeq]
        exact ⟨K.mul_mem (K.mul_mem (K.mul_mem y.2 m.2) (K.inv_mem y.2)) (K.inv_mem m.2), hc⟩
      have h1 : (y * m * y⁻¹ * m⁻¹ : ↥K) ∈ aschbacherSolvableCore p ↥K :=
        hmemθ _ (by simpa using hcK)
      have h2 : π (y * m * y⁻¹ * m⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      have h3 : ⁅π y, π m⁆ = 1 := by
        rw [commutatorElement_def]
        simpa [map_mul, map_inv] using h2
      exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    have hlift : ∀ x : ↥K, ∃ m : ↥K, (m : G) ∈ K' ∧ π x = π m := by
      intro x
      obtain ⟨m, hm, n, hn, hmn⟩ := exists_mul_of_eq_sup_core hMK hrel' x.2
      have hn' : (⟨n, hθK_le hn⟩ : ↥K) ∈ aschbacherSolvableCore p ↥K := hmemθ _ hn
      have hxm : x = (⟨m, (mem_inf.mp hm).1⟩ : ↥K) * ⟨n, hθK_le hn⟩ := Subtype.ext hmn.symm
      refine ⟨⟨m, (mem_inf.mp hm).1⟩, (mem_inf.mp hm).2, ?_⟩
      have hπn : π ⟨n, hθK_le hn⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hn'
      rw [hxm, map_mul, hπn, mul_one]
    have hQ : ∀ q₁ q₂ : ↥K ⧸ aschbacherSolvableCore p ↥K, q₁ * q₂ = q₂ * q₁ := by
      intro q₁ q₂
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q₁
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q₂
      obtain ⟨m, hm, hxm⟩ := hlift x
      have := hcomm m hm y
      show π x * π y = π y * π x
      rw [hxm]
      exact this
    obtain ⟨-, -, u, v, huv⟩ := hq
    apply huv
    induction u using QuotientGroup.induction_on with
    | H u' =>
      induction v using QuotientGroup.induction_on with
      | H v' =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (hQ u' v')

end CFSG.RankThree.PartOne
