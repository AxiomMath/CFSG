module

public import CFSG.RankThree.PartTwo.Notation
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.CGT.PushingUpLit.CGT6.RouteCGrp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofComp
public import CFSG.Assembly.InCatalog
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {H : Type*} [Group H] [Finite H]

theorem isComponent_map_pCore_of_mem_thetaComponents {L : Subgroup H}
    (hL : L ∈ thetaComponents 3 H)
    (hθ : CFSG.pCore 2 L = aschbacherSolvableCore 3 L) :
    CFSG.IsComponent (L.map (QuotientGroup.mk' (CFSG.pCore 2 H))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpi : (CFSG.pCore 2 L).map L.subtype = L ⊓ CFSG.pCore 2 H := by
    have h := CFSG.LocalCores.prime_set_core_subnormal_intersection
      (G := H) {q : Nat.Primes | (q : ℕ) = 2} hL.2.1
    rwa [← CFSG.pCore_eq_piCore (G := L) 2, ← CFSG.pCore_eq_piCore (G := H) 2] at h
  have hM : ∀ l : L, l ∈ CFSG.pCore 2 L ↔
      QuotientGroup.mk' (CFSG.pCore 2 H) (l : H) = 1 := by
    intro l
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hl
      have hmem : (l : H) ∈ (CFSG.pCore 2 L).map L.subtype := ⟨l, hl, rfl⟩
      exact (hpi ▸ hmem).2
    · intro hl
      have hmem : (l : H) ∈ L ⊓ CFSG.pCore 2 H := ⟨l.2, hl⟩
      rw [← hpi] at hmem
      obtain ⟨x, hx, hxl⟩ := hmem
      exact (Subtype.ext hxl) ▸ hx
  obtain ⟨η, -⟩ := CFSG.RankThree.exists_quotient_mulEquiv_map
    (f := QuotientGroup.mk' (CFSG.pCore 2 H)) L (CFSG.pCore 2 L) hM
  have hq : IsQuasisimple (L ⧸ CFSG.pCore 2 L) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hθ).symm hL.2.2
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv η hq,
    hL.2.1.map (QuotientGroup.mk'_surjective _)⟩

theorem eq_of_map_pCore_eq {L L' : Subgroup H}
    (hL : L ∈ thetaComponents 3 H) (hL' : L' ∈ thetaComponents 3 H)
    (h : L.map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      L'.map (QuotientGroup.mk' (CFSG.pCore 2 H))) : L = L' := by
  have hO2θ : CFSG.pCore 2 H ≤ aschbacherSolvableCore 3 H :=
    (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := H) Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
  set N := CFSG.pCore 2 H with hN
  set Θ := aschbacherSolvableCore 3 H with hΘ
  set πN := QuotientGroup.mk' N with hπN
  set πΘ := QuotientGroup.mk' Θ with hπΘ
  let q : H ⧸ N →* H ⧸ Θ := QuotientGroup.map N Θ (MonoidHom.id H) hO2θ
  have hq : ∀ x : H, q (πN x) = πΘ x := fun x =>
    QuotientGroup.map_mk' N Θ (MonoidHom.id H) hO2θ x
  have hmap : L.map πΘ = L'.map πΘ := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : πN x ∈ L'.map πN := by
        rw [← h]
        exact Subgroup.mem_map_of_mem πN hx
      obtain ⟨y, hy, hyx⟩ := hx'
      refine ⟨y, hy, ?_⟩
      have := congrArg q hyx
      simpa [hq] using this
    · rintro y ⟨x, hx, rfl⟩
      have hx' : πN x ∈ L.map πN := by
        rw [h]
        exact Subgroup.mem_map_of_mem πN hx
      obtain ⟨y, hy, hyx⟩ := hx'
      refine ⟨y, hy, ?_⟩
      have := congrArg q hyx
      simpa [hq] using this
  calc L = inSubgroup perfectResidual ((L.map πΘ).comap πΘ) :=
        (CFSG.RankThree.perfectResidual_comap_map_of_mem_thetaComponents
          Nat.prime_three hL).symm
    _ = inSubgroup perfectResidual ((L'.map πΘ).comap πΘ) := by rw [hmap]
    _ = L' := CFSG.RankThree.perfectResidual_comap_map_of_mem_thetaComponents
        Nat.prime_three hL'

theorem eq_or_eq_or_eq_of_isComponent {Q : Type*} [Group Q] [Finite Q]
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Q) ≤ 2)
    (hcomp : ∀ K : Subgroup Q, CFSG.IsComponent K →
      Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K)
    {K₁ K₂ K₃ : Subgroup Q} (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂)
    (h₃ : CFSG.IsComponent K₃) : K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := by
  classical
  by_contra h
  have h12 : K₁ ≠ K₂ := fun he => h (Or.inl he)
  have h13 : K₁ ≠ K₃ := fun he => h (Or.inr (Or.inl he))
  have h23 : K₂ ≠ K₃ := fun he => h (Or.inr (Or.inr he))
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnc : ∀ K : Subgroup Q, CFSG.IsComponent K →
      ∃ e ∈ K, orderOf e = 5 ∧ ∃ c ∈ K, e * c ≠ c * e := by
    intro K hK
    obtain ⟨hZ, h5dvd⟩ := hcomp K hK
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 h5dvd
    refine ⟨(x : Q), x.2, ?_, ?_⟩
    · rwa [Subgroup.orderOf_coe]
    · by_contra hc
      have hc' : ∀ c ∈ K, (x : Q) * c = c * (x : Q) := by
        intro c hcK
        by_contra hne
        exact hc ⟨c, hcK, hne⟩
      have hxZ : (⟨(x : Q), x.2⟩ : K) ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro c
        exact Subtype.ext (hc' c c.2).symm
      rw [hZ, Subgroup.mem_bot] at hxZ
      have hx1 : (x : Q) = 1 := congrArg Subtype.val hxZ
      have hord1 : orderOf (x : Q) = 1 := by rw [hx1, orderOf_one]
      rw [Subgroup.orderOf_coe, hx] at hord1
      omega
  have hmem : ∀ K ∈ ({K₁, K₂, K₃} : Finset (Subgroup Q)),
      CFSG.IsComponent K ∧
        ∃ e ∈ K, orderOf e = 5 ∧ ∃ c ∈ K, e * c ≠ c * e := by
    intro K hK
    rcases Finset.mem_insert.mp hK with hK₁ | hK
    · rw [hK₁]
      exact ⟨h₁, hnc K₁ h₁⟩
    rcases Finset.mem_insert.mp hK with hK₂ | hK
    · rw [hK₂]
      exact ⟨h₂, hnc K₂ h₂⟩
    have hK₃ : K = K₃ := Finset.mem_singleton.mp hK
    rw [hK₃]
    exact ⟨h₃, hnc K₃ h₃⟩
  have hcard := CFSG.LocalAnalysis.RankThreeUC.AGL81C.card_le_pRank_of_components
    (p := 5) (by norm_num) ({K₁, K₂, K₃} : Finset (Subgroup Q)) hmem
  have hc : ({K₁, K₂, K₃} : Finset (Subgroup Q)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  rw [hc] at hcard
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 5 (↥(⊤ : Subgroup Q)),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 5) (H := (⊤ : Subgroup Q))] at hcard
  omega

theorem eq_or_eq_or_eq_of_mem_thetaComponents
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup (H ⧸ CFSG.pCore 2 H)) ≤ 2)
    (hcomp : ∀ K : Subgroup (H ⧸ CFSG.pCore 2 H), CFSG.IsComponent K →
      Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K)
    (hθ : ∀ L ∈ thetaComponents 3 H, CFSG.pCore 2 L = aschbacherSolvableCore 3 L)
    {L₁ L₂ L₃ : Subgroup H}
    (h₁ : L₁ ∈ thetaComponents 3 H) (h₂ : L₂ ∈ thetaComponents 3 H)
    (h₃ : L₃ ∈ thetaComponents 3 H) :
    L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃ := by
  have hc₁ := isComponent_map_pCore_of_mem_thetaComponents h₁ (hθ L₁ h₁)
  have hc₂ := isComponent_map_pCore_of_mem_thetaComponents h₂ (hθ L₂ h₂)
  have hc₃ := isComponent_map_pCore_of_mem_thetaComponents h₃ (hθ L₃ h₃)
  rcases eq_or_eq_or_eq_of_isComponent h5 hcomp hc₁ hc₂ hc₃ with h12 | h13 | h23
  · exact Or.inl (eq_of_map_pCore_eq h₁ h₂ h12)
  · exact Or.inr (Or.inl (eq_of_map_pCore_eq h₁ h₃ h13))
  · exact Or.inr (Or.inr (eq_of_map_pCore_eq h₂ h₃ h23))

theorem map_eq_of_mem_thetaComponents
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup (H ⧸ CFSG.pCore 2 H)) ≤ 2)
    (hcomp : ∀ K : Subgroup (H ⧸ CFSG.pCore 2 H), CFSG.IsComponent K →
      Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K)
    (hθ : ∀ L ∈ thetaComponents 3 H, CFSG.pCore 2 L = aschbacherSolvableCore 3 L)
    {σ : MulAut H} {n : ℕ} (hσ : σ ^ (3 ^ n) = 1) {L : Subgroup H}
    (hL : L ∈ thetaComponents 3 H) :
    L.map σ.toMonoidHom = L := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set τ : MulAut (H ⧸ CFSG.pCore 2 H) := Crit167.quotPCoreAut H σ with hτdef
  have hτ : τ ^ (3 ^ n) = 1 := by
    rw [hτdef]
    rw [← map_pow, hσ, map_one]
  have hcL : CFSG.IsComponent (L.map π) :=
    isComponent_map_pCore_of_mem_thetaComponents hL (hθ L hL)
  have hfix : (L.map π).map τ.toMonoidHom = L.map π :=
    Comp167.map_eq_of_isComponent (H := H ⧸ CFSG.pCore 2 H) h5 hcomp hτ hcL
  have hcompπ : π.comp σ.toMonoidHom = τ.toMonoidHom.comp π := by
    ext x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hπ, hτdef]
    change QuotientGroup.mk' (CFSG.pCore 2 H) (σ x) =
      Crit167.quotPCoreAut H σ ((x : H) : H ⧸ CFSG.pCore 2 H)
    rw [Crit167.quotPCoreAut_apply_mk]
    rfl
  have hmap : (L.map σ.toMonoidHom).map π = L.map π := by
    calc (L.map σ.toMonoidHom).map π
        = (L.map π).map τ.toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map, hcompπ]
      _ = L.map π := hfix
  exact eq_of_map_pCore_eq (map_mulEquiv_mem_thetaComponents Nat.prime_three σ hL) hL hmap

theorem mem_normalizer_of_mem_thetaComponentsIn {G : Type*} [Group G] [Finite G]
    {X : Subgroup G}
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ 2)
    (hcomp : ∀ K : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X), CFSG.IsComponent K →
      Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K)
    (hθ : ∀ L ∈ thetaComponents 3 ↥X, CFSG.pCore 2 L = aschbacherSolvableCore 3 L)
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) {n : ℕ} (hgn : g ^ (3 ^ n) = 1)
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn X) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hKX, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set a : Subgroup.normalizer (X : Set G) := ⟨g, hg⟩ with ha
  set σ : MulAut ↥X := X.normalizerMonoidHom a with hσ_def
  have ha' : a ^ (3 ^ n) = 1 := by
    apply Subtype.ext
    simpa using hgn
  have hσ : σ ^ (3 ^ n) = 1 := by
    change (X.normalizerMonoidHom a) ^ (3 ^ n) = 1
    rw [← map_pow, ha', map_one]
  have hfix := map_eq_of_mem_thetaComponents h5 hcomp hθ hσ hK'
  have hcomp_sub : X.subtype.comp σ.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp X.subtype := by
    ext x
    rfl
  have hmapK : K.map (MulAut.conj g).toMonoidHom = K := by
    calc K.map (MulAut.conj g).toMonoidHom
        = ((K.subgroupOf X).map X.subtype).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hKX]
      _ = (K.subgroupOf X).map ((MulAut.conj g).toMonoidHom.comp X.subtype) := by
          rw [Subgroup.map_map]
      _ = (K.subgroupOf X).map (X.subtype.comp σ.toMonoidHom) := by rw [hcomp_sub]
      _ = ((K.subgroupOf X).map σ.toMonoidHom).map X.subtype := by rw [Subgroup.map_map]
      _ = (K.subgroupOf X).map X.subtype := by rw [hfix]
      _ = K := Subgroup.map_subgroupOf_eq_of_le hKX
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapK

theorem le_normalizer_of_mem_thetaComponentsIn {G : Type*} [Group G] [Finite G]
    {X : Subgroup G}
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ 2)
    (hcomp : ∀ K : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X), CFSG.IsComponent K →
      Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K)
    (hθ : ∀ L ∈ thetaComponents 3 ↥X, CFSG.pCore 2 L = aschbacherSolvableCore 3 L)
    {A : Subgroup G} (hA : IsPGroup 3 A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn X) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  intro a ha
  obtain ⟨n, hn⟩ := hA ⟨a, ha⟩
  have han : a ^ (3 ^ n) = 1 := by
    simpa using congrArg Subtype.val hn
  exact mem_normalizer_of_mem_thetaComponentsIn h5 hcomp hθ (hAX ha) han hK

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
