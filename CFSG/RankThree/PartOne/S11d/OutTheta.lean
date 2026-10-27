module

public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.Assembly.CatalogTransport
import CFSG.RankThree.PartOne.S11d.Common
import CFSG.RankThree.PartOne.S11.FivePlus
import CFSG.RankThree.PartOne.S11.SecTenEight
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def PlaneNoInnerPart : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J A : Subgroup H) (c : H),
    p.Prime → 5 ≤ p → localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
    Catalog (↥J ⧸ Subgroup.center ↥J) →
    A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
    (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) → False

@[expose] def PlaneNoInnerPartWith
    (P : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J A : Subgroup H) (c : H),
    p.Prime → 5 ≤ p → localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
    Catalog (↥J ⧸ Subgroup.center ↥J) → P H p J →
    A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
    (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) → False

@[expose] def SectionProvider
    (P : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → ∀ (I : Subgroup G) (Γ : Type) [Group Γ]
    [Finite Γ] (φ : ↥I →* Γ) (p : ℕ), p.Prime → 5 ≤ p → localRank p Γ ≤ 3 →
    CFSG.IsQuasisimple ↥φ.range → Catalog (↥φ.range ⧸ Subgroup.center ↥φ.range) →
    P Γ p φ.range

namespace OutTheta

variable {G : Type} [Group G] [Finite G]

theorem exists_quotient_model {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I A : Subgroup G}
    (hAI : A ≤ Subgroup.normalizer (I : Set G)) (hA : IsPGroup p A) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (φ : ↥I →* Γ) (ψ : ↥A →* Γ),
      (∀ i : ↥I, φ i = 1 ↔ i ∈ aschbacherSolvableCore p ↥I) ∧ Function.Injective ψ ∧
      (∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
        φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i)) ∧
      localRank p Γ ≤ evenRank G := by
  classical
  have hIX : I ≤ I ⊔ A := le_sup_left
  have hAX : A ≤ I ⊔ A := le_sup_right
  obtain ⟨hθI, hθnorm⟩ := theta_le_and_normal p I
  have hIθ : I ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore p) I : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hθI).mp hθnorm
  have hAθ : A ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore p) I : Subgroup G) : Set G) :=
    le_normalizer_theta_of_le_normalizer hp hAI
  have hXθ : I ⊔ A ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore p) I : Subgroup G) : Set G) := sup_le hIθ hAθ
  set N : Subgroup ↥(I ⊔ A) :=
    (inSubgroup (aschbacherSolvableCore p) I).subgroupOf (I ⊔ A) with hN
  have hNn : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hθI.trans hIX)).mpr hXθ
  have hθcard : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) I : Subgroup G) := by
    have h1 : Nat.card (inSubgroup (aschbacherSolvableCore p) I : Subgroup G) =
        Nat.card (aschbacherSolvableCore p ↥I) :=
      Subgroup.card_map_of_injective I.subtype_injective
    rw [h1]
    exact (solvable_prime_complement_core_characterization (H := ↥I) hp).2.2.1
  have hNcard : ¬ p ∣ Nat.card N := by
    have : Nat.card N = Nat.card (inSubgroup (aschbacherSolvableCore p) I : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hθI.trans hIX)).toEquiv
    rw [this]
    exact hθcard
  let π : ↥(I ⊔ A) →* ↥(I ⊔ A) ⧸ N := QuotientGroup.mk' N
  refine ⟨↥(I ⊔ A) ⧸ N, inferInstance, inferInstance, π.comp (Subgroup.inclusion hIX),
    π.comp (Subgroup.inclusion hAX), ?_, ?_, ?_, ?_⟩
  · intro i
    change (QuotientGroup.mk (Subgroup.inclusion hIX i) : ↥(I ⊔ A) ⧸ N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    change (i : G) ∈ (aschbacherSolvableCore p ↥I).map I.subtype ↔ _
    exact Subgroup.mem_map_iff_mem I.subtype_injective
  · rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (QuotientGroup.mk (Subgroup.inclusion hAX a) : ↥(I ⊔ A) ⧸ N) = 1 := ha
    rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
    have h2 : (a : G) ∈ (inSubgroup (aschbacherSolvableCore p) I : Subgroup G) := h1
    obtain ⟨k, hk⟩ := hA a
    have hk' : ((a : G)) ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    set y : ↥(inSubgroup (aschbacherSolvableCore p) I : Subgroup G) := ⟨(a : G), h2⟩ with hy
    have hy1 : y ^ (p ^ k) = 1 := Subtype.ext hk'
    have hd1 : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hy1
    have hd2 : orderOf y ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) I : Subgroup G) :=
      orderOf_dvd_natCard y
    have hcop : Nat.Coprime (p ^ k)
        (Nat.card (inSubgroup (aschbacherSolvableCore p) I : Subgroup G)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hθcard)
    have hord : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    have hy1' : y = 1 := orderOf_eq_one_iff.mp hord
    have h3 : (a : G) = 1 := congrArg Subtype.val hy1'
    exact Subtype.ext h3
  · intro a i
    change (QuotientGroup.mk (Subgroup.inclusion hAX a) : ↥(I ⊔ A) ⧸ N) *
      QuotientGroup.mk (Subgroup.inclusion hIX i) *
        (QuotientGroup.mk (Subgroup.inclusion hAX a))⁻¹ =
      QuotientGroup.mk (Subgroup.inclusion hIX (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i))
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  · have h1 : localRank p (↥(I ⊔ A) ⧸ N) ≤ localRank p ↥(I ⊔ A) :=
      CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 N hNcard
    have h2 : localRank p ↥(I ⊔ A) ≤ evenRank ↥(I ⊔ A) :=
      CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2
    have h3 : evenRank ↥(I ⊔ A) ≤ evenRank G := Sec9A.evenRank_subgroup_le _
    exact h1.trans (h2.trans h3)

theorem disjoint_zpowers_of_not_mem {p : ℕ} (hp : p.Prime) {x y : G} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hyx : y ∉ Subgroup.zpowers x) :
    Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.disjoint_def]
  intro z hzx hzy
  by_contra hz1
  have hzp : ∀ w : G, w ^ p = 1 → ∀ k : ℤ, (w ^ k) ^ p = 1 := fun w hw k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hzx' : z ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzx
    exact hzp x hx k
  have hzord : orderOf z = p := orderOf_eq_prime hzx' hz1
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hz1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzx
    simp
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hz1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzy
    simp
  have hxord : orderOf x = p := orderOf_eq_prime hx hx1
  have hyord : orderOf y = p := orderOf_eq_prime hy hy1
  have hz_le_x : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hzx
  have hz_le_y : Subgroup.zpowers z ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hzy
  have hcz : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have hcx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  have hcy : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyord]
  have hzx_eq : Subgroup.zpowers z = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hz_le_x (by rw [hcz, hcx])
  have hzy_eq : Subgroup.zpowers z = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hz_le_y (by rw [hcz, hcy])
  apply hyx
  rw [← hzx_eq, hzy_eq]
  exact Subgroup.mem_zpowers y

omit [Finite G] in
theorem exists_mul_of_mem_sup_centralizer' {H : Type} [Group H] {J : Subgroup H} {x : H}
    (hx : x ∈ J ⊔ Subgroup.centralizer (J : Set H)) :
    ∃ j ∈ J, ∃ z ∈ Subgroup.centralizer (J : Set H), x = j * z := by
  have hle : J ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set H) : Set H) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.le_centralizer_iff.mpr le_rfl
  have h := Subgroup.coe_mul_of_left_le_normalizer_right J (Subgroup.centralizer (J : Set H)) hle
  have hx' : x ∈ ((J ⊔ Subgroup.centralizer (J : Set H) : Subgroup H) : Set H) := hx
  rw [h] at hx'
  obtain ⟨j, hj, z, hz, rfl⟩ := hx'
  exact ⟨j, hj, z, hz, rfl⟩

omit [Group G] [Finite G] in
theorem isElementaryAbelian_range' {p : ℕ} {A S : Type} [Group A] [Group S]
    [hA : IsElementaryAbelian p A] (f : A →* S) : IsElementaryAbelian p f.range := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, hA.is_comm.comm a b]
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    show (f a) ^ p = 1
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) a, map_one]

theorem inCatalog_thetaQuotient {p : ℕ} (hp : p.Prime) (hKP : CFSG.IsKProper G) {d : G}
    (hCtop : Subgroup.centralizer ({d} : Set G) ≠ ⊤) {I : Subgroup G}
    (hI : I ∈ thetaComponentsAt p d) :
    InCatalog ((↥I ⧸ aschbacherSolvableCore p ↥I) ⧸
      Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I)) := by
  obtain ⟨hIC, hL⟩ := mem_thetaComponentsAt_iff.mp hI
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set e : ↥(I.subgroupOf C) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIC with he
  have hLq : CFSG.IsQuasisimple
      (↥(I.subgroupOf C) ⧸ aschbacherSolvableCore p ↥(I.subgroupOf C)) := hL.2.2
  have h1 := inCatalog_quotient_center_of_thetaComponent hKP hCtop hLq
  let eθ : (↥(I.subgroupOf C) ⧸ aschbacherSolvableCore p ↥(I.subgroupOf C)) ≃*
      (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv hp e)
  let eZ := QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) eθ
    (Subgroup.map_center_eq eθ)
  obtain ⟨i, ⟨ψ⟩⟩ := h1
  exact ⟨i, ⟨eZ.symm.trans ψ⟩⟩

end OutTheta

open OutTheta in
theorem outPCyclicTheta_of_planeWith
    (P : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hP : SectionProvider P) (hplane : PlaneNoInnerPartWith P) : OutPCyclicTheta := by
  intro G _ _ p A hS d hdA hd1 I hI u huA hu1 v hvA hvu
  classical
  have hp : p.Prime := sectionTenSetup_prime hS
  have hp3 : 3 < p := sectionTenSetup_three_lt hS
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    subst h4
    norm_num at hp
  have : Fact p.Prime := ⟨hp⟩
  have hevG : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id hS
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hIC : I ≤ Subgroup.centralizer ({d} : Set G) := (mem_thetaComponentsAt_iff.mp hI).1
  have hAI : A ≤ Subgroup.normalizer (I : Set G) := fun x hx =>
    mem_normalizer_of_mem_centralizer_thetaComponentsAt hp hp3 hevG hI
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm x hx d hdA)) (hApow x hx)
  have hdN : d ∈ Subgroup.normalizer (I : Set G) := hAI hdA
  have htriv : thetaQuotientConj p I ⟨d, hdN⟩ = 1 := by
    rw [thetaQuotientConj_eq_one_iff]
    intro k hk
    have hkd : k * d = d * k := Subgroup.mem_centralizer_singleton_iff.mp (hIC hk)
    have h1 : d * k * d⁻¹ * k⁻¹ = 1 := by rw [← hkd]; group
    rw [h1]
    exact Subgroup.one_mem _
  by_cases hdU : d ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v
  · exact ⟨d, hdU, hd1, hdN, by rw [htriv]; exact Subgroup.one_mem _⟩
  by_contra hno
  push Not at hno
  set U : Subgroup G := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hU
  have hUle : U ≤ A := sup_le (Subgroup.zpowers_le.mpr huA) (Subgroup.zpowers_le.mpr hvA)
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ Subgroup.one_mem _)
  have hcu : Nat.card (Subgroup.zpowers u) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hApow u huA) hu1]
  have hcv : Nat.card (Subgroup.zpowers v) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hApow v hvA) hv1]
  have hcd : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hApow d hdA) hd1]
  have hcommuv : Commute u v := hAcomm u huA v hvA
  have hvnorm : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left hcommuv k).eq
  have hcardU : Nat.card U = p ^ 2 := by
    rw [hU, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hvnorm
      (disjoint_zpowers_of_not_mem hp (hApow u huA) (hApow v hvA) hvu), hcu, hcv]
    ring
  have hdisj_Ud : Disjoint U (Subgroup.zpowers d) := by
    rw [Subgroup.disjoint_def]
    intro z hzU hzd
    by_contra hz1
    have hzp : z ^ p = 1 := hApow z (hUle hzU)
    have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
    have hle : Subgroup.zpowers z ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hzd
    have hcz : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
    have heq : Subgroup.zpowers z = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hcd])
    apply hdU
    have hdz : d ∈ Subgroup.zpowers z := by rw [heq]; exact Subgroup.mem_zpowers d
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdz
    rw [← hk]
    exact Subgroup.zpow_mem _ hzU k
  have hdnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro h hh
    exact hAcomm h (hUle hh) d hdA
  have hAeq : U ⊔ Subgroup.zpowers d = A := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUle (Subgroup.zpowers_le.mpr hdA)) ?_
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hdnorm hdisj_Ud,
      hcardU, hcd, hAcard]
    ring_nf
    exact le_refl _
  have hdecomp : ∀ a ∈ A, ∃ b ∈ U, ∃ k : ℤ, a = b * d ^ k := by
    intro a ha
    rw [← hAeq] at ha
    exact (S11d.mem_sup_zpowers_iff (fun β hβ => hAcomm β (hUle hβ) d hdA)).mp ha
  obtain ⟨Γ, _, _, φ, ψ, hker, hψinj, hcompat, hrank⟩ :=
    exists_quotient_model hp hp2 hAI (IsElementaryAbelian.isPGroup p A)
  have hkerφ : φ.ker = aschbacherSolvableCore p ↥I := by
    ext i
    exact hker i
  let eQJ : (↥I ⧸ aschbacherSolvableCore p ↥I) ≃* ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hQq : CFSG.IsQuasisimple (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  have hJq : CFSG.IsQuasisimple ↥φ.range := LocalCores.isQuasisimple_of_mulEquiv eQJ hQq
  have hCtop : Subgroup.centralizer ({d} : Set G) ≠ ⊤ :=
    EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hd1
  have hcatQ := inCatalog_thetaQuotient hp hKP hCtop hI
  have hJcat : Catalog (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
    have hin : InCatalog (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
      let eT := QuotientGroup.congr (Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I))
        (Subgroup.center ↥φ.range) eQJ (Subgroup.map_center_eq eQJ)
      obtain ⟨i, ⟨ψ'⟩⟩ := hcatQ
      exact ⟨i, ⟨eT.symm.trans ψ'⟩⟩
    have hJs := hJq.2.1
    exact hbridge _ hJq.2.2 hin
  have hA'N : ψ.range ≤ Subgroup.normalizer (φ.range : Set Γ) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (hcompat a i).symm⟩
    · rintro ⟨i, hi⟩
      refine ⟨I.normalizerMonoidHom ⟨((a⁻¹ : ↥A) : G), hAI (a⁻¹).2⟩ i, ?_⟩
      rw [← hcompat a⁻¹ i, map_inv, hi]
      group
  have hA'e : IsElementaryAbelian p ψ.range := isElementaryAbelian_range' ψ
  have hA'card : Nat.card ψ.range = p ^ 3 := by
    rw [← hAcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hcA' : ψ ⟨d, hdA⟩ ∈ ψ.range := ⟨_, rfl⟩
  have hc1 : ψ ⟨d, hdA⟩ ≠ 1 := by
    intro h
    have := hψinj (h.trans (map_one ψ).symm)
    exact hd1 (congrArg Subtype.val this)
  have hcC : ψ ⟨d, hdA⟩ ∈ Subgroup.centralizer (φ.range : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    have h1 := hcompat ⟨d, hdA⟩ i
    have h2 : I.normalizerMonoidHom ⟨d, hAI hdA⟩ i = i := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hid : (i : G) * d = d * (i : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hIC i.2)
      exact mul_inv_eq_iff_eq_mul.mpr hid.symm
    rw [h2] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hmain : ∀ x ∈ ψ.range, x ∈ φ.range ⊔ Subgroup.centralizer (φ.range : Set Γ) →
      x ∈ Subgroup.zpowers (ψ ⟨d, hdA⟩) := by
    rintro _ ⟨a, rfl⟩ hx
    obtain ⟨j, hj, z, hz, hjz⟩ := exists_mul_of_mem_sup_centralizer' hx
    obtain ⟨i₀, rfl⟩ := hj
    have hin : InnerOnTheta p I (a : G) := by
      refine ⟨hAI a.2, (i₀ : ↥I ⧸ aschbacherSolvableCore p ↥I), ?_⟩
      ext q
      induction q using QuotientGroup.induction_on with
      | H k =>
        rw [MulAut.conj_apply, thetaQuotientConj_mk, ← QuotientGroup.mk_inv,
          ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        apply (hker _).mp
        have hzk : z * φ k * z⁻¹ = φ k :=
          mul_inv_eq_iff_eq_mul.mpr ((Subgroup.mem_centralizer_iff.mp hz (φ k) ⟨k, rfl⟩).symm)
        have h1 : φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ k) =
            φ i₀ * φ k * (φ i₀)⁻¹ := by
          rw [← hcompat a k, hjz]
          calc φ i₀ * z * φ k * (φ i₀ * z)⁻¹ = φ i₀ * (z * φ k * z⁻¹) * (φ i₀)⁻¹ := by group
            _ = φ i₀ * φ k * (φ i₀)⁻¹ := by rw [hzk]
        rw [map_mul, map_inv, h1, map_mul, map_mul, map_inv]
        group
    obtain ⟨b, hb, k, hbk⟩ := hdecomp (a : G) a.2
    have hbN : b ∈ Subgroup.normalizer (I : Set G) := hAI (hUle hb)
    have hb1 : b = 1 := by
      by_contra hb1
      apply hno b hb hb1
      obtain ⟨haN, hrange⟩ := hin
      refine ⟨hbN, ?_⟩
      have e1 : (⟨(a : G), haN⟩ : Subgroup.normalizer (I : Set G)) =
          ⟨b, hbN⟩ * ⟨d, hdN⟩ ^ k := Subtype.ext (by simp [hbk])
      have e2 : thetaQuotientConj p I ⟨(a : G), haN⟩ = thetaQuotientConj p I ⟨b, hbN⟩ := by
        rw [e1, map_mul, map_zpow, htriv, one_zpow, mul_one]
      rwa [e2] at hrange
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have had : (a : G) = d ^ k := by rw [hbk, hb1, one_mul]
    have hak : a = (⟨d, hdA⟩ : ↥A) ^ k := Subtype.ext (by simpa using had)
    rw [hak, map_zpow]
  exact hplane Γ p φ.range ψ.range (ψ ⟨d, hdA⟩) hp hp5 (hrank.trans hevG) hJq hJcat
    (hP G hevG I Γ φ p hp hp5 (hrank.trans hevG) hJq hJcat) hA'N hA'e hA'card hcA' hc1 hcC hmain

end CFSG.RankThree.PartOne
