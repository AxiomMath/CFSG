module

public import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec13.Item134Residual

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem mem_range_conj_of_pow_three_pow
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (σ : MulAut X) {k : ℕ}
    (hσ : σ ^ 3 ^ k = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
  set φ : Outer X ≃* Multiplicative (ZMod 2) := (equivalence e).trans f
  have hsq : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h1 : φ (σ : Outer X) = 1 := by
    have h3 : φ (σ : Outer X) ^ 3 ^ k = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one, map_one]
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at h3
    exact h3
  have h2 : (σ : Outer X) = 1 := φ.injective (h1.trans (map_one φ).symm)
  have h4 : σ ∈ inner X := (QuotientGroup.eq_one_iff σ).mp h2
  exact h4


theorem j2_exists_conj_eq_inv (h415 : Sec4.Item4_15) {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {z : X}
    (hz1 : z ≠ 1)
    (hzP : z ∈ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) :
    ∃ g : X, g * z * g⁻¹ = z⁻¹ := by
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, ⟨eN⟩⟩, -⟩ := h415 X hX P _ rfl _ rfl
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  have hZ3 : Nat.card Z = 3 := by
    rw [hZdef, ← Sec14.map_subtype_center_eq,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hHeis.1.2.2.2
  have hC : Nat.card (Subgroup.centralizer (Z : Set X)) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six hext
  have hPGL : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 2)) = 720 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := CFSG.GorensteinWalter.pgl2_card_formula (GaloisField 3 2)
    rw [GaloisField.card 3 2 (by norm_num)] at h
    rw [h]
    norm_num
  have hN : Nat.card (Subgroup.normalizer (Z : Set X)) = 2160 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Z.subgroupOf (Subgroup.normalizer (Z : Set X))), Nat.card_congr eN.toEquiv, hPGL,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hZ3]
  have hzZ : Subgroup.zpowers z = Z := Sec14.j2_zpowers_eq h415 hX P hz1 hzP.1
    ⟨P, hzP.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzP.2 y hy)⟩
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.normalizer (Z : Set X) ≤ Subgroup.centralizer (Z : Set X) := by
    intro g hg
    have hgz : g * z * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hg z).mp hzP
    have hgz' : g * z * g⁻¹ = z := by
      rcases KFacts.KS14.j2_mem_inf_centralizer_eq h415 hX P hzP hz1 hgz with h1 | h1 | h1
      · exfalso
        apply hz1
        have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
        rw [this, h1]
        group
      · exact h1
      · exfalso
        apply hcon g
        have hz3 : z * z * z = 1 := by
          have : z ^ 3 = 1 := by
            rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, hzZ, hZ3]
          rwa [pow_succ, pow_two] at this
        rw [h1, eq_inv_iff_mul_eq_one]
        exact hz3
    rw [← hzZ, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hgz']
  have := Subgroup.card_le_of_le hle
  rw [hN, hC] at this
  norm_num at this

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem exists_inv_mul_commute
    (H : Base A c L d K) {S : Subgroup G} (hS : IsSylowOf 3 S L) {ρ : G}
    (hρL : ρ ∈ Subgroup.normalizer (L : Set G)) (hρS : ρ ∈ Subgroup.normalizer (S : Set G))
    {k : ℕ} (hρ : ρ ^ 3 ^ k = 1) :
    ∃ s ∈ S, ∀ x ∈ S, s⁻¹ * ρ * x = x * (s⁻¹ * ρ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S', rfl⟩ := hS
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hinj : Set.InjOn π (S' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three S'.isPGroup'
  set ρ' : Subgroup.normalizer (L : Set G) := ⟨ρ, hρL⟩ with hρ'
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ρ') with hσ
  have hσk : σ ^ 3 ^ k = 1 := by
    have h1 : ρ' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hρ)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨q, hq⟩ := mem_range_conj_of_pow_three_pow H.quot σ hσk
  have hσapp : ∀ x : ↥L, σ (π x) = π (L.normalizerMonoidHom ρ' x) := fun x => rfl
  have hqapp : ∀ y, q * y * q⁻¹ = σ y := fun y => by rw [← hq]; rfl
  have hρS' : ∀ x ∈ (S' : Subgroup ↥L), L.normalizerMonoidHom ρ' x ∈ (S' : Subgroup ↥L) := by
    intro x hx
    have h1 : ρ * (x : G) * ρ⁻¹ ∈ (S' : Subgroup ↥L).map L.subtype :=
      (Subgroup.mem_normalizer_iff.mp hρS x).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = L.normalizerMonoidHom ρ' x := Subtype.ext hyx
    exact this ▸ hy
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S'.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S' : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  have hqN : q ∈ Subgroup.normalizer ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
      Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [hqapp]
    rw [SetLike.mem_coe, hSb] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hσapp]
    exact Subgroup.mem_map_of_mem π (hρS' x hx)
  have hq3 : q ^ 3 ^ k = 1 := by
    have hc : q ^ 3 ^ k ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : MulAut.conj (q ^ 3 ^ k) = 1 := by rw [map_pow, hq, hσk]
      have h2 := congrArg (fun φ : MulAut _ => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * q ^ 3 ^ k = q ^ 3 ^ k * y * (q ^ 3 ^ k)⁻¹ * q ^ 3 ^ k := by rw [h2]
        _ = q ^ 3 ^ k * y := by group
    rw [H.center_quot, Subgroup.mem_bot] at hc
    exact hc
  have hqS : q ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    have hdvd : orderOf q ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hq3
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hp : IsPGroup 3 (Subgroup.zpowers q) :=
      IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
    have hsup := hp.to_sup_of_normal_right' Sb.isPGroup' (Subgroup.zpowers_le.mpr hqN)
    have heq := Sb.3 hsup le_sup_right
    exact heq ▸ (le_sup_left : Subgroup.zpowers q ≤ _) (Subgroup.mem_zpowers q)
  rw [hSb] at hqS
  obtain ⟨s₁, hs₁, hs₁q⟩ := hqS
  refine ⟨(s₁ : G), ⟨s₁, hs₁, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  set y : ↥L := s₁⁻¹ * L.normalizerMonoidHom ρ' x * s₁ with hy
  have hyS : y ∈ (S' : Subgroup ↥L) := mul_mem (mul_mem (inv_mem hs₁) (hρS' x hx)) hs₁
  have hπy : π y = π x := by
    rw [hy, map_mul, map_mul, map_inv, ← hσapp, ← hqapp, hs₁q]
    group
  have hyx := hinj hyS hx hπy
  have hyx' : (s₁ : G)⁻¹ * (ρ * (x : G) * ρ⁻¹) * s₁ = x := congrArg Subtype.val hyx
  calc (s₁ : G)⁻¹ * ρ * x = (s₁ : G)⁻¹ * (ρ * (x : G) * ρ⁻¹) * s₁ * ((s₁ : G)⁻¹ * ρ) := by group
    _ = x * ((s₁ : G)⁻¹ * ρ) := by rw [hyx']

end Base

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem exists_mem_L_conj_eq_inv (H : Base A c L d K) : ∃ t ∈ L, t * d * t⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdL, S₀, hdS₀, hS₀d⟩ := H.exists_d_mem_L
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h => H.ne_one (congrArg Subtype.val h)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S₀.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S₀ : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨hdb1, -⟩ := bar_facts_of_central hd'1 ⟨S₀, hdS₀, hS₀d⟩
  have hdbZ : π d' ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
      Subgroup.centralizer ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine ⟨hSb ▸ Subgroup.mem_map_of_mem π hdS₀, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [hSb] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hS₀d hx)]
  obtain ⟨gb, hgb⟩ := j2_exists_conj_eq_inv H.h415 H.quot Sb hdb1 hdbZ
  have hD3 : IsPGroup 3 (Subgroup.zpowers d') :=
    S₀.isPGroup'.to_le (Subgroup.zpowers_le.mpr hdS₀)
  have hgbN : gb ∈ Subgroup.normalizer (((Subgroup.zpowers d').map π :
      Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [SetLike.mem_coe, MonoidHom.map_zpowers] at hy ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hgb]
    exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers _)) k
  rw [normalizer_map_mk_eq hD3] at hgbN
  obtain ⟨t, htN, rfl⟩ := hgbN
  have htd : t * d' * t⁻¹ ∈ Subgroup.zpowers d' :=
    (Subgroup.mem_normalizer_iff.mp htN d').mp (Subgroup.mem_zpowers d')
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hD3
  have heq : t * d' * t⁻¹ = d'⁻¹ := hinj htd (inv_mem (Subgroup.mem_zpowers d'))
    (by rw [map_inv, map_mul, map_mul, map_inv]; exact hgb)
  exact ⟨t, t.2, congrArg Subtype.val heq⟩

end Base

section Tools

omit [Finite G] in
theorem exists_isSylowOf_le {P K : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 3 P) :
    ∃ Q : Subgroup G, IsSylowOf 3 Q K ∧ P ≤ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

omit [Finite G] in
theorem isSylowOf_of_maximal {P K : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 3 P)
    (hmax : ∀ Q : Subgroup G, P ≤ Q → Q ≤ K → IsPGroup 3 Q → Q = P) : IsSylowOf 3 P K := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_le hPK hP
  rw [← hmax Q hPQ hQ.le hQ.isPGroup]
  exact hQ

theorem le_of_isSylowOf_of_le_normalizer {B P K : Subgroup G} (hP : IsSylowOf 3 P K)
    (hB : IsPGroup 3 B) (hBK : B ≤ K) (hKB : K ≤ Subgroup.normalizer (B : Set G)) : B ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsup := hP.isPGroup.to_sup_of_normal_right' hB (hP.le.trans hKB)
  have heq := hP.eq_of_le le_sup_left (sup_le hP.le hBK) hsup
  exact heq ▸ le_sup_right

theorem exists_conj_of_isSylowOf {P Q K : Subgroup G} (hP : IsSylowOf 3 P K)
    (hQ : IsSylowOf 3 Q K) : ∃ m ∈ K, Q = P.map (MulAut.conj m).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq K P' Q'
  refine ⟨m, m.2, ?_⟩
  rw [← hm, Sec14.coe_sylow_smul_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_normalizer_zpowers_of_mem_centralizer {c x : G}
    (hx : x ∈ Subgroup.centralizer ({c} : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [SetLike.mem_coe, ← conj_zpow,
    show x * c * x⁻¹ = c by rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]]
  exact Subgroup.zpow_mem_zpowers c k

end Tools

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem c_mem_centralizer_inf (H : Base A c L d K) :
    c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ he => H.comm_L he.2

theorem exists_decomp (H : Base A c L d K) {a : G} (ha : a ∈ A) :
    ∃ k : ℤ, ∃ e ∈ A ⊓ L, a = c ^ k * e := by
  rw [H.eq_sup] at ha
  exact KFacts.KS14.exists_zpow_mul_of_mem_sup H.c_mem_centralizer_inf ha

theorem commute_of_commute_S (H : Base A c L d K) {S : Subgroup G} (hES : A ⊓ L ≤ S) {γ : G}
    (hγc : γ * c = c * γ) (hγS : ∀ x ∈ S, γ * x = x * γ) {a : G} (ha : a ∈ A) :
    γ * a = a * γ := by
  obtain ⟨k, e, he, rfl⟩ := H.exists_decomp ha
  have h1 : Commute γ (c ^ k) := Commute.zpow_right hγc k
  have h2 : Commute γ e := hγS e (hES he)
  exact (h1.mul_right h2).eq

theorem conj_mem_of_mem_S (H : Base A c L d K) {S : Subgroup G} (hSD : SylowData A L d K S)
    {s : G} (hs : s ∈ S) {a : G} (ha : a ∈ A) : s * a * s⁻¹ * a⁻¹ ∈ Subgroup.zpowers d := by
  obtain ⟨k, e, he, rfl⟩ := H.exists_decomp ha
  have hsL : s ∈ L := hSD.isSylowOf.le hs
  have hsc : Commute s (c ^ k) := Commute.zpow_right (H.comm_L hsL) k
  have h1 := hSD.commutator_mem s hs e (hSD.inf_le he)
  have hce : Commute (c ^ k) (s * e * s⁻¹ * e⁻¹) := by
    refine Commute.zpow_left ?_ k
    have hm : s * e * s⁻¹ * e⁻¹ ∈ L := by
      have heL : e ∈ L := he.2
      exact mul_mem (mul_mem (mul_mem hsL heL) (inv_mem hsL)) (inv_mem heL)
    exact (H.comm_L hm).symm
  have : s * (c ^ k * e) * s⁻¹ * (c ^ k * e)⁻¹ = c ^ k * (s * e * s⁻¹ * e⁻¹) * (c ^ k)⁻¹ := by
    calc s * (c ^ k * e) * s⁻¹ * (c ^ k * e)⁻¹ = (s * c ^ k) * e * s⁻¹ * e⁻¹ * (c ^ k)⁻¹ := by
          group
      _ = (c ^ k * s) * e * s⁻¹ * e⁻¹ * (c ^ k)⁻¹ := by rw [hsc.eq]
      _ = c ^ k * (s * e * s⁻¹ * e⁻¹) * (c ^ k)⁻¹ := by group
  rw [this, hce.eq, mul_inv_cancel_right]
  exact h1

theorem S_le_normalizer (H : Base A c L d K) {S : Subgroup G} (hSD : SylowData A L d K S) :
    S ≤ Subgroup.normalizer (A : Set G) := fun s hs =>
  Subgroup.mem_normalizer_fintype fun a ha => by
    have h1 := H.conj_mem_of_mem_S hSD hs ha
    have h2 : s * a * s⁻¹ = (s * a * s⁻¹ * a⁻¹) * a := by group
    rw [SetLike.mem_coe, h2]
    exact mul_mem ((Subgroup.zpowers_le.mpr H.mem_A) h1) ha

end Base

omit [Finite G] in
theorem le_centralizer_of_mem_center_map {P : Subgroup G} {x : G}
    (hx : x ∈ (Subgroup.center P).map P.subtype) : P ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨z, hz, rfl⟩ := hx
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)

structure TData (A : Subgroup G) (c : G) (L : Subgroup G) (d : G) (S T : Subgroup G) : Prop where
  isSylowOf : IsSylowOf 3 T
    (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G))
  S_le : S ≤ T
  A_le : A ≤ T
  le_c : T ≤ Subgroup.centralizer ({c} : Set G)
  le_d : T ≤ Subgroup.centralizer ({d} : Set G)
  conj_mem : ∀ τ ∈ T, ∀ a ∈ A, τ * a * τ⁻¹ * a⁻¹ ∈ Subgroup.zpowers d
  isSylowOf_cd : IsSylowOf 3 T
    (Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G))
  mem_B : ∀ z ∈ T, (∀ τ ∈ T, z * τ = τ * z) → z ^ 3 = 1 →
    z ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem exists_mem_S_commute
    (H : Base A c L d K) {S : Subgroup G} (hSD : SylowData A L d K S) {R : Subgroup G}
    (hR : IsPGroup 3 R) (hSR : S ≤ R) (hRc : R ≤ Subgroup.centralizer ({c} : Set G)) {ρ : G}
    (hρ : ρ ∈ R) : ∃ s ∈ S, ∀ a ∈ A, s⁻¹ * ρ * a = a * (s⁻¹ * ρ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRL : R ≤ Subgroup.normalizer (L : Set G) :=
    Sec12.le_normalizer_of_mem_thetaComponentsAt H.h45 H.data.toTheoremFourHyp
      H.data.orderOf_eq H.data.mem_thetaComponentsAt hR
      (fun x hx => mem_normalizer_zpowers_of_mem_centralizer (hRc hx))
  have hRLS : R ⊓ L = S :=
    hSD.isSylowOf.eq_of_le (le_inf hSR hSD.isSylowOf.le) inf_le_right (hR.to_le inf_le_left)
  have hρS : ρ ∈ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, ← hRLS]
    exact Subgroup.mem_inf.mpr ⟨R.mul_mem (R.mul_mem hρ (hSR hx)) (R.inv_mem hρ),
      (Subgroup.mem_normalizer_iff.mp (hRL hρ) x).mp (hSD.isSylowOf.le hx)⟩
  obtain ⟨k, hk⟩ := hR ⟨ρ, hρ⟩
  have hk' : ρ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨s, hs, hγ⟩ := H.exists_inv_mul_commute hSD.isSylowOf (hRL hρ) hρS hk'
  refine ⟨s, hs, fun a ha => H.commute_of_commute_S hSD.inf_le ?_ hγ ha⟩
  have hsc : s * c = c * s := H.comm_L (hSD.isSylowOf.le hs)
  have hρc : ρ * c = c * ρ := Subgroup.mem_centralizer_singleton_iff.mp (hRc hρ)
  calc s⁻¹ * ρ * c = s⁻¹ * (c * ρ) := by rw [mul_assoc, hρc]
    _ = c * (s⁻¹ * ρ) := by
      rw [← mul_assoc, ← mul_assoc, (Commute.inv_left (show Commute s c from hsc)).eq]

theorem le_normalizer_of_le_centralizer
    (H : Base A c L d K) {S : Subgroup G}
    (hSD : SylowData A L d K S) {R : Subgroup G} (hR : IsPGroup 3 R) (hSR : S ≤ R)
    (hRc : R ≤ Subgroup.centralizer ({c} : Set G)) : R ≤ Subgroup.normalizer (A : Set G) := by
  intro ρ hρ
  obtain ⟨s, hs, hγ⟩ := H.exists_mem_S_commute hSD hR hSR hRc hρ
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have h1 : ρ * a * ρ⁻¹ = s * a * s⁻¹ := by
    have h2 : ρ = s * (s⁻¹ * ρ) := by group
    calc ρ * a * ρ⁻¹ = s * ((s⁻¹ * ρ) * a) * (s⁻¹ * ρ)⁻¹ * s⁻¹ := by group
      _ = s * a * s⁻¹ := by rw [hγ a ha]; group
  rw [SetLike.mem_coe, h1]
  exact (Subgroup.mem_normalizer_iff.mp (H.S_le_normalizer hSD hs) a).mp ha

theorem exists_tData
    (H : Base A c L d K) {S : Subgroup G} (hSD : SylowData A L d K S) :
    ∃ T : Subgroup G, TData A c L d S T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 S := hSD.isSylowOf.isPGroup
  have hSN : S ≤ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    le_inf (H.S_le_normalizer hSD)
      (fun x hx => mem_normalizer_zpowers_of_mem_centralizer (hSD.le_centralizer hx))
  obtain ⟨T, hT, hST⟩ := exists_isSylowOf_le hSN hSp
  have hB := H.le_center T hT
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_center_map (hB (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
  have hTd : T ≤ Subgroup.centralizer ({d} : Set G) :=
    le_centralizer_of_mem_center_map (hB (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  have hTp : IsPGroup 3 T := hT.isPGroup
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [H.data.card_eq]; norm_num)
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (H.data.commute ha H.mem_A)
  have hAT : A ≤ T := le_of_isSylowOf_of_le_normalizer hT hAp
    (le_inf Subgroup.le_normalizer
      (fun x hx => mem_normalizer_zpowers_of_mem_centralizer (hAd hx))) inf_le_left
  refine ⟨T, hT, hST, hAT, hTc, hTd, ?_, ?_, ?_⟩
  ·
    intro τ hτ a ha
    obtain ⟨s, hs, hγ⟩ := H.exists_mem_S_commute hSD hTp hST hTc hτ
    have h1 : τ * a * τ⁻¹ = s * a * s⁻¹ := by
      calc τ * a * τ⁻¹ = s * ((s⁻¹ * τ) * a) * (s⁻¹ * τ)⁻¹ * s⁻¹ := by group
        _ = s * a * s⁻¹ := by rw [hγ a ha]; group
    rw [h1]
    exact H.conj_mem_of_mem_S hSD hs ha
  ·
    refine isSylowOf_of_maximal (le_inf hTc hTd) hTp fun R hTR hRcd hR => ?_
    have hRA := H.le_normalizer_of_le_centralizer hSD hR (hST.trans hTR)
      (hRcd.trans inf_le_left)
    exact hT.eq_of_le hTR (le_inf hRA
      (fun x hx => mem_normalizer_zpowers_of_mem_centralizer (hRcd hx).2)) hR
  ·
    intro z hzT hzc hz3
    have hcomm : ∀ x ∈ A, ∀ y ∈ Subgroup.zpowers z, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x z from (hzc x (hAT hx)).symm) k).eq
    have hEA := isElemAbelian_sup H.data.isElemAbelian (isElemAbelian_zpowers hz3) hcomm
    have heq := H.data.eq_of_le hEA le_sup_left
    have hzA : z ∈ A := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    obtain ⟨k, e, he, rfl⟩ := H.exists_decomp hzA
    have heS : e ∈ Subgroup.zpowers d := by
      refine hSD.mem_zpowers_of_central e (hSD.inf_le he) fun s hs => ?_
      have h1 : (c ^ k * e) * s = s * (c ^ k * e) := hzc s (hST hs)
      have h2 : Commute (c ^ k) s :=
        Commute.zpow_left (H.comm_L (hSD.isSylowOf.le hs)).symm k
      have h3 : c ^ k * (e * s) = c ^ k * (s * e) := by
        rw [← mul_assoc, h1, ← mul_assoc, ← h2.eq, mul_assoc]
      exact mul_left_cancel h3
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c k))
      (Subgroup.mem_sup_right heS)

end Base

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem exists_conj_inv (H : Base A c L d K) {S T : Subgroup G} (hTD : TData A c L d S T) :
    ∃ t ∈ Subgroup.normalizer (T : Set G), t * c = c * t ∧ t * d * t⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t₀, ht₀L, ht₀d⟩ := H.exists_mem_L_conj_eq_inv
  have ht₀c : t₀ * c = c * t₀ := H.comm_L ht₀L
  set Y := Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) with hY
  set T' := T.map (MulAut.conj t₀).toMonoidHom with hT'
  have hT'Y : T' ≤ Y := by
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨hτc, hτd⟩ := hTD.isSylowOf_cd.le hτ
    have hτc' : τ * c = c * τ := Subgroup.mem_centralizer_singleton_iff.mp hτc
    have hτd' : τ * d = d * τ := Subgroup.mem_centralizer_singleton_iff.mp hτd
    have key : ∀ x : G, τ * x = x * τ →
        (t₀ * τ * t₀⁻¹) * (t₀ * x * t₀⁻¹) = (t₀ * x * t₀⁻¹) * (t₀ * τ * t₀⁻¹) := by
      intro x hx
      calc (t₀ * τ * t₀⁻¹) * (t₀ * x * t₀⁻¹) = t₀ * (τ * x) * t₀⁻¹ := by group
        _ = t₀ * (x * τ) * t₀⁻¹ := by rw [hx]
        _ = (t₀ * x * t₀⁻¹) * (t₀ * τ * t₀⁻¹) := by group
    have htc : t₀ * c * t₀⁻¹ = c := by rw [ht₀c, mul_inv_cancel_right]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · change t₀ * τ * t₀⁻¹ * c = c * (t₀ * τ * t₀⁻¹)
      have := key c hτc'
      rwa [htc] at this
    · change t₀ * τ * t₀⁻¹ * d = d * (t₀ * τ * t₀⁻¹)
      have h1 := key d hτd'
      rw [ht₀d] at h1
      have h2 := (Commute.inv_right (show Commute (t₀ * τ * t₀⁻¹) d⁻¹ from h1)).eq
      rwa [inv_inv] at h2
  have hT'syl : IsSylowOf 3 T' Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hT'Y ?_
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj t₀).injective]
    exact hTD.isSylowOf_cd.card_eq
  obtain ⟨m, hmY, hm⟩ := exists_conj_of_isSylowOf hTD.isSylowOf_cd hT'syl
  obtain ⟨hmc, hmd⟩ := hmY
  have hmc' : m * c = c * m := Subgroup.mem_centralizer_singleton_iff.mp hmc
  have hmd' : m * d = d * m := Subgroup.mem_centralizer_singleton_iff.mp hmd
  refine ⟨m⁻¹ * t₀, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show T.map (MulAut.conj (m⁻¹ * t₀)).toMonoidHom = T
    have h1 : T.map (MulAut.conj (m⁻¹ * t₀)).toMonoidHom =
        (T.map (MulAut.conj t₀).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [h1, ← hT', hm, Subgroup.map_map]
    convert Subgroup.map_id T using 2
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  · have h1 : m⁻¹ * c = c * m⁻¹ := (Commute.inv_left (show Commute m c from hmc')).eq
    rw [mul_assoc, ht₀c, ← mul_assoc, h1, mul_assoc]
  · have h1 : m⁻¹ * d⁻¹ * m = d⁻¹ := by
      have h2 : m⁻¹ * d * m = d := by rw [mul_assoc, ← hmd', ← mul_assoc, inv_mul_cancel, one_mul]
      calc m⁻¹ * d⁻¹ * m = (m⁻¹ * d * m)⁻¹ := by group
        _ = d⁻¹ := by rw [h2]
    calc m⁻¹ * t₀ * d * (m⁻¹ * t₀)⁻¹ = m⁻¹ * (t₀ * d * t₀⁻¹) * m := by group
      _ = d⁻¹ := by rw [ht₀d, h1]

end Base

end CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
