module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res2ProofTheta
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.OddKernel.SimpleQuotient
import CFSG.RankThree.PartTwo.Sec5.Bender.Core

public section

open CFSG Subgroup
open CFSG.RankThree.PartTwo.Sec16.Proof166Res2
  (eq_one_of_inr_mem_centralizer apply_eq_of_inl_mul_inr rank3II_3_6_pow)

instance r116_finite_holomorph (P : Type*) [Group P] [Finite P] :
    Finite (P ⋊[MonoidHom.id (MulAut P)] MulAut P) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem r116_inl_mul_inr {P : Type*} [Group P] {σ : MulAut P} {w : P} (h : σ w = w) :
    (SemidirectProduct.inl w : P ⋊[MonoidHom.id (MulAut P)] MulAut P) *
      SemidirectProduct.inr σ = SemidirectProduct.inr σ * SemidirectProduct.inl w := by
  have h0 := SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut P)) σ w
  rw [MonoidHom.id_apply, h, map_inv] at h0
  calc (SemidirectProduct.inl w : P ⋊[MonoidHom.id (MulAut P)] MulAut P) * SemidirectProduct.inr σ
      = (SemidirectProduct.inr σ * SemidirectProduct.inl w * (SemidirectProduct.inr σ)⁻¹) *
          SemidirectProduct.inr σ := by rw [← h0]
    _ = SemidirectProduct.inr σ * SemidirectProduct.inl w := by group

theorem r116_inl_range_inf_centralizer {P : Type*} [Group P] (σ : MulAut P) :
    (SemidirectProduct.inl : P →* P ⋊[MonoidHom.id (MulAut P)] MulAut P).range ⊓
      Subgroup.centralizer ({SemidirectProduct.inr σ} : Set (P ⋊[MonoidHom.id (MulAut P)] MulAut P)) =
    (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id P)).map
      (SemidirectProduct.inl : P →* P ⋊[MonoidHom.id (MulAut P)] MulAut P) := by
  ext v
  constructor
  · rintro ⟨⟨w, rfl⟩, hv⟩
    have hv' : (SemidirectProduct.inl w : P ⋊[MonoidHom.id (MulAut P)] MulAut P) ∈
        Subgroup.centralizer ({SemidirectProduct.inr σ} : Set (P ⋊[MonoidHom.id (MulAut P)] MulAut P)) :=
      hv
    rw [Subgroup.mem_centralizer_singleton_iff] at hv'
    exact Subgroup.mem_map_of_mem (SemidirectProduct.inl : P →* P ⋊[MonoidHom.id (MulAut P)] MulAut P)
      (K := MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id P)) (x := w)
      (apply_eq_of_inl_mul_inr hv')
  · rintro ⟨w, hw, rfl⟩
    exact ⟨MonoidHom.mem_range.mpr ⟨w, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (r116_inl_mul_inr (σ := σ) (w := w) hw)⟩

theorem r116_assembly_pRank_eq {G : Type*} [Group G] [Finite G] (p : ℕ) (K : Subgroup G) :
    CFSG.Assembly.pRank p K = CFSG.pRank p ↥K :=
  ((CFSG.SectionRank.pRank_eq_open_pRank_top p ↥K).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm).symm

theorem r116_pRank_le {P : Type*} [Group P] [Finite P] (p : ℕ) (hp : 1 < p) (σ : MulAut P) :
    CFSG.Assembly.pRank p ((SemidirectProduct.inl : P →* P ⋊[MonoidHom.id (MulAut P)] MulAut P).range ⊓
      Subgroup.centralizer ({SemidirectProduct.inr σ} : Set (P ⋊[MonoidHom.id (MulAut P)] MulAut P))) ≤
    CFSG.Assembly.pRank p (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id P)) := by
  rw [r116_inl_range_inf_centralizer σ, r116_assembly_pRank_eq, r116_assembly_pRank_eq]
  let e := Subgroup.equivMapOfInjective (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id P))
    (SemidirectProduct.inl : P →* P ⋊[MonoidHom.id (MulAut P)] MulAut P)
    SemidirectProduct.inl_injective
  exact CFSG.RankThree.OddKernel.pRank_le_of_injective hp e.symm.toMonoidHom e.symm.injective

theorem rank3II_3_6_pow_hom {N : Type*} [Group N] {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq3 : 3 < q) {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (φ : N →* MulAut P) {U X : Subgroup N} {x : N} (hU : IsPGroup 2 U)
    (hXx : X = Subgroup.zpowers x) (hX : IsPGroup q X) (hUX : ⁅U, X⁆ = U)
    (hU1 : ∃ u ∈ U, φ u ≠ 1)
    (hfix : ∀ u ∈ U, φ u ≠ 1 →
      CFSG.Assembly.pRank p (MonoidHom.eqLocus (φ u).toMonoidHom (MonoidHom.id P)) ≤ 2) :
    q = 5 := by
  let f : N →* (P ⋊[MonoidHom.id (MulAut P)] MulAut P) := SemidirectProduct.inr.comp φ
  set P' : Subgroup (P ⋊[MonoidHom.id (MulAut P)] MulAut P) :=
    (SemidirectProduct.inl : P →* P ⋊[MonoidHom.id (MulAut P)] MulAut P).range with hP'
  set U' : Subgroup (P ⋊[MonoidHom.id (MulAut P)] MulAut P) := U.map f with hU'
  set X' : Subgroup (P ⋊[MonoidHom.id (MulAut P)] MulAut P) := X.map f with hX'
  have hP'p : IsPGroup p P' := by
    rw [hP', MonoidHom.range_eq_map]
    exact (hP.to_subgroup ⊤).map _
  have hX'eq : X' = Subgroup.zpowers (f x) := by
    rw [hX', hXx, MonoidHom.map_zpowers]
  have hX'q : IsPGroup q X' := hX.map f
  have hU'2 : IsPGroup 2 U' := hU.map f
  have hU'X' : ⁅U', X'⁆ = U' := by
    rw [hU', hX', ← Subgroup.map_commutator, hUX]
  have hnorm : ∀ K : Subgroup (P ⋊[MonoidHom.id (MulAut P)] MulAut P),
      K ≤ Subgroup.normalizer (P' : Set (P ⋊[MonoidHom.id (MulAut P)] MulAut P)) := by
    intro K
    have : P'.Normal := by
      rw [hP', SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    rw [Subgroup.normalizer_eq_top_iff.mpr this]
    exact le_top
  obtain ⟨u₀, hu₀U, hu₀1⟩ := hU1
  have hU'1 : U' ≠ ⊥ := by
    intro h0
    have hmem : f u₀ ∈ U' := Subgroup.mem_map_of_mem f hu₀U
    rw [h0, Subgroup.mem_bot] at hmem
    exact hu₀1 (SemidirectProduct.inr_injective (hmem.trans (map_one _).symm))
  have hfaith : U' ⊓ Subgroup.centralizer (P' : Set (P ⋊[MonoidHom.id (MulAut P)] MulAut P)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨n, -, rfl⟩, hnC⟩
    rw [Subgroup.mem_bot]
    have hnC' : (SemidirectProduct.inr (φ n) : P ⋊[MonoidHom.id (MulAut P)] MulAut P) ∈
        Subgroup.centralizer (P' : Set (P ⋊[MonoidHom.id (MulAut P)] MulAut P)) := hnC
    show (SemidirectProduct.inr (φ n) : P ⋊[MonoidHom.id (MulAut P)] MulAut P) = 1
    rw [eq_one_of_inr_mem_centralizer hnC', map_one]
  have hfix' : ∀ w ∈ U', w ≠ 1 →
      CFSG.Assembly.pRank p (P' ⊓ Subgroup.centralizer
        ({w} : Set (P ⋊[MonoidHom.id (MulAut P)] MulAut P))) ≤ 2 := by
    rintro _ ⟨n, hn, rfl⟩ hw1
    have hn1 : φ n ≠ 1 := by
      intro h1
      apply hw1
      show (SemidirectProduct.inr (φ n) : P ⋊[MonoidHom.id (MulAut P)] MulAut P) = 1
      rw [h1, map_one]
    exact (r116_pRank_le p hp.one_lt (φ n)).trans (hfix n hn hn1)
  exact rank3II_3_6_pow hp hp2 hq hq3 hP'p hU'2 hX'eq hX'q hU'X' hU'1 (hnorm U') (hnorm X')
    hfaith hfix'

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem e1c_conj_mem_inSubgroup {G : Type*} [Group G] [Finite G] (p : ℕ) {X : Subgroup G}
    {g y : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hy : y ∈ CFSG.inSubgroup (CFSG.pCore p) X) :
    g * y * g⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore p) X := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  let φ : MulAut X := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix := (inferInstance : (CFSG.pCore p X).Characteristic).fixed φ
  have hφk : φ k ∈ CFSG.pCore p X := by
    rw [← hfix] at hk
    exact hk
  exact Subgroup.mem_map.mpr ⟨φ k, hφk, rfl⟩

theorem e1c_normalizer_le_inSubgroup {G : Type*} [Group G] [Finite G] (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.inSubgroup (CFSG.pCore p) X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨e1c_conj_mem_inSubgroup p hg, fun h => ?_⟩
  have := e1c_conj_mem_inSubgroup p (Subgroup.inv_mem _ hg) h
  simpa [mul_assoc] using this

theorem e1c_phi_apply {G : Type*} [Group G] (P : Subgroup G)
    (n : Subgroup.normalizer (P : Set G)) (h : P) :
    ((P.normalizerMonoidHom n h : P) : G) = (n : G) * (h : G) * (n : G)⁻¹ := rfl

theorem e1c_core_bot {G : Type*} [Group G] {θ : Subgroup G} {p : ℕ}
    (h : CFSG.inSubgroup (CFSG.pCore p) θ = ⊥) : CFSG.pCore p θ = ⊥ := by
  apply Subgroup.map_injective (f := θ.subtype) θ.subtype_injective
  rw [Subgroup.map_bot]
  exact h

theorem e1c_fit_two_bot {Θ : Type*} [Group Θ] [Finite Θ] (hcore : CFSG.pCore 2 Θ = ⊥)
    {V : Subgroup Θ} (hV2 : IsPGroup 2 V) (hVF : V ≤ CFSG.fittingSubgroup Θ) :
    ∀ v ∈ V, v = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV' : IsPGroup 2 (V.subgroupOf (CFSG.fittingSubgroup Θ)) :=
    hV2.comap_of_injective (CFSG.fittingSubgroup Θ).subtype
      (CFSG.fittingSubgroup Θ).subtype_injective
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hV'
  have hQle : (Q : Subgroup (CFSG.fittingSubgroup Θ)).map (CFSG.fittingSubgroup Θ).subtype ≤
      CFSG.pCore 2 Θ :=
    Sylow.map_le_pCore (N := CFSG.fittingSubgroup Θ) inferInstance inferInstance 2 Q
  rw [hcore, le_bot_iff] at hQle
  intro v hv
  have hvF : v ∈ CFSG.fittingSubgroup Θ := hVF hv
  have hmem0 : (⟨v, hvF⟩ : CFSG.fittingSubgroup Θ) ∈ V.subgroupOf (CFSG.fittingSubgroup Θ) := hv
  have hmem : (⟨v, hvF⟩ : CFSG.fittingSubgroup Θ) ∈ (Q : Subgroup (CFSG.fittingSubgroup Θ)) :=
    hQ hmem0
  have hmap : v ∈ (Q : Subgroup (CFSG.fittingSubgroup Θ)).map (CFSG.fittingSubgroup Θ).subtype :=
    Subgroup.mem_map.mpr ⟨⟨v, hvF⟩, hmem, rfl⟩
  rw [hQle] at hmap
  exact Subgroup.mem_bot.mp hmap

theorem e1c_exists_prime {G : Type*} [Group G] [Finite G] {θ U : Subgroup G}
    (hθs : Group.IsSolvable θ) (hθ3 : ¬ 3 ∣ Nat.card θ)
    (hO2 : CFSG.inSubgroup (CFSG.pCore 2) θ = ⊥) (hUθ : U ≤ θ) (hU2 : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ ∃ u ∈ U, ∃ p ∈ CFSG.inSubgroup (CFSG.pCore r) θ,
      u * p ≠ p * u := by
  by_contra hcon
  push Not at hcon
  have hcore2 : CFSG.pCore 2 θ = ⊥ := e1c_core_bot hO2
  have hV2 : IsPGroup 2 (U.subgroupOf θ) :=
    hU2.comap_of_injective θ.subtype θ.subtype_injective
  have hcent : ∀ q : (Nat.card θ).primeFactors.attach,
      U.subgroupOf θ ≤ Subgroup.centralizer (CFSG.pCore q.1.1 θ : Set θ) := by
    intro q
    have hqp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have hqd : q.1.1 ∣ Nat.card θ := Nat.dvd_of_mem_primeFactors q.1.2
    by_cases h2 : q.1.1 = 2
    · rw [h2, hcore2]
      intro v _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
    · by_cases h3 : q.1.1 = 3
      · exact (hθ3 (h3 ▸ hqd)).elim
      · have hq3 : 3 < q.1.1 := by
          have := hqp.two_le
          omega
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        apply Subtype.ext
        have hvU : (v : G) ∈ U := Subgroup.mem_subgroupOf.mp hv
        have hpG : (p : G) ∈ CFSG.inSubgroup (CFSG.pCore q.1.1) θ :=
          Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
        exact (hcon q.1.1 hqp hq3 (v : G) hvU (p : G) hpG).symm
  have hVF : U.subgroupOf θ ≤ CFSG.fittingSubgroup θ :=
    (CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores hcent).trans
      (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hθs)
  have hne : ∃ u ∈ U, u ≠ 1 := by
    by_contra hne
    push Not at hne
    exact hU1 (eq_bot_iff.mpr fun u hu => Subgroup.mem_bot.mpr (hne u hu))
  obtain ⟨u, hu, hu1⟩ := hne
  have hv : (⟨u, hUθ hu⟩ : θ) ∈ U.subgroupOf θ := Subgroup.mem_subgroupOf.mpr hu
  exact hu1 (congrArg Subtype.val (e1c_fit_two_bot hcore2 hV2 hVF _ hv))

theorem e1_core {G : Type*} [Group G] [Finite G]
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → ∀ Q : Subgroup G, IsPGroup r Q → ∀ u : G, u ≠ 1 →
      IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank r ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2)
    {θ S : Subgroup G} (hθs : Group.IsSolvable θ) (hθ3 : ¬ 3 ∣ Nat.card θ)
    (hO2 : inSubgroup (CFSG.pCore 2) θ = ⊥) (hS2 : IsPGroup 2 S) (hSθ : S ≤ θ)
    {x : G} {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hxq : IsPGroup q (Subgroup.zpowers x))
    (hxθ : x ∈ Subgroup.normalizer (θ : Set G)) (hxS : x ∈ Subgroup.normalizer (S : Set G))
    (hxS1 : ⁅S, Subgroup.zpowers x⁆ ≠ ⊥) : q = 5 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup G, U = ⁅S, Subgroup.zpowers x⁆ := ⟨_, rfl⟩
  have hXS : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.zpowers_le.mpr hxS
  have hUS : U ≤ S := by
    rw [hUdef]
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers x) (K := S)).mp hXS
  have hUθ : U ≤ θ := hUS.trans hSθ
  have hU2 : IsPGroup 2 U := hS2.to_le hUS
  have hU1 : U ≠ ⊥ := by
    rw [hUdef]
    exact hxS1
  obtain ⟨k, hk⟩ := hxq.exists_card_eq
  obtain ⟨m, hm⟩ := hS2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card S) := by
    rw [hk, hm]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).mpr (by omega))
  have hUX : ⁅U, Subgroup.zpowers x⁆ = U := by
    apply le_antisymm
    · apply (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers x) (K := U)).mp
      rw [hUdef]
      exact Subgroup.normalizer_commutator_ge_right S (Subgroup.zpowers x)
    · rw [hUdef]
      exact CFSG.RankThree.PartTwo.Sec5.Bender.commutator_le_commutator_commutator S
        (Subgroup.zpowers x) hXS hcop
  obtain ⟨r, hr, hr3, u0, hu0U, p0, hp0P, hcomm⟩ :=
    e1c_exists_prime hθs hθ3 hO2 hUθ hU2 hU1
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = CFSG.inSubgroup (CFSG.pCore r) θ := ⟨_, rfl⟩
  have hP2 : IsPGroup r P := by
    rw [hPdef]
    exact (CFSG.pCore_isPGroup (p := r) (G := ↥θ)).map θ.subtype
  have hθN : θ ≤ Subgroup.normalizer (P : Set G) := by
    rw [hPdef]
    exact fun g hg => e1c_normalizer_le_inSubgroup r θ (Subgroup.le_normalizer hg)
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := by
    rw [hPdef]
    exact e1c_normalizer_le_inSubgroup r θ hxθ
  have hUN : U ≤ Subgroup.normalizer (P : Set G) := hUθ.trans hθN
  have hp0P' : p0 ∈ P := by
    rw [hPdef]
    exact hp0P
  have hU'' : IsPGroup 2 (U.subgroupOf (Subgroup.normalizer (P : Set G))) :=
    hU2.comap_of_injective (Subgroup.normalizer (P : Set G)).subtype
      (Subgroup.normalizer (P : Set G)).subtype_injective
  have hZ : (Subgroup.zpowers x).comap (Subgroup.normalizer (P : Set G)).subtype =
      Subgroup.zpowers (⟨x, hxN⟩ : Subgroup.normalizer (P : Set G)) := by
    ext n
    rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, Subtype.ext hj⟩
    · rintro ⟨j, hj⟩
      subst hj
      exact ⟨j, rfl⟩
  have hX'' : IsPGroup q (Subgroup.zpowers (⟨x, hxN⟩ : Subgroup.normalizer (P : Set G))) := by
    rw [← hZ]
    exact hxq.comap_of_injective (Subgroup.normalizer (P : Set G)).subtype
      (Subgroup.normalizer (P : Set G)).subtype_injective
  have hUX'' : ⁅U.subgroupOf (Subgroup.normalizer (P : Set G)),
      Subgroup.zpowers (⟨x, hxN⟩ : Subgroup.normalizer (P : Set G))⁆ =
      U.subgroupOf (Subgroup.normalizer (P : Set G)) := by
    apply Subgroup.map_injective (f := (Subgroup.normalizer (P : Set G)).subtype)
      (Subgroup.normalizer (P : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUN,
      MonoidHom.map_zpowers]
    exact hUX
  have hU1'' : ∃ u ∈ U.subgroupOf (Subgroup.normalizer (P : Set G)),
      P.normalizerMonoidHom u ≠ 1 := by
    refine ⟨⟨u0, hUN hu0U⟩, Subgroup.mem_subgroupOf.mpr hu0U, ?_⟩
    intro h
    apply hcomm
    have h3 : (u0 : G) * p0 * (u0 : G)⁻¹ = p0 :=
      congrArg (fun φ : MulAut P => ((φ ⟨p0, hp0P'⟩ : P) : G)) h
    exact mul_inv_eq_iff_eq_mul.mp h3
  have hfix : ∀ v ∈ U.subgroupOf (Subgroup.normalizer (P : Set G)),
      P.normalizerMonoidHom v ≠ 1 →
      CFSG.Assembly.pRank r (MonoidHom.eqLocus (P.normalizerMonoidHom v).toMonoidHom
        (MonoidHom.id ↥P)) ≤ 2 := by
    intro v hv hφv
    have hvU : (v : G) ∈ U := Subgroup.mem_subgroupOf.mp hv
    have hv1 : (v : G) ≠ 1 := by
      intro h1
      apply hφv
      have hv' : v = 1 := Subtype.ext h1
      rw [hv', map_one]
    have h2v : IsPGroup 2 (Subgroup.zpowers (v : G)) :=
      hU2.to_le (Subgroup.zpowers_le.mpr hvU)
    have hloc' := hloc r hr hr3 P hP2 (v : G) hv1 h2v
    rw [SectionRank.pRank_coe_eq_openPRank] at hloc'
    have hmapD : (MonoidHom.eqLocus (P.normalizerMonoidHom v).toMonoidHom
        (MonoidHom.id ↥P)).map P.subtype ≤ P ⊓ Subgroup.centralizer {(v : G)} := by
      rintro g hg
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
      have he' : (P.normalizerMonoidHom v).toMonoidHom e = (MonoidHom.id ↥P) e := he
      have h3 : (v : G) * (e : G) * (v : G)⁻¹ = (e : G) := congrArg Subtype.val he'
      refine Subgroup.mem_inf.mpr ⟨e.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    have hle1 := SectionRank.pRank_le_map hr.one_lt P.subtype P.subtype_injective
      (MonoidHom.eqLocus (P.normalizerMonoidHom v).toMonoidHom (MonoidHom.id ↥P))
    have hle2 := SectionRank.pRank_mono hr.one_lt hmapD
    exact (hle1.trans hle2).trans hloc'
  exact rank3II_3_6_pow_hom (p := r) (q := q) hr (by omega) hq hq3 (P := ↥P) hP2
    P.normalizerMonoidHom (U := U.subgroupOf (Subgroup.normalizer (P : Set G)))
    (X := Subgroup.zpowers (⟨x, hxN⟩ : Subgroup.normalizer (P : Set G)))
    (x := ⟨x, hxN⟩) hU'' rfl hX'' hUX'' hU1'' hfix

end CFSG.RankThree.PartTwo.Sec11
