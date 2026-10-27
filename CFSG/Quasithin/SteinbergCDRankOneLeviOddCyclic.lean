module

public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.GraphFixedIntrinsicPairs
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LieType.Chevalley.RootWeightFiltrationData
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise commutatorElement

theorem exists_injective_of_le_sup {G : Type*} [Group G] {Q R P : Subgroup G}
    (hRQ : R ≤ normalizer (Q : Set G)) (hQR : Q ⊓ R = ⊥) (hPQR : P ≤ Q ⊔ R)
    (hPQ : P ⊓ Q = ⊥) : ∃ κ : P →* R, Function.Injective κ := by
  set M := Q ⊔ R with hM
  have hQM : Q ≤ M := le_sup_left
  have hRM : R ≤ M := le_sup_right
  have hMn : M ≤ normalizer (Q : Set G) := sup_le le_normalizer hRQ
  have : (Q.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hQM).2 hMn
  set f := QuotientGroup.mk' (Q.subgroupOf M) with hf
  have hker : ∀ m : M, f m = 1 ↔ (m : G) ∈ Q := fun m => by
    rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  set θ : R →* M ⧸ Q.subgroupOf M := f.comp (inclusion hRM) with hθ
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hrQ : (r : G) ∈ Q ⊓ R := ⟨(hker _).1 hr, r.2⟩
    rw [hQR, mem_bot] at hrQ
    exact Subtype.ext hrQ
  have hθsurj : Function.Surjective θ := by
    intro m
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) m
    have hm : (m : G) ∈ ((R ⊔ Q : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact m.2
    rw [coe_mul_of_left_le_normalizer_right R Q hRQ] at hm
    obtain ⟨r, hr, q, hq, hrq⟩ := hm
    have hrq' : r * q = m := hrq
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [hθ, MonoidHom.comp_apply, ← inv_mul_eq_one, ← map_inv, ← map_mul, hker]
    have e : (((inclusion hRM ⟨r, hr⟩)⁻¹ * m : M) : G) = q := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_inclusion, ← hrq']
      group
    rw [e]
    exact hq
  set e := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  set ι : P →* M ⧸ Q.subgroupOf M := f.comp (inclusion hPQR)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hpQ : (p : G) ∈ P ⊓ Q := ⟨p.2, (hker _).1 hp⟩
    rw [hPQ, mem_bot] at hpQ
    exact Subtype.ext hpQ
  exact ⟨e.symm.toMonoidHom.comp ι, e.symm.injective.comp hιinj⟩

theorem commutatorElement_mem_of_mem_sup {G : Type*} [Group G] {N T : Subgroup G}
    (hTN : T ≤ normalizer (N : Set G)) (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {x y : G}
    (hx : x ∈ N ⊔ T) (hy : y ∈ N ⊔ T) : ⁅x, y⁆ ∈ N := by
  have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hx
  have hy' : y ∈ ((N ⊔ T : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left N T hTN] at hx' hy'
  obtain ⟨n₁, hn₁, t₁, ht₁, rfl⟩ := hx'
  obtain ⟨n₂, hn₂, t₂, ht₂, rfl⟩ := hy'
  have hc : t₂ * t₁⁻¹ = t₁⁻¹ * t₂ := by
    have h := hT t₁ ht₁ t₂ ht₂
    calc t₂ * t₁⁻¹ = t₁⁻¹ * (t₁ * t₂) * t₁⁻¹ := by group
      _ = t₁⁻¹ * (t₂ * t₁) * t₁⁻¹ := by rw [h]
      _ = t₁⁻¹ * t₂ := by group
  have e : ⁅n₁ * t₁, n₂ * t₂⁆ =
      n₁ * (t₁ * n₂ * t₁⁻¹) * (t₂ * n₁⁻¹ * t₂⁻¹) * n₂⁻¹ := by
    rw [commutatorElement_def]
    calc n₁ * t₁ * (n₂ * t₂) * (n₁ * t₁)⁻¹ * (n₂ * t₂)⁻¹ =
          n₁ * t₁ * n₂ * (t₂ * t₁⁻¹) * n₁⁻¹ * t₂⁻¹ * n₂⁻¹ := by group
      _ = n₁ * t₁ * n₂ * (t₁⁻¹ * t₂) * n₁⁻¹ * t₂⁻¹ * n₂⁻¹ := by rw [hc]
      _ = n₁ * (t₁ * n₂ * t₁⁻¹) * (t₂ * n₁⁻¹ * t₂⁻¹) * n₂⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hn₁ ((mem_normalizer_iff.1 (hTN ht₁) n₂).1 hn₂))
    ((mem_normalizer_iff.1 (hTN ht₂) _).1 (inv_mem hn₁))) (inv_mem hn₂)

theorem isCyclic_of_le_perfect_of_le_sup {G : Type*} [Group G] {X Q R T : Subgroup G}
    (hX : X ≤ Q ⊔ R ⊔ T) (hRX : R ≤ X) (hTX : T ≤ X) (hXQ : X ≤ normalizer (Q : Set G))
    (hTR : T ≤ normalizer (R : Set G)) (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hQ : IsPGroup 2 Q) (hQR : Q ⊓ R = ⊥) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hRcyc : ∀ P' : Subgroup G, P' ≤ R → IsPGroup r P' → IsCyclic P')
    {A : Subgroup G} (hAX : A ≤ X) (hA : Group.IsPerfect A) {P : Subgroup G} (hPA : P ≤ A)
    (hP : IsPGroup r P) : IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ normalizer ((Q ⊔ R : Subgroup G) : Set G) := fun t ht =>
    inf_normalizer_le_normalizer_sup Q R ⟨hXQ (hTX ht), hTR ht⟩
  have hAN : A ≤ Q ⊔ R := by
    rw [← isPerfect_iff.1 hA, commutator_le]
    intro a ha b hb
    exact commutatorElement_mem_of_mem_sup hTN hT (hX (hAX ha)) (hX (hAX hb))
  have hPQ : P ⊓ Q = ⊥ := (IsPGroup.disjoint_of_ne r 2 hr2 P Q hP hQ).eq_bot
  obtain ⟨κ, hκ⟩ := exists_injective_of_le_sup (fun x hx => hXQ (hRX hx)) hQR (hPA.trans hAN)
    hPQ
  have hrange : IsPGroup r κ.range := hP.of_surjective κ.rangeRestrict κ.rangeRestrict_surjective
  have hP' : IsCyclic (κ.range.map R.subtype) := hRcyc _ (by
    rintro _ ⟨x, -, rfl⟩
    exact x.2) (hrange.map R.subtype)
  have e : P ≃* κ.range.map R.subtype :=
    (MonoidHom.ofInjective hκ).trans (κ.range.equivMapOfInjective R.subtype R.subtype_injective)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem isCyclic_of_le_range_of_ker_scalar {F : Type*} [Field F] [Finite F] [CharP F 2]
    {G : Type*} [Group G] (φ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (hφ : ∀ g ∈ φ.ker, ∃ l : F, (g : Matrix (Fin 2) (Fin 2) F) = l • 1) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {P' : Subgroup G} (hP'R : P' ≤ φ.range) (hP' : IsPGroup r P') :
    IsCyclic P' := by
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl⟩ := hφ g hg
    exact CFSG.LinearAlgebra.SteinbergBQ.eq_one_of_scalar_charTwo (by simp [hl]) (by simp [hl])
      (by simp [hl])
  have hS := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hr2 (P'.comap φ)
    (hP'.comap_of_injective φ hinj)
  have e : P'.comap φ ≃* (P'.comap φ).map φ := (P'.comap φ).equivMapOfInjective φ hinj
  rw [map_comap_eq_self hP'R] at e
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem isCyclic_of_le_bot {G : Type*} [Group G] {P' : Subgroup G} (h : P' ≤ ⊥) : IsCyclic P' := by
  rw [le_bot_iff] at h
  subst h
  infer_instance

variable {K : Type} [Field K]

theorem ordinary_isCyclic_of_levi
    {τ : Tag} [Finite K] [CharP K 2] {J : Set (Fin τ.rank)}
    {R : Subgroup (ModGL τ K)}
    (hRJ : Subgroup.closure {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} = R)
    (hTR : torusGroup τ K ≤ normalizer (R : Set (ModGL τ K))) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hRcyc : ∀ P' : Subgroup (ModGL τ K), P' ≤ R → IsPGroup r P' → IsCyclic P')
    {A : Subgroup (ModGL τ K)} (hAJ : A ≤ parabolicSubgroup τ K J) (hA : Group.IsPerfect A)
    {P : Subgroup (ModGL τ K)} (hPA : P ≤ A) (hP : IsPGroup r P) : IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQP, hQn, -, hMP, hQM, hQMP, -, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors τ K J
  have hM : parabolicLevi τ K J = torusGroup τ K ⊔ R := by
    rw [← hRJ]
    rfl
  have hRM : R ≤ parabolicLevi τ K J := hM ▸ le_sup_right
  have hTM : torusGroup τ K ≤ parabolicLevi τ K J := hM ▸ le_sup_left
  refine isCyclic_of_le_perfect_of_le_sup (Q := parabolicRadical τ K J) (R := R)
    (T := torusGroup τ K) ?_ (hRM.trans hMP) (hTM.trans hMP)
    ((normal_subgroupOf_iff_le_normalizer hQP).1 hQn) hTR
    (triangular_borel_structure.{0, 0} τ K).1 (hfin 2).2.1 ?_ hr2 hRcyc hAJ hA hPA hP
  · rw [← hQMP, hM]
    exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le le_sup_right (le_sup_right.trans le_sup_left))
  · refine eq_bot_iff.2 fun g hg => ?_
    rw [← hQM]
    exact ⟨hg.1, hRM hg.2⟩

theorem ordinary_empty_isCyclic
    {τ : Tag} [Finite K] [CharP K 2] {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {A : Subgroup (ModGL τ K)} (hAJ : A ≤ parabolicSubgroup τ K ∅)
    (hA : Group.IsPerfect A) {P : Subgroup (ModGL τ K)} (hPA : P ≤ A) (hP : IsPGroup r P) :
    IsCyclic P := by
  refine ordinary_isCyclic_of_levi (R := ⊥) ?_ (le_normalizer_of_normal) hr2
    (fun P' h _ => isCyclic_of_le_bot h) hAJ hA hPA hP
  rw [eq_bot_iff, closure_le]
  rintro _ ⟨j, hj, -⟩
  exact absurd hj (Set.notMem_empty j)

theorem closure_xUnit_yUnit_eq
    {τ : Tag} (i : Fin τ.rank) :
    Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) =
      rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := by
  rw [Subgroup.closure_union, rootSubgroup, rootSubgroup]
  congr 2
  · ext g
    simp [pinnedX_single]
  · ext g
    simp [pinnedX_neg_single]

theorem ordinary_singleton_isCyclic
    {τ : Tag} [Finite K] [CharP K 2] (i : Fin τ.rank) {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {A : Subgroup (ModGL τ K)}
    (hAJ : A ≤ parabolicSubgroup τ K {i}) (hA : Group.IsPerfect A) {P : Subgroup (ModGL τ K)}
    (hPA : P ≤ A) (hP : IsPGroup r P) : IsCyclic P := by
  obtain ⟨ρ, -, -, -, -, hrange, hker, -, -⟩ := exceptional_ordinary_rank_one_central_image τ K i
  have hset : {g | ∃ j ∈ ({i} : Set (Fin τ.rank)), ∃ c : K,
      g = xUnit τ K j c ∨ g = yUnit τ K j c} =
        Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i) := by
    ext g
    simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq, Set.mem_union,
      Set.mem_range]
    constructor
    · rintro ⟨c, rfl | rfl⟩
      · exact Or.inl ⟨c, rfl⟩
      · exact Or.inr ⟨c, rfl⟩
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨c, Or.inl rfl⟩
      · exact ⟨c, Or.inr rfl⟩
  refine ordinary_isCyclic_of_levi (R := ρ.range) (by rw [hset, hrange]) ?_ hr2
    (fun P' h hP' => isCyclic_of_le_range_of_ker_scalar ρ
      (fun g hg => by obtain ⟨l, -, hl⟩ := hker g hg; exact ⟨l, hl⟩) hr2 h hP') hAJ hA hPA hP
  rw [hrange, closure_xUnit_yUnit_eq]
  exact fun h hh => inf_normalizer_le_normalizer_sup _ _
    ⟨torusGroup_le_normalizer_rootSubgroup (isRoot_single τ i) hh,
      torusGroup_le_normalizer_rootSubgroup (isRoot_neg_single τ i) hh⟩

theorem mem_simpleOrbitRoots_of_mem_parabolicPosRoots
    {t : TwistTag} {a : Fin t.foldedTag.rank}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ parabolicPosRoots t.tag (t.orbitUnion {a})) :
    α ∈ simpleOrbitRoots t a := by
  obtain ⟨⟨hr, hz⟩, -, hp⟩ := hα
  have key : ∀ k < t.tag.rootCertificate.roots.length, ∀ c : Fin t.foldedTag.rank,
      0 < height (t.tag.rootCertificate.root k) ∧
        (∀ i, t.orbitIndex i ≠ c → t.tag.rootCertificate.root k i = 0) →
      ∃ j ∈ t.orbit c, t.tag.rootCertificate.root k = Pi.single j 1 := by
    cases t <;> decide +kernel
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hr
  obtain ⟨j, hj, he⟩ := key k hk a ⟨hp, fun i hi => hz i fun h =>
    hi ((mem_orbitUnion_iff_orbitIndex).1 h)⟩
  exact ⟨j, hj, he.symm⟩

theorem parabolicPosRoots_orbitUnion_empty (t : TwistTag) :
    parabolicPosRoots t.tag (t.orbitUnion ∅) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun α hα => ?_
  obtain ⟨⟨-, hz⟩, -, hp⟩ := hα
  have h0 : ∀ i, α i = 0 := fun i => hz i fun h => by
    rw [mem_orbitUnion_iff_orbitIndex] at h
    exact h
  simp [height, h0] at hp

variable {t : TwistTag}

theorem fixed_isCyclic_of_levi
    [Finite K] [CharP K 2] {σ : K ≃+* K}
    {J : Set (Fin t.foldedTag.rank)} {R : Subgroup (ModGL t.tag K)}
    (hV : graphFixedParabolicLeviUnipotent t K σ.toRingHom J ≤ R)
    (hn : ∀ b ∈ J, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) ∈ R)
    (hRX : R ≤ graphFixedParabolic t K σ.toRingHom J)
    (hRM : R ≤ parabolicLevi t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom)
    (hTR : graphFixedRootTorus t K σ.toRingHom ≤ normalizer (R : Set (ModGL t.tag K)))
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hRcyc : ∀ P' : Subgroup (ModGL t.tag K), P' ≤ R → IsPGroup r P' → IsCyclic P')
    {A : Subgroup (ModGL t.tag K)} (hAJ : A ≤ graphFixedParabolic t K σ.toRingHom J)
    (hA : Group.IsPerfect A) {P : Subgroup (ModGL t.tag K)} (hPA : P ≤ A)
    (hP : IsPGroup r P) : IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, hQM, -, hQX, hQn, -, -, hB, -, -, -, hfin, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  refine isCyclic_of_le_perfect_of_le_sup (Q := graphFixedParabolicRadical t K σ.toRingHom J)
    (R := R) (T := graphFixedRootTorus t K σ.toRingHom) ?_ hRX
    (graphFixedRootTorus_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic t K _ J))
    ((normal_subgroupOf_iff_le_normalizer hQX).1 hQn) hTR
    (fun x hx y hy => (triangular_borel_structure.{0, 0} t.tag K).1 x hx.1.1 y hy.1.1)
    (hfin 2) ?_ hr2 hRcyc hAJ hA hPA hP
  · refine sup_le (fun b hb => ?_) ((closure_le _).2 ?_)
    · have hb' : b ∈ (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) := hb
      rw [hB] at hb'
      obtain ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩ := hb'
      exact mul_mem (mem_sup_left (mem_sup_left hq))
        (mul_mem (mem_sup_right hh) (mem_sup_left (mem_sup_right (hV hv))))
    · rintro _ ⟨b, hb, rfl⟩
      exact mem_sup_left (mem_sup_right (hn b hb))
  · refine eq_bot_iff.2 fun g hg => ?_
    rw [← hQM]
    exact ⟨hg.1, hRM hg.2⟩

theorem fixed_empty_isCyclic
    [Finite K] [CharP K 2] (σ : K ≃+* K) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {A : Subgroup (ModGL t.tag K)} (hAJ : A ≤ graphFixedParabolic t K σ.toRingHom ∅)
    (hA : Group.IsPerfect A) {P : Subgroup (ModGL t.tag K)} (hPA : P ≤ A) (hP : IsPGroup r P) :
    IsCyclic P := by
  refine fixed_isCyclic_of_levi (R := ⊥) ?_ (fun b hb => absurd hb (Set.notMem_empty b)) bot_le
    bot_le le_normalizer_of_normal hr2 (fun P' h _ => isCyclic_of_le_bot h) hAJ hA hPA hP
  intro v hv
  have hv' := (mem_inf.1 hv).1
  rw [parabolicLeviUnipotent, parabolicPosRoots_orbitUnion_empty] at hv'
  have hbot : rootSpan t.tag K (∅ : Set (Fin t.tag.rank → ℤ)) = ⊥ :=
    eq_bot_iff.2 (iSup₂_le fun α hα => absurd hα (Set.notMem_empty α))
  rwa [hbot] at hv'

theorem orbitRankOneHom_range_eq
    (σ : K →+* K) (a : Fin t.foldedTag.rank) :
    (orbitRankOneHom t K σ a).range =
      rootSpan t.tag K (simpleOrbitRoots t a) ⊓ twistedFixedGroup t K σ ⊔
        rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
          twistedFixedGroup t K σ := by
  rw [orbitRankOneHom_range, Subgroup.closure_union, closure_range_orbitX, ← orbitYSubgroup_eq]
  rfl

theorem fixed_singleton_isCyclic
    [Finite K] [CharP K 2] (σ : K ≃+* K) (a : Fin t.foldedTag.rank)
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {A : Subgroup (ModGL t.tag K)}
    (hAJ : A ≤ graphFixedParabolic t K σ.toRingHom {a}) (hA : Group.IsPerfect A)
    {P : Subgroup (ModGL t.tag K)} (hPA : P ≤ A) (hP : IsPGroup r P) : IsCyclic P := by
  set Γ := twistedFixedGroup t K σ.toRingHom
  set E := simpleOrbitRoots t a with hE
  set E' := (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a) with hE'
  have hEroot : ∀ α ∈ E, IsRoot t.tag α := by
    rintro _ ⟨i, -, rfl⟩
    exact isRoot_single _ i
  have hE'root : ∀ α ∈ E', IsRoot t.tag α := by
    rintro _ ⟨i, -, rfl⟩
    exact isRoot_neg_single _ i
  have hX : ∀ c, (orbitX t K σ.toRingHom a c : ModGL t.tag K) ∈ rootSpan t.tag K E ⊓ Γ :=
    orbitX_mem t σ.toRingHom a
  have hY : ∀ c, (orbitY t K σ.toRingHom a c : ModGL t.tag K) ∈ rootSpan t.tag K E' ⊓ Γ :=
    fun c => (mem_rootSpan_negSimpleOrbitRoots_iff a).2 ⟨c, rfl⟩
  have hrange := orbitRankOneHom_range_eq σ.toRingHom a
  have hA_a : ∀ i ∈ t.orbit a, i ∈ t.orbitUnion {a} := fun i hi =>
    (mem_orbitUnion_iff_orbitIndex).2 ((t.mem_orbit_iff).1 hi)
  have hEM : rootSpan t.tag K E ≤ parabolicLevi t.tag K (t.orbitUnion {a}) := by
    refine iSup₂_le fun α hα => ?_
    obtain ⟨i, hi, rfl⟩ := hα
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, pinnedX_single]
    exact mem_sup_right (subset_closure ⟨i, hA_a i hi, c, Or.inl rfl⟩)
  have hE'M : rootSpan t.tag K E' ≤ parabolicLevi t.tag K (t.orbitUnion {a}) := by
    refine iSup₂_le fun α hα => ?_
    obtain ⟨i, hi, rfl⟩ := hα
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, pinnedX_neg_single]
    exact mem_sup_right (subset_closure ⟨i, hA_a i hi, c, Or.inr rfl⟩)
  refine fixed_isCyclic_of_levi (R := (orbitRankOneHom t K σ.toRingHom a).range) ?_ ?_ ?_ ?_ ?_
    hr2 (fun P' h hP' => isCyclic_of_le_range_of_ker_scalar _ (fun g hg => by
      obtain ⟨l, -, hl⟩ := eq_smul_one_of_mem_ker_orbitRankOneHom hg
      exact ⟨l, hl⟩) hr2 h hP') hAJ hA hPA hP
  · intro v hv
    obtain ⟨hvS, hvΓ⟩ := mem_inf.1 hv
    rw [hrange]
    exact mem_sup_left ⟨rootSpan_mono (fun α hα => mem_simpleOrbitRoots_of_mem_parabolicPosRoots
      hα) hvS, hvΓ⟩
  · rintro b rfl
    rw [hrange, canonicalRep_orbitReflection_eq_orbitN t σ.toRingHom b, orbitN, coe_mul, coe_mul]
    exact mul_mem (mul_mem (mem_sup_left (hX _)) (mem_sup_right (hY _))) (mem_sup_left (hX _))
  · rw [hrange]
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨c, rfl⟩ := (mem_rootSpan_simpleOrbitRoots_iff σ.toRingHom a).1 hg
      exact graphFixedRootBorel_le_graphFixedParabolic t K _ _
        (graphFixedPosUnipotent_le_graphFixedRootBorel
          (orbitX_mem_graphFixedPosUnipotent t σ.toRingHom a c))
    · obtain ⟨c, rfl⟩ := (mem_rootSpan_negSimpleOrbitRoots_iff a).1 hg
      exact orbitY_mem_graphFixedParabolic a c
  · rw [hrange]
    exact sup_le (inf_le_inf_right _ hEM) (inf_le_inf_right _ hE'M)
  · intro h hh
    obtain ⟨⟨hhH, hhΓ⟩, -⟩ := mem_inf.1 hh
    rw [hrange]
    exact inf_normalizer_le_normalizer_sup _ _
      ⟨inf_normalizer_le_normalizer_inf ⟨torusGroup_le_normalizer_rootSpan hEroot hhH,
          le_normalizer hhΓ⟩,
        inf_normalizer_le_normalizer_inf ⟨torusGroup_le_normalizer_rootSpan hE'root hhH,
          le_normalizer hhΓ⟩⟩

theorem char_two_rank_one_levi_parabolic_perfect_odd_cyclic
    {K : Type} [Field K] [Finite K]
    [CharP K 2] (D : RootWeightDatum K) {J : Set (Fin D.rank)} (hJ : J.encard ≤ 1)
    {A : Subgroup (ModGL D.tag K)} (hAJ : A ≤ D.parabolic J) (hA : Group.IsPerfect A) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {P : Subgroup (ModGL D.tag K)} (hPA : P ≤ A)
    (hP : IsPGroup r P) : IsCyclic P := by
  have : Fact r.Prime := ⟨hr⟩
  cases D with
  | ordinary τ =>
    rcases Set.encard_le_one_iff_eq.1 hJ with rfl | ⟨i, rfl⟩
    · exact ordinary_empty_isCyclic hr2 hAJ hA hPA hP
    · exact ordinary_singleton_isCyclic i hr2 hAJ hA hPA hP
  | fixed t σ hσ =>
    rcases Set.encard_le_one_iff_eq.1 hJ with rfl | ⟨a, rfl⟩
    · exact fixed_empty_isCyclic σ hr2 hAJ hA hPA hP
    · exact fixed_singleton_isCyclic σ a hr2 hAJ hA hPA hP

end CFSG.Quasithin.SteinbergCD
