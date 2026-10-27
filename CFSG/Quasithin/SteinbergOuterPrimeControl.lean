module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived

public noncomputable section

namespace CFSG.Quasithin.OuterPrimeControl

open Matrix CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem isCyclic_of_isPGroup_of_ker_coprime {G H : Type*} [Group G] [Group H] [Finite G]
    [IsCyclic H] (f : G →* H) {ℓ : ℕ} [Fact ℓ.Prime] (hker : Nat.Coprime (Nat.card f.ker) ℓ)
    {V : Subgroup G} (hV : IsPGroup ℓ V) : IsCyclic V := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hV
  have hdisj : Disjoint V f.ker := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hm]
    exact (Nat.Coprime.pow_right m hker).symm
  refine isCyclic_of_injective (f.comp V.subtype) ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 := Subgroup.disjoint_def.1 hdisj x.2 hx
  exact Subtype.ext h1

theorem isCyclic_of_isPGroup_of_cyclic_section {G : Type*} [Group G] [Finite G] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) {N M : Subgroup G} (hNM : N ≤ M) (hMn : M.Normal)
    (hMi : M.index ≤ 2) [(N.subgroupOf M).Normal] (hcyc : IsCyclic (M ⧸ N.subgroupOf M))
    (hN : Nat.Coprime (Nat.card N) ℓ) {V : Subgroup G} (hV : IsPGroup ℓ V) : IsCyclic V := by
  have hVM : V ≤ M := by
    intro v hv
    obtain ⟨a, ha⟩ := hV ⟨v, hv⟩
    have hva : v ^ ℓ ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hodd : Odd (ℓ ^ a) := (Nat.Prime.eq_two_or_odd' (Fact.out)).resolve_left hℓ |>.pow
    obtain ⟨b, hb⟩ := hodd
    have hv2 : v ^ 2 ∈ M := by
      have hidx := Subgroup.pow_index_mem M v
      rcases (by have := M.index_ne_zero_of_finite; omega : M.index = 1 ∨ M.index = 2) with h | h
      · rw [Subgroup.index_eq_one.1 h]
        exact Subgroup.mem_top _
      · rwa [h] at hidx
    have h1 : v * (v ^ 2) ^ b = 1 := by
      rw [← pow_mul, ← pow_succ', show 2 * b + 1 = ℓ ^ a from hb.symm, hva]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact M.inv_mem (M.pow_mem hv2 b)
  have hVp : IsPGroup ℓ (V.subgroupOf M) :=
    hV.of_equiv (Subgroup.subgroupOfEquivOfLe hVM).symm
  have hker : Nat.Coprime (Nat.card (QuotientGroup.mk' (N.subgroupOf M)).ker) ℓ := by
    rw [QuotientGroup.ker_mk', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
    exact hN
  have := isCyclic_of_isPGroup_of_ker_coprime (QuotientGroup.mk' (N.subgroupOf M)) hker hVp
  exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hVM).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hVM).symm.injective

theorem pRank_le_one_of_forall_isCyclic {G : Type*} [Group G] [Finite G] {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (h : ∀ V : Subgroup G, IsPGroup ℓ V → IsCyclic V) :
    CFSG.pRank ℓ G ≤ 1 := by
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have hcyc := h A (CFSG.IsElementaryAbelian.isPGroup ℓ A)
  have hexp : Monoid.exponent A = Nat.card A := IsCyclic.exponent_eq_card
  have hdvd : ℓ ^ r ∣ ℓ ^ 1 := by
    rw [← hcard, ← hexp, pow_one]
    exact CFSG.IsElementaryAbelian.exponent_dvd_p ℓ A
  exact (Nat.pow_dvd_pow_iff_le_right hℓ.out.one_lt).1 hdvd

theorem isCyclic_of_isPGroup_of_injective {G H : Type*} [Group G] [Group H] (ι : G →* H)
    (hι : Function.Injective ι) {ℓ : ℕ}
    (h : ∀ V : Subgroup H, IsPGroup ℓ V → IsCyclic V) {V : Subgroup G} (hV : IsPGroup ℓ V) :
    IsCyclic V := by
  have := h (V.map ι) (hV.map ι)
  exact isCyclic_of_injective (V.equivMapOfInjective ι hι).toMonoidHom
    (V.equivMapOfInjective ι hι).injective

theorem outer_projectiveSL_isCyclic_of_isPGroup {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (hℓd : ¬ ℓ ∣ Nat.gcd n (Nat.card K - 1))
    {V : Subgroup (Outer (projectiveSL n K))} (hV : IsPGroup ℓ V) : IsCyclic V := by
  classical
  set π := QuotientGroup.mk' (inner (projectiveSL n K)) with hπ
  obtain ⟨hR, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDR, hER, -, ⟨g, hgE, hg⟩, -, hEidx, -⟩ :=
    standard_outer_quotients (K := K) (n := n)
  have hnormal : ∀ X : Subgroup (MulAut (projectiveSL n K)),
      (X.subgroupOf (standardAutGroup n K)).Normal → X.Normal := by
    intro X hX
    constructor
    intro x hx y
    have := hX.conj_mem ⟨x, by rw [hR]; trivial⟩ (Subgroup.mem_subgroupOf.2 hx)
      ⟨y, by rw [hR]; trivial⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hDn := hnormal _ hDR
  have hEn := hnormal _ hER
  set N := (linearAutGroup n K).map π with hN
  set M := (semilinearAutGroup n K).map π with hM
  have hNM : N ≤ M := Subgroup.map_mono linearAutGroup_le_semilinearAutGroup
  have hMn : M.Normal := hEn.map π (QuotientGroup.mk'_surjective _)
  have hNn : N.Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ semilinearAutGroup n K := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hID.trans linearAutGroup_le_semilinearAutGroup
  have hMi : M.index ≤ 2 := by
    rw [hM, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker,
      ← Subgroup.relIndex_top_right, ← hR]
    exact hEidx
  have hcyc : IsCyclic (M ⧸ N.subgroupOf M) := by
    refine ⟨⟨QuotientGroup.mk ⟨π g, Subgroup.mem_map_of_mem π hgE⟩, fun x => ?_⟩⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := hg e he
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk ⟨π g, _⟩ : M ⧸ N.subgroupOf M) ^ (-k) = QuotientGroup.mk ⟨π e, hy⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (((⟨π g, Subgroup.mem_map_of_mem π hgE⟩ : M) ^ (-k))⁻¹ * ⟨π e, hy⟩ : M) =
        ⟨π (g ^ k * e), hNM (Subgroup.mem_map_of_mem π hk)⟩ := by
      ext
      simp [map_mul, map_zpow, _root_.zpow_neg]
    rw [h1]
    exact Subgroup.mem_map_of_mem π hk
  have hNcard : Nat.card N ∣ Nat.gcd n (Nat.card K - 1) := by
    have hD : linearAutGroup n K = (conjAut n K).range := by
      rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    have hNeq : N = (π.comp (conjAut n K)).range := by
      rw [hN, hD, MonoidHom.range_comp]
    rw [hNeq]
    exact (linear_diagonal_outer (K := K) (n := n) (by omega)).2
  have hNc : Nat.Coprime (Nat.card N) ℓ :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => hℓd (h.trans hNcard)).symm
  exact isCyclic_of_isPGroup_of_cyclic_section hℓ hNM hMn hMi hcyc hNc hV

theorem card_ker_quotientFieldProjection_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (quotientFieldProjection K).ker ∣ Nat.gcd 2 (Nat.card K - 1) := by
  rw [quotientFieldProjection_ker, ← Subgroup.index_ker]
  have hle : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ≤
      (diagonalHom K).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (pGammaL2PSLRange K)
      (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨y, rfl⟩
  refine (Subgroup.index_dvd_of_le hle).trans ?_
  rw [Subgroup.index_eq_card]
  exact card_pgl_quotient_psl_dvd K

@[expose] def semilinearOuterEquiv (K : Type) [Field K] [Finite K] :
    SemilinearQuotient K ≃* Outer (PSL2 K) :=
  (semilinearQuotientEquivCoordinateEG K).trans
    ((coordinateOuterQuotientEquiv K).trans (coordinateOuterEquivPSL K))

theorem outer_psl2_isCyclic_of_isPGroup (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ 2) {V : Subgroup (Outer (PSL2 K))} (hV : IsPGroup ℓ V) : IsCyclic V := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite (SemilinearQuotient K) := Finite.of_equiv _ (semilinearOuterEquiv K).symm.toEquiv
  have hker : Nat.Coprime (Nat.card (quotientFieldProjection K).ker) ℓ := by
    refine ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => hℓ ?_).symm
    have h2 := h.trans ((card_ker_quotientFieldProjection_dvd K).trans (Nat.gcd_dvd_left _ _))
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2
  refine isCyclic_of_isPGroup_of_injective (semilinearOuterEquiv K).symm.toMonoidHom
    (semilinearOuterEquiv K).symm.injective ?_ hV
  intro W hW
  exact isCyclic_of_isPGroup_of_ker_coprime (quotientFieldProjection K) hker hW

theorem ringEquiv_eq_refl_of_card_prime {K : Type} [Field K] [Finite K]
    (hK : (Nat.card K).Prime) (σ : K ≃+* K) : σ = RingEquiv.refl K := by
  have : Fact (Nat.card K).Prime := ⟨hK⟩
  have hchar : CharP K (Nat.card K) :=
    finite_field_prime_power_characteristic hK (k := 1) le_rfl (by rw [pow_one])
  have := Fintype.ofFinite K
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl (Nat.card K)) K) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨(ZMod.castHom _ K).injective, ?_⟩
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
  ext x
  obtain ⟨m, rfl⟩ := hbij.2 x
  rw [RingEquiv.refl_apply, ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]

theorem outer_psl2_isCyclic (K : Type) [Field K] [Finite K]
    (hq : Even (Nat.card K) ∨ (Nat.card K).Prime) : IsCyclic (Outer (PSL2 K)) := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite (SemilinearQuotient K) := Finite.of_equiv _ (semilinearOuterEquiv K).symm.toEquiv
  suffices IsCyclic (SemilinearQuotient K) from
    isCyclic_of_surjective (semilinearOuterEquiv K).toMonoidHom (semilinearOuterEquiv K).surjective
  rcases hq with hq | hq
  ·
    have h1 : Nat.card (quotientFieldProjection K).ker = 1 := by
      have hd := card_ker_quotientFieldProjection_dvd K
      have hg : Nat.gcd 2 (Nat.card K - 1) = 1 := by
        have hq1 : 1 ≤ Nat.card K := Nat.card_pos
        obtain ⟨r, hr⟩ := hq
        have : Nat.card K - 1 = 2 * (r - 1) + 1 := by omega
        rw [this, Nat.gcd_comm, Nat.gcd_mul_left_add_left, Nat.gcd_one_left]
      rw [hg] at hd
      exact Nat.dvd_one.1 hd
    have hinj : Function.Injective (quotientFieldProjection K) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
      exact h1
    exact isCyclic_of_injective _ hinj
  ·
    have htop : (quotientFieldProjection K).ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [MonoidHom.mem_ker, ringEquiv_eq_refl_of_card_prime hq (quotientFieldProjection K x)]
      rfl
    have hd := card_ker_quotientFieldProjection_dvd K
    rw [htop, Subgroup.card_top] at hd
    have h2 : Nat.card (SemilinearQuotient K) ∣ 2 := hd.trans (Nat.gcd_dvd_left _ _)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · have : Subsingleton (SemilinearQuotient K) := (Nat.card_eq_one_iff_unique.1 h).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card h

theorem perfect_projective_linear_central_quotient_outer_prime_control (J : Type*) [Group J]
    [Finite J] [Group.IsPerfect J] (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (e : J ⧸ Subgroup.center J ≃* projectiveSL n K) :
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ Nat.gcd n (Nat.card K - 1) →
      (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1) ∧
    ((n = 2 ∨ n = 3) → ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
      (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1) ∧
    (n = 2 → (Even (Nat.card K) ∨ (Nat.card K).Prime) → IsCyclic (Outer J)) := by
  have hmain : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ Nat.gcd n (Nat.card K - 1) →
      ∀ V : Subgroup (Outer J), IsPGroup ℓ V → IsCyclic V := by
    intro ℓ hℓ hℓ2 hℓd V hV
    have : Fact ℓ.Prime := ⟨hℓ⟩
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · set e₂ : J ⧸ Subgroup.center J ≃* PSL2 K :=
        e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm
      exact isCyclic_of_isPGroup_of_injective _ (outer_comp_injective J e₂)
        (fun W hW => outer_psl2_isCyclic_of_isPGroup K hℓ2 hW) hV
    · exact isCyclic_of_isPGroup_of_injective _ (outer_comp_injective J e)
        (fun W hW => outer_projectiveSL_isCyclic_of_isPGroup hn3 hℓ2 hℓd hW) hV
  have hpart : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ Nat.gcd n (Nat.card K - 1) →
      (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1 := by
    intro ℓ hℓ hℓ2 hℓd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact ⟨fun P => hmain ℓ hℓ hℓ2 hℓd P P.isPGroup',
      pRank_le_one_of_forall_isCyclic (hmain ℓ hℓ hℓ2 hℓd)⟩
  refine ⟨hpart, fun hn23 ℓ hℓ hℓ5 => hpart ℓ hℓ (by omega) fun hdvd => ?_, fun hn2 hq => ?_⟩
  · have h1 : ℓ ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
    have h2 := Nat.le_of_dvd (by omega) h1
    omega
  · subst hn2
    set e₂ : J ⧸ Subgroup.center J ≃* PSL2 K :=
      e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm
    have := outer_psl2_isCyclic K hq
    exact isCyclic_of_injective _ (outer_comp_injective J e₂)

end CFSG.Quasithin.OuterPrimeControl
