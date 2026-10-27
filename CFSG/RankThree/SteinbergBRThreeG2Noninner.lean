module

public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTThreeG2Subfield
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public noncomputable section

namespace CFSG.RankThree.SteinbergBR.ThreeG2

open CFSG.LieType.Chevalley

theorem conj_inner_eq_of_conj_mul {C : Type*} [Group C] (g : C) (ψ β T : MulAut C)
    (hψT : ψ * T = T * ψ) (h : MulAut.conj g * ψ * β * (MulAut.conj g * ψ)⁻¹ = T) :
    MulAut.conj (ψ⁻¹ g) * β * (MulAut.conj (ψ⁻¹ g))⁻¹ = T := by
  have hc : MulAut.conj (ψ⁻¹ g) = ψ⁻¹ * MulAut.conj g * ψ := by
    rw [← mulAut_mul_conj_mul_inv, inv_inv]
  rw [hc]
  calc ψ⁻¹ * MulAut.conj g * ψ * β * (ψ⁻¹ * MulAut.conj g * ψ)⁻¹
      = ψ⁻¹ * (MulAut.conj g * ψ * β * (MulAut.conj g * ψ)⁻¹) * ψ := by group
    _ = ψ⁻¹ * T * ψ := by rw [h]
    _ = T := by rw [mul_assoc, ← hψT, inv_mul_cancel_left]

end CFSG.RankThree.SteinbergBR.ThreeG2

namespace CFSG.RankThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT CFSG.RankThree.LocalRank
  CFSG.RankThree.SteinbergBR.ThreeG2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem three_G2_noninner_odd_prime_local_core_trivial {f p : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K)))
    (hB : (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup ReeTag.G2.tag K)) ∉
      (MulAut.conj : adjointGroup ReeTag.G2.tag K →* MulAut (adjointGroup ReeTag.G2.tag K)).range)
    (hαp : orderOf α = p) (x : adjointGroup ReeTag.G2.tag K) (a : ℕ) (ha : a < 2 * f)
    (hxa : (α : MulAut (adjointGroup ReeTag.G2.tag K)) =
      MulAut.conj x * ReeTag.G2.finiteExceptionalAut K ^ a) :
    p ∣ f ∧ Even a ∧
      (∃ σ : K ≃+* K, (∀ c, σ c = c ^ 3 ^ (a / 2)) ∧ orderOf σ = p ∧
        ReeTag.G2.finiteExceptionalAut K ^ a = entrywiseAdjointAut ReeTag.G2.tag σ ∧
        orderOf (ReeTag.G2.finiteExceptionalAut K ^ a) = p) ∧
      (∃ h : adjointGroup ReeTag.G2.tag K,
        MulAut.conj h * (α : MulAut (adjointGroup ReeTag.G2.tag K)) * (MulAut.conj h)⁻¹ =
          ReeTag.G2.finiteExceptionalAut K ^ a) ∧
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have : NeZero (2 * f) := ⟨by omega⟩
  set C := adjointGroup ReeTag.G2.tag K
  set α' : MulAut C := (α : MulAut C) with hα'
  have hα'p : orderOf α' = p := by rw [hα', Subgroup.orderOf_coe, hαp]
  have hα'pow : α' ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one α'
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  have hΘα : Θ α' = Multiplicative.ofAdd (a : ZMod (2 * f)) := hΘ α' _ a hxa
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hα
    rw [hxa, pow_zero, mul_one]
    exact ⟨_, rfl⟩
  have hdvd : 2 * f ∣ p * a := by
    have h1 : Θ (α' ^ p) = 1 := by rw [hα'pow, map_one]
    rwa [map_pow, hΘα, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff] at h1
  have hp2f : p ∣ 2 * f := by
    by_contra hnd
    have hcop : Nat.Coprime (2 * f) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    exact ha0 (Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hdvd) ha)
  have hpf : p ∣ f :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hp2f
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have h2d : 2 * d ∣ a := by
    have h1 : p * (2 * d) ∣ p * a := by
      rw [show p * (2 * d) = 2 * f by rw [hd]; ring]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos h1
  obtain ⟨j, hj⟩ := h2d
  have hjp : j < p := by
    by_contra hjp
    have h1 : 2 * d * p ≤ 2 * d * j := Nat.mul_le_mul_left _ (not_lt.1 hjp)
    have h2 : 2 * d * p = 2 * f := by rw [hd]; ring
    omega
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h => ha0 (by rw [hj, h, mul_zero])
  have ha2 : a / 2 = d * j := by
    rw [hj, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_three hf hK
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ 3 ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow_of_dvd (by omega) (by rw [hord, ← hdp]; exact Dvd.intro p rfl), hord,
      ← hdp, Nat.mul_div_cancel_left p hd0]
  have hFrT : ReeTag.G2.finiteFrobeniusAut K ^ d = entrywiseAdjointAut ReeTag.G2.tag T := by
    rw [← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 (σ := T) (j := d) hT,
      FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]
  have hφT : ReeTag.G2.finiteExceptionalAut K ^ (2 * d) = entrywiseAdjointAut ReeTag.G2.tag T := by
    rw [finiteExceptionalAut_pow_two_mul, hFrT]
  obtain ⟨r, hr⟩ := exists_mul_mod_eq_one hp hj0 hjp
  obtain ⟨⟨y, k⟩, hyk, -⟩ := hNF (α' ^ r)
  dsimp only at hyk
  have hk2d : (k : ℕ) = 2 * d := by
    have h1 : Θ (α' ^ r) = Multiplicative.ofAdd (((k : ℕ) : ZMod (2 * f))) := hΘ _ y k hyk
    rw [map_pow, hΘα, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul] at h1
    have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (Multiplicative.ofAdd.injective h1)
    have ht : r * a = 2 * d + 2 * f * (r * j / p) := by
      have h3 := Nat.div_add_mod (r * j) p
      rw [hr] at h3
      rw [hj, hd]
      calc r * (2 * d * j) = 2 * d * (r * j) := by ring
        _ = 2 * d * (p * (r * j / p) + 1) := by rw [h3]
        _ = 2 * d + 2 * (p * d) * (r * j / p) := by ring
    have h2d2f : 2 * d < 2 * f := by
      have : d < f := by rw [← hdp]; exact lt_mul_right hd0 hp.one_lt
      omega
    rw [ht, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2d2f, Nat.mod_eq_of_lt k.isLt] at h2
    exact h2.symm
  have hβ : α' ^ r = MulAut.conj y * entrywiseAdjointAut ReeTag.G2.tag T := by
    rw [hyk, hk2d, hφT]
  have hβp : (MulAut.conj y * entrywiseAdjointAut ReeTag.G2.tag T) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hα'pow, one_pow]
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : MulAut C,
      ψ₀ * (MulAut.conj y * entrywiseAdjointAut ReeTag.G2.tag T) * ψ₀⁻¹ =
        entrywiseAdjointAut ReeTag.G2.tag T := by
    have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact exists_conj_eq_entrywiseAdjointAut ReeTag.G2.tag K hK hd0 hp.one_lt.le hdp T hT
      (AlgebraicClosure K) y hβp
  obtain ⟨⟨g, b⟩, hgb, -⟩ := hNF ψ₀
  dsimp only at hgb
  have hcommT : ReeTag.G2.finiteExceptionalAut K ^ (b : ℕ) * entrywiseAdjointAut ReeTag.G2.tag T =
      entrywiseAdjointAut ReeTag.G2.tag T * ReeTag.G2.finiteExceptionalAut K ^ (b : ℕ) := by
    rw [← hφT]
    exact ((Commute.refl _).pow_pow _ _).eq
  set h₀ : C := (ReeTag.G2.finiteExceptionalAut K ^ (b : ℕ))⁻¹ g with hh₀def
  have hh₀ : MulAut.conj h₀ * (MulAut.conj y * entrywiseAdjointAut ReeTag.G2.tag T) *
      (MulAut.conj h₀)⁻¹ = entrywiseAdjointAut ReeTag.G2.tag T :=
    conj_inner_eq_of_conj_mul g _ _ _ hcommT (by rw [← hgb]; exact hψ₀)
  have hTj : entrywiseAdjointAut ReeTag.G2.tag (T ^ j) = ReeTag.G2.finiteExceptionalAut K ^ a := by
    rw [entrywiseAdjointAut_pow, ← hφT, ← pow_mul, hj]
  have hψα : MulAut.conj h₀ * α' * (MulAut.conj h₀)⁻¹ = ReeTag.G2.finiteExceptionalAut K ^ a := by
    have hαβ : α' = (α' ^ r) ^ j := by rw [← pow_mul, pow_eq_self_of_mod_eq_one hα'p hr]
    rw [hαβ, ← conj_pow, hβ, hh₀, ← entrywiseAdjointAut_pow, hTj]
  have hTjp : orderOf (T ^ j) = p := by
    refine orderOf_eq_prime ?_ (pow_ne_one_of_lt_orderOf hj0.ne' (by rw [hTord]; exact hjp))
    rw [← pow_mul, mul_comm, pow_mul, ← hTord, pow_orderOf_eq_one, one_pow]
  have hrank : 0 < ReeTag.G2.tag.rank := by decide
  have hφap : orderOf (ReeTag.G2.finiteExceptionalAut K ^ a) = p := by
    rw [← hTj, orderOf_entrywiseAdjointAut hrank, hTjp]
  have hTr : (T ^ j) ^ r = T := by
    rw [← pow_mul, pow_eq_self_of_mod_eq_one hTord (by rw [mul_comm]; exact hr)]
  have hFrδ : ReeTag.G2.finiteFrobeniusAut K ^ d =
      entrywiseAdjointAut ReeTag.G2.tag (T ^ j) ^ r := by
    rw [hFrT, ← entrywiseAdjointAut_pow, hTr]
  set σ := T ^ j with hσdef
  set δ := entrywiseAdjointAut ReeTag.G2.tag σ with hδdef
  obtain ⟨-, hkcard⟩ := card_fixSubfield Nat.prime_three hf hK σ
  rw [hTjp, ← hdp, Nat.mul_div_cancel _ hp.pos] at hkcard
  obtain ⟨hJC, -, hfixing, -, -⟩ :=
    three_G2_subfield_normalizer_and_pointwise_automorphism_centralizer hf hd0 ⟨p, hdp.symm⟩ hK
      (fixSubfield σ) hkcard
  set J := subfieldImage ReeTag.G2.tag (fixSubfield σ) with hJ
  have hZ : Subgroup.center C = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hΓJ : entrywiseFixedGroup ReeTag.G2.tag σ = fixedFieldImage ReeTag.G2.tag σ :=
    CFSG.ComponentClassification.UnbalancedCatalog.entrywiseFixedGroup_eq_fixedFieldImage σ
  have hmemJ : ∀ g : C, (g : ModGL ReeTag.G2.tag K) ∈ J ↔ δ g = g := by
    intro g
    refine (Subgroup.ext_iff.1 hΓJ (g : ModGL ReeTag.G2.tag K)).symm.trans ?_
    rw [mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  have hZk : Subgroup.center (adjointGroup ReeTag.G2.tag (fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  have h3d : 3 ≤ 3 ^ d := by
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd0
  have hmodel : ChevalleyExceptionalModel J .G2 3 d :=
    ⟨⟨Nat.prime_three, hd0, rfl, h3d⟩, fixSubfield σ, inferInstance, inferInstance, hkcard,
      ⟨(fixedFieldImageEquiv (τ := ReeTag.G2.tag) σ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm⟩⟩
  have hsimple : IsSimpleGroup J := (CFSG.LieType.Simplicity.fam_g2_simplicity _ 3 d hmodel).2
  have hnc : ¬∀ u v : J, u * v = v * u := not_commute_fixedFieldImage hrank σ
  have hNδ : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {δ} := by
    rintro _ ⟨j', hj', rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j').1 (Subgroup.mem_subgroupOf.1 hj')]
  have hnormal : (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer {δ})).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j', hj', hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [SetLike.mem_coe] at hj'
    have hgδ : δ * (g : MulAut C) = g * δ :=
      Subgroup.mem_centralizer_iff.1 g.2 δ (Set.mem_singleton δ)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut C) j', ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc δ ((g : MulAut C) j') = (δ * (g : MulAut C)) j' := rfl
        _ = (g * δ : MulAut C) j' := by rw [hgδ]
        _ = (g : MulAut C) (δ j') := rfl
        _ = (g : MulAut C) j' := by rw [(hmemJ j').1 (Subgroup.mem_subgroupOf.1 hj')]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  have hcent : Subgroup.centralizer {δ} ⊓ Subgroup.centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = Subgroup.zpowers δ := by
    refine le_antisymm (fun β hβ => ?_) ?_
    · obtain ⟨-, hβN⟩ := Subgroup.mem_inf.1 hβ
      have hfixβ : β ∈ fixingSubgroup (MulAut C) (((J.subgroupOf C) : Subgroup C) : Set C) := by
        refine (mem_fixingSubgroup_iff _).2 fun u hu => ?_
        rw [MulAut.smul_def]
        have hn : MulAut.conj u ∈ (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) :=
          ⟨u, hu, rfl⟩
        have h1 : MulAut.conj u * β = β * MulAut.conj u :=
          Subgroup.mem_centralizer_iff.1 hβN _ hn
        have h2 : MulAut.conj (β u) = MulAut.conj u := by
          rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
        exact hinj h2
      rw [hfixing] at hfixβ
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hfixβ
      rw [hFrδ]
      exact Subgroup.zpow_mem _ (Subgroup.npow_mem_zpowers δ r) m
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
        fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
          fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)
  refine ⟨⟨d, hd⟩, ⟨d * j, by rw [hj]; ring⟩, ⟨σ, fun c => ?_, hTjp, hTj.symm, hφap⟩,
    ⟨h₀, hψα⟩, aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB α hαp
      (MulAut.conj h₀) δ (hψα.trans hTj.symm) hsimple hnc
      ((J.subgroupOf C).equivMapOfInjective _ hinj) hNδ hnormal hcent⟩
  rw [hσdef, hTdef, ← pow_mul, ringAut_pow_apply_of_frobenius hfr, ha2]

end CFSG.RankThree
