module

public import CFSG.Quasithin.SteinbergCGA7ListedActorSupport
public import CFSG.Quasithin.SteinbergBSA7RankTwoThreeNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SteinbergBQDeletedSymmetricRankTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSectionRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCG

open Module Subgroup Equiv
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight)

section Transport

variable {G P : Type*} [Group G] [Group P] {N : Subgroup G}

theorem mem_zpowers_symm_iff (e : P ≃* N) {b : G} (hb : b ∈ N) (x : P) :
    x ∈ zpowers (e.symm ⟨b, hb⟩) ↔ ((e x : N) : G) ∈ zpowers b := by
  simp only [mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, map_zpow, MulEquiv.apply_symm_apply, SubgroupClass.coe_zpow]
  · rintro ⟨k, hk⟩
    refine ⟨k, e.injective ?_⟩
    rw [map_zpow, MulEquiv.apply_symm_apply]
    exact Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk)

theorem map_subgroupOf_le_normalizer (e : P ≃* N) {b : G} (hb : b ∈ N) {R : Subgroup G}
    (hR : R ≤ normalizer (zpowers b : Set G)) :
    (R.subgroupOf N).map e.symm.toMonoidHom ≤ normalizer (zpowers (e.symm ⟨b, hb⟩) : Set P) := by
  rintro _ ⟨y, hy, rfl⟩
  have hg : (y : G) ∈ normalizer (zpowers b : Set G) := hR hy
  rw [mem_normalizer_iff]
  intro h
  rw [mem_zpowers_symm_iff, mem_zpowers_symm_iff]
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul, map_inv,
    MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.mp hg _

end Transport

section Classical

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem eq_top_and_finrank_eq_two_of_classical {N R : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hR : ABGLocalTools.IsSylowOf 2 R N) {b : V ≃ₗ[ZMod 2] V} (hbN : b ∈ N) (hb : orderOf b = 3)
    (hRb : R ≤ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2)
    (halt : N = ⊤ ∨
      (∃ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
        N = TauCeti.BilinForm.isometryGroup β) ∨
      ∃ q : QuadraticForm (ZMod 2) V, (QuadraticMap.polarBilin q).Nondegenerate ∧
        N = TauCeti.QuadraticMap.orthogonalGroup q) :
    N = ⊤ ∧ finrank (ZMod 2) V = 2 := by
  have : Finite (V ≃ₗ[ZMod 2] V) := SteinbergBS.RankTwoThree.finite_linearEquiv V
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hobs := SteinbergBS.rank_two_three_subgroup_classical_normalizer_obstruction hb rfl rfl hrank
  have hd2 : 2 ≤ finrank (ZMod 2) V := by
    have := Submodule.finrank_le (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    omega
  have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
  have hRN := hR.le
  rcases halt with hN | ⟨β, hβ, hnd, hN⟩ | ⟨q, hq, hN⟩
  ·
    refine ⟨hN, ?_⟩
    subst hN
    by_contra hne
    have hc : Nat.card R = 2 ^ (Nat.card (V ≃ₗ[ZMod 2] V)).factorization 2 := by
      rw [hR.card_eq, Subgroup.card_top]
    obtain ⟨-, -, -, -, -, hsyl⟩ := hobs.1 _ rfl
    exact hsyl (by omega) (Sylow.ofCard R hc) (by rw [Sylow.coe_ofCard]; exact hRb)
  ·
    subst hN
    obtain ⟨n, hn⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.alternating_nondegenerate_form_finrank_even β hβ hnd
    have h2 : finrank (ZMod 2) V = 2 := by
      by_contra hne
      obtain ⟨-, -, -, -, -, -, -, -, -, hsyl⟩ := hobs.2.1 n β (by omega) hβ hnd hbN
      obtain ⟨Q, hQ⟩ := hR
      exact hsyl (by omega) Q (by rw [hQ]; exact le_inf hRN hRb)
    refine ⟨?_, h2⟩
    rw [eq_top_iff]
    intro g _
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    have h1 : (g x ≠ 0 ∧ g y ≠ 0 ∧ g x ≠ g y) ↔ (x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y) := by
      simp only [ne_eq, LinearEquiv.map_eq_zero_iff, EmbeddingLike.apply_eq_iff_eq]
    rw [SteinbergBS.RankTwoThree.bilin_apply_eq_ite h2 hβ hnd,
      SteinbergBS.RankTwoThree.bilin_apply_eq_ite h2 hβ hnd]
    split_ifs with hx hy hy
    · rfl
    · exact absurd (h1.mp hx) hy
    · exact absurd (h1.mpr hy) hx
    · rfl
  ·
    subst hN
    have hbq : ∀ x, q (b x) = q x := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hbN
    obtain ⟨halt', -, hq1, -⟩ := SteinbergBS.RankTwoThree.orthogonal_facts hq hbq hb3 hrank
    obtain ⟨n, hn⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.alternating_nondegenerate_form_finrank_even _ halt' hq
    have h2 : finrank (ZMod 2) V = 2 := by
      by_contra hne
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsyl⟩ :=
        hobs.2.2 n q (by omega) (by omega) hq hbN
      obtain ⟨Q, hQ⟩ := hR
      exact hsyl Q (by rw [hQ]; exact le_inf hRN hRb)
    have hU : LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hrank.trans h2.symm)
    have hmem : ∀ v, v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) := fun v => by
      rw [hU]
      exact Submodule.mem_top
    refine ⟨?_, h2⟩
    rw [eq_top_iff]
    intro g _
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    by_cases hv : v = 0
    · rw [hv, map_zero]
    · rw [hq1 _ (hmem _) (by rwa [ne_eq, LinearEquiv.map_eq_zero_iff]), hq1 _ (hmem _) hv]

theorem eq_and_nonempty_mulEquiv_of_eq_top {H N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNH : N ≤ H)
    (hN : N = ⊤) (h2 : finrank (ZMod 2) V = 2) : H = N ∧ Nonempty (H ≃* Perm (Fin 3)) := by
  have hHN : H = N := le_antisymm (hN ▸ le_top) hNH
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_three h2
  exact ⟨hHN, ⟨((MulEquiv.subgroupCongr (hHN.trans hN)).trans Subgroup.topEquiv).trans e⟩⟩

end Classical

section Deleted

@[expose] def coordPerm {m : ℕ} (σ : Perm (Fin m)) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑σ⁻¹

theorem coordPerm_mem_evenWeight {m : ℕ} (σ : Perm (Fin m)) {x : Fin m → ZMod 2}
    (hx : x ∈ evenWeight (Fin m)) : coordPerm σ x ∈ evenWeight (Fin m) := by
  change ∑ i, x (σ⁻¹ i) = 0
  rw [Equiv.sum_comp σ⁻¹ x]
  exact hx

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_map_coordPerm_sub_one {m : ℕ} (b : V ≃ₗ[ZMod 2] V) (c : Perm (Fin m))
    (f : V ≃ₗ[ZMod 2] evenWeight (Fin m))
    (hf : ∀ v i, (f (b v) : Fin m → ZMod 2) i = (f v : Fin m → ZMod 2) (c⁻¹ i)) :
    finrank (ZMod 2) ((evenWeight (Fin m)).map (coordPerm c - 1)) =
      finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) := by
  let A : V →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    (evenWeight (Fin m)).subtype ∘ₗ (f : V →ₗ[ZMod 2] evenWeight (Fin m))
  have hA : Function.Injective A := Subtype.val_injective.comp f.injective
  have hAv : ∀ v, A (((b : V →ₗ[ZMod 2] V) - LinearMap.id : V →ₗ[ZMod 2] V) v) =
      (coordPerm c - 1 : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (f v : Fin m → ZMod 2) := by
    intro v
    funext i
    change ((f (b v - v) : evenWeight (Fin m)) : Fin m → ZMod 2) i =
      (f v : Fin m → ZMod 2) (c⁻¹ i) - (f v : Fin m → ZMod 2) i
    rw [map_sub, Submodule.coe_sub, Pi.sub_apply, hf]
  have hmap : (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)).map A =
      (evenWeight (Fin m)).map (coordPerm c - 1) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
      exact ⟨f v, (f v).2, (hAv v).symm⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨_, ⟨f.symm ⟨x, hx⟩, rfl⟩, ?_⟩
      rw [hAv, LinearEquiv.apply_symm_apply]
  rw [← hmap]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective A hA _)).symm

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_map_mkQ_coordPerm_sub_one {m : ℕ} (b : V ≃ₗ[ZMod 2] V) (c : Perm (Fin m))
    (Z : Submodule (ZMod 2) (Fin m → ZMod 2))
    (f : V ≃ₗ[ZMod 2] (evenWeight (Fin m) ⧸ Z.comap (evenWeight (Fin m)).subtype))
    (hf : ∀ v (x y : evenWeight (Fin m)), f v = Submodule.Quotient.mk x →
      (∀ i, (y : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (c⁻¹ i)) →
      f (b v) = Submodule.Quotient.mk y) :
    finrank (ZMod 2) (((evenWeight (Fin m)).map (coordPerm c - 1)).map Z.mkQ) =
      finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) := by
  let ι := (Z.comap (evenWeight (Fin m)).subtype).mapQ Z (evenWeight (Fin m)).subtype le_rfl
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hw
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hw
  let A : V →ₗ[ZMod 2] (Fin m → ZMod 2) ⧸ Z := ι ∘ₗ (f : V →ₗ[ZMod 2] _)
  have hA : Function.Injective A := hι.comp f.injective
  have hAv : ∀ v (x : evenWeight (Fin m)), f v = Submodule.Quotient.mk x →
      A (((b : V →ₗ[ZMod 2] V) - LinearMap.id : V →ₗ[ZMod 2] V) v) =
        Z.mkQ ((coordPerm c - 1 : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
          (x : Fin m → ZMod 2)) := by
    intro v x hx
    have hy := hf v x ⟨coordPerm c x, coordPerm_mem_evenWeight c x.2⟩ hx fun i => rfl
    change ι (f (b v - v)) = Submodule.Quotient.mk (coordPerm c x - x)
    rw [map_sub, hy, hx, map_sub, Submodule.mapQ_apply, Submodule.mapQ_apply,
      Submodule.Quotient.mk_sub]
    rfl
  have hmap : (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)).map A =
      ((evenWeight (Fin m)).map (coordPerm c - 1)).map Z.mkQ := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (f v)
      exact ⟨_, ⟨x, x.2, rfl⟩, (hAv v x hx.symm).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨_, ⟨f.symm (Submodule.Quotient.mk ⟨x, hx⟩), rfl⟩, ?_⟩
      rw [hAv _ ⟨x, hx⟩ (LinearEquiv.apply_symm_apply _ _)]
  rw [← hmap]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective A hA _)).symm

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_of_odd_deleted {H N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set (V ≃ₗ[ZMod 2] V))) {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    (ψ : Perm (Fin m) ≃* N) (f : V ≃ₗ[ZMod 2] evenWeight (Fin m))
    (hf : ∀ σ v i, (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin m → ZMod 2) i =
      (f v : Fin m → ZMod 2) (σ⁻¹ i)) :
    H = N := by
  let E : (V ≃ₗ[ZMod 2] V) ≃* LinearMap.GeneralLinearGroup (ZMod 2) (evenWeight (Fin m)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv f)
  let ρΔ : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) (evenWeight (Fin m)) :=
    E.toMonoidHom.comp (N.subtype.comp ψ.toMonoidHom)
  have hρ : ∀ σ (x : evenWeight (Fin m)) i,
      (((ρΔ σ : LinearMap.GeneralLinearGroup (ZMod 2) (evenWeight (Fin m))) :
        evenWeight (Fin m) →ₗ[ZMod 2] evenWeight (Fin m)) x : Fin m → ZMod 2) i =
        (x : Fin m → ZMod 2) (σ⁻¹ i) := by
    intro σ x i
    have h := hf σ (f.symm x) i
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  obtain ⟨-, hnorm, -, -⟩ :=
    QuasithinUnique.odd_deleted_symmetric_actor_is_self_normalizing hm
      hodd (fun _ => Iff.rfl) ρΔ hρ
  have hrange : ρΔ.range = N.map E.toMonoidHom := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply le_antisymm _ hNH
  rw [← Subgroup.map_le_map_iff_of_injective (f := E.toMonoidHom) E.injective]
  calc H.map E.toMonoidHom ≤ (normalizer (N : Set (V ≃ₗ[ZMod 2] V))).map E.toMonoidHom :=
        Subgroup.map_mono hHN
    _ = normalizer ((N.map E.toMonoidHom : Subgroup _) :
        Set (LinearMap.GeneralLinearGroup (ZMod 2) (evenWeight (Fin m)))) :=
        Subgroup.map_equiv_normalizer_eq N E
    _ = N.map E.toMonoidHom := by rw [← hrange, hnorm]

end Deleted

theorem not_nine_le_of_section {G : Type*} [Group G] [Finite G]
    (hG : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9) {Q : Type*} [Group Q]
    (Y : Subgroup G) {H N : Subgroup Q} (ρ : Y →* H) (hρ : Function.Surjective ρ) (hNH : N ≤ H)
    {m : ℕ} (ψ : Perm (Fin m) ≃* N) : ¬ 9 ≤ m := by
  intro hm
  obtain ⟨ι, hι⟩ := exists_injective_pi_perm_three hm
  let κ : (Fin 3 → Perm (Fin 3)) →* H := (Subgroup.inclusion hNH).comp (ψ.toMonoidHom.comp ι)
  have hκ : Function.Injective κ := (Subgroup.inclusion_injective hNH).comp (ψ.injective.comp hι)
  let θ₀ : (κ.range.comap ρ) →* (Fin 3 → Perm (Fin 3)) :=
    (MonoidHom.ofInjective hκ).symm.toMonoidHom.comp (ρ.subgroupComap κ.range)
  have hθ₀ : Function.Surjective θ₀ :=
    (MonoidHom.ofInjective hκ).symm.surjective.comp (ρ.subgroupComap_surjective κ.range hρ)
  let θ : ((κ.range.comap ρ).map Y.subtype) →* (Fin 3 → Perm (Fin 3)) :=
    θ₀.comp ((κ.range.comap ρ).equivMapOfInjective Y.subtype Y.subtype_injective).symm.toMonoidHom
  have hθ : Function.Surjective θ := hθ₀.comp (MulEquiv.surjective _)
  have h3 := QuasithinUnique.Setup.Lift.sym_three_pow_section_forces_three_rank 3 _ θ hθ
  obtain ⟨A, hA, hcard⟩ := exists_isElementaryAbelian_card_pRank Nat.prime_three G
  have h9 := hG A hA
  rw [hcard] at h9
  have h27 : 3 ^ 3 ≤ 3 ^ CFSG.pRank 3 G := Nat.pow_le_pow_right (by norm_num) h3
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem eq_and_S3_or_S7_of_deleted {G : Type*} [Group G] [Finite G]
    (hG : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9) (Y : Subgroup G)
    {H N R : Subgroup (V ≃ₗ[ZMod 2] V)} (ρ : Y →* H) (hρ : Function.Surjective ρ) (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set (V ≃ₗ[ZMod 2] V))) (hR : ABGLocalTools.IsSylowOf 2 R N)
    {b : V ≃ₗ[ZMod 2] V} (hbN : b ∈ N) (hb : orderOf b = 3)
    (hRb : R ≤ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2)
    {m : ℕ} (hm : 3 ≤ m) (ψ : Perm (Fin m) ≃* N)
    (hW : (Odd m ∧ ∃ f : V ≃ₗ[ZMod 2] evenWeight (Fin m), ∀ σ v i,
        (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin m → ZMod 2) i = (f v : Fin m → ZMod 2) (σ⁻¹ i)) ∨
      (Even m ∧ ∃ f : V ≃ₗ[ZMod 2] (evenWeight (Fin m) ⧸
          (Submodule.span (ZMod 2) {fun _ => 1}).comap (evenWeight (Fin m)).subtype),
        ∀ σ v (x y : evenWeight (Fin m)), f v = Submodule.Quotient.mk x →
          (∀ i, (y : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i)) →
          f ((ψ σ : V ≃ₗ[ZMod 2] V) v) = Submodule.Quotient.mk y)) :
    H = N ∧ ((Nonempty (H ≃* Perm (Fin 3)) ∧ finrank (ZMod 2) V = 2) ∨
      (finrank (ZMod 2) V = 6 ∧ ∃ ψ : Perm (Fin 7) ≃* H, ∃ f : V ≃ₗ[ZMod 2] evenWeight (Fin 7),
        ∀ σ v i, (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin 7 → ZMod 2) i =
          (f v : Fin 7 → ZMod 2) (σ⁻¹ i))) := by
  classical
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (V ≃ₗ[ZMod 2] V) := SteinbergBS.RankTwoThree.finite_linearEquiv V
  set c : Perm (Fin m) := ψ.symm ⟨b, hbN⟩ with hc
  have hψc : ((ψ c : N) : V ≃ₗ[ZMod 2] V) = b := by rw [hc, MulEquiv.apply_symm_apply]
  have hc3 : orderOf c = 3 := by rw [hc, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hb]
  have hR'card : Nat.card ((R.subgroupOf N).map ψ.symm.toMonoidHom) =
      2 ^ (Nat.card (Perm (Fin m))).factorization 2 := by
    rw [card_map_of_injective ψ.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe hR.le).toEquiv, hR.card_eq, Nat.card_congr ψ.toEquiv]
  have hS : ((Sylow.ofCard _ hR'card : Sylow 2 (Perm (Fin m))) : Subgroup (Perm (Fin m))) ≤
      normalizer (zpowers c : Set (Perm (Fin m))) := by
    rw [Sylow.coe_ofCard]
    exact map_subgroupOf_le_normalizer ψ hbN hRb
  have hcb : ∀ v, ((ψ c : N) : V ≃ₗ[ZMod 2] V) v = b v := fun v => by rw [hψc]
  have hWodd : Odd m → ∀ f : V ≃ₗ[ZMod 2] evenWeight (Fin m), (∀ σ v i,
      (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin m → ZMod 2) i = (f v : Fin m → ZMod 2) (σ⁻¹ i)) →
      finrank (ZMod 2) ((evenWeight (Fin m)).map (coordPerm c - 1)) = 2 := by
    intro _ f hf
    rw [finrank_map_coordPerm_sub_one b c f fun v i => by rw [← hcb]; exact hf c v i, hrank]
  have hdeg : m % 4 = 3 := by
    rcases hW with ⟨hodd, f, hf⟩ | ⟨heven, f, hf⟩
    · have h := QuasithinUnique.deleted_symmetric_rank_two_three_normalizer_degrees
        hm coordPerm (fun _ _ _ => rfl) (Δ := evenWeight (Fin m)) (fun _ => Iff.rfl) rfl hc3
        (fun _ => hWodd hodd f hf) (fun h => absurd hodd (Nat.not_odd_iff_even.mpr h))
      exact h.2.2.1.mp ⟨_, hS⟩
    · have hWeven : finrank (ZMod 2) (((evenWeight (Fin m)).map (coordPerm c - 1)).map
          (Submodule.span (ZMod 2) {fun _ => 1}).mkQ) = 2 := by
        rw [finrank_map_mkQ_coordPerm_sub_one b c _ f fun v x y hx hy => by
          rw [← hcb]; exact hf c v x y hx hy, hrank]
      have h := QuasithinUnique.deleted_symmetric_rank_two_three_normalizer_degrees
        hm coordPerm (fun _ _ _ => rfl) (Δ := evenWeight (Fin m)) (fun _ => Iff.rfl) rfl hc3
        (fun h => absurd heven (Nat.not_even_iff_odd.mpr h)) (fun _ => hWeven)
      exact h.2.2.1.mp ⟨_, hS⟩
  rcases hW with ⟨hodd, f, hf⟩ | ⟨heven, -⟩
  swap
  · obtain ⟨k, hk⟩ := heven
    omega
  have hm9 : ¬ 9 ≤ m := not_nine_le_of_section hG Y ρ hρ hNH ψ
  have hHN' : H = N := eq_of_odd_deleted hNH hHN hm hodd ψ f hf
  have hfin : finrank (ZMod 2) V = m - 1 := by
    rw [f.finrank_eq]
    exact QuasithinUnique.SteinbergBQ.DeletedModule.finrank_delta (fun _ => Iff.rfl) (by omega)
  refine ⟨hHN', ?_⟩
  have hm37 : m = 3 ∨ m = 7 := by omega
  rcases hm37 with rfl | rfl
  · exact Or.inl ⟨⟨(MulEquiv.subgroupCongr hHN').trans ψ.symm⟩, hfin⟩
  · exact Or.inr ⟨hfin, ψ.trans (MulEquiv.subgroupCongr hHN'.symm), f, hf⟩

theorem listed_binary_normal_actor_forces_S3_or_S7 {G : Type*} [Group G] [Finite G]
    (hG : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9) [Nontrivial V]
    (Y : Subgroup G) {H N T : Subgroup (V ≃ₗ[ZMod 2] V)} (ρ : Y →* H) (hρ : Function.Surjective ρ)
    (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (hT : ABGLocalTools.IsSylowOf 2 T H)
    {b : V ≃ₗ[ZMod 2] V} (hbN : b ∈ N) (hb : orderOf b = 3)
    (hTb : T ≤ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2)
    (halt : N = ⊤ ∨
      (∃ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
        N = TauCeti.BilinForm.isometryGroup β) ∨
      (∃ q : QuadraticForm (ZMod 2) V, (QuadraticMap.polarBilin q).Nondegenerate ∧
        N = TauCeti.QuadraticMap.orthogonalGroup q) ∨
      ∃ m : ℕ, 3 ≤ m ∧ ∃ ψ : Perm (Fin m) ≃* N,
        (Odd m ∧ ∃ f : V ≃ₗ[ZMod 2] evenWeight (Fin m), ∀ σ v i,
          (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin m → ZMod 2) i = (f v : Fin m → ZMod 2) (σ⁻¹ i)) ∨
        (Even m ∧ ∃ f : V ≃ₗ[ZMod 2] (evenWeight (Fin m) ⧸
            (Submodule.span (ZMod 2) {fun _ => 1}).comap (evenWeight (Fin m)).subtype),
          ∀ σ v (x y : evenWeight (Fin m)), f v = Submodule.Quotient.mk x →
            (∀ i, (y : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i)) →
            f ((ψ σ : V ≃ₗ[ZMod 2] V) v) = Submodule.Quotient.mk y)) :
    H = N ∧
      ((Nonempty (H ≃* Perm (Fin 3)) ∧ finrank (ZMod 2) V = 2) ∨
        (finrank (ZMod 2) V = 6 ∧ ∃ ψ : Perm (Fin 7) ≃* H, ∃ f : V ≃ₗ[ZMod 2] evenWeight (Fin 7),
          ∀ σ v i, (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin 7 → ZMod 2) i =
            (f v : Fin 7 → ZMod 2) (σ⁻¹ i))) ∧
      normalizer (T : Set (V ≃ₗ[ZMod 2] V)) ⊓ H = T := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (V ≃ₗ[ZMod 2] V) := SteinbergBS.RankTwoThree.finite_linearEquiv V
  have hHN : H ≤ normalizer (N : Set (V ≃ₗ[ZMod 2] V)) := le_normalizer_of_normal_subgroupOf hNH
  have hR : ABGLocalTools.IsSylowOf 2 (T ⊓ N) N := hT.inf_of_le_normalizer hNH hHN
  have hRb : T ⊓ N ≤ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) := inf_le_left.trans hTb
  have key : H = N ∧ ((Nonempty (H ≃* Perm (Fin 3)) ∧ finrank (ZMod 2) V = 2) ∨
      (finrank (ZMod 2) V = 6 ∧ ∃ ψ : Perm (Fin 7) ≃* H, ∃ f : V ≃ₗ[ZMod 2] evenWeight (Fin 7),
        ∀ σ v i, (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin 7 → ZMod 2) i =
          (f v : Fin 7 → ZMod 2) (σ⁻¹ i))) := by
    rcases halt with h | h | h | ⟨m, hm, ψ, hW⟩
    · obtain ⟨hN, h2⟩ := eq_top_and_finrank_eq_two_of_classical hR hbN hb hRb hrank (Or.inl h)
      obtain ⟨hHN', he⟩ := eq_and_nonempty_mulEquiv_of_eq_top hNH hN h2
      exact ⟨hHN', Or.inl ⟨he, h2⟩⟩
    · obtain ⟨hN, h2⟩ :=
        eq_top_and_finrank_eq_two_of_classical hR hbN hb hRb hrank (Or.inr (Or.inl h))
      obtain ⟨hHN', he⟩ := eq_and_nonempty_mulEquiv_of_eq_top hNH hN h2
      exact ⟨hHN', Or.inl ⟨he, h2⟩⟩
    · obtain ⟨hN, h2⟩ :=
        eq_top_and_finrank_eq_two_of_classical hR hbN hb hRb hrank (Or.inr (Or.inr h))
      obtain ⟨hHN', he⟩ := eq_and_nonempty_mulEquiv_of_eq_top hNH hN h2
      exact ⟨hHN', Or.inl ⟨he, h2⟩⟩
    · exact eq_and_S3_or_S7_of_deleted hG Y ρ hρ hNH hHN hR hbN hb hRb hrank hm ψ hW
  refine ⟨key.1, key.2, ?_⟩
  rcases key.2 with ⟨⟨e⟩, -⟩ | ⟨-, ψ, -, -⟩
  · apply normalizer_inf_eq_of_mulEquiv hT.le e
    apply normalizer_eq_of_card_two_perm_three
    rw [card_map_subgroupOf hT.le e, hT.card_eq, Nat.card_congr e.toEquiv,
      factorization_card_perm_three]
    rfl
  · apply normalizer_inf_eq_of_mulEquiv hT.le ψ.symm
    apply normalizer_eq_of_card_sixteen_perm_seven
    rw [card_map_subgroupOf hT.le ψ.symm, hT.card_eq, ← Nat.card_congr ψ.toEquiv,
      factorization_card_perm_seven]
    rfl

end CFSG.Quasithin.SteinbergCG
