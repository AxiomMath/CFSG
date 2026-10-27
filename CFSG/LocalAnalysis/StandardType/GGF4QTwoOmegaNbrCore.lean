module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRealizers
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.LieType.ReflectionGroups.F4ModThreeSigned
import CFSG.LieType.SeitzGeneration.ExcHighThree.Closing
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGF4QTwoOmegaEnd
import CFSG.LocalAnalysis.StandardType.GGF4QTwoWeylForm
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentGroup
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.LieType.ReflectionGroups.F4ModThree

@[expose] def GGOmegaTwoEndCoords {G : Type} [Group G] (Bs M : Subgroup G) (v : G)
    (τ : Multiplicative (Fin 3 → ZMod 3) →* G) : Prop :=
  Function.Injective τ ∧ τ.range = Bs ⊓ M ∧
  (∀ b ∈ Bs, ∃ k : ℤ, ∃ t ∈ Bs ⊓ M, b = v ^ k * t) ∧
  (∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
    ∃ n ∈ M, n ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ u : Multiplicative (Fin 3 → ZMod 3),
      n * τ u * n⁻¹ = τ (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd u (σ i))) ∧
  (∀ u : Fin 3 → ZMod 3, Two.weight u = 3 →
    Group.IsSolvable ↥(M ⊓ Subgroup.centralizer {τ (Multiplicative.ofAdd u)})) ∧
  (∀ u : Fin 3 → ZMod 3, Two.weight u = 2 → ∀ J : Subgroup G,
    J ≤ M ⊓ Subgroup.centralizer {τ (Multiplicative.ofAdd u)} → ⁅J, J⁆ = J → J ≠ ⊥ →
      Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set G)) = 9) ∧
  (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∃ X : Subgroup G,
    X ≤ M ⊓ Subgroup.centralizer {τ (Multiplicative.ofAdd (Pi.single i 1)),
      τ (Multiplicative.ofAdd (Pi.single j 1))} ∧
    IsSimpleGroup ↥X ∧ (∃ a b : ↥X, a * b ≠ b * a) ∧
    τ (Multiplicative.ofAdd (Pi.single k 1)) ∈ X) ∧
  (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ s : ZMod 3, s ≠ 0 →
    Group.IsSolvable ↥(M ⊓ Subgroup.centralizer {τ (Multiplicative.ofAdd (Pi.single i 1)),
      τ (Multiplicative.ofAdd (Pi.single j 1 + s • Pi.single k 1))}))

private theorem exists_conj_twoTor_signedPerm (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ∃ n ∈ Two.omega, ∀ v : Fin 3 → ZMod 3,
      n * Two.tor v * n⁻¹ = Two.tor (fun i => ε i * v (σ i)) :=
  exists_mem_modelOmega_conj_cmEquiv_signedPerm (K := ZMod 2) (b := 1) (c := 1) (by decide +kernel)
    (by decide +kernel) σ ε hε

theorem ggF4QTwoOmegaNbr_bstar_split_zpowers {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} (hBs : GGBstar p B Bs) {X : Subgroup G} (hZ : Subgroup.center ↥X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹)
    {v : G} (hv : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers v) :
    ∀ b ∈ Bs, ∃ k : ℤ, ∃ t ∈ Bs ⊓ X, b = v ^ k * t := by
  intro b hb
  obtain ⟨x, hx, c, hc, rfl⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b hb
  have hc' := hc
  rw [hv] at hc'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
  exact ⟨k, x, hx, Subgroup.mem_centralizer_iff.mp hc.2 x hx.2⟩

theorem card_bstar_inf_of_split {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    (hBs : GGBstar p B Bs) {X : Subgroup G} (hZ : Subgroup.center ↥X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹)
    {v : G} (hv : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers v)
    (hcard : Nat.card ↥Bs = 3 ^ 4) (hv3 : orderOf v = 3) : Nat.card ↥(Bs ⊓ X) = 27 := by
  have h := card_ggBstar_split hBs hZ hnorm hinner
  rw [hv, Nat.card_zpowers, hv3, hcard] at h
  omega

private theorem map_inf_centralizer {H K : Type*} [Group H] [Group K] {f : H →* K}
    (hf : Function.Injective f) (R : Subgroup H) (S : Set H) :
    (R ⊓ Subgroup.centralizer S).map f = R.map f ⊓ Subgroup.centralizer (f '' S) := by
  ext k
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_image]
  constructor
  · rintro ⟨h, ⟨hR, hc⟩, rfl⟩
    refine ⟨⟨h, hR, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hc s hs]
  · rintro ⟨⟨h, hR, rfl⟩, hc⟩
    refine ⟨h, ⟨hR, fun s hs => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc _ ⟨s, hs, rfl⟩

open CFSG.LieType.SeitzGeneration.ExcHighThree (isSolvable_map_iff) in
theorem exists_ggOmegaTwoEndCoords {G : Type} [Group G] [Finite G] {B Bs M : Subgroup G} {v : G}
    (hBstar : GGBstar 3 B Bs) (hcard : Nat.card ↥Bs = 3 ^ 4)
    (hvBs : v ∈ Bs) (hMv : M ≤ Subgroup.centralizer {v})
    (hZ : Subgroup.center ↥M = ⊥)
    (hM : LargeEvenMarking ↥M
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1))
    (hnorm : Bs ≤ Subgroup.normalizer (M : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ M, ∀ k ∈ M, b * k * b⁻¹ = g * k * g⁻¹)
    (hCv : Bs ⊓ Subgroup.centralizer (M : Set G) = Subgroup.zpowers v) :
    ∃ τ : Multiplicative (Fin 3 → ZMod 3) →* G, GGOmegaTwoEndCoords Bs M v τ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : ZMod 2) ≠ 0 := by decide +kernel
  have hbc : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide +kernel
  have hBea : CFSG.Open.IsElemAbelian 3 Bs := hBstar.2.1
  have hTea : CFSG.Open.IsElemAbelian 3 ((Bs ⊓ M).subgroupOf M) :=
    (hBea.mono inf_le_left).subgroupOf M
  have hTcard : ∀ n, Nat.card ↥(Bs ⊓ M) = n → Nat.card ↥((Bs ⊓ M).subgroupOf M) = n := by
    intro n hn
    rw [← hn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hv1 : v ≠ 1 := by
    rintro rfl
    have hsplit := card_ggBstar_split hBstar hZ hnorm hinner
    rw [hCv, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot, mul_one, hcard] at hsplit
    obtain ⟨ψ₁⟩ := nonempty_mulEquiv_twoOmega_of_marking hZ hM
    have hU : CFSG.GroupTheory.UniqueElemSylow 3 3 ↥Two.omega :=
      CFSG.GroupTheory.UniqueElemSylow.of_mulEquiv (omegaEquiv (toModelIso h3 hbc))
        (CFSG.GroupTheory.WeirSylow.uniqueElemSylow_statedOmega_quadMinus_four (ZMod 2) hbc
          (by rw [Nat.card_zmod]; decide +kernel))
    have hle := (hU.of_mulEquiv ψ₁.symm).pRank_le (by norm_num)
    have hge : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hTea (hTcard _ hsplit.symm)
    omega
  have hv3 : orderOf v = 3 := orderOf_eq_prime (hBea.2 v hvBs) hv1
  have hT : Nat.card ↥(Bs ⊓ M) = 27 :=
    card_bstar_inf_of_split hBstar hZ hnorm hinner hCv hcard hv3
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_twoOmega_of_marking_torus hZ hM hTea (hTcard 27 hT)
  obtain ⟨c, hc⟩ : ∃ c : Multiplicative (Fin 3 → ZMod 3) →* ↥Two.omega,
      ∀ u, (c u : Two.Aut) = cm (ZMod 2) u := ⟨cmOmega h3 hbc, fun _ => rfl⟩
  have hcinj : Function.Injective c := fun a b h =>
    cm_injective ((hc a).symm.trans ((congrArg Subtype.val h).trans (hc b)))
  have hcm : cm (ZMod 2) = Two.omega.subtype.comp c := MonoidHom.ext fun u => (hc u).symm
  have hιc : ∀ u, Two.omega.subtype (c (Multiplicative.ofAdd u)) = Two.tor u := fun u => hc _
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥Two.omega →* G, ∀ y, χ y = (ψ.symm y : G) :=
    ⟨M.subtype.comp ψ.symm.toMonoidHom, fun _ => rfl⟩
  have hχinj : Function.Injective χ := fun a b h =>
    ψ.symm.injective (Subtype.ext ((hχ a).symm.trans (h.trans (hχ b))))
  have hχtop : (⊤ : Subgroup ↥Two.omega).map χ = M := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      rw [hχ]
      exact (ψ.symm y).2
    · intro hx
      exact ⟨ψ ⟨x, hx⟩, trivial, by rw [hχ, MulEquiv.symm_apply_apply]⟩
  have hχr : χ.range = M := by rw [MonoidHom.range_eq_map, hχtop]
  have hιtop : (⊤ : Subgroup ↥Two.omega).map Two.omega.subtype = Two.omega := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCM1 : ∀ x, M ⊓ Subgroup.centralizer {χ x} = (⊤ ⊓ Subgroup.centralizer {x}).map χ := by
    intro x
    rw [map_inf_centralizer hχinj, hχtop, Set.image_singleton]
  have hCM2 : ∀ x y, M ⊓ Subgroup.centralizer {χ x, χ y} =
      (⊤ ⊓ Subgroup.centralizer {x, y}).map χ := by
    intro x y
    rw [map_inf_centralizer hχinj, hχtop, Set.image_pair]
  have hCΩ1 : ∀ x, Two.omega ⊓ Subgroup.centralizer {Two.omega.subtype x} =
      (⊤ ⊓ Subgroup.centralizer {x}).map Two.omega.subtype := by
    intro x
    rw [map_inf_centralizer Two.omega.subtype_injective, hιtop, Set.image_singleton]
  have hCΩ2 : ∀ x y, Two.omega ⊓ Subgroup.centralizer {Two.omega.subtype x, Two.omega.subtype y} =
      (⊤ ⊓ Subgroup.centralizer {x, y}).map Two.omega.subtype := by
    intro x y
    rw [map_inf_centralizer Two.omega.subtype_injective, hιtop, Set.image_pair]
  have hrange : (χ.comp c).range = Bs ⊓ M := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : ψ.symm (c u) ∈ (Bs ⊓ M).subgroupOf M :=
        (hψ _).mpr (by rw [MulEquiv.apply_symm_apply, hc]; exact ⟨u, rfl⟩)
      rw [MonoidHom.comp_apply, hχ]
      exact h1
    · intro hx
      obtain ⟨u, hu⟩ := (hψ ⟨x, hx.2⟩).mp hx
      refine ⟨u, ?_⟩
      have h1 : c u = ψ ⟨x, hx.2⟩ := Subtype.ext ((hc u).trans hu)
      rw [MonoidHom.comp_apply, hχ, h1, MulEquiv.symm_apply_apply]
  have hsplit := ggF4QTwoOmegaNbr_bstar_split_zpowers hBstar hZ hnorm hinner hCv
  refine ⟨χ.comp c, hχinj.comp hcinj, hrange, hsplit, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro σ ε hε
    obtain ⟨n₀, hn₀, hconj⟩ := exists_conj_twoTor_signedPerm σ ε hε
    have hnM : χ ⟨n₀, hn₀⟩ ∈ M := by
      rw [hχ]
      exact (ψ.symm _).2
    have hconjτ : ∀ u : Multiplicative (Fin 3 → ZMod 3),
        χ ⟨n₀, hn₀⟩ * (χ.comp c) u * (χ ⟨n₀, hn₀⟩)⁻¹ =
          (χ.comp c) (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd u (σ i)) := by
      intro u
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc, hc]
      exact hconj (Multiplicative.toAdd u)
    refine ⟨χ ⟨n₀, hn₀⟩, hnM, ?_, hconjτ⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj _).injective).ge
    rw [Subgroup.map_le_iff_le_comap]
    intro b hb
    obtain ⟨k, t, ht, rfl⟩ := hsplit b hb
    rw [← hrange] at ht
    obtain ⟨u, rfl⟩ := ht
    have hcomm : Commute (χ ⟨n₀, hn₀⟩) (v ^ k) :=
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hMv hnM)) k
    have heq : χ ⟨n₀, hn₀⟩ * (v ^ k * (χ.comp c) u) * (χ ⟨n₀, hn₀⟩)⁻¹ =
        v ^ k * (χ ⟨n₀, hn₀⟩ * (χ.comp c) u * (χ ⟨n₀, hn₀⟩)⁻¹) := by
      rw [← mul_assoc (χ ⟨n₀, hn₀⟩), hcomm.eq]
      simp only [mul_assoc]
    change χ ⟨n₀, hn₀⟩ * (v ^ k * (χ.comp c) u) * (χ ⟨n₀, hn₀⟩)⁻¹ ∈ Bs
    rw [heq, hconjτ]
    exact Bs.mul_mem (Bs.zpow_mem hvBs k) (hrange.le ⟨_, rfl⟩).1
  ·
    intro u hu
    have h := Two.isSolvable_centralizer_of_weight_eq_three u hu
    rw [← hιc, hCΩ1, isSolvable_map_iff _ Two.omega.subtype_injective] at h
    rw [MonoidHom.comp_apply, hCM1, isSolvable_map_iff _ hχinj]
    exact h
  ·
    intro u hu J hJ hJJ hJbot
    have hJM : J ≤ χ.range := hχr ▸ hJ.trans inf_le_left
    obtain ⟨L, rfl⟩ : ∃ L : Subgroup ↥Two.omega, L.map χ = J :=
      ⟨J.comap χ, Subgroup.map_comap_eq_self hJM⟩
    rw [MonoidHom.comp_apply, hCM1, Subgroup.map_le_map_iff_of_injective hχinj] at hJ
    rw [← Subgroup.map_commutator, (Subgroup.map_injective hχinj).eq_iff] at hJJ
    have hLbot : L ≠ ⊥ := fun h => hJbot (by rw [h, Subgroup.map_bot])
    have h9 := Two.card_torus_inf_centralizer_of_weight_eq_two u hu (L.map Two.omega.subtype)
      (by rw [← hιc, hCΩ1]; exact Subgroup.map_mono hJ)
      (by rw [← Subgroup.map_commutator, hJJ])
      (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ Two.omega.subtype_injective])
    rw [hcm, MonoidHom.range_comp, Subgroup.coe_map,
      ← map_inf_centralizer Two.omega.subtype_injective,
      Subgroup.card_map_of_injective Two.omega.subtype_injective] at h9
    rw [MonoidHom.range_comp, Subgroup.coe_map, ← map_inf_centralizer hχinj,
      Subgroup.card_map_of_injective hχinj]
    exact h9
  ·
    intro i j k hij hik hjk
    obtain ⟨X', hX'le, hX's, ⟨a, b, hab⟩, hk⟩ :=
      Two.exists_simple_le_centralizer_coord_pair i j k hij hik hjk
    have hX'Ω : X' ≤ Two.omega.subtype.range := by
      rw [Subgroup.range_subtype]
      exact hX'le.trans inf_le_left
    obtain ⟨L, rfl⟩ : ∃ L : Subgroup ↥Two.omega, L.map Two.omega.subtype = X' :=
      ⟨X'.comap Two.omega.subtype, Subgroup.map_comap_eq_self hX'Ω⟩
    rw [← hιc, ← hιc, hCΩ2, Subgroup.map_le_map_iff_of_injective Two.omega.subtype_injective]
      at hX'le
    have e : ↥(L.map χ) ≃* ↥(L.map Two.omega.subtype) :=
      (L.equivMapOfInjective χ hχinj).symm.trans
        (L.equivMapOfInjective _ Two.omega.subtype_injective)
    refine ⟨L.map χ, ?_, (MulEquiv.isSimpleGroup_congr e).mpr hX's,
      ⟨e.symm a, e.symm b, fun h => hab ?_⟩, ?_⟩
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hCM2]
      exact Subgroup.map_mono hX'le
    · simpa using congrArg e h
    · obtain ⟨y, hy, hyeq⟩ := hk
      rw [← hιc] at hyeq
      rw [Two.omega.subtype_injective hyeq] at hy
      exact ⟨_, hy, rfl⟩
  ·
    intro i j k hij hik hjk s hs
    have h := Two.isSolvable_centralizer_mixed_pair i j k hij hik hjk s hs
    rw [← hιc, ← hιc, hCΩ2, isSolvable_map_iff _ Two.omega.subtype_injective] at h
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hCM2, isSolvable_map_iff _ hχinj]
    exact h

private def elt {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (w : Fin 4 → ZMod 3) : G :=
  ((θ.symm (Multiplicative.ofAdd w) : ↥Bs) : G)

private theorem elt_mem {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (w : Fin 4 → ZMod 3) : elt θ w ∈ Bs :=
  (θ.symm (Multiplicative.ofAdd w)).2

private theorem elt_injective {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) : Function.Injective (elt θ) := fun _ _ h =>
  Multiplicative.ofAdd.injective (θ.symm.injective (Subtype.ext h))

private theorem elt_add {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (w₁ w₂ : Fin 4 → ZMod 3) :
    elt θ (w₁ + w₂) = elt θ w₁ * elt θ w₂ := by
  simp only [elt, ofAdd_add, map_mul, Subgroup.coe_mul]

private theorem elt_zsmul {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (k : ℤ) (w : Fin 4 → ZMod 3) :
    elt θ (k • w) = elt θ w ^ k := by
  simp only [elt, ofAdd_zsmul, map_zpow, Subgroup.coe_zpow]

private theorem elt_zero {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) : elt θ 0 = 1 := by
  simp [elt]

private theorem exists_elt_eq {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) {g : G} (hg : g ∈ Bs) : ∃ w, elt θ w = g :=
  ⟨Multiplicative.toAdd (θ ⟨g, hg⟩), by simp [elt]⟩

private def coordMap {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (a : MulAut ↥Bs) :
    (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3) where
  toFun w := Multiplicative.toAdd (θ (a (θ.symm (Multiplicative.ofAdd w))))
  map_zero' := by simp
  map_add' w₁ w₂ := by simp [ofAdd_add]

private theorem coordMap_apply {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (a : MulAut ↥Bs) (w : Fin 4 → ZMod 3) :
    coordMap θ a w = Multiplicative.toAdd (θ (a (θ.symm (Multiplicative.ofAdd w)))) :=
  rfl

private theorem coordMap_mul {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (a b : MulAut ↥Bs) (w : Fin 4 → ZMod 3) :
    coordMap θ (a * b) w = coordMap θ a (coordMap θ b w) := by
  simp [coordMap_apply]

private theorem coordMap_one {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (w : Fin 4 → ZMod 3) : coordMap θ 1 w = w := by
  simp [coordMap_apply]

private theorem coordMap_injective {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (a : MulAut ↥Bs) :
    Function.Injective (coordMap θ a) := fun w₁ w₂ h => by
  simpa [coordMap_apply] using h

private theorem elt_coordMap {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) {a : MulAut ↥Bs} {n : G}
    (hn : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = n * b * n⁻¹) (w : Fin 4 → ZMod 3) :
    elt θ (coordMap θ a w) = n * elt θ w * n⁻¹ := by
  simp only [elt, coordMap_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply, hn]

private theorem coordMap_bil {G : Type} [Group G] {Bs : Subgroup G}
    {θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)} {a : MulAut ↥Bs}
    (ha : ∀ b c : ↥Bs, f4Bil3 (Multiplicative.toAdd (θ (a b))) (Multiplicative.toAdd (θ (a c))) =
      f4Bil3 (Multiplicative.toAdd (θ b)) (Multiplicative.toAdd (θ c)))
    (w₁ w₂ : Fin 4 → ZMod 3) :
    f4Bil3 (coordMap θ a w₁) (coordMap θ a w₂) = f4Bil3 w₁ w₂ := by
  simpa [coordMap_apply] using
    ha (θ.symm (Multiplicative.ofAdd w₁)) (θ.symm (Multiplicative.ofAdd w₂))

private theorem mem_f4Cross3_iff_of_isometry {g : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3)}
    (hg : ∀ a b, f4Bil3 (g a) (g b) = f4Bil3 a b) (hinj : Function.Injective g)
    {x : Fin 4 → ZMod 3} (hx : g x = x) (w : Fin 4 → ZMod 3) :
    g w ∈ f4Cross3 x ↔ w ∈ f4Cross3 x := by
  have hnx : g (-x) = -x := (map_neg g x).trans (congrArg _ hx)
  have e3 : f4Bil3 x (g w) = f4Bil3 x w := by
    have := hg x w
    rwa [hx] at this
  have e4 : f4Q3 (g w) = f4Q3 w := by rw [f4Q3, f4Q3, hg]
  simp only [f4Cross3, f4Frame3, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | h | ⟨h1, h2⟩)
    · exact Or.inl (hinj (h.trans hx.symm))
    · exact Or.inr (Or.inl (hinj (h.trans hnx.symm)))
    · exact Or.inr (Or.inr ⟨e3.symm.trans h1, e4.symm.trans h2⟩)
  · rintro (h | h | ⟨h1, h2⟩)
    · exact Or.inl ((congrArg g h).trans hx)
    · exact Or.inr (Or.inl ((congrArg g h).trans hnx))
    · exact Or.inr (Or.inr ⟨e3.trans h1, e4.trans h2⟩)

private def coordStab {G : Type} [Group G] {Bs : Subgroup G}
    (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)) (S : Finset (Fin 4 → ZMod 3)) :
    Subgroup (MulAut ↥Bs) where
  carrier := {a | ∀ w, coordMap θ a w ∈ S ↔ w ∈ S}
  mul_mem' := by
    intro a b ha hb w
    rw [coordMap_mul]
    exact (ha _).trans (hb w)
  one_mem' := by
    intro w
    rw [coordMap_one]
  inv_mem' := by
    intro a ha w
    have := ha (coordMap θ a⁻¹ w)
    rw [← coordMap_mul, mul_inv_cancel, coordMap_one] at this
    exact this.symm

private theorem ggAutomizer_le_coordStab {G : Type} [Group G] {Bs M : Subgroup G} {v : G}
    {θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)}
    (hθ : ∀ a ∈ ggAutomizer M Bs, ∀ b c : ↥Bs,
      f4Bil3 (Multiplicative.toAdd (θ (a b))) (Multiplicative.toAdd (θ (a c))) =
        f4Bil3 (Multiplicative.toAdd (θ b)) (Multiplicative.toAdd (θ c)))
    (hMv : M ≤ Subgroup.centralizer {v}) {v' : Fin 4 → ZMod 3} (hv' : elt θ v' = v) :
    ggAutomizer M Bs ≤ coordStab θ (f4Cross3 v') := by
  intro a ha w
  obtain ⟨n, hnM, -, hn⟩ := mem_ggAutomizer_iff.mp ha
  refine mem_f4Cross3_iff_of_isometry (coordMap_bil (hθ a ha)) (coordMap_injective θ a) ?_ w
  apply elt_injective θ
  rw [elt_coordMap θ hn, hv', Subgroup.mem_centralizer_singleton_iff.mp (hMv hnM),
    mul_inv_cancel_right]

private def polar3 (u w : Fin 3 → ZMod 3) : ZMod 3 :=
  (Two.weight (u + w) : ZMod 3) - Two.weight u - Two.weight w

private theorem weight_cases : ∀ u : Fin 3 → ZMod 3,
    u = 0 ∨ Two.weight u = 1 ∨ Two.weight u = 2 ∨ Two.weight u = 3 := by
  decide +kernel

private theorem signs_ne_zero :
    ∀ i j : Fin 3, Function.update (fun _ => (1 : ZMod 3)) i (-1) j ≠ 0 := by
  decide

private theorem signs_apply : ∀ (i : Fin 3) (u : Fin 3 → ZMod 3) (j : Fin 3),
    Function.update (fun _ => (1 : ZMod 3)) i (-1) j * u j = Function.update u i (-u i) j := by
  decide +kernel

private theorem exists_polar3_weight_two : ∀ u : Fin 3 → ZMod 3, (Two.weight u : ZMod 3) = 2 →
    ∃ i j k : Fin 3, ∃ s : ZMod 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ s ≠ 0 ∧
      polar3 u (Pi.single i 1) = 0 ∧ polar3 u (Pi.single j 1 + s • Pi.single k 1) = 0 := by
  decide +kernel

private theorem exists_polar3_weight_one : ∀ u : Fin 3 → ZMod 3, (Two.weight u : ZMod 3) = 1 →
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (u = Pi.single k 1 ∨ u = -Pi.single k 1) ∧
      ∀ w : Fin 3 → ZMod 3, polar3 u w = 0 →
        ∃ a b : Fin 3, w = (a : ℕ) • Pi.single i 1 + (b : ℕ) • Pi.single j 1 := by
  decide +kernel

private theorem zmod3_sq_eq_one : ∀ c : ZMod 3, c ≠ 0 → c ^ 2 = 1 := by decide

private theorem zmod3_add_self : ∀ q : ZMod 3, q + q = -q := by decide

private theorem zmod3_eq_two_of_neg : ∀ q w : ZMod 3, q ≠ 0 → -q = w * q → w = 2 := by decide

private theorem zmod3_eq_one_of_neg : ∀ q w : ZMod 3, q ≠ 0 → -q = w * -q → w = 1 := by decide

private theorem f4Bil3_smul_left (x : ZMod 3) (u w : Fin 4 → ZMod 3) :
    f4Bil3 (x • u) w = x * f4Bil3 u w := by
  simp only [f4Bil3, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
  ring

private theorem f4Bil3_smul_right (x : ZMod 3) (u w : Fin 4 → ZMod 3) :
    f4Bil3 u (x • w) = x * f4Bil3 u w := by
  rw [f4Bil3_comm, f4Bil3_smul_left, f4Bil3_comm]

private theorem f4Q3_smul (c : ZMod 3) (u : Fin 4 → ZMod 3) : f4Q3 (c • u) = c ^ 2 * f4Q3 u := by
  rw [f4Q3, f4Q3, f4Bil3_smul_left, f4Bil3_smul_right]
  ring

private theorem f4Q3_zero : f4Q3 0 = 0 := by decide

private theorem intCast_smul_eq_zsmul (k : ℤ) (x : Fin 4 → ZMod 3) :
    ((k : ℤ) : ZMod 3) • x = k • x := by
  funext i
  simp [zsmul_eq_mul]

private theorem f4Bil3_eq_polar3 (τ' : (Fin 3 → ZMod 3) →+ (Fin 4 → ZMod 3))
    {v' : Fin 4 → ZMod 3}
    (hQτ : ∀ u, f4Q3 (τ' u) = (Two.weight u : ZMod 3) * f4Q3 v') (u w : Fin 3 → ZMod 3) :
    f4Bil3 (τ' u) (τ' w) = polar3 u w * f4Q3 v' := by
  have h := f4Q3_add (τ' u) (τ' w)
  rw [← map_add, hQτ (u + w), hQτ u, hQτ w] at h
  rw [polar3, sub_mul, sub_mul, h]
  ring

private theorem false_of_simple_of_solvable_centralizer {C : Type*} [Group C]
    (M : Subgroup C) [M.Normal] (R : Subgroup C)
    (hsol : Group.IsSolvable ↥(M ⊓ Subgroup.centralizer (R : Set C)))
    (X : Subgroup C) (hXR : X ≤ Subgroup.centralizer (R : Set C))
    [IsSimpleGroup ↥X] (hXna : ∃ a b : ↥X, a * b ≠ b * a)
    (m : C) (hmX : m ∈ X) (hmM : m ∈ M) (hm1 : m ≠ 1) : False := by
  have hXM : X ≤ M := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf X) with h | h
    · exfalso
      have hm : (⟨m, hmX⟩ : ↥X) ∈ M.subgroupOf X := hmM
      rw [h, Subgroup.mem_bot] at hm
      exact hm1 (congrArg Subtype.val hm)
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥X) ∈ M.subgroupOf X := h ▸ Subgroup.mem_top _
      exact hx'
  have := hsol
  have : Group.IsSolvable ↥X :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (le_inf hXM hXR))
  obtain ⟨a, b, hab⟩ := hXna
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)

private theorem exists_coords_of_endCoords {G : Type} [Group G] {Bs M : Subgroup G} {v : G}
    {τ : Multiplicative (Fin 3 → ZMod 3) →* G} (hcard : Nat.card ↥Bs = 3 ^ 4)
    {θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)}
    (hθ : ∀ a ∈ ggAutomizer M Bs, ∀ b c : ↥Bs,
      f4Bil3 (Multiplicative.toAdd (θ (a b))) (Multiplicative.toAdd (θ (a c))) =
        f4Bil3 (Multiplicative.toAdd (θ b)) (Multiplicative.toAdd (θ c)))
    (hMv : M ≤ Subgroup.centralizer {v}) (hE : GGOmegaTwoEndCoords Bs M v τ)
    {v' : Fin 4 → ZMod 3} (hv' : elt θ v' = v) :
    v ∉ M ∧ ∃ τ' : (Fin 3 → ZMod 3) →+ (Fin 4 → ZMod 3),
      (∀ u, elt θ (τ' u) = τ (Multiplicative.ofAdd u)) ∧
      f4Q3 v' ≠ 0 ∧ (∀ u, f4Bil3 v' (τ' u) = 0) ∧
      (∀ u, f4Q3 (τ' u) = (Two.weight u : ZMod 3) * f4Q3 v') ∧
      ∀ w, f4Bil3 v' w = 0 → ∃ u, τ' u = w := by
  obtain ⟨hinj, hrange, hsplit, hsp, -⟩ := hE
  have hmemτ : ∀ u, τ u ∈ Bs ⊓ M := fun u => hrange ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩
  have hvM : v ∉ M := by
    intro hvM
    have h1 : Bs ⊓ M = Bs := le_antisymm inf_le_left fun b hb => by
      obtain ⟨k, t, ht, rfl⟩ := hsplit b hb
      exact ⟨hb, M.mul_mem (M.zpow_mem hvM k) ht.2⟩
    have h2 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [hrange, h1, hcard] at h2
    simp [Nat.card_eq_fintype_card] at h2
  refine ⟨hvM, ?_⟩
  choose f hf using fun u : Fin 3 → ZMod 3 => exists_elt_eq θ (hmemτ (Multiplicative.ofAdd u)).1
  let τ' : (Fin 3 → ZMod 3) →+ (Fin 4 → ZMod 3) :=
    AddMonoidHom.mk' f fun u₁ u₂ => elt_injective θ (by
      rw [elt_add, hf, hf, hf, ofAdd_add, map_mul])
  have hτ' : ∀ u, elt θ (τ' u) = τ (Multiplicative.ofAdd u) := hf
  have hτinj : Function.Injective τ' := fun u₁ u₂ h => by
    have := congrArg (elt θ) h
    rw [hτ', hτ'] at this
    exact Multiplicative.ofAdd.injective (hinj this)
  have hvτ : v' ∉ Set.range τ' := by
    rintro ⟨u, hu⟩
    apply hvM
    rw [← hv', ← hu, hτ']
    exact (hmemτ _).2
  have hreal : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ g : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3),
        (∀ a b, f4Bil3 (g a) (g b) = f4Bil3 a b) ∧ g v' = v' ∧
        ∀ u, g (τ' u) = τ' (fun i => ε i * u (σ i)) := by
    intro σ ε hε
    obtain ⟨n, hnM, hnN, hn⟩ := hsp σ ε hε
    refine ⟨coordMap θ (ggConjAut Bs hnN),
      coordMap_bil (hθ _ (ggConjAut_mem_ggAutomizer hnM hnN)), ?_, fun u => ?_⟩
    · apply elt_injective θ
      rw [elt_coordMap θ (ggConjAut_apply Bs hnN), hv',
        Subgroup.mem_centralizer_singleton_iff.mp (hMv hnM), mul_inv_cancel_right]
    · apply elt_injective θ
      rw [elt_coordMap θ (ggConjAut_apply Bs hnN), hτ', hτ', hn, toAdd_ofAdd]
  have hsign : ∀ i : Fin 3, ∃ g : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3),
      (∀ a b, f4Bil3 (g a) (g b) = f4Bil3 a b) ∧
      g v' = v' ∧ ∀ u, g (τ' u) = τ' (Function.update u i (-u i)) := by
    intro i
    obtain ⟨g, hg, hgv, hgτ⟩ := hreal 1 _ (signs_ne_zero i)
    refine ⟨g, hg, hgv, fun u => ?_⟩
    rw [hgτ]
    congr 1
    funext j
    rw [Equiv.Perm.one_apply, signs_apply]
  have hswap : ∀ i j : Fin 3, ∃ g : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3),
      (∀ a b, f4Bil3 (g a) (g b) = f4Bil3 a b) ∧
      g v' = v' ∧ ∀ u, g (τ' u) = τ' (u ∘ Equiv.swap i j) := by
    intro i j
    obtain ⟨g, hg, hgv, hgτ⟩ := hreal (Equiv.swap i j) (fun _ => 1) (fun _ => one_ne_zero)
    refine ⟨g, hg, hgv, fun u => ?_⟩
    rw [hgτ]
    congr 1
    funext k
    simp
  obtain ⟨hQv, hBv, hQτ⟩ := f4Q3_tau_of_signedPerms v' τ' hτinj hvτ hsign hswap
  refine ⟨τ', hτ', hQv, hBv, fun u => hQτ u, fun w hw => ?_⟩
  have hv0 : v' ≠ 0 := fun h => hQv (by rw [h, f4Q3_zero])
  have himage : Finset.univ.image τ' =
      Finset.univ.filter fun w : Fin 4 → ZMod 3 => f4Bil3 v' w = 0 := by
    refine Finset.eq_of_subset_of_card_le (fun w hw => ?_) ?_
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBv u⟩
    · rw [card_f4Perp3 v' hv0, Finset.card_image_of_injective _ hτinj]
      decide
  have hw' : w ∈ Finset.univ.image τ' := by
    rw [himage]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
  obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hw'
  exact ⟨u, hu⟩

theorem false_of_ggOmegaTwoEndCoords {G : Type} [Group G] [Finite G] {Bs L K D J : Subgroup G}
    {x y : G} (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcard : Nat.card ↥Bs = 3 ^ 4)
    (hW : GGWeylOfType 3 CoxeterMatrix.F₄
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer {x}) (hKy : K ≤ Subgroup.centralizer {y})
    {τx τy : Multiplicative (Fin 3 → ZMod 3) →* G}
    (hEx : GGOmegaTwoEndCoords Bs L x τx) (hEy : GGOmegaTwoEndCoords Bs K y τy)
    (hLn : (L.subgroupOf (Subgroup.centralizer {x})).Normal)
    (hxD : x ∈ D) (hyD : y ∈ D) (hDcard : Nat.card ↥D = 9)
    (hyx : y ∉ Subgroup.zpowers x)
    (hJL : J ≤ L) (hJD : J ≤ Subgroup.centralizer (D : Set G)) (hJJ : ⁅J, J⁆ = J)
    (hJbot : J ≠ ⊥) (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) = D) : False := by
  obtain ⟨θ, hθ, hmove⟩ := exists_f4Coords_of_ggWeylOfType_F4 hBs hcard hW
  have hθL := fun a (ha : a ∈ ggAutomizer L Bs) => hθ a (Subgroup.mem_sup_left ha)
  have hθK := fun a (ha : a ∈ ggAutomizer K Bs) => hθ a (Subgroup.mem_sup_right ha)
  obtain ⟨x', hx'⟩ := exists_elt_eq θ hxBs
  obtain ⟨y', hy'⟩ := exists_elt_eq θ hyBs
  obtain ⟨hxL, τx', hτx', hQx, hBx, hQτx, hperpx⟩ :=
    exists_coords_of_endCoords hcard hθL hLx hEx hx'
  obtain ⟨-, τy', hτy', hQy, -, hQτy, hperpy⟩ := exists_coords_of_endCoords hcard hθK hKy hEy hy'
  obtain ⟨-, hrx, hsplitx, -, hw3, hw2, -, hmix⟩ := hEx
  obtain ⟨-, hry, hsplity, -, -, -, hpair, -⟩ := hEy
  obtain ⟨k, z, hzT, hyz⟩ := hsplitx y hyBs
  have hzD : z ∈ D := by
    have : z = x ^ (-k) * y := by rw [hyz, zpow_neg, inv_mul_cancel_left]
    rw [this]
    exact D.mul_mem (D.zpow_mem hxD _) hyD
  obtain ⟨uz, huz⟩ : ∃ uz, τx (Multiplicative.ofAdd uz) = z := by
    obtain ⟨u, hu⟩ : z ∈ τx.range := hrx ▸ hzT
    exact ⟨Multiplicative.toAdd u, hu⟩
  have hJz : J ≤ L ⊓ Subgroup.centralizer {τx (Multiplicative.ofAdd uz)} := fun g hg => by
    refine Subgroup.mem_inf.mpr ⟨hJL hg, ?_⟩
    rw [huz, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hJD hg)) z hzD).symm
  have hwz : Two.weight uz = 1 := by
    rcases weight_cases uz with h0 | h1 | h2 | h3
    · exfalso
      apply hyx
      rw [hyz, ← huz, h0, ofAdd_zero, map_one, mul_one]
      exact Subgroup.zpow_mem_zpowers x k
    · exact h1
    · exfalso
      have h9 := hw2 uz h2 J hJz hJJ hJbot
      rw [hrx, inf_assoc, inf_left_comm, hCJ] at h9
      have hLD : L ⊓ D = D := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h9, hDcard])
      exact hxL (hLD.symm ▸ hxD : x ∈ L ⊓ D).1
    · exact absurd (CFSG.Quasithin.J4ZCent.eq_bot_of_perfect_of_le_solvable (hw3 uz h3) hJz hJJ)
        hJbot
  set z' := τx' uz with hz'
  have hz'el : elt θ z' = z := by rw [hz', hτx', huz]
  have hzQ : f4Q3 z' = f4Q3 x' := by rw [hz', hQτx, hwz, Nat.cast_one, one_mul]
  have hzB : f4Bil3 x' z' = 0 := hBx uz
  have hzF : z' ∈ f4Frame3 x' := by
    simp only [f4Frame3, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hzB, hzQ⟩
  have hy'eq : y' = ((k : ℤ) : ZMod 3) • x' + z' := by
    rw [intCast_smul_eq_zsmul]
    exact elt_injective θ (by rw [elt_add, elt_zsmul, hx', hz'el, hy', hyz])
  have hc : ((k : ℤ) : ZMod 3) ≠ 0 := by
    intro hc
    have hyF : y' ∈ f4Frame3 x' := by rw [hy'eq, hc, zero_smul, zero_add]; exact hzF
    have hcross : f4Cross3 y' = f4Cross3 x' := f4Cross3_eq_of_mem_f4Frame3 x' hQx y' hyF
    have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ coordStab θ (f4Cross3 x') :=
      sup_le (ggAutomizer_le_coordStab hθL hLx hx')
        (hcross ▸ ggAutomizer_le_coordStab hθK hKy hy')
    obtain ⟨a, ha, w, hw, hwa⟩ := hmove x' hQx
    exact hwa (((hle ha) w).mpr hw)
  have hQy' : f4Q3 y' = -f4Q3 x' := by
    rw [hy'eq, f4Q3_add, f4Q3_smul, f4Bil3_smul_left, zmod3_sq_eq_one _ hc, one_mul, hzQ, hzB,
      mul_zero, add_zero, zmod3_add_self]
  obtain ⟨m', hxm, hzm, hQm⟩ := exists_f4Witness x' hQx z' hzF
  have hym : f4Bil3 y' m' = 0 := by
    rw [hy'eq, f4Bil3_add_left, f4Bil3_smul_left, hxm, hzm, mul_zero, add_zero]
  obtain ⟨um, hum⟩ := hperpx m' hxm
  obtain ⟨um', hum'⟩ := hperpy m' hym
  have hwm : (Two.weight um : ZMod 3) = 2 := by
    have h := hQτx um
    rw [hum, hQm] at h
    exact zmod3_eq_two_of_neg _ _ hQx h
  have hwm' : (Two.weight um' : ZMod 3) = 1 := by
    have h := hQτy um'
    rw [hum', hQm, hQy'] at h
    exact zmod3_eq_one_of_neg _ _ hQx h
  obtain ⟨i, j, k₀, s, hij, hik, hjk, hs, hpi, hpjk⟩ := exists_polar3_weight_two um hwm
  obtain ⟨i', j', k', hij', hik', hjk', hum'k, hspan⟩ := exists_polar3_weight_one um' hwm'
  obtain ⟨X, hXK, hXs, hXna, hXk⟩ := hpair i' j' k' hij' hik' hjk'
  have hyX : y ∈ Subgroup.centralizer (X : Set G) := Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKy (hXK hh).1)
  have hiX : τy (Multiplicative.ofAdd (Pi.single i' 1)) ∈ Subgroup.centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      ((Subgroup.mem_centralizer_iff.mp (hXK hh).2) _ (Set.mem_insert _ _)).symm
  have hjX : τy (Multiplicative.ofAdd (Pi.single j' 1)) ∈ Subgroup.centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      ((Subgroup.mem_centralizer_iff.mp (hXK hh).2) _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))).symm
  have hcent : ∀ w, f4Bil3 m' w = 0 → elt θ w ∈ Subgroup.centralizer (X : Set G) := by
    intro w hw
    obtain ⟨k₂, t, ht, hwt⟩ := hsplity (elt θ w) (elt_mem θ w)
    obtain ⟨u, hu⟩ : ∃ u, τy (Multiplicative.ofAdd u) = t := by
      obtain ⟨u, hu⟩ : t ∈ τy.range := hry ▸ ht
      exact ⟨Multiplicative.toAdd u, hu⟩
    have hweq : w = ((k₂ : ℤ) : ZMod 3) • y' + τy' u := by
      rw [intCast_smul_eq_zsmul]
      exact elt_injective θ (by rw [elt_add, elt_zsmul, hy', hτy', hu, hwt])
    have hpol : polar3 um' u = 0 := by
      have h1 := f4Bil3_eq_polar3 τy' hQτy um' u
      rw [hum'] at h1
      have h2 : f4Bil3 m' (τy' u) = 0 := by
        rw [hweq, f4Bil3_add_right, f4Bil3_smul_right, f4Bil3_comm m' y', hym, mul_zero,
          zero_add] at hw
        exact hw
      rw [h2] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hQy
    obtain ⟨a, b, hab⟩ := hspan u hpol
    have ht' : t = τy (Multiplicative.ofAdd (Pi.single i' 1)) ^ (a : ℕ) *
        τy (Multiplicative.ofAdd (Pi.single j' 1)) ^ (b : ℕ) := by
      rw [← hu, hab, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
    rw [hwt, ht']
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hyX k₂)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hiX _) (Subgroup.pow_mem _ hjX _))
  have hpolx : ∀ u, polar3 um u = 0 → τx (Multiplicative.ofAdd u) ∈
      Subgroup.centralizer (X : Set G) := fun u hu => by
    rw [← hτx']
    exact hcent _ (by rw [← hum, f4Bil3_eq_polar3 τx' hQτx, hu, zero_mul])
  have hr₁X := hpolx _ hpi
  have hr₂X := hpolx _ hpjk
  have hxX : x ∈ Subgroup.centralizer (X : Set G) := by
    rw [← hx']
    exact hcent x' (by rw [f4Bil3_comm, hxm])
  have hmemL : ∀ u, τx (Multiplicative.ofAdd u) ∈ L := fun u =>
    (hrx ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩ : τx (Multiplicative.ofAdd u) ∈ Bs ⊓ L).2
  have hm1 : elt θ m' ≠ 1 := by
    rw [← elt_zero θ]
    intro h
    have h0 := elt_injective θ h
    rw [h0, f4Q3_zero] at hQm
    exact hQx (neg_eq_zero.mp hQm.symm)
  have hmX : elt θ m' ∈ X := by
    rw [← hum', hτy']
    rcases hum'k with h | h
    · rw [h]
      exact hXk
    · have key : τy (Multiplicative.ofAdd (-Pi.single k' 1)) =
          (τy (Multiplicative.ofAdd (Pi.single k' 1)))⁻¹ :=
        map_inv τy (Multiplicative.ofAdd (Pi.single k' 1))
      rw [h, key]
      exact X.inv_mem hXk
  have hmL : elt θ m' ∈ L := by
    rw [← hum, hτx']
    exact hmemL um
  have hXC : X ≤ Subgroup.centralizer {x} := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hxX) h hh)
  have : (L.subgroupOf (Subgroup.centralizer {x})).Normal := hLn
  have : IsSimpleGroup ↥X := hXs
  have : Nontrivial ↥(X.subgroupOf (Subgroup.centralizer {x})) :=
    (Subgroup.subgroupOfEquivOfLe hXC).toEquiv.nontrivial
  have : IsSimpleGroup ↥(X.subgroupOf (Subgroup.centralizer {x})) :=
    IsSimpleGroup.isSimpleGroup_of_surjective (Subgroup.subgroupOfEquivOfLe hXC).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXC).symm.surjective
  refine false_of_simple_of_solvable_centralizer
    (L.subgroupOf (Subgroup.centralizer {x}))
    (Subgroup.closure {⟨_, hLx (hmemL (Pi.single i 1))⟩,
      ⟨_, hLx (hmemL (Pi.single j 1 + s • Pi.single k₀ 1))⟩}) ?_
    (X.subgroupOf (Subgroup.centralizer {x})) ?_ ?_ ⟨elt θ m', hXC hmX⟩ hmX hmL
    (fun h => hm1 (congrArg Subtype.val h))
  · have := hmix i j k₀ hij hik hjk s hs
    rw [Subgroup.centralizer_closure]
    refine solvable_of_solvable_injective (f := MonoidHom.codRestrict
      ((Subgroup.centralizer {x}).subtype.comp (Subgroup.subtype _))
      (L ⊓ Subgroup.centralizer {τx (Multiplicative.ofAdd (Pi.single i 1)),
        τx (Multiplicative.ofAdd (Pi.single j 1 + s • Pi.single k₀ 1))}) fun g => ?_) ?_
    · obtain ⟨hgL, hgc⟩ := Subgroup.mem_inf.mp g.2
      refine Subgroup.mem_inf.mpr ⟨hgL, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ (rfl | rfl)
      · exact congrArg Subtype.val
          ((Subgroup.mem_centralizer_iff.mp hgc) _ (Set.mem_insert _ _))
      · exact congrArg Subtype.val
          ((Subgroup.mem_centralizer_iff.mp hgc) _ (Set.mem_insert_of_mem _ rfl))
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  · rw [Subgroup.centralizer_closure]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ (rfl | rfl)
    · exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hr₁X) g hg).symm
    · exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hr₂X) g hg).symm
  · obtain ⟨a, b, hab⟩ := hXna
    refine ⟨(Subgroup.subgroupOfEquivOfLe hXC).symm a,
      (Subgroup.subgroupOfEquivOfLe hXC).symm b, fun h => hab ?_⟩
    simpa using congrArg (Subgroup.subgroupOfEquivOfLe hXC) h

end CFSG.StandardType
