module

import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof15Res7

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem map_inf_centralizer_eq_inf {X W : Subgroup G} {d : G} (hWX : W ≤ X)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hdX : d ∈ X) (hd3 : d ^ 3 = 1) :
    ((W ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf X).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) =
      (W.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) ⊓
        Subgroup.centralizer
          ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨d, hdX⟩} :
            Set (↥X ⧸ aschbacherSolvableCore 3 ↥X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set π := QuotientGroup.mk' θ with hπ
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  obtain ⟨-, hθ3⟩ := Sec6.theta_solvable_and_not_dvd X
  have hWθ : W ≤ Subgroup.normalizer (θX : Set G) := hWX.trans (Sec6.le_normalizer_theta X)
  have hZW : Subgroup.zpowers d ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.mpr hdW
  have hZX : Subgroup.zpowers d ≤ X := Subgroup.zpowers_le.mpr hdX
  have hZ3 : IsPGroup 3 (Subgroup.zpowers d) := by
    rintro ⟨b, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hd3, one_zpow]
  have hπmk : ∀ y : G, ∀ hy : y ∈ X, π ⟨y, hy⟩ = ((⟨y, hy⟩ : ↥X) : ↥X ⧸ θ) := fun _ _ => rfl
  refine le_antisymm (le_inf ?_ ?_) ?_
  · exact Subgroup.map_mono fun y hy =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).1
  · rintro _ ⟨x, hx, rfl⟩
    have hxd : (x : G) * d = d * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hx).2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxd
  set N := θX.subgroupOf W with hN
  have hNn : N.Normal := by
    constructor
    intro n hn w
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hWθ w.2) n).mp hn
  let α : Subgroup.zpowers d →* MulAut W := W.normalizerMonoidHom.comp (Subgroup.inclusion hZW)
  have hα : ∀ (b : Subgroup.zpowers d) (w : W), ((α b w : W) : G) = b * w * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hNα : ∀ b : Subgroup.zpowers d, ∀ n ∈ N, α b n ∈ N := by
    intro b n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hα]
    exact (Subgroup.mem_normalizer_iff.mp
      (Sec6.le_normalizer_theta X (hZX b.2)) _).mp hn
  have hcop : ¬ 3 ∣ Nat.card N := by
    intro h3
    apply hθ3
    have h1 : Nat.card N = Nat.card (θX ⊓ W : Subgroup G) := by
      rw [hN, ← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : θX ⊓ W ≤ W)).toEquiv
    rw [h1] at h3
    exact h3.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hZ3 α N hNα hcop
  rintro _ ⟨⟨x, hxW, rfl⟩, hqC⟩
  have hxW' : (x : G) ∈ W := Subgroup.mem_subgroupOf.mp hxW
  have hqC' : π x * π ⟨d, hdX⟩ = π ⟨d, hdX⟩ * π x :=
    Subgroup.mem_centralizer_singleton_iff.mp hqC
  have hfix : ((⟨x, hxW'⟩ : W) : W ⧸ N) ∈
      {q : W ⧸ N | ∀ b, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
        α N hNα b q = q} := by
    intro b
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    set b' : ↥X := ⟨b, hZX b.2⟩ with hb'
    have hb'k : b' = (⟨d, hdX⟩ : ↥X) ^ k := Subtype.ext (by simp [hb', hk])
    have hcomm : π b' * π x = π x * π b' := by
      rw [hb'k, map_zpow]
      exact (Commute.zpow_left hqC'.symm k)
    set e : ↥X := b' * x⁻¹ * b'⁻¹ * x with he
    have he1 : π e = 1 := by
      have hc : Commute (π b') (π x) := hcomm
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, hc.inv_right.eq]
      group
    have heθ : e ∈ θ := (QuotientGroup.eq_one_iff e).mp he1
    have hval : ((α b ⟨x, hxW'⟩ : W)⁻¹ * ⟨x, hxW'⟩ : W).val = (e : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, he]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb']
      group
    rw [hval]
    exact ⟨e, heθ, rfl⟩
  rw [hlift] at hfix
  obtain ⟨c₀, hc₀, hc₀w⟩ := hfix
  have hc₀d : (c₀ : G) ∈ Subgroup.centralizer ({d} : Set G) := by
    have h := congrArg Subtype.val (hc₀ ⟨d, Subgroup.mem_zpowers d⟩)
    rw [hα] at h
    change d * (c₀ : G) * d⁻¹ = c₀ at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c₀ : G) * d = d * c₀ * d⁻¹ * d := by rw [h]
      _ = d * c₀ := by group
  refine ⟨⟨c₀, hWX c₀.2⟩, Subgroup.mem_subgroupOf.mpr ⟨c₀.2, hc₀d⟩, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc₀w
  obtain ⟨t, ht, hte⟩ := hc₀w
  have hte' : (t : G) = (c₀ : G)⁻¹ * x := by simpa using hte
  have he : (⟨c₀, hWX c₀.2⟩ : ↥X)⁻¹ * x = t := by
    apply Subtype.ext
    rw [hte', Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he]
  exact ht

omit [Finite G] in
theorem pCore_two_eq_ker {K M : Type*} [Group K] [Group M] (ρ : K →* M)
    (hρ : Function.Surjective ρ) (hker : IsPGroup 2 ρ.ker) (hM : CFSG.pCore 2 M = ⊥) :
    CFSG.pCore 2 K = ρ.ker := by
  apply le_antisymm
  · intro x hx
    have hnorm : ((CFSG.pCore 2 K).map ρ).Normal :=
      Subgroup.Normal.map inferInstance ρ hρ
    have hp : IsPGroup 2 ((CFSG.pCore 2 K).map ρ) := CFSG.pCore_isPGroup.map ρ
    have hle : (CFSG.pCore 2 K).map ρ ≤ CFSG.pCore 2 M := le_sSup ⟨hnorm, hp⟩
    rw [hM] at hle
    have : ρ x ∈ (CFSG.pCore 2 K).map ρ := ⟨x, hx, rfl⟩
    simpa using hle this
  · exact le_sSup ⟨inferInstance, hker⟩

omit [Finite G] in
theorem nonempty_quot_pCore_two_equiv {K M : Type*} [Group K] [Group M] (ρ : K →* M)
    (hρ : Function.Surjective ρ) (hker : IsPGroup 2 ρ.ker) (hM : CFSG.pCore 2 M = ⊥) :
    Nonempty (K ⧸ CFSG.pCore 2 K ≃* M) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (pCore_two_eq_ker ρ hρ hker hM)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

omit [Finite G] in
theorem map_subtype_subgroupOf_map {K L : Subgroup G} (hKL : K ≤ L) {Q : Type*} [Group Q]
    (π : ↥L →* Q) (S : Subgroup ↥K) :
    ((S.map K.subtype).subgroupOf L).map π = S.map (π.comp (Subgroup.inclusion hKL)) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_subgroupOf.mp hx
    refine ⟨s, hs, ?_⟩
    have : Subgroup.inclusion hKL s = x := Subtype.ext hsx
    rw [MonoidHom.comp_apply, this]
  · rintro ⟨s, hs, rfl⟩
    exact ⟨Subgroup.inclusion hKL s, Subgroup.mem_subgroupOf.mpr ⟨s, hs, rfl⟩, rfl⟩

theorem map_inSubgroup_perfectResidual_subgroupOf {K L : Subgroup G} (hKL : K ≤ L) {Q : Type*}
    [Group Q] [Finite Q] (π : ↥L →* Q) :
    ((inSubgroup perfectResidual K).subgroupOf L).map π =
      inSubgroup perfectResidual ((K.subgroupOf L).map π) := by
  set K' := (K.subgroupOf L).map π with hK'
  have hmem : ∀ x : ↥K, (π.comp (Subgroup.inclusion hKL)) x ∈ K' := fun x =>
    ⟨Subgroup.inclusion hKL x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  set ψ : ↥K →* ↥K' := (π.comp (Subgroup.inclusion hKL)).codRestrict K' hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hcomp : π.comp (Subgroup.inclusion hKL) = K'.subtype.comp ψ := rfl
  have h := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψs
  rw [inSubgroup, map_subtype_subgroupOf_map hKL, hcomp, ← Subgroup.map_map, inSubgroup]
  exact congrArg (Subgroup.map K'.subtype) h

theorem map_oPrimeResidualOf_subgroupOf {K L : Subgroup G} (hKL : K ≤ L) {Q : Type*}
    [Group Q] (π : ↥L →* Q) :
    ((oPrimeResidualOf 3 K).subgroupOf L).map π = oPrimeResidualOf 3 ((K.subgroupOf L).map π) := by
  set K' := (K.subgroupOf L).map π with hK'
  have hmem : ∀ x : ↥K, (π.comp (Subgroup.inclusion hKL)) x ∈ K' := fun x =>
    ⟨Subgroup.inclusion hKL x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  set ψ : ↥K →* ↥K' := (π.comp (Subgroup.inclusion hKL)).codRestrict K' hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hcomp : π.comp (Subgroup.inclusion hKL) = K'.subtype.comp ψ := rfl
  have h := Sec17.Proof171Steps.map_oPrimeResidual_three ψ hψs
  rw [oPrimeResidualOf, map_subtype_subgroupOf_map hKL, hcomp, ← Subgroup.map_map,
    oPrimeResidualOf]
  exact congrArg (Subgroup.map K'.subtype) h

end CFSG.RankThree.PartTwo.Sec15.Proof15Res7
