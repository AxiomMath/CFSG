module

public import CFSG.RankThree.PartTwo.Sec15.Item1424ProofSteps
import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1424Steps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem map_inf_centralizer_of_not_dvd_ker {Γ M : Type*} [Group Γ] [Finite Γ] [Group M]
    (f : Γ →* M) {r : ℕ} (hr : r.Prime) {B X : Subgroup Γ} (hB : IsPGroup r B)
    (hBX : B ≤ Subgroup.normalizer (X : Set Γ)) (hk : ¬ r ∣ Nat.card f.ker) :
    (X ⊓ Subgroup.centralizer (B : Set Γ)).map f =
      X.map f ⊓ Subgroup.centralizer ((B.map f : Subgroup M) : Set M) := by
  have : Fact r.Prime := ⟨hr⟩
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction B X hBX
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro z ⟨b, hb, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp hx.2 b hb)
  · intro y hy
    obtain ⟨x, hxX, hxy⟩ := hy.1
    let ρ := f.domRestrict X
    let fibre : SubMulAction B X :=
      ⟨{z | ρ z = y}, by
        intro b z hz
        change f (b.val * z.val * b.val⁻¹) = y
        rw [map_mul, map_mul, map_inv]
        change f b.val * ρ z * (f b.val)⁻¹ = y
        rw [hz]
        have hc := Subgroup.mem_centralizer_iff.mp hy.2 (f b.val)
          (Subgroup.mem_map_of_mem f b.property)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]⟩
    have hfib : Nat.card fibre = Nat.card ρ.ker := by
      have hfeq : {z : X | ρ z = y} = ρ ⁻¹' {ρ (⟨x, hxX⟩ : X)} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        change (ρ z = y) ↔ ρ z = f x
        rw [hxy]
      exact (Nat.card_congr (Set.equivOfEq hfeq)).trans
        (Nat.card_congr (ρ.fiberEquivKer (⟨x, hxX⟩ : X)))
    have hkdvd : Nat.card ρ.ker ∣ Nat.card f.ker := by
      have hle : ρ.ker.map X.subtype ≤ f.ker := by
        rintro _ ⟨z, hz, rfl⟩
        exact hz
      have := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective X.subtype_injective] at this
    have hnd : ¬ r ∣ Nat.card fibre := by
      rw [hfib]
      exact fun h => hk (h.trans hkdvd)
    obtain ⟨z, hfix⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card fibre hnd
    refine ⟨z.val.val, ⟨z.val.property, ?_⟩, z.property⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    have heq := congrArg (fun w : fibre => w.val.val) (hfix (⟨b, hb⟩ : B))
    change b * z.val.val * b⁻¹ = z.val.val at heq
    exact mul_inv_eq_iff_eq_mul.mp heq

theorem map_le_normalizer_map {Γ M : Type*} [Group Γ] [Group M] (f : Γ →* M)
    {X N : Subgroup Γ} (h : X ≤ Subgroup.normalizer (N : Set Γ)) :
    X.map f ≤ Subgroup.normalizer ((N.map f : Subgroup M) : Set M) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨x * n * x⁻¹, (Subgroup.mem_normalizer_iff.mp (h hx) n).mp hn, by simp⟩
  · rintro ⟨n, hn, hnm⟩
    refine ⟨x⁻¹ * n * x, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem (h hx)) n).mp hn
      simpa using this
    · rw [map_mul, map_mul, map_inv, hnm]
      group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_le_sup (A Y : Subgroup G) : CFSG.Open.pCoreOf 2 Y ≤ A ⊔ Y :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans le_sup_right

omit [Finite G] in
theorem card_ker_eq {A Y : Subgroup G} {M : Type*} [Group M] {f : ↥(A ⊔ Y) →* M}
    (hker : f.ker = kerAO2 A Y) : Nat.card f.ker = Nat.card (CFSG.Open.pCoreOf 2 Y) := by
  rw [hker, kerAO2]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le_sup A Y)).toEquiv

theorem not_three_dvd_card_ker {A Y : Subgroup G} {M : Type*} [Group M] {f : ↥(A ⊔ Y) →* M}
    (hker : f.ker = kerAO2 A Y) : ¬ 3 ∣ Nat.card f.ker := by
  rw [card_ker_eq hker]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  rw [hk]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem inf_pCoreOf_eq_bot_of_coprime {Y X : Subgroup G} (hX : Nat.Coprime 2 (Nat.card X)) :
    X ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk]
  exact Nat.Coprime.pow_right k hX.symm

omit [Finite G] in
theorem card_map_of_inf_pCoreOf_eq_bot {A Y : Subgroup G} {M : Type*} [Group M]
    {f : ↥(A ⊔ Y) →* M} (hker : f.ker = kerAO2 A Y) {X : Subgroup G} (hXY : X ≤ A ⊔ Y)
    (hX : X ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    Nat.card ((X.subgroupOf (A ⊔ Y)).map f) = Nat.card X := by
  have hinj : Function.Injective (f.comp (X.subgroupOf (A ⊔ Y)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : f x = 1 := hx
    have hxk : (x : ↥(A ⊔ Y)) ∈ f.ker := hx1
    rw [hker, kerAO2, Subgroup.mem_subgroupOf] at hxk
    have hxX : ((x : ↥(A ⊔ Y)) : G) ∈ X := Subgroup.mem_subgroupOf.mp x.2
    have hmem : ((x : ↥(A ⊔ Y)) : G) ∈ X ⊓ CFSG.Open.pCoreOf 2 Y := ⟨hxX, hxk⟩
    rw [hX, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext (Subtype.ext hmem))
  have h1 : (X.subgroupOf (A ⊔ Y)).map f = (f.comp (X.subgroupOf (A ⊔ Y)).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv]

omit [Finite G] in
theorem eq_of_map_eq {A Y : Subgroup G} {M : Type*} [Group M] {f : ↥(A ⊔ Y) →* M}
    (hker : f.ker = kerAO2 A Y) {X : Subgroup G} (hX : X ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)
    {x y : ↥(A ⊔ Y)} (hx : (x : G) ∈ X) (hy : (y : G) ∈ X) (hxy : f x = f y) : x = y := by
  have hk : x * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  rw [hker, kerAO2, Subgroup.mem_subgroupOf] at hk
  have hmem : ((x * y⁻¹ : ↥(A ⊔ Y)) : G) ∈ X ⊓ CFSG.Open.pCoreOf 2 Y :=
    ⟨by simpa using mul_mem hx (inv_mem hy), hk⟩
  rw [hX, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp (Subtype.ext hmem)

omit [Finite G] in
theorem le_map_comap_of_map_le {H X : Subgroup G} {M : Type*} [Group M] (f : ↥H →* M)
    (J : Subgroup M) (hXH : X ≤ H) (h : (X.subgroupOf H).map f ≤ J) :
    X ≤ (J.comap f).map H.subtype := by
  intro x hx
  exact ⟨⟨x, hXH hx⟩, h ⟨⟨x, hXH hx⟩, hx, rfl⟩, rfl⟩

omit [Finite G] in
theorem map_mem_of_le_map_comap {H X : Subgroup G} {M : Type*} [Group M] (f : ↥H →* M)
    {J : Subgroup M} (hXJ : X ≤ (J.comap f).map H.subtype) {x : ↥H} (hx : (x : G) ∈ X) :
    f x ∈ J := by
  obtain ⟨γ, hγ, hγx⟩ := hXJ hx
  have : γ = x := Subtype.ext hγx
  rw [← this]
  exact hγ

omit [Finite G] in
theorem map_le_of_le_map_comap {H X : Subgroup G} {M : Type*} [Group M] (f : ↥H →* M)
    {J : Subgroup M} (hXJ : X ≤ (J.comap f).map H.subtype) : (X.subgroupOf H).map f ≤ J := by
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_of_le_map_comap f hXJ hx

theorem exists_quotMap {A L Y : Subgroup G} {c : G} {n : ℕ} (hctx : Ctx1424 G A c L Y n) :
    ∃ (T : Type) (_ : Group T) (f : ↥(A ⊔ Y) →* Multiplicative (ZMod 3) × T),
      Sec4.IsoLThreePi T 2 n ∧ Function.Surjective f ∧ f.ker = kerAO2 A Y := by
  let _ := kerAO2_normal hctx.le_normalizer
  obtain ⟨T, _, hT, ⟨ψ⟩⟩ := hctx.iso
  refine ⟨T, inferInstance, ψ.toMonoidHom.comp (QuotientGroup.mk' (kerAO2 A Y)), hT,
    ψ.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem index_subgroupOf_dvd_twentySeven {A Y : Subgroup G}
    (hYA : A ≤ Subgroup.normalizer (Y : Set G)) (hA : Nat.card A = 27) :
    (Y.subgroupOf (A ⊔ Y)).index ∣ 27 := by
  have h1 := Subgroup.card_mul_index (Y.subgroupOf (A ⊔ Y))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at h1
  have h2 := Sec6.card_sup_mul_card_inf hYA
  rw [← h1, hA] at h2
  have hY : 0 < Nat.card Y := Nat.card_pos
  refine ⟨Nat.card (A ⊓ Y : Subgroup G), ?_⟩
  have h3 : Nat.card Y * ((Y.subgroupOf (A ⊔ Y)).index * Nat.card (A ⊓ Y : Subgroup G)) =
      Nat.card Y * 27 := by
    rw [← mul_assoc, h2, mul_comm]
  exact (Nat.eq_of_mul_eq_mul_left hY h3).symm

theorem index_map_dvd_twentySeven {A Y : Subgroup G}
    (hYA : A ≤ Subgroup.normalizer (Y : Set G)) (hA : Nat.card A = 27) {M : Type*} [Group M]
    {f : ↥(A ⊔ Y) →* M} (hfs : Function.Surjective f) (hker : f.ker = kerAO2 A Y) :
    ((Y.subgroupOf (A ⊔ Y)).map f).index ∣ 27 := by
  have hkY : f.ker ≤ Y.subgroupOf (A ⊔ Y) := by
    rw [hker, kerAO2]
    exact Subgroup.comap_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  rw [Subgroup.index_map_eq _ hfs hkY]
  exact index_subgroupOf_dvd_twentySeven hYA hA

omit [Finite G] in
theorem map_inf_eq_map {A Y L : Subgroup G} (hYL : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y)
    {M : Type*} [Group M] {f : ↥(A ⊔ Y) →* M} (hker : f.ker = kerAO2 A Y) :
    ((Y ⊓ L).subgroupOf (A ⊔ Y)).map f = (Y.subgroupOf (A ⊔ Y)).map f := by
  refine le_antisymm (Subgroup.map_mono (Subgroup.comap_mono inf_le_left)) ?_
  refine map_le_of_le_map_comap f (hYL.le.trans ?_)
  refine sup_le (le_map_comap_of_map_le f _ (inf_le_left.trans le_sup_right) le_rfl) ?_
  intro x hx
  have hxk : (⟨x, pCoreOf_le_sup A Y hx⟩ : ↥(A ⊔ Y)) ∈ f.ker := by
    rw [hker, kerAO2]
    exact hx
  have h1 : f ⟨x, pCoreOf_le_sup A Y hx⟩ ∈ ((Y ⊓ L).subgroupOf (A ⊔ Y)).map f := by
    rw [MonoidHom.mem_ker.mp hxk]
    exact one_mem _
  exact ⟨⟨x, pCoreOf_le_sup A Y hx⟩, h1, rfl⟩

theorem aschbacherSolvableCore_eq_bot {A L Y : Subgroup G} {c : G} {n : ℕ}
    (hctx : Ctx1424 G A c L Y n) : aschbacherSolvableCore 3 ↥L = ⊥ := by
  have : IsSimpleGroup ↥L := hctx.simple
  rcases (aschbacherSolvableCore_normal 3 ↥L).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hctx.std.toSec13Data.mem_lA.1
    obtain ⟨-, -, a, b, hab⟩ := hq
    have : Subsingleton (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact hab (Subsingleton.elim _ _)

end CFSG.RankThree.PartTwo.Sec15.Proof1424Steps
