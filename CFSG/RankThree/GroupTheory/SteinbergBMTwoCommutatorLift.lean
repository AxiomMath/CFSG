module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {A : Type*} [Group A]

theorem map_actionCommutator {X Y : Type*} [Group X] [Group Y] [MulDistribMulAction A X]
    [MulDistribMulAction A Y] (f : X →* Y) (hf : ∀ (a : A) (x : X), f (a • x) = a • f x)
    (K : Subgroup X) : (actionCommutator A K).map f = actionCommutator A (K.map f) := by
  unfold actionCommutator
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨h, hh, a, rfl⟩, rfl⟩
    exact ⟨f h, ⟨h, hh, rfl⟩, a, by rw [map_mul, map_inv, hf]⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, a, rfl⟩
    exact ⟨h⁻¹ * (a • h), ⟨h, hh, a, rfl⟩, by rw [map_mul, map_inv, hf]⟩

theorem actionCommutator_le_of_invariant {X : Type*} [Group X] [MulDistribMulAction A X]
    {K : Subgroup X} (hK : ∀ a : A, ∀ x ∈ K, a • x ∈ K) : actionCommutator A K ≤ K := by
  refine (closure_le _).2 ?_
  rintro _ ⟨h, hh, a, rfl⟩
  exact K.mul_mem (K.inv_mem hh) (hK a h hh)

theorem smul_mem_actionCommutator_of_invariant {X : Type*} [Group X] [MulDistribMulAction A X]
    {K : Subgroup X} (hK : ∀ a : A, ∀ x ∈ K, a • x ∈ K) (a : A) {x : X}
    (hx : x ∈ actionCommutator A K) : a • x ∈ actionCommutator A K := by
  have hle : actionCommutator A K ≤
      (actionCommutator A K).comap (MulDistribMulAction.toMonoidHom X a) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨h, hh, b, rfl⟩
    change a • (h⁻¹ * (b • h)) ∈ actionCommutator A K
    have e : a • (h⁻¹ * (b • h)) = (a • h)⁻¹ * ((a * b * a⁻¹) • (a • h)) := by
      rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul, inv_mul_cancel_right]
    rw [e]
    exact gen_mem_actionCommutator (hK a h hh) _
  exact hle hx

theorem coprime_two_commutator_lifts_through_invariant_supplement {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L : Type*} [Group L] [Finite A] [Finite L] [MulDistribMulAction A L]
    (hA : IsPGroup p A) (N : Subgroup L) [N.Normal] [CFSG.IsInvariant A L N]
    (hpN : ¬ p ∣ Nat.card N) (M : Subgroup L) (hMinv : ∀ a : A, ∀ x ∈ M, a • x ∈ M)
    (hLMN : M ⊔ N = ⊤) (E : Subgroup (L ⧸ N)) (hE1 : E ≠ ⊥) (hE2 : IsPGroup 2 E)
    (hEinv : ∀ a : A, ∀ x ∈ E, a • x ∈ E) (hEA : actionCommutator A E = E) :
    ∃ T : Subgroup L, T ≤ M ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ (∀ a : A, ∀ x ∈ T, a • x ∈ T) ∧
      actionCommutator A T = T ∧ T.map (QuotientGroup.mk' N) = E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπdef
  have hπA : ∀ (a : A) (l : L), π (a • l) = a • π l := fun a l =>
    (MulAction.Quotient.smul_mk (H := N) a l).symm
  set Y := M ⊓ E.comap π with hYdef
  have hYinv : ∀ a : A, ∀ x ∈ Y, a • x ∈ Y := fun a x hx =>
    ⟨hMinv a x hx.1, by
      show π (a • x) ∈ E
      rw [hπA]
      exact hEinv a _ hx.2⟩
  have hYE : Y.map π = E := by
    refine le_antisymm (map_le_iff_le_comap.mpr inf_le_right) fun e he => ?_
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N e
    have hl : l ∈ ((M ⊔ N : Subgroup L) : Set L) := by
      rw [hLMN]
      exact mem_top l
    rw [mul_normal M N] at hl
    obtain ⟨m, hm, n, hn, rfl⟩ := hl
    have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    have hπmn : π (m * n) = π m := by rw [map_mul, hπn, mul_one]
    refine ⟨m, ⟨hm, ?_⟩, hπmn.symm⟩
    show π m ∈ E
    rw [← hπmn]
    exact he
  have hpY : Nat.Coprime p (Nat.card Y) := by
    have hcard := card_ker_mul_card_range (π.comp Y.subtype)
    have hrange : (π.comp Y.subtype).range = E := by
      rw [MonoidHom.range_comp, range_subtype, hYE]
    have hker : Nat.card (π.comp Y.subtype).ker ∣ Nat.card N := by
      rw [← card_map_of_injective Y.subtype_injective]
      refine card_dvd_of_le ?_
      rintro _ ⟨y, hy, rfl⟩
      have : π y = 1 := hy
      exact (QuotientGroup.eq_one_iff (y : L)).mp this
    rw [hrange] at hcard
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2
    rw [hk] at hcard
    rw [← hcard]
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (h.trans hker)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have : CFSG.IsInvariant A L Y := ⟨fun a g => ⟨fun hg => hYinv a g hg, fun hg => by
    have := hYinv a⁻¹ _ hg
    rwa [inv_smul_smul] at this⟩⟩
  obtain ⟨P₀, -, hP₀⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing
    (ActorType := A) (GroupType := Y) p 2 hp Nat.prime_two hA hpY ⊥ IsPGroup.of_bot
    fun a x hx => by
      rw [mem_bot] at hx ⊢
      rw [hx, smul_one]
  have hP₀inv : ∀ a : A, ∀ x ∈ (P₀ : Subgroup Y), a • x ∈ (P₀ : Subgroup Y) := by
    intro a x hx
    have heq : a • (P₀ : Subgroup Y) = (P₀ : Subgroup Y) := by
      rw [← Sylow.pointwise_smul_def, hP₀ a]
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul x a _ hx
  set P := (P₀ : Subgroup Y).map Y.subtype with hPdef
  have hPinv : ∀ a : A, ∀ x ∈ P, a • x ∈ P := by
    rintro a _ ⟨y, hy, rfl⟩
    exact ⟨a • y, hP₀inv a y hy, rfl⟩
  have hP2 : IsPGroup 2 P := P₀.isPGroup'.map Y.subtype
  have hφ : ∀ y : Y, (π.comp Y.subtype) y ∈ E := fun y => y.2.2
  set φ : Y →* E := (π.comp Y.subtype).codRestrict E hφ with hφdef
  have hφs : Function.Surjective φ := by
    rintro ⟨e, he⟩
    rw [← hYE] at he
    obtain ⟨l, hl, hle⟩ := he
    exact ⟨⟨l, hl⟩, Subtype.ext hle⟩
  have hPE : P.map π = E := by
    have hmax := (P₀.mapSurjective hφs).is_maximal' (hE2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at hmax
    have h1 : P.map π = ((P₀ : Subgroup Y).map φ).map E.subtype := by
      rw [hPdef, map_map, map_map]
      rfl
    rw [h1, ← hmax, ← MonoidHom.range_eq_map, range_subtype]
  have h2A : ¬ 2 ∣ Nat.card A := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hA
    rw [hj]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have : CFSG.IsInvariant A Y (P₀ : Subgroup Y) :=
    ⟨fun a g => ⟨fun hg => hP₀inv a g hg, fun hg => by
      have := hP₀inv a⁻¹ _ hg
      rwa [inv_smul_smul] at this⟩⟩
  have hfact := (coprime_pgroup_commutator_factorization (A := A) (Q := (P₀ : Subgroup Y))
    Nat.prime_two P₀.isPGroup' h2A).2
  set ι : (P₀ : Subgroup Y) →* L := Y.subtype.comp (P₀ : Subgroup Y).subtype with hιdef
  have hι : ∀ (a : A) (x : (P₀ : Subgroup Y)), ι (a • x) = a • ι x := fun _ _ => rfl
  have hιP : (⊤ : Subgroup (P₀ : Subgroup Y)).map ι = P := by
    rw [hιdef, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  set T := actionCommutator A P with hTdef
  have hT : T = (actionCommutator A (⊤ : Subgroup (P₀ : Subgroup Y))).map ι := by
    rw [map_actionCommutator ι hι, hιP]
  have hTP : T ≤ P := actionCommutator_le_of_invariant hPinv
  refine ⟨T, hTP.trans ((map_subtype_le _).trans inf_le_left), ?_, hP2.to_le hTP,
    fun a x hx => smul_mem_actionCommutator_of_invariant hPinv a hx, ?_, ?_⟩
  · intro hT1
    apply hE1
    rw [← hEA, ← hPE, ← map_actionCommutator π hπA, ← hTdef, hT1, Subgroup.map_bot]
  · rw [hT, ← map_actionCommutator ι hι, hfact]
  · rw [hTdef, map_actionCommutator π hπA, hPE, hEA]

end CFSG.RankThree.GroupTheory.SteinbergBM
