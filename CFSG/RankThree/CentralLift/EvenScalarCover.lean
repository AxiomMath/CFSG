module

public import CFSG.RankThree.CentralLift.LinearScalarCover
public import CFSG.RankThree.CentralLift.ClassicalCoverTools
public import CFSG.RankThree.CentralLiftU.EvenSplit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars projectiveSL proj)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU equivStatedSU)

universe u

theorem existsUnique_comp_eq_of_pullback_section {H L Q : Type*} [Group H] [Group L] [Group Q]
    {β : H →* Q} {η : L →* Q} (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center L)
    {p : ℕ} (hCp : IsPGroup p η.ker)
    (hsplit : ∀ (P : Subgroup (H × L)) (ρ : P →* H), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center P → IsPGroup p ρ.ker → ∃! s : H →* P, ρ.comp s = MonoidHom.id H) :
    ∃! φ : H →* L, η.comp φ = β := by
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_pullback_section hη hC hCp
    fun P ρ hρ hρC hρp => (hsplit P ρ hρ hρC hρp).exists
  refine ⟨φ, hφ, fun φ' hφ' => ?_⟩
  set P := (β.comp (MonoidHom.fst H L)).eqLocus (η.comp (MonoidHom.snd H L)) with hP
  set ρ := (MonoidHom.fst H L).comp P.subtype with hρ
  have hmemP : ∀ y : H × L, y ∈ P ↔ β y.1 = η y.2 := fun _ => Iff.rfl
  have hρs : Function.Surjective ρ := by
    intro h
    obtain ⟨l, hl⟩ := hη (β h)
    exact ⟨⟨(h, l), (hmemP _).2 hl.symm⟩, rfl⟩
  have hρker : ∀ y : P, y ∈ ρ.ker ↔ (y : H × L).1 = 1 := fun _ => Iff.rfl
  have hkerη : ∀ y : P, y ∈ ρ.ker → (y : H × L).2 ∈ η.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, ← (hmemP _).1 y.2, (hρker y).1 hy, map_one]
  have hA : ρ.ker ≤ Subgroup.center P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hc := Subgroup.mem_center_iff.1 (hC (hkerη y hy)) (z : H × L).2
    have h1 : (y : H × L).1 = 1 := (hρker y).1 hy
    refine Subtype.ext (Prod.ext ?_ hc)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Prod.fst_mul, Prod.fst_mul, h1, mul_one, one_mul]
  have hAp : IsPGroup p ρ.ker := by
    refine hCp.of_injective
      ((MonoidHom.snd _ L).comp (P.subtype.comp ρ.ker.subtype) |>.codRestrict η.ker
        fun y => hkerη y y.2) fun y z hyz => ?_
    have h2 : (y : P).1.2 = (z : P).1.2 := congrArg Subtype.val hyz
    exact Subtype.ext (Subtype.ext (Prod.ext (((hρker y).1 y.2).trans ((hρker z).1 z.2).symm)
      h2))
  let sec : ∀ ψ : H →* L, η.comp ψ = β → H →* P := fun ψ hψ =>
    ((MonoidHom.id H).prod ψ).codRestrict P fun h => by
      rw [hmemP]
      exact (DFunLike.congr_fun hψ h).symm
  have hsec : ∀ ψ hψ, ρ.comp (sec ψ hψ) = MonoidHom.id H := fun _ _ => MonoidHom.ext fun _ => rfl
  obtain ⟨s, -, hs⟩ := hsplit P ρ hρs hA hAp
  have h1 := (hs _ (hsec φ' hφ')).trans (hs _ (hsec φ hφ)).symm
  refine MonoidHom.ext fun h => ?_
  have := congrArg (fun t : H →* P => ((t h : P) : H × L).2) h1
  exact this

theorem existsUnique_section_of_mulEquiv {S S' E : Type*} [Group S] [Group S'] [Group E]
    (e : S' ≃* S) {ρ : E →* S}
    (h' : ∃! s' : S' →* E, (e.symm.toMonoidHom.comp ρ).comp s' = MonoidHom.id _) :
    ∃! s : S →* E, ρ.comp s = MonoidHom.id _ := by
  obtain ⟨s', hs', huniq⟩ := h'
  have hs'x : ∀ x, e.symm (ρ (s' x)) = x := fun x => DFunLike.congr_fun hs' x
  refine ⟨s'.comp e.symm.toMonoidHom, MonoidHom.ext fun x => e.symm.injective ?_, fun t ht => ?_⟩
  · change e.symm (ρ (s' (e.symm x))) = e.symm x
    rw [hs'x]
  · have htx : ∀ x, ρ (t x) = x := fun x => DFunLike.congr_fun ht x
    have h1 := huniq (t.comp e.toMonoidHom) (MonoidHom.ext fun y => by
      change e.symm (ρ (t (e y))) = y
      rw [htx, MulEquiv.symm_apply_apply])
    refine MonoidHom.ext fun x => ?_
    have h2 := DFunLike.congr_fun h1 (e.symm x)
    change t (e (e.symm x)) = s' (e.symm x) at h2
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2

theorem odd_card_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hG : IsPGroup p G) : Odd (Nat.card G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hG.exists_card_eq
  rw [hm]
  exact (hp.odd_of_ne_two hp2).pow

section Families

variable {p f : ℕ} {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

theorem even_field_linear_perfect_central_large_prime_scalar_cover (hp : p.Prime) (hp3 : 3 < p)
    {k : Type} [Field k] (hk : Nat.card k = 2 ^ f) {n : ℕ} (hn : 2 ≤ n)
    (η : L →* projectiveSL n k) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center L)
    (hCp : IsPGroup p η.ker) :
    (∃! φ : SpecialLinearGroup (Fin n) k →* L, η.comp φ = proj n k) ∧
    ∀ φ : SpecialLinearGroup (Fin n) k →* L, η.comp φ = proj n k →
      Function.Surjective φ ∧ φ.ker ≤ scalars n k ∧ (scalars n k).map φ = η.ker ∧
      (∃ e : SpecialLinearGroup (Fin n) k ⧸ φ.ker ≃* L,
        ∀ h : SpecialLinearGroup (Fin n) k, e (h : SpecialLinearGroup (Fin n) k ⧸ φ.ker) = φ h ∧
          η (e (h : SpecialLinearGroup (Fin n) k ⧸ φ.ker)) = proj n k h) ∧
      Nonempty (η.ker ≃* scalars n k ⧸ φ.ker.subgroupOf (scalars n k)) ∧
      IsCyclic η.ker ∧ Nat.card η.ker ∣ Nat.gcd n (2 ^ f - 1) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f two_ne_zero)
  have : Fintype k := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  refine ⟨CFSG.SectionRank.EvenCover.even_linear_existsUnique_lift hn hη hC
    (odd_card_of_isPGroup hp (by omega) hCp) (proj n k), fun φ hφ => ?_⟩
  have h := exact_scalar_cover_map_of_comp_eq (by omega) hC hφ
  rw [hk] at h
  exact h

theorem even_field_unitary_perfect_central_large_prime_scalar_cover (hp : p.Prime) (hp3 : 3 < p)
    {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ} (hn : 3 ≤ n)
    (η : L →* StatedProj (StatedSU n (2 ^ f) K)) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃! φ : StatedSU n (2 ^ f) K →* L,
      η.comp φ = QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))) ∧
    ∀ φ : StatedSU n (2 ^ f) K →* L,
      η.comp φ = QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) →
      Function.Surjective φ ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) ∧
      ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)).map φ = η.ker ∧
      (∃ e : StatedSU n (2 ^ f) K ⧸ φ.ker ≃* L, ∀ g : StatedSU n (2 ^ f) K,
        e (g : StatedSU n (2 ^ f) K ⧸ φ.ker) = φ g ∧
        η (e (g : StatedSU n (2 ^ f) K ⧸ φ.ker)) =
          QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) g) ∧
      Nonempty (η.ker ≃* (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) ⧸
        φ.ker.subgroupOf ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))) ∧
      IsCyclic η.ker ∧ Nat.card η.ker ∣ Nat.gcd n (2 ^ f + 1) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.charP
  have hF := CFSG.LieType.Steinberg.card_eq_sq_of_unitaryFieldData h
  set D := (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) with hD
  have hsplit : ∀ (P : Subgroup (StatedSU n (2 ^ f) K × L)) (ρ : P →* StatedSU n (2 ^ f) K),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center P → IsPGroup p ρ.ker →
      ∃! s : StatedSU n (2 ^ f) K →* P, ρ.comp s = MonoidHom.id _ := by
    intro P ρ hρ hρC hρp
    set e := equivStatedSU (p := 2) hF n
    refine existsUnique_section_of_mulEquiv e ?_
    have hker : (e.symm.toMonoidHom.comp ρ).ker = ρ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ e.symm.injective]
    have hρ' : Function.Surjective (e.symm.toMonoidHom.comp ρ) := e.symm.surjective.comp hρ
    by_cases he : Even n
    · obtain ⟨s, hs, huniq, -⟩ := CFSG.SectionRank.EvenCover.even_su_central_odd_extension_splitting
        hF (by omega) he hρ' (hker ▸ hρC) (hker ▸ odd_card_of_isPGroup hp (by omega) hρp)
      exact ⟨s, MonoidHom.ext hs, fun τ hτ => huniq τ (DFunLike.congr_fun hτ)⟩
    · obtain ⟨s, hs, huniq, -⟩ :=
        CFSG.RankThree.CentralLiftU.su_odd_central_large_prime_extension_splitting_two h hp hp3
          hn he hρ' (hker ▸ hρC) (hker ▸ hρp)
      exact ⟨s, MonoidHom.ext hs, fun τ hτ => huniq τ (DFunLike.congr_fun hτ)⟩
  refine ⟨existsUnique_comp_eq_of_pullback_section hη hC hCp hsplit, fun φ hφ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := cover_map_of_comp_eq (QuotientGroup.mk'_surjective D) hC hφ
  rw [QuotientGroup.ker_mk'] at h2 h3 h5
  obtain ⟨ψ⟩ := h5
  have hcycD : IsCyclic D := CFSG.SectionRank.OddCover.isCyclic_scalars (by omega) _
  have hcyc : IsCyclic η.ker :=
    isCyclic_of_surjective (ψ.symm.toMonoidHom.comp (QuotientGroup.mk' _))
      (ψ.symm.surjective.comp (QuotientGroup.mk'_surjective _))
  refine ⟨h1, h2, h3, h4, ⟨ψ⟩, hcyc, ?_⟩
  rw [Nat.card_congr ψ.toEquiv, ← (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF
    (by omega)).2.2]
  exact Subgroup.card_quotient_dvd_card _

end Families

end CFSG.RankThree.CentralLift
