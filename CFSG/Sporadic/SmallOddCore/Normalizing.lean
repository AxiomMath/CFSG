module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import CFSG.Certificates.SchreierChainOrder
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup

theorem centralizer_eq_bot_of_transitive {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} (b : Fin n)
    (htrans : ∀ x : Fin n, ∃ g ∈ P, g b = x)
    (hfix : ∀ x : Fin n, x ≠ b → ∃ s ∈ P, s b = b ∧ s x ≠ x) :
    centralizer (P : Set (Equiv.Perm (Fin n))) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_centralizer_iff] at hv
  have hvb : v b = b := by
    by_contra hne
    obtain ⟨s, hs, hsb, hsx⟩ := hfix (v b) hne
    apply hsx
    have := congrArg (fun f : Equiv.Perm (Fin n) => f b) (hv s hs)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hsb] at this
    exact this
  rw [mem_bot]
  ext x
  obtain ⟨g, hg, rfl⟩ := htrans x
  have := congrArg (fun f : Equiv.Perm (Fin n) => f b) (hv g hg)
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, hvb] at this
  simp only [Equiv.Perm.coe_one, id_eq]
  rw [← this]

theorem transitive_of_orbitSize {n : ℕ} (Q : CFSG.Certificates.RawSchreierDatum n)
    (hQ : CFSG.Certificates.ValidSchreier Q) (h0 : 0 < Q.baseCount)
    (hsize : Q.orbitSize ⟨0, h0⟩ = n) :
    ∀ x : Fin n, ∃ g ∈ Q.originalSubgroup, g (Q.base.get ⟨0, h0⟩) = x := by
  classical
  have hcard : Nat.card (Q.orbitPoints ⟨0, h0⟩) = n := by
    rw [← Q.orbitSize_eq_card, hsize]
  have huniv : Q.orbitPoints ⟨0, h0⟩ = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    · rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      calc n = Nat.card ↑(Q.orbitPoints ⟨0, h0⟩) := hcard.symm
        _ = (Q.orbitPoints ⟨0, h0⟩).ncard := Nat.card_coe_set_eq _
        _ ≤ _ := le_rfl
  intro x
  have hx : x ∈ Q.orbitPoints ⟨0, h0⟩ := by rw [huniv]; trivial
  rw [Q.orbitPoints_eq_orbit, MulAction.mem_orbit_iff] at hx
  obtain ⟨g, hg⟩ := hx
  refine ⟨g, ?_, hg⟩
  have h1 : (g : Equiv.Perm (Fin n)) ∈ Q.levelSubgroup 0 := g.2
  exact (Q.levelSubgroup_zero_eq_original hQ).le h1

section Model

variable {M : Type*} [Group M] [Finite M] {P : Subgroup M} {U : M}

theorem normalizing_model (hU2 : U ^ 2 = 1) (hUP : U ∉ P) (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P)
    (hC : centralizer (P : Set M) = ⊥) :
    P.map (MulAut.conj U).toMonoidHom = P ∧
      (∀ x, x ∈ P ⊔ zpowers U ↔ x ∈ P ∨ x * U ∈ P) ∧ P ⊓ zpowers U = ⊥ ∧
      (P.subgroupOf (P ⊔ zpowers U)).Normal ∧ Nat.card ↥(P ⊔ zpowers U) = 2 * Nat.card P ∧
      ∃ φ : ↥(P ⊔ zpowers U) →* MulAut P, Function.Injective φ ∧
        (∀ (x : ↥(P ⊔ zpowers U)) (p : P), ((φ x p : P) : M) = (x : M) * p * (x : M)⁻¹) ∧
        (P.subgroupOf (P ⊔ zpowers U)).map φ = (MulAut.conj : P →* MulAut P).range ∧
        Function.Injective (MulAut.conj : P →* MulAut P) := by
  set R := P ⊔ zpowers U
  have hUU : U * U = 1 := by rw [← sq, hU2]
  have hUinv : U⁻¹ = U := inv_eq_of_mul_eq_one_right hUU
  have hRmem : ∀ x, x ∈ R ↔ x ∈ P ∨ x * U ∈ P := fun x => mem_sup_zpowers_iff hU2 hUn
  have hmap : P.map (MulAut.conj U).toMonoidHom = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨p, hp, rfl⟩
      exact hUn p hp
    · rw [Subgroup.card_map_of_injective (MulAut.conj U).injective]
  have hRn : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    intro x hx p hp
    rcases (hRmem x).1 hx with hxP | hxU
    · exact P.mul_mem (P.mul_mem hxP hp) (P.inv_mem hxP)
    · have h1 : U⁻¹ * p * U ∈ P := by
        have := hUn p hp
        rw [hUinv] at this ⊢
        exact this
      have : x * p * x⁻¹ = (x * U) * (U⁻¹ * p * U) * (x * U)⁻¹ := by group
      rw [this]
      exact P.mul_mem (P.mul_mem hxU h1) (P.inv_mem hxU)
  have hPR : P ≤ R := le_sup_left
  have hnormal : (P.subgroupOf R).Normal := by
    refine ⟨fun p hp x => ?_⟩
    rw [mem_subgroupOf] at hp ⊢
    exact hRn x x.2 p hp
  have hinf : P ⊓ zpowers U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxU⟩ := mem_inf.mp hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxU
    have hord : orderOf U = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime hU2 fun h => hUP (h ▸ P.one_mem)
    rw [← zpow_mod_orderOf, hord] at hxP ⊢
    simp only [Nat.cast_ofNat] at hxP ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero]
      exact one_mem _
    · rw [h, zpow_one] at hxP
      exact absurd hxP hUP
  let e : ↥(P.subgroupOf R) ≃* P := subgroupOfEquivOfLe hPR
  let φ : ↥R →* MulAut P := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hφ : ∀ (x : R) (p : P), ((φ x p : P) : M) = (x : M) * p * (x : M)⁻¹ := by
    intro x p
    change ((e (MulAut.conjNormal x (e.symm p)) : P) : M) = _
    rw [show ((e (MulAut.conjNormal x (e.symm p)) : P) : M) =
      ((MulAut.conjNormal x (e.symm p) : ↥(P.subgroupOf R)) : R) from rfl,
      MulAut.conjNormal_apply]
    rfl
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxc : (x : M) ∈ centralizer (P : Set M) := by
      rw [mem_centralizer_iff]
      intro p hp
      have := hφ x ⟨p, hp⟩
      rw [hx, MulAut.one_apply] at this
      change p = (x : M) * p * (x : M)⁻¹ at this
      calc p * x = (x : M) * p * (x : M)⁻¹ * x := by rw [← this]
        _ = x * p := by group
    rw [hC, mem_bot] at hxc
    rw [mem_bot]
    exact Subtype.ext hxc
  have hconjinj : Function.Injective (MulAut.conj : P →* MulAut P) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    have hpc : (p : M) ∈ centralizer (P : Set M) := by
      rw [mem_centralizer_iff]
      intro q hq
      have := congrArg (fun α : MulAut P => ((α ⟨q, hq⟩ : P) : M)) hp
      simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
      calc q * p = (p : M) * q * (p : M)⁻¹ * p := by rw [this]
        _ = p * q := by group
    rw [hC, mem_bot] at hpc
    rw [mem_bot]
    exact Subtype.ext hpc
  have himage : (P.subgroupOf R).map φ = (MulAut.conj : P →* MulAut P).range := by
    ext α
    simp only [mem_map, mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
      rw [hφ, MulAut.conj_apply]
      rfl
    · rintro ⟨p, rfl⟩
      refine ⟨⟨p, hPR p.2⟩, p.2, MulEquiv.ext fun q => Subtype.ext ?_⟩
      rw [hφ, MulAut.conj_apply]
      rfl
  exact ⟨hmap, hRmem, hinf, hnormal, card_sup_zpowers hU2 hUn hUP, φ, hφinj, hφ, himage,
    hconjinj⟩

theorem full_automorphism_model (hU2 : U ^ 2 = 1) (hUP : U ∉ P)
    (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P) (hC : centralizer (P : Set M) = ⊥)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer P) ≤ 2) :
    ∃ e : ↥(P ⊔ zpowers U) ≃* MulAut P,
      (∀ (x : ↥(P ⊔ zpowers U)) (p : P), ((e x p : P) : M) = (x : M) * p * (x : M)⁻¹) ∧
      (P.subgroupOf (P ⊔ zpowers U)).map e.toMonoidHom =
        CFSG.ComponentClassification.OuterAutomorphisms.inner P ∧
      Nonempty (CFSG.ComponentClassification.OuterAutomorphisms.Outer P ≃*
        Multiplicative (ZMod 2)) ∧
      Nat.card (MulAut P) = 2 * Nat.card P := by
  classical
  obtain ⟨-, -, -, -, hRcard, φ, hφinj, hφ, himage, hconjinj⟩ :=
    normalizing_model hU2 hUP hUn hC
  set Inn := CFSG.ComponentClassification.OuterAutomorphisms.inner P
  have hInn : Nat.card Inn = Nat.card P :=
    (Nat.card_congr (MonoidHom.ofInjective hconjinj).toEquiv).symm
  have hAut := Inn.card_eq_card_quotient_mul_card_subgroup
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hle : Nat.card (MulAut P) ≤ Nat.card ↥(P ⊔ zpowers U) := by
    rw [hAut, hInn, hRcard]
    exact Nat.mul_le_mul_right _ hout
  have hge : Nat.card ↥(P ⊔ zpowers U) ≤ Nat.card (MulAut P) :=
    Nat.card_le_card_of_injective φ hφinj
  have hbij : Function.Bijective φ := by
    refine ⟨hφinj, ?_⟩
    have : Finite (MulAut P) := inferInstance
    exact (Function.Injective.bijective_of_nat_card_le hφinj hle).2
  let e := MulEquiv.ofBijective φ hbij
  have hcardAut : Nat.card (MulAut P) = 2 * Nat.card P := by
    rw [← hRcard]; exact le_antisymm hle hge
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer P) = 2 := by
    rw [hcardAut, hInn] at hAut
    exact (Nat.eq_of_mul_eq_mul_right hPpos hAut).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨e, hφ, himage, ⟨mulEquivOfPrimeCardEq hOut (by simp)⟩, hcardAut⟩

omit [Finite M] in
theorem autModel_of {R : Subgroup M} (hPR : P ≤ R) (hRn : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (e : ↥R ≃* MulAut P) (he : ∀ (x : ↥R) (p : P), ((e x p : P) : M) = (x : M) * p * (x : M)⁻¹)
    (hC : centralizer (P : Set M) = ⊥) : AutModel P R where
  le := hPR
  conj_mem := hRn
  surj α := ⟨e.symm α, (e.symm α).2, fun p => by rw [← he, MulEquiv.apply_symm_apply]⟩
  inj x _ hx := by
    have : x ∈ centralizer (P : Set M) := by
      rw [mem_centralizer_iff]
      intro p hp
      exact (hx p hp).symm
    rwa [hC, mem_bot] at this

end Model

end CFSG.Sporadic.SmallOddCore
