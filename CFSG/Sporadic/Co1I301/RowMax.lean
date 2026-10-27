module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo1Nat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Max

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1I301

open Subgroup CFSG.Open CFSG.Sporadic.Co1Patterson CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.H301 CFSG.LocalAnalysis.GLTheoremA.H301B
open CFSG.Blueprint (NativeSporadic.Co1)

private theorem exists_mem_normalizer_of_not_le {G : Type*} [Group G] [Finite G]
    {Q R' : Subgroup G} (hR : IsPGroup 2 R') (hRR : Q ≤ R') (hne : ¬ R' ≤ Q) :
    ∃ y ∈ R', y ∈ Subgroup.normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.isNilpotent
  set Q' : Subgroup R' := Q.subgroupOf R'
  have hlt : Q' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun r hr => ?_
    have h1 : (⟨r, hr⟩ : R') ∈ Q' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
  have hconj : ∀ u : R', u ∈ Subgroup.normalizer (Q' : Set R') → ∀ q ∈ Q,
      (u : G) * q * (u : G)⁻¹ ∈ Q := by
    intro u hu q hq
    have h1 := (Subgroup.mem_normalizer_iff.1 hu ⟨q, hRR hq⟩).1 (Subgroup.mem_subgroupOf.2 hq)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have hN : (y : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconj y hyN q, fun hq => ?_⟩
    have h := hconj y⁻¹ ((Subgroup.normalizer (Q' : Set R')).inv_mem hyN) _ hq
    rw [Subgroup.coe_inv, inv_inv] at h
    have e : (y : G)⁻¹ * ((y : G) * q * (y : G)⁻¹) * (y : G) = q := by group
    rwa [e] at h
  exact ⟨y, y.2, hN, fun h => hyQ (Subgroup.mem_subgroupOf.2 h)⟩

private theorem hMax_aux {K A : Type*} [Group K] [Group A] {K₀ B Q : Subgroup K}
    (hmax : ∀ R' : Subgroup K, IsPGroup 2 R' → B ≤ Subgroup.normalizer (R' : Set K) →
      Q ≤ R' → R' = Q)
    (hOut : ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g) (ι : K →* A)
    (hι : Function.Injective ι) (hN : ι.range.Normal)
    (hC : Subgroup.centralizer (ι.range : Set A) = ⊥) (R' : Subgroup A) (hR' : IsPGroup 2 R')
    (hKB : (K₀ ⊔ B).map ι ≤ Subgroup.normalizer (R' : Set A)) (hQ : Q.map ι ≤ R') :
    R' = Q.map ι := by
  have htop := range_eq_top_of_forall_inner hOut ι hι hN hC
  have hR'eq : R' = (R'.comap ι).map ι := by
    rw [Subgroup.map_comap_eq, htop, top_inf_eq]
  rw [hR'eq, hmax (R'.comap ι) (hR'.comap_of_injective ι hι)
    ((Subgroup.map_le_iff_le_comap.1 ((Subgroup.map_mono le_sup_right).trans hKB)).trans
      (Subgroup.le_normalizer_comap ι)) (Subgroup.map_le_iff_le_comap.1 hQ)]


theorem eq_co1R_of_invariant (D : TwoCentralData 4 aNC co1R) {B₁ : Subgroup NativeSporadic.Co1}
    (hB : IsElemAbelian 3 B₁) (hBc : Nat.card B₁ = 3 ^ 4)
    (hBa : B₁ ≤ centralizer ({aNC} : Set NativeSporadic.Co1)) (R' : Subgroup NativeSporadic.Co1)
    (hR : IsPGroup 2 R') (hBR : B₁ ≤ Subgroup.normalizer (R' : Set NativeSporadic.Co1))
    (hRR : co1R ≤ R') : R' = co1R := by
  haveI : Finite NativeSporadic.Co1 := CFSG.Sporadic.Co1.fam_co1_simplicity.1
  refine le_antisymm ?_ hRR
  by_contra hne
  obtain ⟨y, hyR, hyN, hyQ⟩ := exists_mem_normalizer_of_not_le hR hRR hne
  let N : Subgroup NativeSporadic.Co1 := R' ⊓ Subgroup.normalizer (co1R : Set NativeSporadic.Co1)
  have hN2 : IsPGroup 2 N := hR.to_le inf_le_left
  have hNa : N ≤ centralizer ({aNC} : Set NativeSporadic.Co1) := fun g hg =>
    (@Subgroup.mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC g).2
      (comm_of_mem_normalizer D.extraspecial D.z_mem D.z_central D.z_ne_one
        (Subgroup.mem_inf.1 hg).2)
  have hBN : B₁ ≤ Subgroup.normalizer (N : Set NativeSporadic.Co1) := by
    intro b hb
    have hbR := Subgroup.mem_normalizer_iff.1 (hBR hb)
    have hbQ : b ∈ Subgroup.normalizer (co1R : Set NativeSporadic.Co1) :=
      D.normalizes b
        ((@Subgroup.mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC b).1
          (hBa hb))
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · exact Subgroup.mem_inf.2 ⟨(hbR n).1 (Subgroup.mem_inf.1 hn).1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hbQ (Subgroup.mem_inf.1 hn).2)
          (Subgroup.inv_mem _ hbQ)⟩
    · have hn' := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨(hbR n).2 hn'.1, ?_⟩
      have e : b⁻¹ * (b * n * b⁻¹) * b = n := by group
      rw [← e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hbQ) hn'.2) hbQ
  exact hyQ (D.contains B₁ N hBa hNa hB hBc hN2 hBN ⟨hyR, hyN⟩)

theorem co1_hMax (D : TwoCentralData 4 aNC co1R) {K₀ B₁ : Subgroup NativeSporadic.Co1}
    (hB : IsElemAbelian 3 B₁) (hBc : Nat.card B₁ = 3 ^ 4)
    (hBa : B₁ ≤ centralizer ({aNC} : Set NativeSporadic.Co1))
    (hOut : ∀ α : MulAut NativeSporadic.Co1, ∃ g : NativeSporadic.Co1, α = MulAut.conj g) :
    ∀ (A : Type) [Group A] [Finite A] (ι : NativeSporadic.Co1 →* A), Function.Injective ι →
      ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
      ∀ R' : Subgroup A, IsPGroup 2 R' →
        (K₀ ⊔ B₁).map ι ≤ Subgroup.normalizer (R' : Set A) →
        co1R.map ι ≤ R' → R' = co1R.map ι := by
  intro A _ _ ι hι hN hC R' hR' hKB hQR'
  exact @hMax_aux NativeSporadic.Co1 A inferInstance inferInstance K₀ B₁ co1R
    (eq_co1R_of_invariant D hB hBc hBa) hOut ι hι hN hC R' hR' hKB hQR'

end CFSG.Sporadic.Co1I301
