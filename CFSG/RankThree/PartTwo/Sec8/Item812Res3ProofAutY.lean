module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofFrattini
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

namespace Item812Res3

theorem autY_props_of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    (h1 : ∀ β : MulAut N, β ^ 3 = 1 → KFacts.IsInnerAut β)
    (h2 : ∀ β : MulAut N, ∀ x : N, x ^ 3 = 1 →
      (∃ y : N, β x = y * x * y⁻¹) ∧ ∃ y : N, β x = y * x⁻¹ * y⁻¹) :
    (∀ β : MulAut M, β ^ 3 = 1 → KFacts.IsInnerAut β) ∧
      ∀ β : MulAut M, ∀ x : M, x ^ 3 = 1 →
        (∃ y : M, β x = y * x * y⁻¹) ∧ ∃ y : M, β x = y * x⁻¹ * y⁻¹ := by
  have happ : ∀ (β : MulAut M) (x : M), MulAut.congr e β (e x) = e (β x) := fun β x => by
    simp [MulAut.congr_apply]
  refine ⟨fun β hβ => ?_, fun β x hx => ?_⟩
  · refine (KFacts.isInnerAut_congr e β).mp (h1 _ ?_)
    rw [← map_pow, hβ, map_one]
  · have hx' : e x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩ := h2 (MulAut.congr e β) (e x) hx'
    refine ⟨⟨e.symm y, e.injective ?_⟩, ⟨e.symm y', e.injective ?_⟩⟩
    · rw [← happ, hy, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · rw [← happ, hy', map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]

section Alt

open Equiv Equiv.Perm

theorem exists_odd_commute_of_pow_three (x : Perm (Fin 9)) (hx : x ^ 3 = 1) :
    ∃ τ : Perm (Fin 9), τ * x = x * τ ∧ sign τ = -1 := by
  by_contra hno
  push Not at hno
  have hle : Subgroup.centralizer {x} ≤ alternatingGroup (Fin 9) := by
    intro τ hτ
    rw [Subgroup.mem_centralizer_singleton_iff] at hτ
    rw [mem_alternatingGroup]
    rcases Int.units_eq_one_or (sign τ) with h | h
    · exact h
    · exact absurd h (hno τ hτ)
  obtain ⟨-, hcard, hcount⟩ := centralizer_le_alternating_iff.mp hle
  have h3 : ∀ c ∈ x.cycleType, c = 3 := by
    intro c hc
    have hc3 : c ∣ 3 := (dvd_of_mem_cycleType hc).trans (orderOf_dvd_of_pow_eq_one hx)
    have h2 : 2 ≤ c := two_le_of_mem_cycleType hc
    rcases (Nat.dvd_prime Nat.prime_three).mp hc3 with h | h <;> omega
  have hrep : x.cycleType = Multiset.replicate (Multiset.card x.cycleType) 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, h3⟩
  have hk : Multiset.card x.cycleType ≤ 1 := by
    have := hcount 3
    rw [hrep, Multiset.count_replicate_self] at this
    exact this
  rw [hrep, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hcard
  omega

theorem exists_conj_eq_inv_perm (x : Perm (Fin 9)) : ∃ π : Perm (Fin 9), π * x * π⁻¹ = x⁻¹ :=
  isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_inv x).symm)

theorem exists_alt_conj_eq (σ : Perm (Fin 9)) (x : alternatingGroup (Fin 9)) (hx : x ^ 3 = 1) :
    ∃ y : alternatingGroup (Fin 9), (y : Perm (Fin 9)) * x * (y : Perm (Fin 9))⁻¹ =
      σ * x * σ⁻¹ := by
  have hx' : (x : Perm (Fin 9)) ^ 3 = 1 := by
    have := congrArg Subtype.val hx
    simpa using this
  rcases Int.units_eq_one_or (sign σ) with hs | hs
  · exact ⟨⟨σ, mem_alternatingGroup.mpr hs⟩, rfl⟩
  · obtain ⟨τ, hτx, hτ⟩ := exists_odd_commute_of_pow_three x hx'
    refine ⟨⟨σ * τ, mem_alternatingGroup.mpr (by rw [map_mul, hs, hτ]; decide)⟩, ?_⟩
    change σ * τ * x * (σ * τ)⁻¹ = σ * x * σ⁻¹
    calc σ * τ * x * (σ * τ)⁻¹ = σ * (τ * x) * τ⁻¹ * σ⁻¹ := by group
      _ = σ * (x * τ) * τ⁻¹ * σ⁻¹ := by rw [hτx]
      _ = σ * x * σ⁻¹ := by group

theorem autY_props_alt :
    (∀ β : MulAut (alternatingGroup (Fin 9)), β ^ 3 = 1 → KFacts.IsInnerAut β) ∧
      ∀ β : MulAut (alternatingGroup (Fin 9)), ∀ x : alternatingGroup (Fin 9), x ^ 3 = 1 →
        (∃ y, β x = y * x * y⁻¹) ∧ ∃ y, β x = y * x⁻¹ * y⁻¹ := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  refine ⟨fun β hβ => ?_, fun β x hx => ?_⟩
  · obtain ⟨σ, rfl⟩ := hbij.2 β
    have hσ3 : σ ^ 3 = 1 := hbij.1 (by rw [map_pow, hβ, map_one])
    have hs : sign σ = 1 := by
      rcases Int.units_eq_one_or (sign σ) with h | h
      · exact h
      · exfalso
        have h1 : sign σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
        rw [h] at h1
        exact absurd h1 (by decide)
    refine ⟨⟨σ, mem_alternatingGroup.mpr hs⟩, ?_⟩
    rw [← MulAut.conjNormal_val]
  · obtain ⟨σ, rfl⟩ := hbij.2 β
    have hβx : ((MulAut.conjNormal σ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
        σ * x * σ⁻¹ := MulAut.conjNormal_apply σ x
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := exists_alt_conj_eq σ x hx
      exact ⟨y, Subtype.ext (by rw [hβx, ← hy]; rfl)⟩
    · obtain ⟨π, hπ⟩ := exists_conj_eq_inv_perm x
      have hx3 : x⁻¹ ^ 3 = 1 := by rw [inv_pow, hx, inv_one]
      obtain ⟨y, hy⟩ := exists_alt_conj_eq (σ * π⁻¹) x⁻¹ hx3
      refine ⟨y, Subtype.ext ?_⟩
      rw [hβx]
      change σ * x * σ⁻¹ = (y : Perm (Fin 9)) * (x⁻¹ : alternatingGroup (Fin 9)) *
        (y : Perm (Fin 9))⁻¹
      rw [hy]
      change σ * x * σ⁻¹ = σ * π⁻¹ * (x : Perm (Fin 9))⁻¹ * (σ * π⁻¹)⁻¹
      rw [← hπ]
      group

end Alt

section Sp

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (exists_eq_spInner_mul_fieldAut
  spInner_eq_conj)

theorem ringEquiv_eq_one_of_card_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (φ : F ≃+* F) : φ = 1 := by
  classical
  have h01 : ∀ x : F, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push Not at hx
    have hsub : ({0, 1, x} : Finset F).card ≤ Fintype.card F := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hx.1.symm]), Finset.card_pair hx.2.symm, hF] at hsub
    · omega
  refine RingEquiv.ext fun x => ?_
  rcases h01 x with rfl | rfl
  · simp
  · simp

theorem isInnerAut_statedProj_statedSp_three_two (β : MulAut (StatedProj (StatedSp 3
    (GaloisField 2 1)))) : KFacts.IsInnerAut β := by
  classical
  have hE := (automorphism_generation (r := 3) (K := GaloisField 2 1) le_rfl).1
  obtain ⟨g, φ, hg⟩ := exists_eq_spInner_mul_fieldAut (r := 3) (K := GaloisField 2 1)
    (hE ▸ Subgroup.mem_top β)
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num), pow_one]
  rw [ringEquiv_eq_one_of_card_two hcard φ, map_one, mul_one, spInner_eq_conj] at hg
  exact ⟨_, hg.symm⟩

end Sp

end Item812Res3

section Final

@[expose] def KFSp62Real : Prop :=
  ∀ x : projSp 3 (GaloisField 2 1), x ^ 3 = 1 → ∃ y : projSp 3 (GaloisField 2 1),
    y * x * y⁻¹ = x⁻¹

open Item812Res3 in
theorem kF812AutY_of (hR : KFSp62Real) : KF812AutY := by
  intro M _ hM
  rcases hM with h9 | h6
  · obtain ⟨e⟩ := h9
    exact autY_props_of_mulEquiv e autY_props_alt.1 autY_props_alt.2
  · obtain ⟨e⟩ := h6
    set e' := Sec4.projSpEquivStatedProj 3 (GaloisField 2 1) with he'
    have hinn : ∀ β : MulAut (projSp 3 (GaloisField 2 1)), KFacts.IsInnerAut β := fun β =>
      (KFacts.isInnerAut_congr e' β).mp (isInnerAut_statedProj_statedSp_three_two _)
    refine autY_props_of_mulEquiv e (fun β _ => hinn β) fun β x hx => ?_
    obtain ⟨y, hy⟩ := hinn β
    have hβx : β x = y * x * y⁻¹ := by rw [← hy, MulAut.conj_apply]
    obtain ⟨z, hz⟩ := hR x hx
    refine ⟨⟨y, hβx⟩, ⟨y * z⁻¹, ?_⟩⟩
    rw [hβx]
    calc y * x * y⁻¹ = y * z⁻¹ * (z * x * z⁻¹) * (y * z⁻¹)⁻¹ := by group
      _ = y * z⁻¹ * x⁻¹ * (y * z⁻¹)⁻¹ := by rw [hz]


theorem fin812Frattini_of_real (hR : KFSp62Real) : Fin812Frattini :=
  fin812Frattini_of (kF812AutY_of hR)

end Final

end CFSG.RankThree.PartTwo.Sec8
