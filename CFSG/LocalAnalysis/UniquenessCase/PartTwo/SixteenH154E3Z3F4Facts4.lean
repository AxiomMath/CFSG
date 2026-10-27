module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.ABGTheoremB.CoverEmbedding
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts4A
public import CFSG.LinearAlgebra.CyclicIrreducibleNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.RepresentationTheory
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup

private theorem s16h_e3_z3_card_sylow_seven
    {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField)}
    (P : Sylow 7 ↥H) (hPbot : (P : Subgroup ↥H) ≠ ⊥) : Nat.card (P : Subgroup ↥H) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Finite OmegaField := by
    haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
    exact Module.finite_of_finite (ZMod 2)
  obtain ⟨k, hk⟩ := (P.isPGroup').exists_card_eq
  have hdvd1 : Nat.card (P : Subgroup ↥H) ∣ Nat.card ↥H := by
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (le_top : (P : Subgroup ↥H) ≤ ⊤))
  have hdvd2 : Nat.card ↥H ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 3) OmegaField) := by
    simpa only [Subgroup.card_top] using (Subgroup.card_dvd_of_le (le_top : H ≤ ⊤))
  have hdvd : Nat.card (P : Subgroup ↥H) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 3) OmegaField) := hdvd1.trans hdvd2
  rw [hk, s16h_e3_z3_card_gl] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have : 7 ^ 2 ∣ 181440 := (pow_dvd_pow 7 h2).trans hdvd
    norm_num at this
  have hk0 : k ≠ 0 := by
    intro h0
    apply hPbot
    rw [Subgroup.eq_bot_iff_card, hk, h0, pow_zero]
  have : k = 1 := by omega
  rw [hk, this, pow_one]

private theorem s16h_e3_z3_map_normalizer_subtype
    {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField)} (S : Subgroup ↥H) :
    (Subgroup.normalizer (S : Set ↥H)).map H.subtype =
      Subgroup.normalizer (S.map H.subtype : Set (Matrix.GeneralLinearGroup (Fin 3) OmegaField)) ⊓
        H := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩), y.2⟩
  · intro hx
    obtain ⟨hxN, hxH⟩ := Subgroup.mem_inf.mp hx
    have hxrange : x ∈ H.subtype.range := by rwa [Subgroup.range_subtype]
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hxrange
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro p
    constructor
    · intro hp
      have hpQ : H.subtype p ∈ S.map H.subtype := Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
      have hmem : H.subtype (y * p * y⁻¹) ∈ S.map H.subtype := by
        have h := (hxN (H.subtype p)).mp hpQ
        simpa only [map_mul, map_inv] using h
      obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hmem
      rwa [H.subtype_injective hqeq] at hq
    · intro hp
      have hpQ : H.subtype (y * p * y⁻¹) ∈ S.map H.subtype :=
        Subgroup.mem_map.mpr ⟨y * p * y⁻¹, hp, rfl⟩
      have hmem : H.subtype p ∈ S.map H.subtype := by
        apply (hxN (H.subtype p)).mpr
        simpa only [map_mul, map_inv] using hpQ
      obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hmem
      rwa [H.subtype_injective hqeq] at hq

theorem s16h_e3_z3_normalizer_seven {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField)}
    (h3 : ¬ 3 ∣ Nat.card ↥H) (P : Sylow 7 ↥H) :
    normalizer (P : Set ↥H) ≤ centralizer (P : Set ↥H) := by
  by_cases hPbot : (P : Subgroup ↥H) = ⊥
  · have hset : (P : Set ↥H) = ((⊥ : Subgroup ↥H) : Set ↥H) := by
      rw [← Sylow.coe_coe, hPbot]
    rw [hset]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = 1 := by simpa using hy
    rw [hy', one_mul, mul_one]
  · haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    haveI : Finite OmegaField := by
      haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
      exact Module.finite_of_finite (ZMod 2)
    set Psub : Subgroup ↥H := (P : Subgroup ↥H) with hPsubdef
    have hPcard : Nat.card Psub = 7 := s16h_e3_z3_card_sylow_seven P hPbot
    set N : Subgroup ↥H := Subgroup.normalizer (P : Set ↥H) with hNdef
    set C : Subgroup ↥H := Subgroup.centralizer (P : Set ↥H) with hCdef
    set Q : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField) := Psub.map H.subtype with hQdef
    set N' : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField) := N.map H.subtype with hN'def
    have hQcard : Nat.card Q = 7 := by
      rw [hQdef, Subgroup.card_map_of_injective H.subtype_injective, hPcard]
    have hQN : Q ≤ N' := by
      rw [hQdef, hN'def]
      exact Subgroup.map_mono (Subgroup.le_normalizer (H := Psub))
    have hQnormal : ∀ g ∈ N', ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
      intro g hg x hx
      rw [hN'def] at hg
      rw [hQdef] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨y * p * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      rw [hNdef] at hy
      exact (Subgroup.mem_normalizer_iff.mp hy p).1 hp
    have hQcyc : IsCyclic Q := isCyclic_of_prime_card hQcard
    have hQirr : IsIrreducibleMatrixRep Q.subtype :=
      s16h_e3_z3_irreducible_of_card_seven Q hQcard
    have hidx : ((Subgroup.centralizer
        (Q : Set (Matrix.GeneralLinearGroup (Fin 3) OmegaField))).subgroupOf N').index ∣ 3 :=
      index_cyclicCentralizer_subgroupOf_dvd (G := N') (H := Q) Nat.prime_three hQcyc hQirr hQnormal
    have hCmap : C.map H.subtype =
        Subgroup.centralizer (Q : Set (Matrix.GeneralLinearGroup (Fin 3) OmegaField)) ⊓ N' := by
      rw [hCdef, hQdef, hN'def, hNdef]
      change (Subgroup.centralizer (Psub : Set ↥H)).map H.subtype =
        Subgroup.centralizer (Psub.map H.subtype :
          Set (Matrix.GeneralLinearGroup (Fin 3) OmegaField)) ⊓
          (Subgroup.normalizer (Psub : Set ↥H)).map H.subtype
      rw [CFSG.ABGTheoremB.Setting.map_centralizer_eq_range_inf H.subtype_injective Psub,
        Subgroup.range_subtype, s16h_e3_z3_map_normalizer_subtype Psub]
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxH, hxc⟩
        exact ⟨hxc, Subgroup.centralizer_le_normalizer _ hxc, hxH⟩
      · rintro ⟨hxc, -, hxH⟩
        exact ⟨hxH, hxc⟩
    have hrel : C.relIndex N = ((Subgroup.centralizer
        (Q : Set (Matrix.GeneralLinearGroup (Fin 3) OmegaField))).subgroupOf N').index := by
      rw [← Subgroup.relIndex_map_map_of_injective C N H.subtype_injective]
      rw [← hN'def, hCmap, Subgroup.inf_relIndex_right]
      rfl
    have hrel3 : C.relIndex N ∣ 3 := hrel ▸ hidx
    have hrelH : C.relIndex N ∣ Nat.card ↥H := by
      refine (Subgroup.relIndex_dvd_card C N).trans ?_
      simpa only [Subgroup.card_top] using (Subgroup.card_dvd_of_le (le_top : N ≤ ⊤))
    have hrel1 : C.relIndex N = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hrel3 with h | h
      · exact h
      · exfalso
        have h3dvd : 3 ∣ Nat.card ↥H := by
          have hcopy := hrelH
          rw [h] at hcopy
          exact hcopy
        exact h3 h3dvd
    exact Subgroup.relIndex_eq_one.mp hrel1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
