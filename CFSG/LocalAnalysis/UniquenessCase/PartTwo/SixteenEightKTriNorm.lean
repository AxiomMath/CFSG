module

import CFSG.Quasithin.Background.SmithB42HatA6Norm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private theorem s16k_conj_center_mem {Q : Type} [CommGroup Q]
    {L' : Subgroup (MulAut Q)} {x : MulAut Q}
    (hxnorm : ∀ l : MulAut Q, l ∈ L' ↔ x * l * x⁻¹ ∈ L')
    (k : ↥L') (hk : k ∈ Subgroup.center ↥L') :
    (⟨x * (k : MulAut Q) * x⁻¹, (hxnorm (k : MulAut Q)).1 k.2⟩ : ↥L') ∈
      Subgroup.center ↥L' := by
  rw [Subgroup.mem_center_iff]
  intro m
  apply Subtype.ext
  show (m : MulAut Q) * (x * (k : MulAut Q) * x⁻¹)
      = (x * (k : MulAut Q) * x⁻¹) * (m : MulAut Q)
  have hm : x⁻¹ * (m : MulAut Q) * x ∈ L' := by
    refine (hxnorm (x⁻¹ * (m : MulAut Q) * x)).2 ?_
    have h : x * (x⁻¹ * (m : MulAut Q) * x) * x⁻¹ = (m : MulAut Q) := by group
    rw [h]
    exact m.2
  have hkc : (k : MulAut Q) * (x⁻¹ * (m : MulAut Q) * x)
      = (x⁻¹ * (m : MulAut Q) * x) * (k : MulAut Q) :=
    (congrArg (fun z : ↥L' => (z : MulAut Q))
      (Subgroup.mem_center_iff.1 hk ⟨x⁻¹ * (m : MulAut Q) * x, hm⟩)).symm
  have h2 : (x * (k : MulAut Q) * x⁻¹) * (m : MulAut Q)
      = (m : MulAut Q) * x * (k : MulAut Q) * x⁻¹ := by
    calc (x * (k : MulAut Q) * x⁻¹) * (m : MulAut Q)
        = x * ((k : MulAut Q) * (x⁻¹ * (m : MulAut Q) * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * (m : MulAut Q) * x) * (k : MulAut Q)) * x⁻¹ := by rw [hkc]
      _ = (m : MulAut Q) * x * (k : MulAut Q) * x⁻¹ := by group
  rw [h2]
  group

private theorem s16k_centralizes_center {Q : Type} [CommGroup Q] [Finite Q]
    {L' N : Subgroup (MulAut Q)} (hL : IsHat ↥L' ↥(alternatingGroup (Fin 6)))
    (hN : ∀ n ∈ N, ∀ l ∈ L', n * l * n⁻¹ ∈ L') {x : MulAut Q} (hxN : x ∈ N)
    (hxodd : Odd (orderOf x)) :
    ∀ k ∈ Subgroup.center ↥L', x * (k : MulAut Q) = (k : MulAut Q) * x := by
  have hxnorm : ∀ l : MulAut Q, l ∈ L' ↔ x * l * x⁻¹ ∈ L' := by
    intro l
    constructor
    · intro hl; exact hN x hxN l hl
    · intro hl
      have h := hN x⁻¹ (N.inv_mem hxN) (x * l * x⁻¹) hl
      have h' : x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ = l := by group
      rw [h'] at h
      exact h
  have hxinvnorm : ∀ l : MulAut Q, l ∈ L' ↔ x⁻¹ * l * x ∈ L' := by
    intro l
    constructor
    · intro hl
      have h := hN x⁻¹ (N.inv_mem hxN) l hl
      simpa using h
    · intro hl
      have h := hN x hxN (x⁻¹ * l * x) hl
      have h' : x * (x⁻¹ * l * x) * x⁻¹ = l := by group
      rw [h'] at h
      exact h
  have hZc3 : Nat.card ((Subgroup.center ↥L').map L'.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (K := Subgroup.center ↥L') (f := L'.subtype)
      L'.subtype_injective]
    exact hL.2.1
  have hxNmem : x ∈ Subgroup.normalizer
      ((Subgroup.center ↥L').map L'.subtype : Subgroup (MulAut Q)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.1 hh
      rw [← hk_eq]
      exact Subgroup.mem_map.2 ⟨_, s16k_conj_center_mem hxnorm k hk, rfl⟩
    · intro hh
      obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.1 hh
      have hxh : x⁻¹ * (k : MulAut Q) * x = h := by
        change x⁻¹ * (L'.subtype k) * x = h
        rw [hk_eq]
        group
      rw [← hxh]
      exact Subgroup.mem_map.2 ⟨_, s16k_conj_center_mem hxinvnorm k hk, rfl⟩
  have hxcen := Asc81c.mem_centralizer_of_odd_of_card_three hZc3 hxodd hxNmem
  intro k hk
  have hmem : (k : MulAut Q) ∈ (Subgroup.center ↥L').map L'.subtype :=
    Subgroup.mem_map.2 ⟨k, hk, rfl⟩
  exact ((Subgroup.mem_centralizer_iff.1 hxcen) (k : MulAut Q) hmem).symm

theorem s16k_pRank_normalizer_hat_a6 {Q : Type} [CommGroup Q] [Finite Q]
    (h2 : ∀ x : Q, x ^ 2 = 1) (hQ : Nat.card Q = 2 ^ 6) {L' N : Subgroup (MulAut Q)}
    (hL : IsHat ↥L' ↥(alternatingGroup (Fin 6)))
    (hN : ∀ n ∈ N, ∀ l ∈ L', n * l * n⁻¹ ∈ L') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p N ≤ CFSG.Open.pRank p L' := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E, hEN, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 N
  refine CFSG.SectionRank.le_pRank hp1 ?_ hE hcard
  intro x hx
  have hxN : x ∈ N := hEN hx
  have hxp : x ^ p = 1 := hE.2 x hx
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hxp)
  have hxnorm : ∀ l : MulAut Q, l ∈ L' ↔ x * l * x⁻¹ ∈ L' := by
    intro l
    constructor
    · intro hl; exact hN x hxN l hl
    · intro hl
      have h := hN x⁻¹ (N.inv_mem hxN) (x * l * x⁻¹) hl
      have h' : x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ = l := by group
      rw [h'] at h
      exact h
  have hxz := s16k_centralizes_center hL hN hxN hxodd
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hL
  have hperf : Group.IsPerfect ↥L' := hq.1
  have hirr : ∀ J : Subgroup Q, (∀ l ∈ L', ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ :=
    (CFSG.Quasithin.H13.hatA6SixIrreducible (V := Q) h2 hQ L' hperf hZ ⟨e⟩).2
  exact CFSG.Quasithin.HatA6.mem_of_normalizes h2 hQ hperf hZ e hirr hxnorm hxz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
