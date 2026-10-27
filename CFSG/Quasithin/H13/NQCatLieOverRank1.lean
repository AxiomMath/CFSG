module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inputs
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

theorem commutator_mem_of_sup_isCyclic {K : Type*} [Group K] {P D : Subgroup K}
    (hD : IsCyclic D) (hsup : P ⊔ D = normalizer (P : Set K)) {x y : K}
    (hx : x ∈ normalizer (P : Set K)) (hy : y ∈ normalizer (P : Set K)) :
    x * y * x⁻¹ * y⁻¹ ∈ P := by
  set N := normalizer (P : Set K) with hNdef
  have hPN : P ≤ N := le_normalizer
  have hDN : D ≤ N := hsup ▸ le_sup_right
  have htop : P.subgroupOf N ⊔ D.subgroupOf N = ⊤ := by
    rw [← subgroupOf_sup hPN hDN, hsup, subgroupOf_self]
  have hDc : IsMulCommutative D := IsCyclic.isMulCommutative
  set π := QuotientGroup.mk' (P.subgroupOf N) with hπ
  have hrep : ∀ a : ↥N, ∃ d : ↥N, (d : K) ∈ D ∧ π a = π d := by
    intro a
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_sup_of_normal_left.mp (htop ▸ mem_top a)
    refine ⟨d, hd, ?_⟩
    have hp1 : π p = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hp
    rw [map_mul, hp1, one_mul]
  obtain ⟨d₁, hd₁, h₁⟩ := hrep ⟨x, hx⟩
  obtain ⟨d₂, hd₂, h₂⟩ := hrep ⟨y, hy⟩
  have hd : d₁ * d₂ = d₂ * d₁ := by
    have h0 := hDc.is_comm.comm ⟨(d₁ : K), hd₁⟩ ⟨(d₂ : K), hd₂⟩
    have h1 : (d₁ : K) * d₂ = d₂ * d₁ := by simpa using Subtype.ext_iff.mp h0
    exact Subtype.ext h1
  have key : (⟨x, hx⟩ : ↥N) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥N)⁻¹ * (⟨y, hy⟩ : ↥N)⁻¹ ∈ P.subgroupOf N := by
    rw [← QuotientGroup.ker_mk' (P.subgroupOf N), MonoidHom.mem_ker, ← hπ, map_mul, map_mul,
      map_mul, map_inv, map_inv, h₁, h₂, ← map_mul, hd, map_mul]
    group
  exact key

theorem isRankOneSylow_of_benderType {K : Type*} [Group K]
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) : IsRankOneSylow K := by
  intro T hT hodd
  have hQ : ((hT.toSylow hodd : Sylow 2 K) : Subgroup K) = T := IsPGroup.toSylow_coe hT hodd
  obtain ⟨t, hc⟩ := h.exists_benderCore (hT.toSylow hodd)
  rw [hQ] at hc
  refine ⟨fun htop => ?_, fun M hTM hM => ?_, fun x hx y hy => ?_⟩
  · have h1 := hc.index_eq
    rw [CFSG.GH74.Uniqueness.Bender.borel, htop, index_top] at h1
    have : 0 < (2 ^ n) ^ i := by positivity
    omega
  · have := h.le_borel_of_sylow_le (hT.toSylow hodd) (by rw [hQ]; exact hTM) hM
    rwa [hQ] at this
  · exact commutator_mem_of_sup_isCyclic hc.isCyclic hc.sup_eq hx hy

theorem l2RankOneSylowFact_holds : L2RankOneSylowFact := by
  intro X _ n hn hL
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hn hL
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  exact isRankOneSylow_of_benderType (.linear n hn e)

@[expose] def LieOvergroupFactRank1 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ k : ℕ, 2 ≤ k ∧ (IsPSL 2 2 k S ∨ IsPSU 3 2 k S ∨ IsSz k S)) →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
      ∀ X : Subgroup S, P ≤ X → Group.IsSolvable ↥X → X ≤ Subgroup.normalizer (P : Set S)

@[expose] def LieOvergroupFactRank2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ k : ℕ, 2 ≤ k ∧
      (IsPSL 3 2 k S ∨ IsPSp4 2 k S ∨ IsG2 2 k S ∨ Is3D4 2 k S ∨ Is2F4 k S)) →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
      ∀ X : Subgroup S, P ≤ X → Group.IsSolvable ↥X → X ≤ Subgroup.normalizer (P : Set S)

theorem exists_benderType_of_rank_one {S : Type} [Group S] {k : ℕ} (hk : 2 ≤ k)
    (h : IsPSL 2 2 k S ∨ IsPSU 3 2 k S ∨ IsSz k S) : ∃ n i e : ℕ, BenderType S n i e := by
  rcases h with hL | hU | hS
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psl2_of_stated hL
    exact ⟨k, 1, 1, .linear k hk e⟩
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hk hU
    have hmodel : CFSG.Theory.Comparator.PSU3Model k = CFSG.Open.PSU3 2 k :=
        CFSG.Models.benderPSU3Model_eq_psu3 k
    exact ⟨k, 3, _, .unitary k hk (e.trans (MulEquiv.subgroupCongr hmodel.symm))⟩
  · obtain ⟨a, ha, -, ⟨e⟩⟩ :=
      CFSG.ComponentClassification.GMS78.exists_mulEquiv_sz_of_suzukiModel hS
    exact ⟨_, 2, 1, .suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))⟩

theorem lieOvergroupFactRank1_holds : LieOvergroupFactRank1 := by
  intro S _ _ hs ⟨k, hk, h⟩ P hP X hPX hX
  obtain ⟨n, i, e, hB⟩ := exists_benderType_of_rank_one hk h
  have hPodd : ¬ 2 ∣ P.index := by
    intro hd
    apply hP.2.2
    change 2 ∣ P.relIndex ⊤
    rwa [relIndex_top_right]
  obtain ⟨hN, hmax, -⟩ := isRankOneSylow_of_benderType hB P hP.2.1 hPodd
  by_cases hXt : X = ⊤
  · exfalso
    subst hXt
    have hsol : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := S)).toMonoidHom)
        (Subgroup.topEquiv (G := S)).surjective
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsol
    refine hN (normalizer_eq_top_iff.mpr ⟨fun p hp g => ?_⟩)
    rw [hcomm g p, mul_inv_cancel_right]
    exact hp
  · exact hmax X hPX hXt

theorem lieOvergroupFact_of (h1 : LieOvergroupFactRank1) (h2 : LieOvergroupFactRank2) :
    LieOvergroupFact := by
  intro S _ _ hs ⟨k, hk, hLie⟩ P hP X hPX hX
  rcases hLie with h | h | h | h | h | h | h | h
  · exact h1 S hs ⟨k, hk, Or.inl h⟩ P hP X hPX hX
  · exact h2 S hs ⟨k, hk, Or.inl h⟩ P hP X hPX hX
  · exact h1 S hs ⟨k, hk, Or.inr (Or.inl h)⟩ P hP X hPX hX
  · exact h2 S hs ⟨k, hk, Or.inr (Or.inl h)⟩ P hP X hPX hX
  · exact h2 S hs ⟨k, hk, Or.inr (Or.inr (Or.inl h))⟩ P hP X hPX hX
  · exact h2 S hs ⟨k, hk, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩ P hP X hPX hX
  · exact h1 S hs ⟨k, hk, Or.inr (Or.inr h)⟩ P hP X hPX hX
  · exact h2 S hs ⟨k, hk, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩ P hP X hPX hX

end CFSG.Quasithin.H13.NQCat
