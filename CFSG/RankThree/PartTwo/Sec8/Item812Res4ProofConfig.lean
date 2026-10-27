module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofOmega
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof811
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofChoice
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item86ResProof
open CFSG.Assembly.RankThreeEven (projSp)

section Final

@[expose] def Pair89CentB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) ⊆
      (Subgroup.zpowers b : Set G)

@[expose] def Pair89GTwoB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n → ∀ m : ℕ, Sec8PairGTwo X a m

@[expose] def Pair89Occurs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, ∃ (c' : G) (L' : Subgroup G) (a' b' : G) (X' : Subgroup G) (n' : ℕ),
      Sec8Pair G A c' L' a' b' X' n' ∧ ((b', X') = p ∨ (c', L') = p)

theorem Sec8Pair.swap
    (h84 : Pair84A) (hsym : Pair84Sym) (hC : Pair89CentB) (hG : Pair89GTwoB)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hLU : ∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) :
    ∃ m : ℕ, Sec8Pair G A b X a c L m := by
  have hrel := hsym G A c L a b X n h c L h.pairRel
  obtain ⟨m, hm⟩ := hrel.2.1
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  refine ⟨m,
    { toHyp81 := hyp81_of_partner h.toHyp81 h.card_eq hbA hb1 h.pairRel.2.2.1 h.mem_pairOmega
        (h84 G A c L a b X n h) (hC G A c L a b X n h)
      card_eq := h.card_eq
      pairRel := hrel
      isGammaIndex := hm
      mem_pairOmega := h.pairRel.1
      not_unitary := hLU
      centralizer_of_unitary := fun ⟨k, hk⟩ => absurd hk (h.not_unitary k)
      gTwo := hG G A c L a b X n h m
      gTwoPartner := Item86ResProof.sec8PairGTwo_forall
        (Item86ResProof.one_le_of_isGammaIndex h.isGammaIndex)
        (Item86ResProof.isGammaType_of_isGammaIndex h.isGammaIndex) h.gTwo }⟩

theorem pair89CentB_of (h87 : Item87) (hXY : Item89XY) : Pair89CentB := by
  intro G _ _ A c L a b X n h x hx
  obtain ⟨Y, hY, hIJ⟩ := h87 G A c L a b X n h
  have hX := (hXY G A c L a b X n h Y hY hIJ).1
  have hC := pair810Center G A c L a b X n h hX
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := by
    have hle : X.map (MulAut.conj x).toMonoidHom ≤ X := by
      rintro _ ⟨l, hl, rfl⟩
      have h1 := hx.2 l hl
      have h2 : x * l * x⁻¹ = x * l * x⁻¹ * l⁻¹ * l := by group
      change x * l * x⁻¹ ∈ X
      rw [h2]
      exact X.mul_mem (Subgroup.map_subtype_le _ h1) hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  have hxC : x ∈ Sec4.thetaQuotCentralizer X := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun l hl => ?_⟩
    have h1 := hx.2 l hl
    have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta X (inv_mem hl)) _).mp h1
    have he : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
    rw [he] at h2
    exact h2
  exact hC ⟨hx.1, hxC⟩

theorem isUnitaryTwo_three_mul_of_isGammaIndex {G : Type} [Group G] [Finite G]
    {A Le : Subgroup G} {d : G} {m : ℕ} (h : IsGammaIndex A Le d m) {k : ℕ}
    (hk : IsUnitaryTwo (Le ⧸ aschbacherSolvableCore 3 Le) k) :
    IsUnitaryTwo (Le ⧸ aschbacherSolvableCore 3 Le) (3 * m) := by
  have hm : 1 ≤ m := one_le_of_isGammaIndex h
  obtain ⟨-, -, -, ⟨j, hj, hjm, he, -⟩ | ⟨htype, -⟩⟩ := h
  · exact ((sigF4_of_reeF4 hm ⟨j, hj, hjm, he⟩).not_isUnitaryTwo hm k hk).elim
  · rcases htype with hD | hG | hU | hS | hSp
    · exact ((sigD4_of_isoTrialityD4 hm hD).not_isUnitaryTwo hm k hk).elim
    · exact ((sigG2_of_isoGTwo hm hG).not_isUnitaryTwo hm k hk).elim
    · exact Or.inl hU
    · exact Or.inr hS
    · obtain ⟨e⟩ := hSp
      exact ((sigSp4_of_projSp hm e).not_isUnitaryTwo hm k hk).elim

theorem pair89GTwoB_of (h87 : Item87) (hXY : Item89XY) : Pair89GTwoB := by
  intro G _ _ A c L a b X n h m
  obtain ⟨Y, hY, hIJ⟩ := h87 G A c L a b X n h
  have hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * 1))) := by
    simpa using (hXY G A c L a b X n h Y hY hIJ).1
  obtain ⟨e⟩ := hX
  have hS := sigSp4_of_projSp le_rfl e
  rintro (hD | hG2)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨q, -, -, hqe, -⟩ := hD
      exact absurd hqe q.exponent_pos.ne'
    · exact ((sigD4_of_isoTrialityD4 hm hD).false_of_sigSp4 hS hm).elim
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨K, _, _, hK, -⟩ := hG2
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
    · exact ((sigG2_of_isoGTwo hm (isoGTwo_of_isoGTwoEven (by omega) hG2)).false_of_sigSp4 hS hm
        le_rfl).elim

theorem pair89InConfig_of (hOcc : Pair89Occurs) (hC : Pair89CentB) (hG : Pair89GTwoB)
    (hsym : Pair84Sym) (h84 : Pair84A) : Pair89InConfig := by
  intro G _ _ A c L a b X n h p hp
  obtain ⟨c', L', a', b', X', n', h', hcase⟩ := hOcc G A c L a b X n h p hp
  rcases hcase with hpart | hfirst
  · exact ⟨c', L', a', b', X', n', h', Or.inl hpart⟩
  · by_cases hLU : ∃ k : ℕ, IsUnitaryTwo (L' ⧸ aschbacherSolvableCore 3 L') k
    · obtain ⟨k, hk⟩ := hLU
      exact ⟨c', L', a', b', X', n', h',
        Or.inr ⟨hfirst, isUnitaryTwo_three_mul_of_isGammaIndex h'.isGammaIndex hk⟩⟩
    · simp only [not_exists] at hLU
      obtain ⟨m, hm⟩ := h'.swap h84 hsym hC hG hLU
      exact ⟨b', X', a', c', L', m, hm, Or.inl hfirst⟩

theorem pair89InConfig_of_xy (hOcc : Pair89Occurs) (h87 : Item87) (hXY : Item89XY)
    (hsym : Pair84Sym) (h84 : Pair84A) : Pair89InConfig :=
  pair89InConfig_of hOcc (pair89CentB_of h87 hXY) (pair89GTwoB_of h87 hXY) hsym h84

end Final

end CFSG.RankThree.PartTwo.Sec8
