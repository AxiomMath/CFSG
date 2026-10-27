module

public import CFSG.RankThree.CentralLift.EvenScalarCover
public import CFSG.RankThree.Classical.EvenSurvivingScalarRank
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars projectiveSL proj scalars_eq_center)

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem isTwoLocal_map_of_mulEquiv {K : Subgroup G} (hK : CFSG.Assembly.IsTwoLocal K)
    (e : G ≃* H) : CFSG.Assembly.IsTwoLocal (K.map e.toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hK
  refine ⟨P.map e.toMonoidHom, ?_, hP2.map _, Subgroup.map_equiv_normalizer_eq P e⟩
  rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P e.injective]

theorem localRank_le_of_mulEquiv [Finite G] [Finite H] (e : G ≃* H) {p : ℕ} (hp : p.Prime) :
    localRank p G ≤ localRank p H := by
  apply csSup_le'
  rintro _ ⟨K, hK, rfl⟩
  calc CFSG.Assembly.pRank p K ≤ CFSG.Assembly.pRank p (K.map e.toMonoidHom) :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp e.toMonoidHom
          e.injective K
    _ ≤ localRank p H :=
        CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt (isTwoLocal_map_of_mulEquiv hK e)

end Transport

section Scalar

variable {p f n : ℕ} {L : Type} [Group L] [Finite L]

theorem prime_dvd_card_of_isPGroup_of_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Z : Subgroup G} (hZ : IsPGroup p Z) (hne : Z ≠ ⊥) : p ∣ Nat.card Z := by
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rcases k with _ | k
  · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])) hne
  · rw [hk]
    exact dvd_pow_self p (Nat.succ_ne_zero k)

theorem even_linear_small_local_rank_prime_center_trivial (hp : p.Prime) (hp3 : 3 < p)
    (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2)
    (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n 2 f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  let e' : L ⧸ Subgroup.center L ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K).symm)
  let η : L →* projectiveSL n K := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hη : Function.Surjective η := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e' (x : L ⧸ Subgroup.center L) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have : Group.IsPerfect L := hL.1
  obtain ⟨⟨φ, hφ, -⟩, hprop⟩ := even_field_linear_perfect_central_large_prime_scalar_cover hp hp3
    hK hn η hη hηker.le (by rw [hηker]; exact hZ)
  obtain ⟨-, hker, -, ⟨e₂, -⟩, ⟨ψ⟩, -, -⟩ := hprop φ hφ
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  have hpR : p ∣ φ.ker.relIndex (scalars n K) := by
    have h1 : Nat.card η.ker = φ.ker.relIndex (scalars n K) := by
      rw [Nat.card_congr ψ.toEquiv]
      rfl
    rw [← h1, hηker]
    exact prime_dvd_card_of_isPGroup_of_ne_bot hZ hne
  set ι := specialLinearGroupEquivStatedSL n K
  have hscal : (scalars n K).map ι.toMonoidHom =
      (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
    rw [scalars_eq_center]
    exact map_center_eq_statedScalars n K
  set B : Subgroup (StatedSL n K) := φ.ker.map ι.toMonoidHom
  have : B.Normal := Subgroup.Normal.map (MonoidHom.normal_ker φ) ι.toMonoidHom ι.surjective
  have hB : B ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
    rw [← hscal]
    exact Subgroup.map_mono hker
  have hpB : p ∣ B.relIndex ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
    rw [← hscal, Subgroup.relIndex_map_map_of_injective _ _ ι.injective]
    exact hpR
  obtain ⟨-, -, -, hrank, h3⟩ := CFSG.RankThree.Classical.even_linear_surviving_scalar_local_rank
    hp hp3 hf hK hn B hB hpB
  have e₃ : StatedSL n K ⧸ B ≃* L := (QuotientGroup.congr φ.ker B ι rfl).symm.trans e₂
  have := localRank_le_of_mulEquiv e₃ hp
  omega

theorem even_unitary_small_local_rank_prime_center_trivial (hp : p.Prime) (hp3 : 3 < p)
    (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2)
    (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let η : L →* StatedProj (StatedSU n (2 ^ f) K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hηker : η.ker = Subgroup.center L := CFSG.LieType.Steinberg.ker_comp_mk' _ e
  have : Group.IsPerfect L := hL.1
  obtain ⟨⟨φ, hφ, -⟩, hprop⟩ := even_field_unitary_perfect_central_large_prime_scalar_cover hp hp3
    h hn η (e.surjective.comp (QuotientGroup.mk'_surjective _)) hηker.le
    (by rw [hηker]; exact hZ)
  obtain ⟨-, hker, -, ⟨e₂, -⟩, ⟨ψ⟩, -, -⟩ := hprop φ hφ
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  have hpB : p ∣ φ.ker.relIndex ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) := by
    have h1 : Nat.card η.ker =
        φ.ker.relIndex ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) := by
      rw [Nat.card_congr ψ.toEquiv]
      rfl
    rw [← h1, hηker]
    exact prime_dvd_card_of_isPGroup_of_ne_bot hZ hne
  obtain ⟨-, -, -, hrank, h3⟩ := CFSG.RankThree.Classical.even_unitary_surviving_scalar_local_rank
    hp hp3 h hn φ.ker hker hpB
  have hrank' : n - 2 ≤ localRank p (StatedSU n (2 ^ f) K ⧸ φ.ker) := hrank
  have := localRank_le_of_mulEquiv e₂ hp
  omega

end Scalar

theorem even_classical_small_local_rank_quasisimple_prime_center_trivial {p n f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus)
    (hM : StatedClassicalModel (L ⧸ Subgroup.center L) t n 2 f) :
    Subgroup.center L = ⊥ := by
  have hodd : Odd (Nat.card (Subgroup.center L)) := odd_card_of_isPGroup hp (by omega) hZ
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact even_linear_small_local_rank_prime_center_trivial hp hp3 hL hZ hloc hM
  · exact even_unitary_small_local_rank_prime_center_trivial hp hp3 hL hZ hloc hM
  · exact (CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hL hodd hM).1
  · obtain ⟨⟨-, -, -, h2⟩, -⟩ := hM
    exact absurd rfl h2
  · exact (CFSG.SectionRank.EvenCover.even_split_orthogonal_odd_cover_catalog_step hL hodd hM).1
  · exact (CFSG.SectionRank.EvenCover.even_nonsplit_orthogonal_odd_cover_catalog_step hL hodd
      hM).1

end CFSG.RankThree.CentralLift
