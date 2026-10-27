module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups


theorem exists_sl2_or_psl2_of_isFundamentalOver {X : Type} [Group X] {q : ℕ}
    {K : Subgroup X} (hK : IsFundamentalOver q K) :
    ∃ (p e₀ e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e₀ ∧ q = p ^ e₀ ∧
      (e = e₀ ∨ e = 3 * e₀) ∧
      (Nonempty (K ≃* SL(2, GaloisField p e)) ∨
        Nonempty (K ≃* PSL(2, GaloisField p e))) := by
  obtain ⟨p, e₀, e, hp, hp2, he₀, hq, he, φ, hφrange, hφker⟩ :=
    uc22s2112r34_exists_sl2_cover hK
  letI : Fact p.Prime := hp
  let φK : SL(2, GaloisField p e) →* K :=
    φ.codRestrict K fun g => by
      rw [← hφrange]
      exact ⟨g, rfl⟩
  have hφKs : Function.Surjective φK := by
    intro k
    have hk : (k : X) ∈ φ.range := by rw [hφrange]; exact k.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hk
    exact ⟨g, Subtype.ext hg⟩
  have hφKker : φK.ker ≤ center SL(2, GaloisField p e) := by
    intro g hg
    apply hφker
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hg))
  exact ⟨p, e₀, e, hp, hp2, he₀, hq, he,
    CFSG.ComponentClassification.RankTwoOddLie.sl2_or_psl2_of_surjective φK hφKs hφKker⟩

theorem sq_eq_one_of_mem_fundamental_centralizer {X : Type} [Group X] {q : ℕ}
    {K : Subgroup X} (hK : IsFundamentalOver q K) {z : X} (hzK : z ∈ K)
    (hzC : z ∈ centralizer (K : Set X)) : z ^ 2 = 1 := by
  obtain ⟨p, e₀, e, hp, -, -, -, -, hSL | hPSL⟩ :=
    exists_sl2_or_psl2_of_isFundamentalOver hK
  · obtain ⟨eK⟩ := hSL
    have hz : eK ⟨z, hzK⟩ ∈ center SL(2, GaloisField p e) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := eK.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg eK (Subtype.ext (mem_centralizer_iff.mp hzC k k.2))
    have hsq : (eK ⟨z, hzK⟩) ^ 2 = 1 := by
      rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hz with h | h <;>
        rw [h] <;> simp
    have hzsq : (⟨z, hzK⟩ : K) ^ 2 = 1 := eK.injective (by
      rw [map_pow, hsq, map_one])
    exact congrArg Subtype.val hzsq
  · obtain ⟨eK⟩ := hPSL
    have hz : eK ⟨z, hzK⟩ ∈ center PSL(2, GaloisField p e) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := eK.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg eK (Subtype.ext (mem_centralizer_iff.mp hzC k k.2))
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot, mem_bot] at hz
    have hz1 : z = 1 := congrArg Subtype.val (eK.injective (hz.trans (map_one eK).symm))
    simp [hz1]

theorem exists_psl2_quotient_of_isFundamentalOver {X : Type} [Group X] {q : ℕ}
    {K : Subgroup X} (hK : IsFundamentalOver q K) :
    ∃ (p e₀ e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e₀ ∧ q = p ^ e₀ ∧
      (e = e₀ ∨ e = 3 * e₀) ∧
      Nonempty (K ⧸ center K ≃* PSL(2, GaloisField p e)) := by
  obtain ⟨p, e₀, e, hp, hp2, he₀, hq, he, hSL | hPSL⟩ :=
    exists_sl2_or_psl2_of_isFundamentalOver hK
  · obtain ⟨eK⟩ := hSL
    exact ⟨p, e₀, e, hp, hp2, he₀, hq, he,
      ⟨QuotientGroup.congr (center K) (center SL(2, GaloisField p e))
        eK (Subgroup.map_center_eq eK)⟩⟩
  · obtain ⟨eK⟩ := hPSL
    let eQ : K ⧸ center K ≃*
        PSL(2, GaloisField p e) ⧸ center PSL(2, GaloisField p e) :=
      QuotientGroup.congr (center K) (center PSL(2, GaloisField p e))
        eK (Subgroup.map_center_eq eK)
    exact ⟨p, e₀, e, hp, hp2, he₀, hq, he,
      ⟨eQ.trans ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p e))).trans
        QuotientGroup.quotientBot)⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
