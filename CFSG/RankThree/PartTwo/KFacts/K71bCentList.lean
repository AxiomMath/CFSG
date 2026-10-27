module

public import CFSG.RankThree.PartTwo.KFacts.K71bRigidity
public import CFSG.RankThree.PartTwo.Sec11.Item112

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem mem_zpowers_of_fixes_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α)
    {β : MulAut X} (hβ : ∀ z, α z = z → β z = z) : β ∈ Subgroup.zpowers α := by
  have hc3 : ∀ {Y : Type} [Group Y] (e : X ≃* Y), MulAut.congr e α ^ 3 = 1 := fun e => by
    rw [← map_pow, hα3, map_one]
  have hcout : ∀ {Y : Type} [Group Y] (e : X ≃* Y), ¬ IsInnerAut (MulAut.congr e α) :=
    fun e h => hout ((isInnerAut_congr e α).mp h)
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hXL⟩ := hL3
    have hq2 : 2 < 2 ^ (3 * n) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
    rcases hXL with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
    · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
        ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
      obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
      have hq₀ : 2 ^ (3 * n / 3) ≠ 2 := by
        rw [Nat.mul_div_cancel_left n (by norm_num)]
        intro h2
        have hn1 : n = 1 := Nat.pow_right_injective (le_refl 2) (h2.trans (pow_one 2).symm)
        subst hn1
        norm_num at hq
      refine mem_zpowers_of_congr (e.trans φ.symm) ?_
      refine mem_zpowers_of_fixes_unitaryPSU h hq2 hq₀ (hc3 (e.trans φ.symm))
        (fun hD => hcout (e.trans φ.symm) ?_) (fixes_congr (e.trans φ.symm) hβ)
      exact isInnerAut_of_mem_psuConj_range h hq hD
    · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 (3 * n))
      refine mem_zpowers_of_congr (e.trans φ) ?_
      refine mem_zpowers_of_fixes_projectiveSL le_rfl (hc3 (e.trans φ))
        (fun hD => hcout (e.trans φ) ?_) (fixes_congr (e.trans φ) hβ)
      exact isInnerAut_of_mem_linearAutGroup (by rwa [GaloisField.card 2 (3 * n) (by omega)]) hD
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := Sec11.exists_mulEquiv_psl2_of_isList1016 hX hL3
    exact mem_zpowers_of_congr e (mem_zpowers_of_fixes_psl2' (hc3 e) (hcout e)
      (fixes_congr e hβ))

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_pow_mem_thetaQuotCentralizer_of_list {L : Subgroup G} {a t : G}
    (hL : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) (ha : Sec4.InducesOuterTheta a L)
    (ha3 : a ^ 3 = 1) (htN : t ∈ Subgroup.normalizer (L : Set G))
    (_ht3 : ∃ k : ℕ, t ^ 3 ^ k = 1) (_hta : t * a = a * t)
    (htK : ∀ k ∈ Sec11.sec11K L a, t * k * t⁻¹ * k⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (Sec11.sec11K L a)) :
    ∃ i : ℕ, t * a ^ i ∈ Sec4.thetaQuotCentralizer L := by
  obtain ⟨haN, hout⟩ := ha
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hα
  set β := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨t, htN⟩) with hβ
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hαout : ¬ IsInnerAut α := hout
  obtain ⟨hZ, hQ, -⟩ := Sec11.fixedPoints_facts_of_isList1016 hL hα3 hαout
  have hfix : ∀ z, α z = z → β z = z := by
    intro z hz
    have hz' : z ∈ (Sec11.kMap L a).range := by
      rw [Sec11.range_kMap_eq haN ha3 hQ.1, Sec11.range_cMap haN ha3]
      exact hz
    obtain ⟨k, rfl⟩ := hz'
    obtain ⟨y, hy, hyk⟩ := htK k k.2
    have hyk' : (y : G) = t * (k : G) * t⁻¹ * (k : G)⁻¹ := hyk
    have hθs := (solvable_prime_complement_core_characterization
      (H := Sec11.sec11K L a) Nat.prime_three).1
    have hker := Sec11.le_ker_kMap_of_normal_solvable haN ha3 hQ hZ _ hθs hy
    rw [MonoidHom.mem_ker] at hker
    have htkL : t * (k : G) * t⁻¹ ∈ L := by
      have hkL : (k : G) ∈ L := Sec11.sec11K_le L a k.2
      exact (Subgroup.mem_normalizer_iff.mp htN _).mp hkL
    have e1 : (⟨t * (k : G) * t⁻¹, htkL⟩ : L) =
        Subgroup.inclusion (Sec11.sec11K_le L a) y * Subgroup.inclusion (Sec11.sec11K_le L a) k :=
      Subtype.ext (by
        change t * (k : G) * t⁻¹ = (y : G) * (k : G)
        rw [hyk']
        group)
    change β ((Subgroup.inclusion (Sec11.sec11K_le L a) k : L) :
      L ⧸ aschbacherSolvableCore 3 L) = _
    rw [hβ, Sec4.thetaQuotMulAut_mk]
    have e2 : Sec4.compAction L ⟨t, htN⟩ (Subgroup.inclusion (Sec11.sec11K_le L a) k) =
        ⟨t * (k : G) * t⁻¹, htkL⟩ := Subtype.ext rfl
    rw [e2, e1, QuotientGroup.mk_mul]
    have e3 : ((Subgroup.inclusion (Sec11.sec11K_le L a) y : L) :
        L ⧸ aschbacherSolvableCore 3 L) = 1 := hker
    rw [e3, one_mul]
    rfl
  obtain ⟨i, hi⟩ := exists_pow_eq_of_mem_zpowers hα3
    (mem_zpowers_of_fixes_of_isList1016 hL hα3 hαout hfix)
  refine ⟨2 * i, ?_⟩
  have hmem : t * a ^ (2 * i) ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem htN (pow_mem haN _)
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  have e4 : (⟨t * a ^ (2 * i), hmem⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨t, htN⟩ * ⟨a, haN⟩ ^ (2 * i) := Subtype.ext (by simp)
  rw [e4, map_mul, map_pow]
  change β * α ^ (2 * i) = 1
  rw [hi, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hα3, one_pow]

end CFSG.RankThree.PartTwo.KFacts
