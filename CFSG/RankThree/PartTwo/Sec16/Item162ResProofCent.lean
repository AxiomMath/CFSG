module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
public import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofA7
import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162

open CFSG Equiv CFSG.RankThree.PartTwo.KFacts.KP2

theorem cOne_mul_cTwo_cycleType : (cOne * cTwo).cycleType = {3, 3} := by
  have h := (eNineF_cycleType 1 1 (by decide)).2.mpr ⟨by decide, by decide⟩
  rwa [show eNineF 1 1 = cOne * cTwo by decide] at h

theorem pow_twelve_of_conj {x y r : Perm (Fin 7)} (hxy : y * x = x * y)
    (hr : x.cycleType = r.cycleType)
    (hr12 : ∀ y' : Perm (Fin 7), y' * r = r * y' → y' ^ 12 = 1) : y ^ 12 = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hr)
  have hy' : (g * y * g⁻¹) * r = r * (g * y * g⁻¹) := by
    rw [← hg]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hxy]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  have h := hr12 _ hy'
  rw [conj_pow] at h
  have h' := congrArg (fun z => g⁻¹ * z * g) h
  simpa [mul_assoc] using h'

theorem pow_twelve_eq_one_of_commute {x y : Perm (Fin 7)} (hx : orderOf x = 3)
    (hxy : y * x = x * y) : y ^ 12 = 1 := by
  rcases cycleType_of_orderOf_eq_three hx with h3 | h33
  · refine pow_twelve_of_conj hxy (h3.trans Step163Alt.cOne_cycleType.symm) fun y' hy' => ?_
    have h := forall_not_of_card_filter_eq_zero card_filter_centralizer_cOne y'
    obtain ⟨i, k, rfl⟩ : ∃ i : Fin 3, ∃ k : Fin 24, y' = cOne ^ (i : ℕ) * symA k := by
      by_contra hne
      exact h ⟨hy', hne⟩
    exact (check_cOne i k).1
  · refine pow_twelve_of_conj hxy (h33.trans cOne_mul_cTwo_cycleType.symm) fun y' hy' => ?_
    have h := forall_not_of_card_filter_eq_zero card_filter_centralizer_cOne_cTwo y'
    obtain ⟨i, j, b, rfl⟩ : ∃ i j : Fin 3, ∃ b : Bool,
        y' = eNineF i j * (if b then tauOne else 1) := by
      by_contra hne
      exact h ⟨hy', hne⟩
    rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul, (check_tauOne i j b).1, one_pow]

theorem isSolvable_of_forall_commute {Q : Type*} [Group Q] [Finite Q]
    (φ : Q ≃* alternatingGroup (Fin 7)) {x : Q} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (K : Subgroup Q) (hK : ∀ k ∈ K, k * x = x * k) : Group.IsSolvable K := by
  have hord : orderOf ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 3 := by
    have h3 : ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hx3, map_one, Subgroup.coe_one]
    have h1 : ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ≠ 1 := by
      intro h
      apply hx1
      apply φ.injective
      rw [map_one]
      exact Subtype.ext h
    exact orderOf_eq_prime h3 h1
  have h12 : ∀ k : K, k ^ 12 = 1 := by
    intro k
    have hc : ((φ k : alternatingGroup (Fin 7)) : Perm (Fin 7)) *
        ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) *
        ((φ k : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hK k k.2]
    have h := pow_twelve_eq_one_of_commute hord hc
    have hk : φ ((k : Q) ^ 12) = 1 := by
      apply Subtype.ext
      rw [map_pow, Subgroup.coe_pow, h, Subgroup.coe_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact φ.injective (hk.trans (map_one φ).symm)
  refine CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable K 2 3 Nat.prime_two
    Nat.prime_three fun p hp hpK => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hdvd : p ∣ 2 ^ 2 * 3 := by
    have := orderOf_dvd_of_pow_eq_one (h12 k)
    rw [hk] at this
    norm_num
    exact this
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_of_le_centralizer {Y X : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (Y : Set G)) (ht3 : t ^ 3 = 1)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) (hXY : X ≤ Y)
    (hXt : X ≤ Subgroup.centralizer {t}) (hX : ¬ Group.IsSolvable ↥X) :
    ∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨-, hZ, hinner, -, -⟩ := KFacts.KS14.a7_facts (↥Y ⧸ N) ⟨φ⟩
  obtain ⟨gb, hgb⟩ := hinner (Step163Alt.conjQuotTwo Y htN)
    ⟨1, by rw [pow_one]; exact Step163Alt.conjQuotTwo_pow_three Y htN ht3⟩
  have hact : ∀ y : ↥Y, π ⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN y).mp y.2⟩ =
      gb * π y * gb⁻¹ := by
    intro y
    have h1 := congrArg (fun σ : MulAut (↥Y ⧸ N) => σ (π y)) hgb
    simp only [hπ, QuotientGroup.mk'_apply] at h1
    rw [Step163Alt.conjQuotTwo_mk, MulAut.conj_apply] at h1
    simpa only [hπ, QuotientGroup.mk'_apply] using h1
  by_cases hgb1 : gb = 1
  · intro y hy
    have h3 := hact ⟨y, hy⟩
    rw [hgb1, one_mul, inv_one, mul_one] at h3
    have h2 := (Step163Alt.mk_eq_mk_iff ⟨y, hy⟩
      ⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN y).mp hy⟩).mp h3.symm
    have e : t * y * t⁻¹ * y⁻¹ = y * (y⁻¹ * (t * y * t⁻¹)) * y⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hy) _).mp h2
  · exfalso
    have hgb3 : gb ^ 3 = 1 := by
      have h1 : MulAut.conj (gb ^ 3) = 1 := by
        rw [map_pow, ← hgb, Step163Alt.conjQuotTwo_pow_three Y htN ht3]
      have hcen : gb ^ 3 ∈ Subgroup.center (↥Y ⧸ N) := by
        rw [Subgroup.mem_center_iff]
        intro q
        have := congrArg (fun σ : MulAut (↥Y ⧸ N) => σ q) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc q * gb ^ 3 = gb ^ 3 * q * (gb ^ 3)⁻¹ * gb ^ 3 := by rw [this]
          _ = gb ^ 3 * q := by group
      rw [hZ, Subgroup.mem_bot] at hcen
      exact hcen
    set X' := X.subgroupOf Y with hX'
    set f : ↥X' →* ↥Y ⧸ N := π.comp X'.subtype with hf
    have hcomm : ∀ z ∈ f.range, z * gb = gb * z := by
      rintro _ ⟨x, rfl⟩
      have hxX : ((x : ↥Y) : G) ∈ X := Subgroup.mem_subgroupOf.mp x.2
      have htx : (⟨t * (x : ↥Y) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN _).mp (x : ↥Y).2⟩ :
          ↥Y) = (x : ↥Y) := by
        apply Subtype.ext
        have hc := Subgroup.mem_centralizer_singleton_iff.mp (hXt hxX)
        simp only
        rw [← hc, mul_inv_cancel_right]
      have h1 := hact (x : ↥Y)
      rw [htx] at h1
      have h2 : f x = π (x : ↥Y) := rfl
      rw [h2]
      calc π (x : ↥Y) * gb = gb * π (x : ↥Y) * gb⁻¹ * gb := by rw [← h1]
        _ = gb * π (x : ↥Y) := by group
    have hsolR : Group.IsSolvable ↥f.range := isSolvable_of_forall_commute φ hgb3 hgb1 _ hcomm
    have hker2 : IsPGroup 2 ↥f.ker := by
      intro k
      have hkN : ((k : ↥X') : ↥Y) ∈ N := by
        have hk := k.2
        rw [MonoidHom.mem_ker] at hk
        exact (QuotientGroup.eq_one_iff _).mp hk
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨_, hkN⟩
      have h1 : ((k : ↥X') : ↥Y) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      simpa using h1
    have hnil : Group.IsNilpotent ↥f.ker := hker2.isNilpotent
    have hsolX' : Group.IsSolvable ↥X' :=
      Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict
        (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
    exact hX (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXY).symm.injective)

end CFSG.RankThree.PartTwo.Sec16.Res162
