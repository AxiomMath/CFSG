module

public import CFSG.RankThree.PartTwo.Sec11.LStarPoints
public import CFSG.RankThree.PartTwo.KFacts.K72Moving
public import CFSG.RankThree.PartTwo.Sec11.Item114
public import CFSG.RankThree.PartTwo.Sec11.LStarL2

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def LThreeMinusPiNoFixedSylow : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec8.IsoLThreeMinusPi X 2 (3 * n) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ KFacts.IsInnerAut α →
      ∀ S : Sylow 3 X, ∃ y ∈ (S : Subgroup X), α y ≠ y

theorem lStarTransvectionL3_of (h97 : Sec9.Item97) (hK : LThreeMinusPiNoFixedSylow) :
    LStarTransvectionL3 := by
  rintro G _ _ A c L a R Y h ⟨n, hn, hL⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  obtain ⟨d, hdL, -, hA⟩ := Sec10.exists_inf_eq_zpowers h97 h.toHyp91
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have haN := h.toHyp81.a_mem_normalizer
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · exact hcN
    · exact haN
    · exact Subgroup.le_normalizer hdAL.2
  have hΩ : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, y * x = x * y) → x ∈ A := fun x hx3 hx =>
    Sec15.mem_of_mem_partTwoF h.mem_partTwoF hx3 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hx y hy)
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hcyc := KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi hn hL
  have hab : ∀ Q : Sylow 3 L, ∀ x ∈ (Q : Subgroup L), ∀ y ∈ (Q : Subgroup L),
      x * y = y * x := by
    intro Q x hx y hy
    have hinj : ∀ z ∈ (Q : Subgroup L), π z = 1 → z = 1 := by
      intro z hz hz1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
      obtain ⟨k, hk⟩ := Q.isPGroup' ⟨z, hz⟩
      have hk' : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have h2 : orderOf z ∣ Nat.card (aschbacherSolvableCore 3 L) :=
        Subgroup.orderOf_dvd_natCard _ hz1
      have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    obtain ⟨S, hS⟩ := (Q.isPGroup'.map π).exists_le_sylow
    have := hcyc S
    have hc : π x * π y = π y * π x := by
      have h1 := (IsCyclic.commGroup (α := S)).mul_comm ⟨π x, hS ⟨x, hx, rfl⟩⟩
        ⟨π y, hS ⟨y, hy, rfl⟩⟩
      exact congrArg Subtype.val h1
    have h2 : π (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
    have h3 := hinj _ ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hx hy)
      ((Q : Subgroup L).inv_mem ((Q : Subgroup L).mul_mem hy hx))) h2
    exact mul_inv_eq_one.mp h3
  set τ₀ := thetaQuotMulAut L (compAction L ⟨a, haN⟩) with hτ₀
  have hτ3 : τ₀ ^ 3 = 1 := h.toHyp81.induced_pow_three
  have hτout : ¬ KFacts.IsInnerAut τ₀ := h.toHyp81.not_isInnerAut_induced
  have hQ : ∀ Q : Sylow 3 L, ¬ ∀ y ∈ (Q : Subgroup L), a * (y : G) = y * a := by
    intro Q hQa
    obtain ⟨y, hy, hy'⟩ := hK _ n hn hL τ₀ hτ3 hτout
      (Q.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L)))
    apply hy'
    rw [Sylow.coe_mapSurjective] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [QuotientGroup.mk'_apply, hτ₀, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show a * z * a⁻¹ = z
    rw [hQa z hz, mul_inv_cancel_right]
  exact KFacts.exists_moving_of_not_centralizes_sylow hcomm hexp hΩ hAN h.a_mem hab hQ

theorem item115_of_noFixedSylow (h97 : Sec9.Item97) (hK : LThreeMinusPiNoFixedSylow) : Item115 :=
  item115_of_lStarL3 h97 (lStarTransvectionL3_of h97 hK)


@[expose] def LThreeMinusPiInverting : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec8.IsoLThreeMinusPi X 2 (3 * n) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ KFacts.IsInnerAut α →
      ∀ x : X, x ^ 3 = 1 → x ≠ 1 → α x = x → ∃ y : X, α y = y ∧ y * x * y⁻¹ = x⁻¹

theorem lStarInvertingL3_of (h97 : Sec9.Item97) (hK : LThreeMinusPiInverting) :
    LStarInvertingL3 := by
  rintro G _ _ A c L a R Y h ⟨n, hn, hL⟩ d hdL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  obtain ⟨h3, hcl⟩ := h97 G A c L a R h.toHyp91
  have hA := hcl d hdL
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hd3 : orderOf d = 3 := by rw [← Nat.card_zpowers, ← hdL, h3]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  have haN := h.toHyp81.a_mem_normalizer
  have hsc : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  set τ₀ := thetaQuotMulAut L (compAction L ⟨a, haN⟩) with hτ₀
  have hτ3 : τ₀ ^ 3 = 1 := h.toHyp81.induced_pow_three
  have hτout : ¬ KFacts.IsInnerAut τ₀ := h.toHyp81.not_isInnerAut_induced
  set db : L ⧸ aschbacherSolvableCore 3 L := ((⟨d, hdAL.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
    with hdb
  have hτd : τ₀ db = db := by
    rw [hdb, hτ₀, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show a * d * a⁻¹ = d
    rw [hcomm a h.a_mem d hdAL.1, mul_inv_cancel_right]
  have hdb3 : db ^ 3 = 1 := by
    rw [hdb, ← QuotientGroup.mk_pow]
    have : (⟨d, hdAL.2⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hexp d hdAL.1)
    rw [this, QuotientGroup.mk_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    rw [hdb, QuotientGroup.eq_one_iff] at h1
    have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
      (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
    have h2 := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_mk, hd3] at h2
    exact hθ3 h2
  obtain ⟨yb, hybτ, hybd⟩ := hK _ n hn hL τ₀ hτ3 hτout db hdb3 hdb1 hτd
  exact KFacts.exists_inverting_of_bar hAe h.mem_A h.a_mem hdAL.1 hA hsc.2 hdAL.2 haN yb hybτ hybd

theorem item117_of_item113 (h97 : Sec9.Item97) (h112 : Item112) (h113 : Item113)
    (h116 : Item116) (hT : LThreeMinusPiNoFixedSylow) (hI : LThreeMinusPiInverting) :
    Item117 :=
  item117_of h97 h112 (item114_of h113) (item115_of_noFixedSylow h97 hT) h116
    (lStarTransvection_of h97 (lStarTransvectionL3_of h97 hT))
    (lStarInverting_of h97 (lStarInvertingL3_of h97 hI))

end CFSG.RankThree.PartTwo.Sec11
