module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeQuotientExclusion

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

open scoped Pointwise

universe u

theorem commuting_join_mem_iff
    {G : Type u} [Group G] (S T : Subgroup G)
    (hTS : T ≤ Subgroup.centralizer (S : Set G)) (g : G) :
    g ∈ S ⊔ T ↔ ∃ s ∈ S, ∃ t ∈ T, s * t = g := by
  have hnorm : T ≤ Subgroup.normalizer (S : Set G) :=
    hTS.trans (Subgroup.centralizer_le_normalizer (S : Set G))
  change g ∈ ((S ⊔ T : Subgroup G) : Set G) ↔ _
  rw [Subgroup.coe_mul_of_right_le_normalizer_left S T hnorm]
  rfl

theorem commuting_disjoint_join_card
    {G : Type u} [Group G] (S T : Subgroup G)
    (hTS : T ≤ Subgroup.centralizer (S : Set G)) (hdis : Disjoint S T) :
    Nat.card (S ⊔ T : Subgroup G) = Nat.card S * Nat.card T := by
  let E := S ⊔ T
  let SE := S.subgroupOf E
  let TE := T.subgroupOf E
  have hdisE : Disjoint SE TE := by
    apply disjoint_iff_inf_le.mpr
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp hdis)
      ⟨hg.1, hg.2⟩)
  have hcompl : SE.IsComplement' TE := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdisE, ?_⟩
    intro g
    obtain ⟨s, hs, t, ht, hst⟩ := (commuting_join_mem_iff S T hTS g).mp g.property
    let sE : E := ⟨s, (le_sup_left : S ≤ E) hs⟩
    let tE : E := ⟨t, (le_sup_right : T ≤ E) ht⟩
    exact ⟨(⟨sE, hs⟩, ⟨tE, ht⟩), Subtype.ext hst⟩
  have hScard : Nat.card SE = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hTcard : Nat.card TE = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  simpa only [hScard, hTcard] using hcompl.card_mul_card.symm

theorem commuting_prime_actor_data
    {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (x y : G)
    (hx : orderOf x = p) (hy : orderOf y = p) (hxy : Commute x y)
    (hdis : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y)) :
    CFSG.IsElementaryAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ∧
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 2 ∧
        ¬ IsCyclic (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) := by
  let : Fact p.Prime := ⟨hp⟩
  let S := Subgroup.zpowers x
  let T := Subgroup.zpowers y
  let : CFSG.IsElementaryAbelian p S :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one
      (orderOf_dvd_iff_pow_eq_one.mp (hx ▸ dvd_rfl))
  let : CFSG.IsElementaryAbelian p T :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one
      (orderOf_dvd_iff_pow_eq_one.mp (hy ▸ dvd_rfl))
  have hTS : T ≤ Subgroup.centralizer (S : Set G) := by
    intro t ht
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (hxy.zpow_zpow i j).eq
  let hE : CFSG.IsElementaryAbelian p (S ⊔ T : Subgroup G) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hTS
  have hcard : Nat.card (S ⊔ T : Subgroup G) = p ^ 2 := by
    rw [commuting_disjoint_join_card S T hTS hdis, Nat.card_zpowers,
      Nat.card_zpowers, hx, hy, pow_two]
  exact ⟨hE, hcard, CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard⟩

theorem isCyclic_ambient_elementary_actor_of_internal_kernel_dichotomy
    {G : Type u} [Group G] [Finite G] (M Q A : Subgroup G)
    [Subgroup.Normalizes A M] [(Q.subgroupOf M).Normal] {p : ℕ}
    (hp : p.Prime) (hpOdd : Odd p) [CFSG.IsElementaryAbelian p A]
    (hM : IsPGroup 2 M) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQproper : ¬ M ≤ Q)
    (hInv : ∀ x : G, x ∈ M → orderOf x = 2 → x ∈ Q)
    (hdichotomy : ∀ a : G, a ∈ A → a ≠ 1 →
      (∀ x : G, x ∈ M → x ∈ Q → a * x * a⁻¹ = x → x = 1) ∨
        (∀ x : G, x ∈ M → a * x * a⁻¹ = x → x ∈ Q)) :
    IsCyclic A := by
  have hQinv := ambient_conjugation_subgroupOf_invariant M Q A hAQ
  have hproper : Q.subgroupOf M ≠ ⊤ := by
    intro h
    exact hQproper (Subgroup.subgroupOf_eq_top.mp h)
  apply isCyclic_elementary_odd_actor_of_kernel_dichotomy hp hpOdd hM
    (Q.subgroupOf M) hQinv hproper
  · intro x hx
    exact hInv x x.property (by simpa only [orderOf_submonoid] using hx)
  · intro a ha
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    rcases hdichotomy a a.property haG with hs | hk
    · left
      intro x hx hax
      apply Subtype.ext
      exact hs x x.property hx (by
        simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          using congrArg Subtype.val hax)
    · right
      intro x hax
      exact hk x x.property (by
        simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          using congrArg Subtype.val hax)

theorem scalar_centralizer_orders_coprime
    {G : Type u} [Group G] [Finite G] (M Q X J : Subgroup G)
    [(Q.subgroupOf M).Normal] [Subgroup.Normalizes X M] [Subgroup.Normalizes J M]
    (hM : IsPGroup 2 M) (hQproper : ¬ M ≤ Q)
    (hInv : ∀ m : G, m ∈ M → orderOf m = 2 → m ∈ Q)
    (hXodd : Odd (Nat.card X)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hJQ : J ≤ Subgroup.normalizer (Q : Set G))
    (hJX : J ≤ Subgroup.centralizer (X : Set G)) (hdis : Disjoint X J)
    (hJfixQ : ∀ y : G, y ∈ J → ∀ m : G, m ∈ Q → y * m * y⁻¹ = m)
    (hscalar : ∀ x : G, x ∈ X → x ≠ 1 →
      ∀ m : G, m ∈ M → m ∈ Q → x * m * x⁻¹ = m → m = 1)
    (hJkernel : ∀ y : G, y ∈ J → y ≠ 1 → Odd (orderOf y) →
      ∀ m : G, m ∈ M → y * m * y⁻¹ = m → m ∈ Q) :
    Nat.Coprime (Nat.card X) (Nat.card J) := by
  apply Nat.coprime_of_dvd
  intro p hp hpX hpJ
  let : Fact p.Prime := ⟨hp⟩
  have hpOdd : Odd p := Odd.of_dvd_nat hXodd hpX
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) p hpX
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  have hxG : orderOf (x : G) = p := by simpa only [orderOf_submonoid] using hx
  have hyG : orderOf (y : G) = p := by simpa only [orderOf_submonoid] using hy
  let S := Subgroup.zpowers (x : G)
  let T := Subgroup.zpowers (y : G)
  let E := S ⊔ T
  have hSX : S ≤ X := Subgroup.zpowers_le.mpr x.property
  have hTJ : T ≤ J := Subgroup.zpowers_le.mpr y.property
  have hdisST : Disjoint S T := hdis.mono hSX hTJ
  have hxy : Commute (x : G) (y : G) := hJX y.property x x.property
  obtain ⟨hEelem, hEcard, hEnc⟩ :=
    commuting_prime_actor_data hp (x : G) (y : G) hxG hyG hxy hdisST
  let : CFSG.IsElementaryAbelian p E := hEelem
  have hEM : E ≤ Subgroup.normalizer (M : Set G) :=
    sup_le (hSX.trans (Subgroup.Normalizes.le_normalizer (A := X) (K := M)))
      (hTJ.trans (Subgroup.Normalizes.le_normalizer (A := J) (K := M)))
  let : Subgroup.Normalizes E M := ⟨hEM⟩
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (hSX.trans hXQ) (hTJ.trans hJQ)
  have hcyc : IsCyclic E := by
    apply isCyclic_ambient_elementary_actor_of_internal_kernel_dichotomy M Q E hp hpOdd hM
      hEQ hQproper hInv
    intro a ha hane
    have hTS : T ≤ Subgroup.centralizer (S : Set G) :=
      hTJ.trans (hJX.trans (Subgroup.centralizer_le hSX))
    obtain ⟨s, hs, t, ht, hst⟩ := (commuting_join_mem_iff S T hTS a).mp ha
    by_cases hsone : s = 1
    · have hate : a = t := by simpa only [hsone, one_mul] using hst.symm
      right
      apply hJkernel a (hate ▸ hTJ ht) hane
      have hatp : orderOf a ∣ p := by
        have hdiv := orderOf_dvd_of_mem_zpowers ht
        simpa only [← hate, hyG] using hdiv
      exact Odd.of_dvd_nat hpOdd hatp
    · left
      intro m hm hQm ham
      have htm := hJfixQ t (hTJ ht) m hQm
      have hsm : s * m * s⁻¹ = m := by
        calc
          s * m * s⁻¹ = s * (t * m * t⁻¹) * s⁻¹ := by rw [htm]
          _ = (s * t) * m * (s * t)⁻¹ := by group
          _ = m := by rw [hst]; exact ham
      exact hscalar s (hSX hs) hsone m hm hQm hsm
  exact hEnc hcyc

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime
