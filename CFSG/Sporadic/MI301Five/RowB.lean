module

public import CFSG.Sporadic.MI301Five.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpOdd
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Open CFSG.Monster.Existence CFSG.EvenSporadicStandard.HNRecog Subgroup

variable {G : Type} [Group G] {α d z : G}

theorem FiveFrame.eq_one_of_mem_zpowers_of_mem_cent (F : FiveFrame α d z) {y : G}
    (hy : y ∈ zpowers d) (hyα : y ∈ cent α) : y = 1 := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
  have hc : α * d ^ j * α⁻¹ = (d ^ j)⁻¹ := by
    have h := map_zpow (MulAut.conj α) d j
    simp only [MulAut.conj_apply, F.inverts, inv_zpow] at h
    exact h
  have hcomm : α * d ^ j * α⁻¹ = d ^ j := by
    rw [← mem_centralizer_singleton_iff.1 hyα, mul_inv_cancel_right]
  have h2 : orderOf (d ^ j) ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_two]
    nth_rewrite 2 [hcomm.symm.trans hc]
    exact mul_inv_cancel _
  have h5 : orderOf (d ^ j) ∣ 5 :=
    (Subgroup.orderOf_dvd_natCard (zpowers d) hy).trans (by rw [Nat.card_zpowers, F.orderOf_d])
  have h1 := Nat.dvd_gcd h2 h5
  rw [show Nat.gcd 2 5 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

private theorem pow_sixty_eq_one (q : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    q ^ 60 = 1 := by
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine Prod.ext ?_ ?_
  · rw [Prod.pow_fst, ← hA, pow_card_eq_one']
    rfl
  · rw [Prod.pow_snd, ← hA, pow_card_eq_one']
    rfl

private theorem pow_five_eq_one_of_shape {C : Type} [Group C] (hX : IsExtraspecialPlusByA5WrTwo C)
    {x : C} (hx : x ^ 25 = 1) : x ^ 5 = 1 := by
  obtain ⟨Q, _, hQ⟩ := hX
  obtain ⟨e⟩ := hQ.quotient
  have hw25 : e (x : C ⧸ Q) ^ 25 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one, map_one]
  have hodd : Odd (orderOf (e (x : C ⧸ Q))) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hw25)
  have hmem := CSide.cSide_mem_commutator_of_odd hodd
  rw [← A5WrTwo.range_baseEmb] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hw60 : e (x : C ⧸ Q) ^ 60 = 1 := by
    rw [← hq, ← map_pow, pow_sixty_eq_one, map_one]
  have hw5 : e (x : C ⧸ Q) ^ 5 = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw25) (orderOf_dvd_of_pow_eq_one hw60)
    rw [show Nat.gcd 25 60 = 5 by norm_num] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  have hQ5 : x ^ 5 ∈ Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact e.injective (by rw [map_pow, hw5, map_one])
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card hQ.plus.2.1
  obtain ⟨k, hk⟩ := hQ2 ⟨x ^ 5, hQ5⟩
  have hk' : (x ^ 5) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h5 : (x ^ 5) ^ 5 = 1 := by rw [← pow_mul, hx]
  have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h5)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem FiveFrame.exists_rowB [Finite G] (F : FiveFrame α d z)
    (hX : IsExtraspecialPlusByA5WrTwo ↥(cent2 α d ⊓ cent z)) :
    ∃ B₁ : Subgroup G, (IsElemAbelian 5 B₁ ∧ Nat.card B₁ = 5 ^ 3) ∧ d ∈ B₁ ∧
      B₁ ≤ zpowers d ⊔ (cent2 α d ⊓ cent z) := by
  set X : Subgroup G := cent2 α d ⊓ cent z with hXdef
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime 5 (n := 2) (G := ↥X)
    (by rw [F.card_z]; norm_num)
  set F₁ : Subgroup G := F₀.map X.subtype with hF₁
  have hF₁X : F₁ ≤ X := map_subtype_le F₀
  have hF₁c : Nat.card F₁ = 5 ^ 2 := (card_map_of_injective X.subtype_injective).trans hF₀
  have hF₁e : ∀ y ∈ F₁, y ^ 5 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h25 : y ^ 25 = 1 := by
      have h := pow_card_eq_one' (x := (⟨y, hy⟩ : F₀))
      rw [hF₀] at h
      simpa using congrArg Subtype.val h
    show (y : G) ^ 5 = 1
    rw [← SubgroupClass.coe_pow, pow_five_eq_one_of_shape hX h25]
    rfl
  have hF₁comm : ∀ a ∈ F₁, ∀ b ∈ F₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hF₀).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg (fun t : F₀ => ((t : ↥X) : G)) h
  have hcomm : ∀ a ∈ zpowers d, ∀ b ∈ F₁, Commute a b := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha
    have hbd : b * d = d * b := mem_centralizer_singleton_iff.1 (hF₁X hb).1.2
    exact Commute.zpow_left hbd.symm j
  have hdisj : Disjoint (zpowers d) F₁ := by
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    exact (mem_bot).2 (F.eq_one_of_mem_zpowers_of_mem_cent (mem_inf.1 hy).1
      (hF₁X (mem_inf.1 hy).2).1.1)
  set φ : ↥(zpowers d) × ↥F₁ →* G := (zpowers d).subtype.noncommCoprod F₁.subtype fun a b =>
    show Commute ((zpowers d).subtype a) (F₁.subtype b) from hcomm a a.2 b b.2 with hφ
  have hinj : Function.Injective φ := Subgroup.mul_injective_of_disjoint hdisj
  have hr : φ.range = zpowers d ⊔ F₁ := by
    rw [hφ, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hpow : ∀ q : ↥(zpowers d) × ↥F₁, q ^ 5 = 1 := fun q => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [Prod.pow_fst, SubgroupClass.coe_pow]
      exact orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard _ q.1.2).trans
        (by rw [Nat.card_zpowers, F.orderOf_d]))
    · rw [Prod.pow_snd, SubgroupClass.coe_pow]
      exact hF₁e _ q.2.2
  have hqc : ∀ q q' : ↥(zpowers d) × ↥F₁, q * q' = q' * q := by
    intro q q'
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 q.1.2
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 q'.1.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (q.1 : G) * q'.1 = q'.1 * q.1
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self d i j).eq
    · show (q.2 : G) * q'.2 = q'.2 * q.2
      exact hF₁comm _ q.2.2 _ q'.2.2
  have hmem : ∀ x ∈ zpowers d ⊔ F₁, x ∈ φ.range := fun x hx => by
    rw [hr]
    exact hx
  refine ⟨zpowers d ⊔ F₁, ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩,
    mem_sup_left (mem_zpowers d), sup_le_sup_left hF₁X _⟩
  · obtain ⟨q, hq⟩ := hmem _ a.2
    obtain ⟨q', hq'⟩ := hmem _ b.2
    show (a : G) * b = b * a
    rw [← hq, ← hq', ← map_mul, ← map_mul, hqc]
  · intro x hx
    obtain ⟨q, rfl⟩ := hmem x hx
    rw [← map_pow, hpow, map_one]
  · rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, F.orderOf_d, hF₁c]
    norm_num

end CFSG.Sporadic.MI301Five
