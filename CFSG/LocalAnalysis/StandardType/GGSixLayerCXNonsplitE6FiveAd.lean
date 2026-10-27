module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6FiveData
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Label
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCyclicCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSpOne

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open scoped MatrixGroups

namespace ExcNonsplit

section Abstract

theorem mem_zpowers_of_pSubgroups_cyclic {C : Type} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q) {a b : C} (ha : orderOf a = p)
    (hb : b ^ p = 1) (hab : a * b = b * a) : b ∈ Subgroup.zpowers a := by
  have : Fact p.Prime := ⟨hp⟩
  have hpa : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hpb : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hb)
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set C) := by
    have hmem : a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left (Commute.symm hab) k).eq)
    exact Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hmem)
  have hQp : IsPGroup p (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup C) :=
    hpa.to_sup_of_normal_right' hpb hnorm
  set Q : Subgroup C := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hQ
  haveI : IsCyclic Q := hcyc Q hQp
  have haQ : Subgroup.zpowers a ≤ Q := le_sup_left
  have hbQ : Subgroup.zpowers b ≤ Q := le_sup_right
  have h1 : (Subgroup.zpowers b).subgroupOf Q ≤ (Subgroup.zpowers a).subgroupOf Q := by
    rw [IsCyclic.subgroup_le_iff_card_dvd,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbQ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe haQ).toEquiv, Nat.card_zpowers,
      Nat.card_zpowers, ha]
    exact orderOf_dvd_of_pow_eq_one hb
  exact h1 (show (⟨b, hbQ (Subgroup.mem_zpowers b)⟩ : Q) ∈ (Subgroup.zpowers b).subgroupOf Q from
    Subgroup.mem_zpowers b)

theorem mem_zpowers_of_central_cover {C C' : Type} [Group C] [Group C'] (π : C →* C') {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hker : ∀ z ∈ π.ker, z ^ 3 = 1)
    (h : ∀ a b : C', a ^ p = 1 → b ^ p = 1 → a * b = b * a → a ≠ 1 → b ∈ Subgroup.zpowers a)
    {a b : C} (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) :
    b ∈ Subgroup.zpowers a := by
  have hcop : Nat.gcd 3 p = 1 := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hker1 : ∀ z, π z = 1 → z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have h3 := hker z hz
    have := pow_gcd_eq_one.mpr ⟨h3, hzp⟩
    rwa [hcop, pow_one] at this
  have hπa1 : π a ≠ 1 := fun h1 => ha1 (hker1 a h1 ha)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h (π a) (π b) (by rw [← map_pow, ha, map_one])
    (by rw [← map_pow, hb, map_one]) (by rw [← map_mul, ← map_mul, hab]) hπa1)
  have hz : π (b * a ^ (-k)) = 1 := by
    rw [map_mul, map_zpow, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
  have hzp : (b * a ^ (-k)) ^ p = 1 := by
    have hc : Commute b (a ^ (-k)) := (Commute.symm hab).zpow_right (-k)
    rw [hc.mul_pow, hb, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha,
      one_zpow]
  have hz1 : b * a ^ (-k) = 1 := hker1 _ hz hzp
  rw [zpow_neg, mul_inv_eq_one] at hz1
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, hz1.symm⟩

end Abstract

section SLTwo


theorem not_ggNbrClauseFiveMarking_of_sl_two_centralizing {G : Type} [Group G] {K : Type} [Field K]
    [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) {a : G} {X : Subgroup G}
    (e : SL(2, K) ≃* ↥X) (hX : X ≤ Subgroup.centralizer ({a} : Set G)) :
    ¬ GGNbrClauseFiveMarking p a X := by
  let ψ' : Matrix.SpecialLinearGroup (Fin (1 + 1)) K →* G := X.subtype.comp e.toMonoidHom
  have hrange : ψ'.range = X := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [ψ']⟩
  have hinj : Function.Injective ψ' := fun x y h => e.injective (Subtype.ext h)
  have hker : ψ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (1 + 1)) K) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ').2 hinj]
    exact bot_le
  have hinn : ∃ k ∈ ψ'.range, ∀ l ∈ ψ'.range, a⁻¹ * l * a = k⁻¹ * l * k := by
    refine ⟨1, one_mem _, fun l hl => ?_⟩
    rw [hrange] at hl
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hX hl)
    rw [inv_one, one_mul, mul_one, mul_assoc, hc, inv_mul_cancel_left]
  have := ClNonsplit.not_ggNbrClauseFiveMarking_sl_two hK hf2 ψ' hker hp hp2 hq1 hq2 hinn
  rwa [hrange] at this

end SLTwo

end ExcNonsplit

namespace E6Nonsplit

section Ad


theorem mem_zpowers_E6_ad_of_five {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 5).eval (Nat.card K : ℤ))
    (a b : ↥(adjointGroup .E6 K)) (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) : b ∈ Subgroup.zpowers a := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have : Fact p.Prime := ⟨hp⟩
  have hcycp := (CFSG.RankThree.PartOne.KE.E6_five_data K Nat.prime_two hf1 hK hp hp5 hpf).1
  exact ExcNonsplit.mem_zpowers_of_pSubgroups_cyclic hp hcycp (orderOf_eq_prime ha ha1) hb hab

theorem not_ggNbrClauseFiveMarking_of_isComponentOf_E6_ad_of_five {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hq1 : ¬ p ∣ Nat.card K - 1)
    (hq2 : ¬ p ∣ Nat.card K + 1)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 5).eval (Nat.card K : ℤ))
    (a : ↥(adjointGroup .E6 K)) (ha : orderOf a = p) (X : Subgroup ↥(adjointGroup .E6 K))
    (hX : IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(adjointGroup .E6 K)))) :
    ¬ GGNbrClauseFiveMarking p a X := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hK4, ⟨e⟩⟩ := E6_five_structure K Nat.prime_two hf1 hK hp hp5 hpf a ha X hX
  have hf2 : 2 ≤ (f : ℕ) := by
    by_contra hlt
    have : (f : ℕ) = 1 := by omega
    rw [hK, this] at hK4
    omega
  exact ExcNonsplit.not_ggNbrClauseFiveMarking_of_sl_two_centralizing hK hf2 hp hp2
    (by rwa [← hK]) (by rwa [← hK]) e hX.1

theorem ggNonsplitCoreAt_E6_ad_of_five {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hq1 : ¬ p ∣ Nat.card K - 1) (hq2 : ¬ p ∣ Nat.card K + 1)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 5).eval (Nat.card K : ℤ))
    (hpC : p ∣ Nat.card ↥(adjointGroup .E6 K)) :
    ExcNonsplit.GGNonsplitCoreAt ↥(adjointGroup .E6 K) p := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
      (Nat.card K : ℤ) + 1 := by simpa [CFSG.RankThree.Chevalley.exhaustionPhi] using hpf
  obtain ⟨hp7, -, -⟩ := CFSG.RankThree.PartOne.KE.CTE6.e6Five_data hp hp5 hpf'
  have : Fact p.Prime := ⟨hp⟩
  refine ExcNonsplit.ggNonsplitCoreAt_of_cyclic_components hp hp2 hp3
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K) hpC ?_ ?_ ?_
  · intro a b ha hb hab ha1
    exact mem_zpowers_E6_ad_of_five hp hp5 hpf a b ha hb hab ha1
  · intro X hX lab hlab hc hM
    exact not_halfSplit_of_isComponentOf_top_ad hp3 hq1 (fun h => by omega) hX hlab hc hM
  · intro a ha X hX _
    exact not_ggNbrClauseFiveMarking_of_isComponentOf_E6_ad_of_five hp hp5 hq1 hq2 hpf a ha X hX

end Ad

end E6Nonsplit

end CFSG.StandardType
