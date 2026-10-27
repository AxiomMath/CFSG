module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432WeylRoute
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofSp4
public import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4
public import CFSG.RankThree.PartTwo.Sec4.Item49OddChar

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem cover_pair_facts {X Y : Type} [Group X] [Group Y] (π : Y →* X)
    (hker : ∀ z ∈ π.ker, z ^ 4 = 1) {a b : Y} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) (hbn : b ∉ Subgroup.zpowers a) :
    orderOf (π a) = 3 ∧ π b ^ 3 = 1 ∧ π a * π b = π b * π a ∧ π b ∉ Subgroup.zpowers (π a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ w : Y, π w = 1 → w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have h4 : w ^ 4 = 1 := hker w (MonoidHom.mem_ker.mpr hw)
    have h1 : w ^ Nat.gcd 3 4 = 1 := pow_gcd_eq_one.mpr ⟨hw3, h4⟩
    rw [show Nat.gcd 3 4 = 1 by norm_num, pow_one] at h1
    exact h1
  have hx3 : π a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hx1 : π a ≠ 1 := fun h => ha1 (key a h ha3)
  have hy3 : π b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hc : π a * π b = π b * π a := by rw [← map_mul, ← map_mul, hab]
  have hn : π b ∉ Subgroup.zpowers (π a) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hw : π ((a ^ k)⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    have hak : (a ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    have hcomm : Commute (a ^ k)⁻¹ b := ((show Commute a b from hab).zpow_left k).inv_left
    have hw3 : ((a ^ k)⁻¹ * b) ^ 3 = 1 := by
      rw [hcomm.mul_pow, inv_pow, hak, inv_one, one_mul, hb3]
    exact hbn (Subgroup.mem_zpowers_iff.mpr ⟨k, inv_mul_eq_one.mp (key _ hw hw3)⟩)
  exact ⟨orderOf_eq_prime hx3 hx1, hy3, hc, hn⟩

theorem listRow_of_cover_pair {X : Type} [Group X] [Finite X] {Y : Type} [Group Y] [Finite Y]
    (π : Y →* X) (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, z ^ 4 = 1)
    (hY : ∀ E : Subgroup Y, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 9 → ∃ g : Y, (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
        ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹)
    {a b : Y} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hbn : b ∉ Subgroup.zpowers a) : ListRow X := by
  obtain ⟨hx0, hy3, hc, hn⟩ := cover_pair_facts π hker ha3 ha1 hb3 hab hbn
  exact listRow_of_cover_weyl π hπ hker hY hx0 hy3 hc hn

@[expose] noncomputable def projCover (K : Type) [Field K] : StatedSp 2 K →* projSp 2 K :=
  ((Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K →* _).comp
    (StatedSp 2 K).subtype).codRestrict
    (projSp 2 K) (fun x => ⟨x, x.2, rfl⟩)

theorem projCover_surjective (K : Type) [Field K] : Function.Surjective (projCover K) := by
  rintro ⟨y, hy⟩
  rw [Item424Res5.projSp_eq_map, Subgroup.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem projCover_ker (K : Type) [Field K] : ∀ z ∈ (projCover K).ker, z ^ 4 = 1 := by
  intro z hz
  have h1 : projCover K z = 1 := MonoidHom.mem_ker.mp hz
  have h2 : z ^ 2 = 1 := Item424Res5.sq_eq_one_of_mk_eq_one (z := z) (congrArg Subtype.val h1)
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]

theorem listRow_projSp_two {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0) :
    ListRow (projSp 2 K) :=
  listRow_of_cover_pair (projCover K) (projCover_surjective K) (projCover_ker K)
    (fun E hc he hcard => Item424Res5.exists_weyl_sp4 h3 E hc he hcard)
    (sp4T_pow_three K) (sp4T_ne_one K) (sp4T'_pow_three K) (sp4T_commute K)
    (sp4T'_not_mem_zpowers K)

theorem three_ne_zero_galoisField_of_three_lt (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (3 : GaloisField p 1) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : GaloisField p 1) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField p 1) p 3).mp h'
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem three_ne_zero_galoisField_two (n : ℕ) : (3 : GaloisField 2 n) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : GaloisField 2 n) = 0 := by exact_mod_cast h
  have hdvd : 2 ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField 2 n) 2 3).mp h'
  norm_num at hdvd

theorem outerRow_projSp_two {K : Type} [Field K] [Finite K] (hodd : ringChar K ≠ 2)
    (hK : Subsingleton (K ≃+* K)) : OuterRow (projSp 2 K) :=
  outerRow_of_not_three_dvd_outer (Item49OddChar.not_three_dvd_card_outer_of_mulEquiv
    (CFSG.PGLModel.projSpEquivStatedProj 2 K)
    (Item49OddChar.not_three_dvd_card_outer_psp4 hodd hK))

theorem rowOf_four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf (projSp 2 (GaloisField p 1)) := by
  intro p _ hp S _ _ _ _ ⟨e⟩
  have hcard : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have hodd : ringChar (GaloisField p 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField p 1) p]
    omega
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSp_two (three_ne_zero_galoisField_of_three_lt p hp),
      outerRow_projSp_two hodd
        (Item49OddChar.subsingleton_ringAut_of_card_prime (Fact.out : p.Prime) hcard)⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
