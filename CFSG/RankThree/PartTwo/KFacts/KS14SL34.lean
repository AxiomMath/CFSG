module

public import CFSG.RankThree.PartTwo.KFacts.KS18SL34
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG
open scoped commutatorElement

theorem card_SL_three_four :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 3) (by norm_num), hK,
    show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem eq_one_of_isPerfect_of_comm {G M : Type*} [Group G] [Group M] [Group.IsPerfect G]
    (f : G →* M) (hM : ∀ a b : M, a * b = b * a) (g : G) : f g = 1 := by
  have hle : commutator G ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hM _ _
  rw [Group.IsPerfect.commutator_eq_top] at hle
  exact hle (Subgroup.mem_top g)

theorem index_ne_three_of_isPerfect {G : Type*} [Group G] [Group.IsPerfect G] (H : Subgroup G) :
    H.index ≠ 3 := by
  intro h3
  classical
  have hfin : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index]
    omega)
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Nat.card (G ⧸ H) = 3 := by
    rw [← Subgroup.index, h3]
  set ρ := MulAction.toPermHom G (G ⧸ H) with hρdef
  have hs : ∀ g, Equiv.Perm.sign (ρ g) = 1 := fun g =>
    eq_one_of_isPerfect_of_comm (Equiv.Perm.sign.comp ρ) (fun a b => mul_comm a b) g
  let ρ' : G →* alternatingGroup (G ⧸ H) :=
    ρ.codRestrict _ fun g => Equiv.Perm.mem_alternatingGroup.mpr (hs g)
  have hA : ∀ a b : alternatingGroup (G ⧸ H), a * b = b * a := by
    have : Nontrivial (G ⧸ H) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hc : Nat.card (alternatingGroup (G ⧸ H)) = 3 := by
      rw [nat_card_alternatingGroup, hcard]
      rfl
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic (alternatingGroup (G ⧸ H)) := isCyclic_of_prime_card hc
    intro a b
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact zpow_mul_comm g m n
  have hρ : ∀ g, ρ g = 1 := fun g => congrArg Subtype.val (eq_one_of_isPerfect_of_comm ρ' hA g)
  have hH : H = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    have h1 : g • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
      have := congrArg (fun σ : Equiv.Perm (G ⧸ H) => σ (QuotientGroup.mk 1)) (hρ g)
      simpa [hρdef] using this
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h1
    simpa using h1
  rw [hH, Subgroup.index_top] at h3
  omega

theorem ks18SL34 : KS18SL34 := by
  intro X _ _ φ N _ hN2 hker
  refine ⟨fun e => ?_⟩
  have hQ : Nat.card (X ⧸ N) = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_projSL_three_four]
  have hX : Nat.card X = 20160 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hQ]
  have hR : Nat.card X = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hdvdR : Nat.card φ.range ∣ 60480 :=
    card_SL_three_four ▸ Subgroup.card_subgroup_dvd_card _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hN2.exists_card_eq
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hker
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hr : Nat.card φ.range = 20160 * j := by
    have h : Nat.card φ.range * Nat.card φ.ker = 20160 * j * Nat.card φ.ker := by
      rw [← hR, hX, hj]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hj2 : j ∣ 2 ^ m := by
    rw [← hm, hj]
    exact Dvd.intro_left _ rfl
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hj2
  have hi0 : i = 0 := by
    rw [hr] at hdvdR
    have h3 : 2 ^ i ∣ 3 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 20160) (by simpa using hdvdR)
    by_contra hne
    have : 2 ∣ 3 := (dvd_pow_self 2 hne).trans h3
    omega
  have hidx : φ.range.index = 3 := by
    have h := φ.range.card_mul_index
    rw [hr, hi0, pow_zero, mul_one, card_SL_three_four] at h
    omega
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact index_ne_three_of_isPerfect _ hidx

end CFSG.RankThree.PartTwo.KFacts.KS14
