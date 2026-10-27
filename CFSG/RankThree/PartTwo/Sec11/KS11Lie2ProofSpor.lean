module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofExcSpor
import CFSG.RankThree.Asc83Table.Extraspecial
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.Sporadic.Schreier.MathieuOddCoreM24
import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

namespace KS11Lie2Proof

variable {W : Type*} [Group W]

theorem pow_three_eq_one_of_sylow [Finite W] {x y : W} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set W)) = 3 ^ (Nat.card W).factorization 3)
    {g : W} (hg : ∃ k : ℕ, g ^ 3 ^ k = 1) : g ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hg
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hp : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨h, hle⟩ := Sec4.Item434AltPerm.exists_le_map_conj_of_card hcard hp
  obtain ⟨u, hu, hgu⟩ := hle (Subgroup.mem_zpowers g)
  rw [← hgu, ← map_pow, Asc83Table.pow_three_eq_one_of_mem hx hzx hzy hy hu, map_one]

theorem mem_inner_of_card_outer_le_two [Finite W] (hout : Nat.card (Outer W) ≤ 2)
    {β : MulAut W} (hβ : ∃ k : ℕ, β ^ 3 ^ k = 1) : β ∈ inner W := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun α : MulAut W => (α : W → W)) DFunLike.coe_injective
  obtain ⟨k, hk⟩ := hβ
  set o : Outer W := QuotientGroup.mk' (inner W) β with ho
  have h1 : o ^ 3 ^ k = 1 := by rw [ho, ← map_pow, hk, map_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
  have h2 : orderOf o ≤ Nat.card (Outer W) := Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard o)
  have hi0 : i = 0 := by
    rcases i with _ | i
    · rfl
    · exfalso
      have h3 : 3 ^ (i + 1) ≤ 2 := hi ▸ h2.trans hout
      have h4 : 3 ≤ 3 ^ (i + 1) := Nat.le_self_pow (by omega) 3
      omega
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact (QuotientGroup.eq_one_iff β).mp hi

theorem aut_pow_three_eq_one [Finite W] (hZ : Subgroup.center W = ⊥)
    (hout : Nat.card (Outer W) ≤ 2) (hW : ∀ g : W, (∃ k : ℕ, g ^ 3 ^ k = 1) → g ^ 3 = 1)
    (β : MulAut W) (hβ : ∃ k : ℕ, β ^ 3 ^ k = 1) : β ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := mem_inner_of_card_outer_le_two hout hβ
  obtain ⟨k, hk⟩ := hβ
  have hc : g ^ 3 ^ k ∈ Subgroup.center W := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 := congrArg (fun φ : MulAut W => φ w) hk
    simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [hZ, Subgroup.mem_bot] at hc
  rw [← map_pow, hW g ⟨k, hc⟩, map_one]

theorem aut_pow_three_eq_one_of_equiv {X Z : Type*} [Group X] [Group Z]
    (hP : Group.IsPerfect W) (f : X ≃* W) (e : Z ≃* _root_.commutator X)
    (h : ∀ β : MulAut W, (∃ k : ℕ, β ^ 3 ^ k = 1) → β ^ 3 = 1)
    (β : MulAut Z) (hβ : ∃ k : ℕ, β ^ 3 ^ k = 1) : β ^ 3 = 1 := by
  have hX : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  let g : Z ≃* W :=
    e.trans (((MulEquiv.subgroupCongr hX.commutator_eq_top).trans Subgroup.topEquiv).trans f)
  obtain ⟨k, hk⟩ := hβ
  apply (MulAut.congr g).injective
  rw [map_pow, map_one]
  exact h _ ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem isPerfect_of_isSimpleGroup [IsSimpleGroup W] {x y : W} (hxy : ⁅x, y⁆ ≠ 1) :
    Group.IsPerfect W := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator W) with h | h
  · exfalso
    apply hxy
    have hmem : ⁅x, y⁆ ∈ _root_.commutator W := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · exact h

theorem center_eq_bot_of_isSimpleGroup [IsSimpleGroup W] {x y : W} (hxy : ⁅x, y⁆ ≠ 1) :
    Subgroup.center W = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center W) with h | h
  · exact h
  · exfalso
    apply hxy
    have hx : x ∈ Subgroup.center W := h ▸ Subgroup.mem_top x
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hx y).symm

section Models

theorem m24_aut_pow_three
    (β : MulAut CFSG.Blueprint.NativeSporadic.M24) (hβ : ∃ k : ℕ, β ^ 3 ^ k = 1) : β ^ 3 = 1 := by
  obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, hcard, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M24 :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have h3 : (Nat.card CFSG.Blueprint.NativeSporadic.M24).factorization 3 = 3 := by
    rw [CFSG.Sporadic.Mathieu.card_M24, show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  have hout : Nat.card (Outer CFSG.Blueprint.NativeSporadic.M24) ≤ 2 := by
    have hinner : inner CFSG.Blueprint.NativeSporadic.M24 = ⊤ :=
      CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
        CFSG.Sporadic.Schreier.m24_mulAut_card
    change (inner CFSG.Blueprint.NativeSporadic.M24).index ≤ 2
    rw [hinner, Subgroup.index_top]
    norm_num
  exact aut_pow_three_eq_one (center_eq_bot_of_isSimpleGroup hz) hout
    (fun g hg => pow_three_eq_one_of_sylow hx hy hzx hzy (by rw [hcard, h3]) hg) β hβ

theorem he_aut_pow_three
    (β : MulAut CFSG.Blueprint.NativeSporadic.He) (hβ : ∃ k : ℕ, β ^ 3 ^ k = 1) : β ^ 3 = 1 := by
  obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, hcard, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
  have : Finite CFSG.Blueprint.NativeSporadic.He :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.He.card_He]; norm_num)
  have h3 : (Nat.card CFSG.Blueprint.NativeSporadic.He).factorization 3 = 3 := by
    rw [CFSG.Sporadic.He.card_He, show (4030387200 : ℕ) = 3 ^ 3 * 149273600 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  exact aut_pow_three_eq_one (center_eq_bot_of_isSimpleGroup hz)
    CFSG.Sporadic.Schreier.AT_He_Schreier.1
    (fun g hg => pow_three_eq_one_of_sylow hx hy hzx hzy (by rw [hcard, h3]) hg) β hβ

end Models

end KS11Lie2Proof

section Proved

theorem sporAutPowThree : SporAutPowThree := by
  intro Z _ _ hZ β hβ
  obtain ⟨X, _, hX, ⟨e⟩⟩ := hZ
  rcases hX with hX | hX
  · obtain ⟨f⟩ := hX
    obtain ⟨x, y, -, -, -, hz, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M24 :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact KS11Lie2Proof.aut_pow_three_eq_one_of_equiv
      (KS11Lie2Proof.isPerfect_of_isSimpleGroup hz) f e KS11Lie2Proof.m24_aut_pow_three β hβ
  · obtain ⟨f⟩ := hX
    obtain ⟨x, y, -, -, -, hz, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
    exact KS11Lie2Proof.aut_pow_three_eq_one_of_equiv
      (KS11Lie2Proof.isPerfect_of_isSimpleGroup hz) f e KS11Lie2Proof.he_aut_pow_three β hβ

theorem centBound119Spor : CentBound119Spor :=
  centBound119Spor_of_sporAutPowThree sporAutPowThree

end Proved

end CFSG.RankThree.PartTwo.Sec11
