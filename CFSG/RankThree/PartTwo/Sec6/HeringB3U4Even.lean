module

public import CFSG.RankThree.PartTwo.Sec6.HeringB3Tools
public import CFSG.RankThree.PartTwo.Sec6.HeringB3U4Eigen
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFU4Inner
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFU4Outer
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
import CFSG.Models.PGLSimple
import CFSG.RankThree.PartOne.N143.HeisenbergThree

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix

section Certs


theorem eq_bot_of_perfect_le_centralizer_even {n : ℕ} (hn : 1 ≤ n) (hne : Even n)
    {x : projSU 4 2 n} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {Y : Subgroup (projSU 4 2 n)}
    (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hYC : Y ≤ Subgroup.centralizer ({x} : Set (projSU 4 2 n))) : Y = ⊥ := by
  set K := GaloisField 2 (2 * n) with hKdef
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  haveI := hU.finite
  haveI : CharP K 2 := hU.charP
  set ψ₀ := Sec4.Res417Six.unitarySUEquivProjSU hn
  set s := ψ₀.symm x with hs
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hU.card, show 2 * n = n * 2 from mul_comm _ _, pow_mul]
    exact Sec4.Res419Two.three_dvd_two_pow_sq_sub_one n
  obtain ⟨ζ, hζ⟩ := Sec4.Res417Six.exists_primitiveRoot_three hdvd
  set ω : K := (ζ : K) with hωdef
  have hω3 : ω ^ 3 = 1 := by
    have := hζ.pow_eq_one
    rw [hωdef, ← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h
    have : ζ = 1 := Units.ext h
    have h31 := hζ.eq_orderOf
    rw [this, orderOf_one] at h31
    omega
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  have hbarω : hU.bar ω = ω := by
    rw [hU.bar_apply]
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 3 * k + 1 := ⟨2 ^ n / 3, by
      have := two_pow_mod_three_of_even hne
      omega⟩
    rw [hk, pow_succ, pow_mul, hω3, one_pow, one_mul]
  have hs3 : s ^ 3 = 1 := by rw [hs, ← map_pow, hx3, map_one]
  have hs1 : s ≠ 1 := fun h => hx1 (by
    have := congrArg ψ₀ h
    rwa [hs, MulEquiv.apply_symm_apply, map_one] at this)
  set g : GL (Fin 4) K := ((s : unitarySU 2 n K 4) : GL (Fin 4) K) with hg
  have hg3 : g ^ 3 = 1 := by
    rw [hg, ← Subgroup.coe_pow, hs3, Subgroup.coe_one]
  have hg1 : g ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hgu : ((g : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ * (g : Matrix (Fin 4) (Fin 4) K) = 1 :=
    ((mem_unitarySU_iff hU).mp s.2).2
  set Y₁ : Subgroup (unitarySU 2 n K 4) := Y.map ψ₀.symm.toMonoidHom with hY₁
  set Y₂ : Subgroup (GL (Fin 4) K) := Y₁.map (unitarySU 2 n K 4).subtype with hY₂
  have e₂ : Y ≃* Y₂ := (Y.equivMapOfInjective ψ₀.symm.toMonoidHom ψ₀.symm.injective).trans
    (Y₁.equivMapOfInjective (unitarySU 2 n K 4).subtype (unitarySU 2 n K 4).subtype_injective)
  have hY₂p : Group.IsPerfect Y₂ :=
    Group.IsPerfect.ofSurjective (f := e₂.toMonoidHom) e₂.surjective
  have hY₂3 : ¬ 3 ∣ Nat.card Y₂ := by rwa [← Nat.card_congr e₂.toEquiv]
  have hY₂g : ∀ y ∈ Y₂, y * g = g * y := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hYC hy)
    have h2 : ψ₀.symm y * s = s * ψ₀.symm y := by
      rw [hs, ← map_mul, ← map_mul, h1]
    exact congrArg Subtype.val h2
  have hbot := eq_bot_of_commute_of_unitary (n := Fin 4) (by simp) hU.bar hω hbarω
    three_ne_zero_of_charTwo hg3 hg1 hgu Y₂ hY₂g hY₂p hY₂3
  have hY₁bot : Y₁ = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective Y₁ (unitarySU 2 n K 4).subtype_injective).mp hbot
  exact (Subgroup.map_eq_bot_iff_of_injective Y ψ₀.symm.injective).mp hY₁bot

theorem b3Fix_projSU_four_inner_charTwo {n : ℕ} (hn : 1 ≤ n) {x : projSU 4 2 n}
    (hx3 : x ^ 3 = 1) : B3Fix (Subgroup.centralizer ({x} : Set (projSU 4 2 n))) := by
  by_cases hx1 : x = 1
  · subst hx1
    have hC : Subgroup.centralizer ({1} : Set (projSU 4 2 n)) = ⊤ := by
      ext z
      refine ⟨fun _ => Subgroup.mem_top z, fun _ => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_one z).trans (one_mul z).symm
    rw [hC]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hs : IsSimpleGroup (projSU 4 2 n) :=
      CFSG.PGLModel.isSimpleGroup_projSU_of_admissible
        ⟨Nat.prime_two, hn, by norm_num, fun h => by have := congrArg Prod.fst h; simp at this⟩
    haveI : Finite (projSU 4 2 n) := inferInstance
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3
      (Sec13.Res5Proof.three_dvd_card_projSU_four 2 n)
    have hy3 : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    have hy1 : y ≠ 1 := fun h => by simp [h] at hy
    exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_isSimpleGroup
      Subgroup.topEquiv.isSimpleGroup ⟨y, Subgroup.mem_top y, hy1, hy3⟩)
  · rcases Nat.even_or_odd n with hne | hno
    · exact b3Fix_of_perfSubnormalBot fun Y hYC _ hYp hY3 =>
        eq_bot_of_perfect_le_centralizer_even hn hne hx3 hx1 hYp hY3 hYC
    · exact b3Fix_of_not_five_dvd fun Y hYC hYp =>
        Sec8.Hering611.not_five_dvd_of_perfect_le_centralizer hno hx3 hx1 hYp hYC

theorem b3Fix_projSU_four_outer {n : ℕ} (hn : 1 ≤ n) {β : MulAut (projSU 4 2 n)}
    (hβ : β ^ 3 = 1) (hout : ¬ IsInnerAut β) {C : Subgroup (projSU 4 2 n)}
    (hC : ∀ z, z ∈ C ↔ β z = z) : B3Fix C := by
  have hCeq : C = Sec4.Item426.fixSub β :=
    Subgroup.ext fun z => by rw [hC z, Sec4.Item426.mem_fixSub]
  subst hCeq
  obtain ⟨hs, k, -, hcard⟩ := Sec8.Hering611.outer_fixSub_simple hn hβ hout
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (projSU 4 2 n) := inferInstance
  have h3 : 3 ∣ Nat.card (Sec4.Item426.fixSub β) := by
    rw [hcard]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (three_dvd_sq_sub_one (not_three_dvd_two_pow k)) _) _) _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hy3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have hy1 : y ≠ 1 := fun h => by simp [h] at hy
  exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_isSimpleGroup hs
    ⟨(y : projSU 4 2 n), y.2, fun h => hy1 (Subtype.ext h), congrArg Subtype.val hy3⟩)

theorem threePrimeB3_projSU_four_charTwo {n : ℕ} (hn : 1 ≤ n) :
    ThreePrimeB3 (projSU 4 2 n) := by
  refine threePrimeB3_of_b3Fix fun β hβ C hC => ?_
  by_cases hin : IsInnerAut β
  · obtain ⟨x, rfl⟩ := hin
    have hx3 := pow_three_eq_one_of_conj_pow_three
      (Sec4.Item419Res3.center_projSU_four_eq_bot hn) hβ
    rw [fixed_conj_eq_centralizer hC]
    exact b3Fix_projSU_four_inner_charTwo hn hx3
  · exact b3Fix_projSU_four_outer hn hβ hin hC

theorem threePrimeB3_of_projSU_four_charTwo {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* projSU 4 2 n) : ThreePrimeB3 X :=
  threePrimeB3_of_mulEquiv e (threePrimeB3_projSU_four_charTwo hn)

end Certs

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
