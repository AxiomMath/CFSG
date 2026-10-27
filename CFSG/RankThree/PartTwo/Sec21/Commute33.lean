module

public import CFSG.RankThree.PartTwo.Sec21.Commute33Rank
public import CFSG.RankThree.PartTwo.Sec21.U4FourGroupLines
public import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartTwo.Sec21.Commute33Odd

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (projSL localRank)
open CFSG.Assembly (IsElemAbelian)
open Subgroup
open scoped commutatorElement Pointwise

namespace Commute33Steps

variable {G : Type} [Group G]

theorem commutator_eq_bot_core [Finite G]
    (hloc : ∀ s : ℕ, s.Prime → 3 < s → localRank s G < 3) {K J A Θ EK EJ : Subgroup G}
    [IsSimpleGroup K] [IsSimpleGroup J] (hK : ⁅K, K⁆ = K) (hJ : ⁅J, J⁆ = J) (hNΘ : ⁅K, J⁆ ≤ Θ)
    (hΘs : Group.IsSolvable Θ) (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hA3 : IsPGroup 3 A)
    (hAK : A ≤ normalizer (K : Set G)) (hAJ : A ≤ normalizer (J : Set G))
    (hΘA : Odd (Nat.card (⁅Θ, A⁆ : Subgroup G)))
    {z : G} (hzA : z ∈ A) (hzK : z ∈ K) (hz1 : z ≠ 1) (hEKK : EK ≤ K) (hEJJ : EJ ≤ J)
    (hEK : IsElemAbelian 2 EK) (hEJ : IsElemAbelian 2 EJ) (hEK4 : Nat.card EK = 4)
    (hEJ4 : Nat.card EJ = 4) : ⁅K, J⁆ = ⊥ := by
  set N : Subgroup G := ⁅K, J⁆ with hNdef
  have hNs : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNΘ)
      (Subgroup.inclusion_injective hNΘ)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h => hΘ3 (h.trans (Subgroup.card_dvd_of_le hNΘ))
  have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  have hS : ∀ S : Subgroup G, S ≤ N → IsPGroup 2 S → A ≤ normalizer (S : Set G) →
      A ≤ centralizer (S : Set G) := by
    intro S hSN hS2 hSA
    have h1 : ⁅S, A⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hSA
    have h2 : ⁅S, A⁆ ≤ ⁅Θ, A⁆ := Subgroup.commutator_mono (hSN.trans hNΘ) le_rfl
    have hbot : ⁅S, A⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨k, hk⟩ := hS2 ⟨x, h1 hx⟩
      have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact Subgroup.mem_bot.mpr (eq_one_of_pow_two_pow hΘA (h2 hx) hxk)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact Subgroup.le_centralizer_iff.mp hbot
  have hNodd : Odd (Nat.card N) := odd_card_commutator hK hNs hA3 hcop hAK hAJ hS hzA hzK hz1
  have hcore : ∀ s : ℕ, s.Prime → ¬ s ∣ Nat.card N → inSubgroup (pCore s) N = ⊥ := by
    intro s hs hsN
    have : Fact s.Prime := ⟨hs⟩
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := s) (G := N)).exists_card_eq
    have hdvd : s ^ k ∣ Nat.card N := hk ▸ Subgroup.card_subgroup_dvd_card _
    have hk0 : k = 0 := by
      by_contra hk0
      exact hsN ((dvd_pow_self s hk0).trans hdvd)
    rw [hk0, pow_zero] at hk
    rw [inSubgroup, Subgroup.card_eq_one.mp hk, Subgroup.map_bot]
  refine eq_bot_of_forall_pCore hNdef hK hJ hNs fun s hs => ?_
  by_cases hsN : s ∣ Nat.card N
  · have hs2 : s ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hsN)
    have hs3' : s ≠ 3 := by
      rintro rfl
      exact hN3 hsN
    have hs3 : 3 < s := by
      have := hs.two_le
      omega
    exact centralizes_pCore_of_odd hloc hK hJ hNs hNodd hEKK hEJJ hEK hEJ hEK4 hEJ4 hs hs3
  · left
    rw [hcore s hs hsN]
    intro k _
    rw [mem_centralizer_iff]
    intro x hx
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    rw [hx, one_mul, mul_one]

theorem sq_eq_one_ZMod2 : ∀ x : Multiplicative (ZMod 2 × ZMod 2), x ^ 2 = 1 := by decide

theorem exists_fourGroup_of_mulEquiv_projSL {X : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (e : X ≃* projSL 2 (GaloisField 2 m)) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  set F := GaloisField 2 m
  have hF : Nat.card F = 2 ^ m := GaloisField.card 2 m (by omega)
  obtain ⟨x, hx0, hx1⟩ : ∃ x : F, x ≠ 0 ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
      intro y
      by_cases hy : y = 0
      · exact ⟨false, by simp [hy]⟩
      · exact ⟨true, by simp [hcon y hy]⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [hF, Nat.card_eq_fintype_card, Fintype.card_bool] at h1
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  set ι₀ : Multiplicative (ZMod 2 × ZMod 2) →* G :=
    X.subtype.comp (e.symm.toMonoidHom.comp ((projSLTwoEquivSL F).symm.toMonoidHom.comp
      (SL2MinimalFaithful.unipotentHom.comp
        (AddMonoidHom.toMultiplicative (U4FourLines.fourAdd x))))) with hι₀
  have hinj : Function.Injective ι₀ :=
    X.subtype_injective.comp (e.symm.injective.comp ((projSLTwoEquivSL F).symm.injective.comp
      (SL2MinimalFaithful.unipotentHom_injective.comp fun a b h =>
        (U4FourLines.fourAdd_injective hx0 hx1) (Multiplicative.ofAdd.injective h))))
  refine ⟨ι₀.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact (e.symm _).2
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha', ← hb', ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, sq_eq_one_ZMod2, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
    rfl

end Commute33Steps

open Commute33Steps

variable {G : Type} [Group G]

theorem commute33 :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → KOfWellDefined A →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, φ ≠ ψ → ∀ m m' : ℕ, 2 ≤ m → 2 ≤ m' →
      Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) →
      Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m')) →
      ∀ b ∈ fixedInG A φ ⊓ fixedInG A ψ, b ≠ 1 →
      ∀ Kb ∈ thetaComponentsAt 3 b, ∀ Jb ∈ thetaComponentsAt 3 b,
        kOf A φ ≤ Kb → kOf A ψ ≤ Jb → Kb ≠ Jb → ⁅kOf A φ, kOf A ψ⁆ = ⊥ := by
  intro G _ _ A E U c L hpair hKW φ hφ ψ hψ _ m m' hm hm' ⟨eK⟩ ⟨eJ⟩ b hb hb1 Kb hKb Jb hJb hKKb
    hJJb hKJb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) := isSimpleGroup_projSL_two hm
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m')) := isSimpleGroup_projSL_two hm'
  have : IsSimpleGroup (kOf A φ) := eK.isSimpleGroup
  have : IsSimpleGroup (kOf A ψ) := eJ.isSimpleGroup
  have hKperf := Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL hm eK)
  have hJperf := Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL hm' eJ)
  have hbA : b ∈ A := by
    obtain ⟨a, -, rfl⟩ := hb.1
    exact a.2
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set Θ := inSubgroup (aschbacherSolvableCore 3) C with hΘ
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  have hΘs : Group.IsSolvable Θ :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    rw [hΘ, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
    exact hθ3
  have hNΘ : ⁅kOf A φ, kOf A ψ⁆ ≤ Θ :=
    (Subgroup.commutator_mono hKKb hJJb).trans
      (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hKb hJb hKJb)
  have hAK := le_normalizer_kOf hAe.1 hKW hφ
  have hAJ := le_normalizer_kOf hAe.1 hKW hψ
  have hΘA : Odd (Nat.card (⁅Θ, A⁆ : Subgroup G)) := hpair.mem_S.2.1 b hbA hb1
  obtain ⟨z, hzK, hz3, hzC⟩ := exists_orderOf_eq_mem_centralizer hA3
    (fun a ha x hx => (mem_normalizer_iff.mp (hAK ha) x).mp hx)
    (three_dvd_card_of_mulEquiv_projSL eK)
  have hzA : z ∈ A := mem_of_mem_centralizer_of_orderOf_eq_three' hAF hzC hz3
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz3
    norm_num at hz3
  obtain ⟨EK, hEKK, hEK, hEK4⟩ := exists_fourGroup_of_mulEquiv_projSL hm eK
  obtain ⟨EJ, hEJJ, hEJ, hEJ4⟩ := exists_fourGroup_of_mulEquiv_projSL hm' eJ
  exact commutator_eq_bot_core hpair.standing.localRank_lt hKperf hJperf hNΘ hΘs hΘ3 hA3 hAK hAJ
    hΘA hzA hzK hz1 hEKK hEJJ hEK hEJ hEK4 hEJ4

end CFSG.RankThree.PartTwo.Sec21
