module

public import CFSG.RankThree.PartOne.KF.F122Engine
public import CFSG.RankThree.PartOne.KF.ClsSpWit
public import CFSG.RankThree.PartOne.KF.F122Glue
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.Blueprint CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.RankThree.PartOne.Sec66T
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (spLinearAutGroup spSemilinearAutGroup
  fieldAut)
open CFSG.RankThree.CASymplecticSubfield (subfieldFixedGroup)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem sl2_center_trivial {K : Type} [Field K] [CharP K 2] {g : SL(2, K)}
    (hg : g ∈ Subgroup.center SL(2, K)) : g = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h1 : (r + 1) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    calc (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
      _ = 1 + 0 + 1 := by rw [hr2, h2, zero_mul]
      _ = 0 := by rw [add_zero]; exact CharTwo.add_self_eq_zero (1 : K)
  have hr1 : r = 1 := by
    have := (pow_eq_zero_iff (two_ne_zero)).mp h1
    exact CharTwo.add_eq_zero.mp this
  ext i j
  have := congrFun (congrFun hrg i) j
  rw [hr1] at this
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem two_le_localRank_of_commuting_SL2 {X : Type} [Group X] [Finite X] {K : Type} [Field K]
    [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card SL(2, K))
    (φ₀ φ₁ : SL(2, K) →* X) (hφ₀ : Function.Injective φ₀) (hφ₁ : Function.Injective φ₁)
    (hcomm : ∀ A B : SL(2, K), φ₀ A * φ₁ B = φ₁ B * φ₀ A) {t : X} (ht : orderOf t = 2)
    (ht₀ : ∀ A, φ₀ A * t = t * φ₀ A) (ht₁ : ∀ A, φ₁ A * t = t * φ₁ A) :
    2 ≤ localRank p X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hp.one_lt.ne hg
  set x₀ := φ₀ g with hx₀
  set x₁ := φ₁ g with hx₁
  have hx₀ord : orderOf x₀ = p := by rw [hx₀, orderOf_injective φ₀ hφ₀ g, hg]
  have hx₁ord : orderOf x₁ = p := by rw [hx₁, orderOf_injective φ₁ hφ₁ g, hg]
  have hx₀p : x₀ ^ p = 1 := by rw [← hx₀ord]; exact pow_orderOf_eq_one _
  have hx₁p : x₁ ^ p = 1 := by rw [← hx₁ord]; exact pow_orderOf_eq_one _
  have h01 : x₀ * x₁ = x₁ * x₀ := hcomm g g
  have hx₁A : x₁ ∉ Subgroup.zpowers x₀ := by
    intro h
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
    have hgi : φ₀ (g ^ i) = x₁ := by rw [map_zpow]; exact hi
    have hcen : g ^ i ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply hφ₀
      rw [map_mul, map_mul, hgi]
      exact hcomm B g
    have h1 := sl2_center_trivial hcen
    rw [h1, map_one] at hgi
    have : x₁ = 1 := hgi.symm
    rw [this, orderOf_one] at hx₁ord
    exact hp.one_lt.ne hx₁ord
  set A : Subgroup X := Subgroup.zpowers x₀ with hA
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self x₀ i j).eq
  have hAp : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨i, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx₀p, _root_.one_zpow]
  have hAcard : Nat.card A = p ^ 1 := by
    rw [hA, Nat.card_zpowers, hx₀ord, pow_one]
  obtain ⟨E, -, hEle, hEcard, hEc, hEp⟩ := Sec66T.exists_elementary_ext hp hAc hAp hAcard hx₁A hx₁p
    (fun a ha => by
      obtain ⟨i, rfl⟩ := ha
      exact (Commute.zpow_left (show Commute x₀ x₁ from h01) i).eq)
  have hEt : ∀ y ∈ E, y * t = t * y := by
    have hle : E ≤ Subgroup.centralizer ({t} : Set X) := by
      refine hEle.trans (sup_le ?_ ?_)
      · rw [hA, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact ht₀ g
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact ht₁ g
    exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hE : CFSG.Assembly.IsElemAbelian p E := by
    exact ⟨⟨⟨fun a b => Subtype.ext (hEc _ a.2 _ b.2)⟩⟩, fun y hy => hEp y hy⟩
  exact CFSG.RankThree.PartTwo.Census.le_localRank_of_commute_involution hp ht hE hEcard hEt

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam commute_lam_lam)
open CFSG.RankThree.CentralCover (sl2Upper coe_sl2Upper sl2Upper_add sl2Upper_zero)
open CFSG.RankThree.PartOne.KFU (mk_lam_injective_of_ne)

theorem two_le_localRank_statedSp_three {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card SL(2, K)) :
    2 ≤ localRank p (StatedProj (StatedSp (2 + 1) K)) := by
  set π := QuotientGroup.mk'
    ((StatedScalars (Fin (2 + 1) ⊕ Fin (2 + 1)) K).subgroupOf (StatedSp (2 + 1) K))
  have hlast : ∀ i : Fin 2, (Fin.last 2 : Fin (2 + 1)) ≠ Fin.castSucc i := fun i h =>
    (Fin.castSucc_lt_last i).ne h.symm
  let φ : Fin 2 → SL(2, K) →* StatedProj (StatedSp (2 + 1) K) := fun i =>
    π.comp (lam (k := K) (Fin.castSucc i))
  have hinj3 := mk_lam_injective_of_ne (K := K) (j := Fin.last 2) (l := 0) (by
    intro h
    have := congrArg Fin.val h
    simp at this)
  have hu : orderOf ((π.comp (lam (k := K) (Fin.last 2))) (sl2Upper 1)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, ← sl2Upper_add, CharTwo.add_self_eq_zero, sl2Upper_zero, map_one]
    · intro h
      rw [← map_one (π.comp (lam (k := K) (Fin.last 2)))] at h
      have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) (hinj3 h)
      simp [coe_sl2Upper] at this
  have hcommAll : ∀ i j : Fin 2, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A :=
    fun i j hij A B => by
      change π (lam _ A) * π (lam _ B) = π (lam _ B) * π (lam _ A)
      rw [← map_mul, ← map_mul,
        (commute_lam_lam ((Fin.castSucc_injective 2).ne hij) A B).eq]
  have hφt : ∀ i : Fin 2, ∀ A, φ i A * (π.comp (lam (k := K) (Fin.last 2))) (sl2Upper 1) =
      (π.comp (lam (k := K) (Fin.last 2))) (sl2Upper 1) * φ i A := fun i A => by
    change π (lam _ A) * π (lam _ (sl2Upper 1)) = π (lam _ (sl2Upper 1)) * π (lam _ A)
    rw [← map_mul, ← map_mul, (commute_lam_lam (hlast i).symm A (sl2Upper 1)).eq]
  exact two_le_localRank_of_commuting_SL2 hp hpK (φ 0) (φ 1)
    (mk_lam_injective_of_ne (hlast 0)) (mk_lam_injective_of_ne (hlast 1))
    (hcommAll 0 1 (by decide)) hu (hφt 0) (hφt 1)

theorem dvd_two_pow_sub_one_of_mul {p f₀ : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ (p * f₀) - 1) :
    p ∣ 2 ^ f₀ - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have h3 : (((2 ^ (p * f₀) - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_sub h1] at h3
  push_cast at h3
  have h4 : (2 : ZMod p) ^ (p * f₀) = (2 : ZMod p) ^ f₀ := by
    rw [mul_comm, pow_mul, ZMod.pow_card]
  rw [h4] at h3
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2]
  push_cast
  exact h3

theorem dvd_two_pow_add_one_of_mul {p f₀ : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ (p * f₀) + 1) :
    p ∣ 2 ^ f₀ + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h3 : (((2 ^ (p * f₀) + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h3
  have h4 : (2 : ZMod p) ^ (p * f₀) = (2 : ZMod p) ^ f₀ := by
    rw [mul_comm, pow_mul, ZMod.pow_card]
  rw [h4] at h3
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h3

theorem not_dvd_two_pow_prime_sub_one {p : ℕ} (hp : p.Prime) : ¬ p ∣ 2 ^ p - 1 := by
  intro h
  have h1 := dvd_two_pow_sub_one_of_mul (f₀ := 1) hp (by rwa [mul_one])
  simp at h1
  exact hp.one_lt.ne' h1

theorem psp_aut_false {T : Type} [Group T] [Finite T] {p n f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hC : StatedClassicalModel T .PSp n 2 f)
    (hnd : ∀ f₀ : ℕ, f = p * f₀ → ¬ (n = 2 ∧ 2 ^ f₀ = 2))
    (hlower : ∀ (f₀ : ℕ) (k : Type) [Field k] [Finite k] [CharP k 2], f = p * f₀ →
      Nat.card k = 2 ^ f₀ → 2 ≤ localRank p (StatedProj (StatedSp n k)))
    {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (hLRA : LocalRankAut p T α) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hadm := hC.1
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp n K)) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'ord : orderOf (MulAut.congr e α) = p := (orderOf_congr e α).trans hord
  have hα'p : MulAut.congr e α ^ p = 1 := by
    have := pow_orderOf_eq_one (MulAut.congr e α)
    rwa [hα'ord] at this
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hf hn hK
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup n K := by
    have hidx' : (spSemilinearAutGroup n K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ spLinearAutGroup n K := by
    intro hD
    have hcop : Nat.gcd 2 (2 ^ f - 1) = 1 := by
      have h1 : (2 : ℕ) ^ f % 2 = 0 := by
        obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hf
        rw [pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ f := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hα'inn (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨hpf, σ, hσord, -, h, -, hαh⟩ := hdesc p hp _ hE hD hα'ord
  obtain ⟨-, hkcard, -, -, hinj, hfixiff, -, hns, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      Nat.prime_two hp (by omega) hp2 hf hn hK σ hσord
  have hff' : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  have hfixeq : fixSub (fieldAut n K σ) = subfieldFixedGroup K n σ := by
    ext x
    exact (hfixiff x).symm
  let eK : ↥(subfieldFixedGroup K n σ) ≃* StatedProj (StatedSp n ↥(descentField σ)) :=
    (MonoidHom.ofInjective hinj).symm
  have hψ : h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ = fieldAut n K σ := by
    rw [hαh]
    group
  have hψ' : fixSub (h⁻¹ * MulAut.congr e α * h⁻¹⁻¹) = fixSub (fieldAut n K σ) := by rw [hψ]
  let e12 : ↥(fixSub α) ≃* ↥(fixSub (fieldAut n K σ)) :=
    ((fixSubEquiv e α).trans (fixSubEquiv h⁻¹ (MulAut.congr e α))).trans
      (MulEquiv.subgroupCongr hψ')
  let eX : ↥(fixSub α) ≃* StatedProj (StatedSp n ↥(descentField σ)) :=
    (e12.trans (MulEquiv.subgroupCongr hfixeq)).trans eK
  have : Fintype ↥(descentField σ) := Fintype.ofFinite _
  have : CharP ↥(descentField σ) 2 :=
    charP_of_card_eq_prime_pow (f := f / p) (by rw [← Nat.card_eq_fintype_card, hkcard])
  have hN : 2 ≤ localRank p ↥(fixSub α) := by
    rw [localRank_eq_of_mulEquiv eX hp]
    exact hlower (f / p) ↥(descentField σ) hff' hkcard
  exact false_of_localRank_fixed hp hαp hαinn (fixSub α) (fun y hy => hy) hN hLRA

theorem kf122Row7_holds : KF122Row 7 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, -, hpq, hC⟩ := hmodel
  refine psp_aut_false hp hp5 hC ?_ ?_ hαp hαinn hLRA
  · rintro f₀ hf ⟨-, h2⟩
    have h1 : f₀ = 1 := by
      have : 2 ^ f₀ = 2 ^ 1 := by rw [h2, pow_one]
      exact Nat.pow_right_injective (le_refl 2) this
    subst h1
    rw [hf, mul_one] at hpq
    exact not_dvd_two_pow_prime_sub_one hp hpq
  · intro f₀ k _ _ _ hf hk
    have hpk : p ∣ 2 ^ f₀ - 1 := dvd_two_pow_sub_one_of_mul hp (hf ▸ hpq)
    refine KFU.le_localRank_statedSp_torus (K := k) hp (by omega) ?_ (by norm_num)
    rw [Nat.card_units, hk]
    exact hpk

theorem kf122Row10_holds : KF122Row 10 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, -, hpq, hC⟩ := hmodel
  refine psp_aut_false hp hp5 hC ?_ ?_ hαp hαinn hLRA
  · rintro f₀ hf ⟨h3, -⟩
    omega
  · intro f₀ k _ _ _ hf hk
    have hpk : p ∣ 2 ^ f₀ + 1 := dvd_two_pow_add_one_of_mul hp (hf ▸ hpq)
    refine two_le_localRank_statedSp_three (K := k) hp ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk]
    have h1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
    have hsq : (2 ^ f₀) ^ 2 - 1 = (2 ^ f₀ + 1) * (2 ^ f₀ - 1) := by
      zify [h1, Nat.one_le_pow 2 (2 ^ f₀) (by omega)]
      ring
    rw [hsq]
    exact (hpk.mul_right _).mul_left _

end CFSG.RankThree.PartOne
