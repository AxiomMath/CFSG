module

public import CFSG.RankThree.PartOne.S11.SecTenEight
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.RankThree.CentralCover.SteinbergBNLinearSplitPrime
public import CFSG.RankThree.PartOne.KC.OddCharacteristicDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.LocalAnalysis.SectionRank.QTK.CoverBTable
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

@[expose] def ExceptionalCenterSmallPrimes : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    CFSG.Blueprint.ExceptionalRep (K ⧸ Subgroup.center K) →
      ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ Nat.card (Subgroup.center K)

@[expose] def SporadicCenterSmallPrimes : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    CFSG.Blueprint.NativeSporadic.SporadicRep (K ⧸ Subgroup.center K) →
      ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ Nat.card (Subgroup.center K)

section Arith

theorem five_le_of_prime' {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have : p = 4 := by omega
  subst this
  norm_num at hp

theorem not_dvd_six {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : ¬ p ∣ 6 := by
  intro h
  have h6 : p ∣ 2 * 3 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

end Arith

section Table

theorem exceptionalOrders_bounds (t : StatedLieTag) (n p f : ℕ) :
    1 ≤ (exceptionalOrders t n p f).1 ∧ (exceptionalOrders t n p f).1 ≤ 4 ∧
      1 ≤ (exceptionalOrders t n p f).2 ∧ (exceptionalOrders t n p f).2 ≤ 4 := by
  unfold exceptionalOrders
  split <;> simp

theorem gcd_bounds (a x : ℕ) (ha : 0 < a) (ha4 : a ≤ 4) : 1 ≤ Nat.gcd a x ∧ Nat.gcd a x ≤ 4 :=
  ⟨Nat.gcd_pos_of_pos_left x ha, (Nat.gcd_le_left x ha).trans ha4⟩

theorem genericOrders_bounds (t : StatedLieTag) (n p f : ℕ) (h1 : t ≠ .PSL) (h2 : t ≠ .PSU) :
    1 ≤ (genericOrders t n p f).1 ∧ (genericOrders t n p f).1 ≤ 4 ∧
      1 ≤ (genericOrders t n p f).2 ∧ (genericOrders t n p f).2 ≤ 4 := by
  unfold genericOrders
  cases t <;> first | exact absurd rfl h1 | exact absurd rfl h2 | skip
  all_goals dsimp only
  all_goals first
    | exact ⟨(gcd_bounds _ _ (by norm_num) (by norm_num)).1,
        (gcd_bounds _ _ (by norm_num) (by norm_num)).2, by norm_num, by norm_num⟩
    | skip
  all_goals first
    | (split_ifs
       · norm_num
       · norm_num
       · exact ⟨(gcd_bounds _ _ (by norm_num) (by norm_num)).1,
           (gcd_bounds _ _ (by norm_num) (by norm_num)).2, by norm_num, by norm_num⟩)
    | skip
  all_goals norm_num

theorem card_generic_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) :=
  CFSG.SectionRank.QTK.CoverB.card_generic_exceptional t n p f

theorem card_center_dvd_of_model
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : StatedLieTag}
    {n ℓ f : ℕ} (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) t n ℓ f) :
    Nat.card (Subgroup.center K) ∣ ((genericOrders t n ℓ f).1 * (genericOrders t n ℓ f).2) *
      ((exceptionalOrders t n ℓ f).1 * (exceptionalOrders t n ℓ f).2) := by
  have : Group.IsPerfect K := hK.1
  have hm : Models.LieModel (K ⧸ Subgroup.center K) t n ℓ f := ⟨hmod.1, .inl hmod⟩
  obtain ⟨-, ⟨e⟩⟩ := hGA _ t n ℓ f hm
  have h1 := ComponentClassification.FooteLit.card_center_dvd_card_hopfMultiplier (Q := K)
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
    Nat.card_congr e.toEquiv, card_generic_exceptional] at h1
  exact h1

theorem prime_dvd_table {t : StatedLieTag} {n ℓ f p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hdvd : p ∣ ((genericOrders t n ℓ f).1 * (genericOrders t n ℓ f).2) *
      ((exceptionalOrders t n ℓ f).1 * (exceptionalOrders t n ℓ f).2)) :
    (t = .PSL ∧ p ∣ n ∧ p ∣ ℓ ^ f - 1) ∨ (t = .PSU ∧ p ∣ n ∧ p ∣ ℓ ^ f + 1) := by
  obtain ⟨he1, he1', he2, he2'⟩ := exceptionalOrders_bounds t n ℓ f
  have hp5 := five_le_of_prime' hp hp3
  have hle : ∀ a : ℕ, 1 ≤ a → a ≤ 4 → ¬ p ∣ a := fun a ha ha4 hpa =>
    absurd (Nat.le_of_dvd (by omega) hpa) (by omega)
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hg | hex
  · by_cases hL : t = .PSL
    · subst hL
      change p ∣ Nat.gcd n (ℓ ^ f - 1) * 1 at hg
      rw [mul_one] at hg
      exact Or.inl ⟨rfl, Nat.dvd_gcd_iff.mp hg |>.1, Nat.dvd_gcd_iff.mp hg |>.2⟩
    by_cases hU : t = .PSU
    · subst hU
      change p ∣ Nat.gcd n (ℓ ^ f + 1) * 1 at hg
      rw [mul_one] at hg
      exact Or.inr ⟨rfl, Nat.dvd_gcd_iff.mp hg |>.1, Nat.dvd_gcd_iff.mp hg |>.2⟩
    obtain ⟨hg1, hg1', hg2, hg2'⟩ := genericOrders_bounds t n ℓ f hL hU
    rcases (Nat.Prime.dvd_mul hp).1 hg with h | h
    · exact absurd h (hle _ hg1 hg1')
    · exact absurd h (hle _ hg2 hg2')
  · rcases (Nat.Prime.dvd_mul hp).1 hex with h | h
    · exact absurd h (hle _ he1 he1')
    · exact absurd h (hle _ he2 he2')

end Table

section Rank

variable {H : Type} [Group H] [Finite H]

theorem localRank_le_three_of_center {K : Subgroup H} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (he : CFSG.twoLocalOddRank H ≤ 3) :
    localRank p H ≤ 3 := by
  have hpH : p ∣ Nat.card H := hpZ.trans ((Subgroup.card_subgroup_dvd_card
    (Subgroup.center K)).trans (Subgroup.card_subgroup_dvd_card K))
  exact (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hp (by omega) hpH).trans he

theorem quotient_cover_ker {K : Type} [Group K] {T : Type} [Group T]
    (e : K ⧸ Subgroup.center K ≃* T) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker ≤ Subgroup.center K := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact hx

theorem sec68_psl (he : CFSG.twoLocalOddRank H ≤ 3) {K : Subgroup H} {p ℓ n f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hmod : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) : False := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hloc := localRank_le_three_of_center (K := K) hp hp3 hpZ he
  have hmod0 := hmod
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hk])
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  let ψ : ↥K ⧸ Subgroup.center ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ : ↥K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨-, -, -, -, -, -, -, hle⟩ :=
    CFSG.RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank K hℓ hp hp3 hpk
      (by omega) φ hφs (quotient_cover_ker ψ)
  have hn : n = 5 := by
    by_cases hℓ2 : ℓ = 2
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      by_contra hne
      have h6 : n = 6 := by omega
      exact not_dvd_six hp hp3 (h6 ▸ hpn)
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      omega
  subst hn
  have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpn
  subst hp5'
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h4 : 4 ≤ evenRank H := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact (even_square_field_linear_five_sections_force_two_local_rank_four (G := H)).1 hf
        (even_of_five_dvd_two_pow_sub_one hpq) hmod0 K π hπ
    · exact (odd_characteristic_split_degree_five_sections_force_two_local_rank_four
        (G := H)).1 hℓ hℓ2 hf (Or.inl rfl) (Or.inl ⟨rfl, hpq⟩) hmod0 K π hπ
  have := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank H
  omega

theorem sec68_psu (he : CFSG.twoLocalOddRank H ≤ 3) {K : Subgroup H} {p ℓ n f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hmod : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) : ℓ = 2 ∧ n = 5 ∧ p = 5 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hloc := localRank_le_three_of_center (K := K) hp hp3 hpZ he
  have hmod0 := hmod
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f k :=
    ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  let φ : ↥K →* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank K hU hp hp3 hpq
      (by omega) φ hφs (quotient_cover_ker ψ)
  have hle := CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp hu
    (le_inf_iff.mp hV).2 hVab hVcard
  have hn : n = 5 := by
    by_cases hℓ2 : ℓ = 2
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      by_contra hne
      have h6 : n = 6 := by omega
      exact not_dvd_six hp hp3 (h6 ▸ hpn)
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      omega
  subst hn
  have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpn
  subst hp5'
  by_cases hℓ2 : ℓ = 2
  · exact ⟨hℓ2, rfl, rfl⟩
  · exfalso
    let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    have h4 : 4 ≤ evenRank H :=
      (odd_characteristic_split_degree_five_sections_force_two_local_rank_four
        (G := H)).1 hℓ hℓ2 hf (Or.inr rfl) (Or.inr ⟨rfl, hpq⟩) hmod0 K π hπ
    have := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank H
    omega

end Rank

section Main

theorem sec6Eight_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hExc : ExceptionalCenterSmallPrimes) (hSpor : SporadicCenterSmallPrimes) :
    Sec6EightMultipliers := by
  intro H _ _ he K p hp hp3 hK hcat hpZ
  have : Group.IsPerfect ↥K := hK.1
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exfalso
    have hdvd := ComponentClassification.FooteLit.card_center_dvd_card_hopfMultiplier
      (Q := ↥K) e
    rw [(hAlt m hm).2] at hdvd
    have h1 := hpZ.trans hdvd
    split_ifs at h1
    · exact not_dvd_six hp hp3 h1
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    have hdvd := card_center_dvd_of_model hGA hK hmod
    rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
    · exact (sec68_psl he hp hp3 hpZ hmod hpn hpq).elim
    · obtain ⟨rfl, rfl, rfl⟩ := sec68_psu he hp hp3 hpZ hmod hpn hpq
      have hf : 1 ≤ f := hmod.1.2.1
      have hord : (genericOrders .PSU 5 2 f).1 * (genericOrders .PSU 5 2 f).2 *
          ((exceptionalOrders .PSU 5 2 f).1 * (exceptionalOrders .PSU 5 2 f).2) = 5 := by
        have h1 : genericOrders .PSU 5 2 f = (Nat.gcd 5 (2 ^ f + 1), 1) := rfl
        have h2 : exceptionalOrders .PSU 5 2 f = (1, 1) := by
          unfold exceptionalOrders
          simp
        rw [h1, h2, Nat.gcd_eq_left hpq]
        norm_num
      rw [hord] at hdvd
      exact ⟨rfl, Nat.dvd_antisymm hdvd hpZ, f, hf, hmod⟩
  · exact absurd hpZ (hExc ↥K hK hex p hp hp3)
  · exact absurd hpZ (hSpor ↥K hK hsp p hp hp3)

end Main

end CFSG.RankThree.PartOne
