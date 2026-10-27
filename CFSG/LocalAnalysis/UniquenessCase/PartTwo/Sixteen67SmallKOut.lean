module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

open scoped Pointwise

theorem exists_orderOf_three_of_split
    (hsplit : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFactSylowSplit) {Q : Type} [Group Q]
    [Finite Q] (J : Subgroup Q) [J.Normal] (hcat : CFSG.Open.IsCatalogGroup ↥J)
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) ≤ 1) (hC : centralizer (J : Set Q) = ⊥)
    (P : Sylow 3 Q) (hPJ : ¬ (P : Subgroup Q) ≤ J) :
    ∃ x : Q, x ∈ (P : Subgroup Q) ∧ x ∉ J ∧ orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ι : Q →* MulAut ↥J := MulAut.conjNormal
  have hι_apply : ∀ (q : Q) (j : ↥J), (ι q j : Q) = q * j * q⁻¹ :=
    fun q j => MulAut.conjNormal_apply q j
  have hιJ : ∀ j : ↥J, ι (j : Q) = MulAut.conj j := fun j => MulAut.conjNormal_val
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hcomm : q ∈ centralizer (J : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h2 : q * j * q⁻¹ = j := by
        have hh : ((ι q ⟨j, hj⟩ : ↥J) : Q) = ((1 : MulAut ↥J) ⟨j, hj⟩ : Q) :=
          congrArg (fun y : ↥J => (y : Q)) (DFunLike.congr_fun hq ⟨j, hj⟩)
        rw [hι_apply q ⟨j, hj⟩] at hh
        simpa [MulAut.one_apply] using hh
      have h3 : q * j = j * q := by
        have hh : (q * j * q⁻¹) * q = j * q := congrArg (· * q) h2
        simpa [mul_assoc] using hh
      exact h3.symm
    exact Subgroup.mem_bot.mp (hC ▸ hcomm)
  have hmem : ∀ q : Q, q ∈ J ↔ ι q ∈ inner ↥J := by
    intro q
    constructor
    · intro hq
      exact MonoidHom.mem_range.mpr ⟨⟨q, hq⟩, (hιJ ⟨q, hq⟩).symm⟩
    · intro hq
      obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp hq
      have hqj : (j : Q) = q := hι (by rw [hιJ j, hj])
      rw [← hqj]
      exact j.2
  have hPp : IsPGroup 3 ((P : Subgroup Q).map ι) := (P.isPGroup'.map ι)
  obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow hPp
  have hcomapP : IsPGroup 3 ((S : Subgroup (MulAut ↥J)).comap ι) :=
    (S.isPGroup').comap_of_injective ι hι
  have hleP : (P : Subgroup Q) ≤ (S : Subgroup (MulAut ↥J)).comap ι := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact hPS (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hcomap_eq : (S : Subgroup (MulAut ↥J)).comap ι = (P : Subgroup Q) :=
    P.is_maximal' hcomapP hleP
  obtain ⟨R, hRS, hRI, hSR⟩ :=
    hsplit 3 Nat.prime_three (by norm_num) ↥J hs hnab hcat hrank S
  let A : Subgroup (MulAut ↥J) := (S : Subgroup (MulAut ↥J)) ⊓ inner ↥J
  have hRN : R ≤ Subgroup.normalizer (A : Set (MulAut ↥J)) := by
    rw [Subgroup.le_set_normalizer_iff]
    intro r hr a ha
    exact ⟨(S : Subgroup (MulAut ↥J)).mul_mem
        ((S : Subgroup (MulAut ↥J)).mul_mem (hRS hr) ha.1)
        ((S : Subgroup (MulAut ↥J)).inv_mem (hRS hr)),
      (inner_normal ↥J).conj_mem a ha.2 r⟩
  have hRA : R ⊔ A = S := by rw [sup_comm]; exact hSR
  have hSset : (S : Set (MulAut ↥J)) =
      (R : Set (MulAut ↥J)) * (A : Set (MulAut ↥J)) := by
    have h := Subgroup.coe_mul_of_left_le_normalizer_right R A hRN
    rwa [hRA] at h
  obtain ⟨p, hpP, hpJ⟩ := Set.not_subset.mp hPJ
  have hPSp : ι p ∈ (S : Set (MulAut ↥J)) :=
    hPS (Subgroup.mem_map.mpr ⟨p, hpP, rfl⟩)
  rw [hSset] at hPSp
  obtain ⟨r, hr, a, ha, hpa⟩ := Set.mem_mul.mp hPSp
  obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp ha.2
  let p₀ : Q := p * (j : Q)⁻¹
  have hp₀ : ι p₀ = r := by
    show ι (p * (↑j)⁻¹) = r
    rw [map_mul, map_inv, hιJ j, hj, ← hpa]
    group
  have hp₀P : p₀ ∈ (P : Subgroup Q) := by
    have hmem' : p₀ ∈ (S : Subgroup (MulAut ↥J)).comap ι := by
      rw [Subgroup.mem_comap]
      show ι p₀ ∈ (S : Subgroup (MulAut ↥J))
      rw [hp₀]
      exact hRS hr
    rw [hcomap_eq] at hmem'
    exact hmem'
  have hr1 : r ≠ 1 := by
    intro hr_eq
    have hpinner : ι p ∈ inner ↥J := by
      rw [← hpa, hr_eq, one_mul]
      exact ha.2
    exact hpJ ((hmem p).mpr hpinner)
  have hrS : r ∈ (S : Subgroup (MulAut ↥J)) := hRS hr
  obtain ⟨k, hkord⟩ := S.isPGroup'.exists_orderOf_eq_pow ⟨r, hrS⟩
  have hord : orderOf r = 3 ^ k := (Subgroup.orderOf_mk r hrS).symm.trans hkord
  have hk : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hk_eq, pow_zero] at hord
    exact hr1 (orderOf_eq_one_iff.mp hord)
  let m : ℕ := k - 1
  have hmk : m < k := by show k - 1 < k; omega
  have hmk1 : m + 1 = k := by show k - 1 + 1 = k; omega
  let r' : MulAut ↥J := r ^ (3 ^ m)
  have hr'R : r' ∈ R := by
    show r ^ (3 ^ m) ∈ R
    exact R.pow_mem hr (3 ^ m)
  have hr'pow : r' ^ 3 = 1 := by
    show (r ^ (3 ^ m)) ^ 3 = 1
    rw [← pow_mul]
    have hpow : 3 ^ m * 3 = orderOf r := by
      rw [← pow_succ, hmk1, hord]
    rw [hpow, pow_orderOf_eq_one]
  have hr'ne1 : r' ≠ 1 := by
    intro h1
    have hdvd : orderOf r ∣ 3 ^ m := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [r'] using h1
    rw [hord] at hdvd
    have hle : 3 ^ k ≤ 3 ^ m := Nat.le_of_dvd (pow_pos (by norm_num) m) hdvd
    have hlt : 3 ^ m < 3 ^ k := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).2 hmk
    omega
  have hr'ord : orderOf r' = 3 := orderOf_eq_prime hr'pow hr'ne1
  let x : Q := p₀ ^ (3 ^ m)
  refine ⟨x, ?_, ?_, ?_⟩
  · show p₀ ^ (3 ^ m) ∈ (P : Subgroup Q)
    exact (P : Subgroup Q).pow_mem hp₀P (3 ^ m)
  · intro hx
    have hιx : ι x = r' := by
      show ι (p₀ ^ (3 ^ m)) = r ^ (3 ^ m)
      rw [map_pow, hp₀]
    have hrmem : r' ∈ inner ↥J := by
      have hinner := (hmem x).mp hx
      rwa [hιx] at hinner
    have hbot : r' ∈ (⊥ : Subgroup (MulAut ↥J)) := by
      have hthis : r' ∈ R ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J :=
        ⟨hr'R, hrmem⟩
      rwa [hRI] at hthis
    have h1 : r' = 1 := Subgroup.mem_bot.mp hbot
    rw [h1] at hr'ord
    simp only [orderOf_one] at hr'ord
    omega
  · have hιx : ι x = r' := by
      show ι (p₀ ^ (3 ^ m)) = r ^ (3 ^ m)
      rw [map_pow, hp₀]
    have h1 := orderOf_injective ι hι x
    rw [hιx, hr'ord] at h1
    exact h1.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
