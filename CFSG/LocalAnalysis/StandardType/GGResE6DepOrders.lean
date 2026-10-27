module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.GH74.Orders.LieType
public import CFSG.Timmesfeld.Final.Orders
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4h_factorization_two_of_profile {m N : ℕ} {Z : ℕ → Prop}
    (h : CFSG.Timmesfeld.Orders.Profile m N Z) : m.factorization 2 = N := by
  obtain ⟨r, hr, hm⟩ := h.two
  have hr2 : ¬ 2 ∣ r := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hr
  have h2 : (2 ^ N * r).factorization 2 = N := by
    rw [Nat.factorization_mul (pow_ne_zero N (by norm_num)) hr.pos.ne']
    change (2 ^ N).factorization 2 + r.factorization 2 = N
    rw [Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hr2, add_zero]
  rwa [hm]

theorem l05nL4h_markedModel
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hperf : commutator X = ⊤)
    (hnt : Nontrivial (X ⧸ Subgroup.center X)) (hlab : LargeEvenInLambda2 lab)
    (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    MarkedModel lab (X ⧸ Subgroup.center X) := by
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hperf hnt
  obtain ⟨R, _, I, F, ⟨e⟩, hm⟩ := largeEvenRawDatum_exists
    (largeEvenRawDatum_markedModel hlab
      (Q := fun R' _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R'))
      (by rintro R _ I F ⟨e⟩; exact nonabelian_of_mulEquiv e ⟨a, b, hab⟩)
      hl)
  exact MarkedModel.of_mulEquiv e.symm hm

private theorem l05nL4h_card_A5 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hA : GGA5Label lab) (hm : MarkedModel lab R) :
    (lab.tag = .A → Nat.card R = CFSG.Open.ordA 5 (2 ^ lab.n)) ∧
    (lab.tag = .twA → Nat.card R = CFSG.Open.ordTwistedA 5 (2 ^ lab.n)) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · have hmodel : LieModel R .PSL 6 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht, hA.1] using hm
    simpa using CFSG.GH74.card_of_lieModel_PSL (by norm_num : (6 : ℕ) ≠ 0) hmodel
  · have hmodel : LieModel R .PSU 6 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht, hA.1] using hm
    have hc := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num : (6 : ℕ) ≠ 0) hmodel
    simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 rfl

private theorem l05nL4h_card_E6 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hE : GGE6DepLabel lab) (hm : MarkedModel lab R) :
    (lab.tag = .E6 → Nat.card R = CFSG.Open.ordE6 (2 ^ lab.n)) ∧
    (lab.tag = .twE6 → Nat.card R = CFSG.Open.ordTwistedE6 (2 ^ lab.n)) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · have hmodel : LieModel R .E6 0 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hm
    have hc := CFSG.Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel
      (by decide : StatedLieTag.E6 ∈ CFSG.Blueprint.chevalleyExceptionalTags) hmodel
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
  · have hmodel : LieModel R .twistedE6 0 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hm
    have hc := CFSG.Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel
      (by decide : StatedLieTag.twistedE6 ∈ CFSG.Blueprint.chevalleyExceptionalTags) hmodel
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc

private theorem l05nL4h_two_part_A5 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hA : GGA5Label lab) (hm : MarkedModel lab R) :
    (Nat.card R).factorization 2 = 15 * lab.n := by
  rcases hA.2 with ⟨ht, _⟩ | ⟨ht, _⟩
  · rw [(l05nL4h_card_A5 hA hm).1 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordA (n := 5) (f := lab.n)
      (by norm_num) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [show 5 * (5 + 1) / 2 = 15 by norm_num, Nat.mul_comm] using this
  · rw [(l05nL4h_card_A5 hA hm).2 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 5) (g := lab.n)
      (by norm_num) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [show 5 * (5 + 1) / 2 = 15 by norm_num, Nat.mul_comm] using this

private theorem l05nL4h_two_part_E6 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hE : GGE6DepLabel lab) (hm : MarkedModel lab R) :
    (Nat.card R).factorization 2 = 36 * lab.n := by
  have hcard := l05nL4h_card_E6 hE hm
  rcases hE with ⟨ht, _⟩ | ⟨ht, _⟩
  · rw [hcard.1 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordE6 (f := lab.n) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [Nat.mul_comm] using this
  · rw [hcard.2 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordTwistedE6 (f := lab.n) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [Nat.mul_comm] using this

private theorem l05nL4h_dvd_ordA_five {q r : ℕ} (hr : r.Prime) (h11 : 11 ≤ r)
    (h : r ∣ q ^ 5 - 1) : r ∣ CFSG.Open.ordA 5 q := by
  set P : ℕ := ∏ i ∈ Finset.Icc 2 6, (q ^ i - 1) with hP
  set g : ℕ := Nat.gcd 6 (q - 1) with hg
  have hPmem : (5 : ℕ) ∈ Finset.Icc 2 6 := by norm_num
  have hq5dvd : q ^ 5 - 1 ∣ P := by
    rw [hP]
    exact Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hPmem
  have hPdvd : r ∣ P := h.trans hq5dvd
  have hgP : g ∣ P := by
    have h1 : g ∣ q - 1 := by rw [hg]; exact Nat.gcd_dvd_right 6 (q - 1)
    exact h1.trans ((Nat.sub_one_dvd_pow_sub_one q 5).trans hq5dvd)
  have hcop : Nat.Coprime r g := by
    have hr6 : ¬ r ∣ 6 := by
      intro hd
      have := Nat.le_of_dvd (by norm_num : 0 < 6) hd
      omega
    have hg6 : g ∣ 6 := by rw [hg]; exact Nat.gcd_dvd_left 6 (q - 1)
    exact (hr.coprime_iff_not_dvd.mpr hr6).coprime_dvd_right hg6
  have hgm : g ∣ q ^ 15 * P := hgP.trans (dvd_mul_left P (q ^ 15))
  have hm : r ∣ g * (q ^ 15 * P / g) := by
    rw [Nat.mul_div_cancel' hgm]
    exact dvd_mul_of_dvd_right hPdvd (q ^ 15)
  have hdiv : r ∣ q ^ 15 * P / g := (hcop.dvd_mul_left).mp hm
  rw [CFSG.Open.ordA, show 5 * (5 + 1) / 2 = 15 by norm_num, show (5 : ℕ) + 1 = 6 by norm_num,
    ← hP, ← hg]
  exact hdiv

theorem ggResE6Dep_two_part_ge_A5
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hperf : commutator X = ⊤)
    (hnt : Nontrivial (X ⧸ Subgroup.center X)) (hlab : LargeEvenInLambda2 lab)
    (hA : GGA5Label lab) (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    15 * lab.n ≤ (Nat.card X).factorization 2 := by
  have hm := l05nL4h_markedModel hperf hnt hlab hl
  have hfacR := l05nL4h_two_part_A5 hlab hA hm
  have hZ0 : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hle : (Nat.card (X ⧸ Subgroup.center X)).factorization 2 ≤
      (Nat.card X).factorization 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
    exact (Nat.factorization_le_factorization_mul_left hZ0) 2
  rw [hfacR] at hle
  exact hle

theorem ggResE6Dep_two_part_le_E6
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hT3 : GGSchurDvdInput)
    (hperf : commutator X = ⊤) (hnt : Nontrivial (X ⧸ Subgroup.center X))
    (hlab : LargeEvenInLambda2 lab) (hE : GGE6DepLabel lab)
    (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    (Nat.card X).factorization 2 ≤ 36 * lab.n + 2 := by
  have hm := l05nL4h_markedModel hperf hnt hlab hl
  have hfacR := l05nL4h_two_part_E6 hlab hE hm
  have hZ12 : Nat.card (Subgroup.center X) ∣ 12 := hT3 X lab hperf hlab (Or.inl hE) hl
  have hZ0 : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hQ0 : Nat.card (X ⧸ Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hZfac : (Nat.card (Subgroup.center X)).factorization 2 ≤ 2 := by
    have h := ((Nat.factorization_le_iff_dvd hZ0 (by norm_num : (12 : ℕ) ≠ 0)).2 hZ12) 2
    have h12 : (12 : ℕ).factorization 2 = 2 := by
      rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num)]
      change (2 ^ 2).factorization 2 + (3 : ℕ).factorization 2 = 2
      rw [Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
    rwa [h12] at h
  have hfacX : (Nat.card X).factorization 2 =
      (Nat.card (X ⧸ Subgroup.center X)).factorization 2 +
        (Nat.card (Subgroup.center X)).factorization 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
      Nat.factorization_mul hQ0 hZ0]
    rfl
  rw [hfacX, hfacR]
  omega

theorem ggResE6Dep_not_prime_dvd_E6
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hT3 : GGSchurDvdInput)
    (hperf : commutator X = ⊤) (hnt : Nontrivial (X ⧸ Subgroup.center X))
    (hlab : LargeEvenInLambda2 lab) (hE : GGE6DepLabel lab)
    (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) {r : ℕ} (hr : r.Prime) (h11 : 11 ≤ r)
    (hZ : (lab.tag = .E6 → ¬ r ∣ CFSG.Open.ordE6 (2 ^ lab.n)) ∧
      (lab.tag = .twE6 → ¬ r ∣ CFSG.Open.ordTwistedE6 (2 ^ lab.n))) :
    ¬ r ∣ Nat.card X := by
  have hm := l05nL4h_markedModel hperf hnt hlab hl
  intro hdvd
  have hQ0 : Nat.card (X ⧸ Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hZ0 : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hcardX : Nat.card X =
      Nat.card (X ⧸ Subgroup.center X) * Nat.card (Subgroup.center X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [hcardX] at hdvd
  rcases (hr.dvd_mul).mp hdvd with hR | hc
  · have hcard := l05nL4h_card_E6 hE hm
    rcases hE with ⟨ht, _⟩ | ⟨ht, _⟩
    · rw [hcard.1 ht] at hR
      exact hZ.1 ht hR
    · rw [hcard.2 ht] at hR
      exact hZ.2 ht hR
  · have hc12 : r ∣ 12 := hc.trans (hT3 X lab hperf hlab (Or.inl hE) hl)
    have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) hc12
    interval_cases r
    · norm_num at hc12
    · norm_num at hr

theorem ggResE6Dep_prime_dvd_A5
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hperf : commutator X = ⊤)
    (hnt : Nontrivial (X ⧸ Subgroup.center X)) (hlab : LargeEvenInLambda2 lab)
    (hA : GGA5Label lab) (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) {n : ℕ}
    (hn : lab.n = 2 * n) {r : ℕ} (hr : r.Prime) (h11 : 11 ≤ r) (hr10 : r ∣ 2 ^ (10 * n) - 1) :
    r ∣ Nat.card X := by
  have hm := l05nL4h_markedModel hperf hnt hlab hl
  have hnot : ¬ 3 ∣ 2 ^ lab.n + 1 := by
    rw [hn]
    have hpow : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    rw [hpow]
    intro h3
    have h4 : 3 ∣ 4 ^ n - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one 4 n
    have h32 : 3 ∣ 2 := by
      have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by norm_num)
      have hsub := Nat.dvd_sub h3 h4
      have hsub2 : (4 ^ n + 1) - (4 ^ n - 1) = 2 := by omega
      rwa [hsub2] at hsub
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h32
    omega
  rcases hA.2 with ⟨ht, h3⟩ | ⟨ht, h3⟩
  · have hcard := (l05nL4h_card_A5 hA hm).1 ht
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hcard]
    apply dvd_mul_of_dvd_left
    rw [hn]
    apply l05nL4h_dvd_ordA_five hr h11
    have hpow : (2 ^ (2 * n)) ^ 5 = 2 ^ (10 * n) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [hpow]
    exact hr10
  · exact absurd h3 hnot

end CFSG.StandardType
