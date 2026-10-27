module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofCore
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJRank
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem j2Syl_comm_central {X : Type} [Group X] {P : Subgroup X}
    (hE : IsExtraspecialPGroup 3 P) {a b : X} (ha : a ∈ P) (hb : b ∈ P) :
    ∀ g ∈ P, g * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * g := by
  intro g hg
  obtain ⟨-, hcomm, -, -⟩ := hE
  have hmem : ⁅(⟨a, ha⟩ : P), (⟨b, hb⟩ : P)⁆ ∈ Subgroup.center P := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨g, hg⟩)
  simpa [commutatorElement_def] using h

theorem j2Syl_exists_sylow {X : Type} [Group X] [Finite X] {B : Subgroup X}
    (hB9 : Nat.card B = 9) : ∃ P : Sylow 3 X, B ≤ (P : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB : IsPGroup 3 B := IsPGroup.of_card (n := 2) (hB9.trans (by norm_num))
  obtain ⟨P, hP⟩ := hB.exists_le_sylow
  exact ⟨P, hP⟩

theorem j2Syl_exists_mem_not_mem {X : Type} [Group X] [Finite X] {P B : Subgroup X}
    (hP27 : Nat.card P = 27) (hB9 : Nat.card B = 9) : ∃ y ∈ P, y ∉ B := by
  by_contra hcon
  have hle : P ≤ B := by
    intro y hy
    by_contra hyB
    exact hcon ⟨y, hy, hyB⟩
  have h := Subgroup.card_le_of_le hle
  rw [hP27, hB9] at h
  omega

theorem j2Syl_eq_of_nine_lt {X : Type} [Group X] [Finite X] {P B H : Subgroup X}
    (hP27 : Nat.card P = 27) (hB9 : Nat.card B = 9) (hBH : B ≤ H) (hHP : H ≤ P)
    {y : X} (hyH : y ∈ H) (hyB : y ∉ B) : H = P := by
  have hdvd : Nat.card H ∣ 3 ^ 3 := by
    have h := Subgroup.card_dvd_of_le hHP
    rw [hP27] at h
    norm_num
    exact h
  obtain ⟨m, hm, hmH⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hgt : 9 < Nat.card H := by
    by_contra hle
    apply hyB
    have hBH' : B = H := Subgroup.eq_of_le_of_card_ge hBH (by rw [hB9]; exact not_lt.mp hle)
    rw [hBH']
    exact hyH
  have hH27 : Nat.card H = 27 := by
    interval_cases m <;> simp only [Nat.reducePow] at hmH <;> omega
  exact Subgroup.eq_of_le_of_card_ge hHP (le_of_eq (hP27.trans hH27.symm))

theorem j2Syl_not_comm
    {X : Type} [Group X] [Finite X]
    (h415 : CFSG.RankThree.PartTwo.Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {d c y : X}
    (hd1 : d ≠ 1) (hcd : c * d = d * c) (hcnd : c ∉ Subgroup.zpowers d)
    (hBP : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ (P : Subgroup X))
    (hP27 : Nat.card (P : Subgroup X) = 27)
    (hB9 : Nat.card ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers c) = 9)
    (hdZ : d ∈ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X))
    (hcP : c ∈ (P : Subgroup X)) (hyP : y ∈ (P : Subgroup X))
    (hyB : y ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c) : y * c ≠ c * y := by
  intro hyc
  have hdC' : d ∈ Subgroup.centralizer ({c} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcd.symm
  have hcC' : c ∈ Subgroup.centralizer ({c} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hyC' : y ∈ Subgroup.centralizer ({c} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyc
  have hHC : (Subgroup.zpowers d ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer ({c} : Set X) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hdC') (Subgroup.zpowers_le.mpr hcC'))
      (Subgroup.zpowers_le.mpr hyC')
  have hHP : (Subgroup.zpowers d ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers y ≤
      (P : Subgroup X) :=
    sup_le hBP (Subgroup.zpowers_le.mpr hyP)
  have hHeq : (Subgroup.zpowers d ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers y =
      (P : Subgroup X) :=
    j2Syl_eq_of_nine_lt hP27 hB9 le_sup_left hHP
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hyB
  have hcZ : c ∈ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨hcP, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have hh' : h ∈ (Subgroup.zpowers d ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers y := by
      rw [hHeq]
      exact hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hHC hh')
  exact hcnd (CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof.j2_mem_zpowers_of_mem_center
    h415 hX P hdZ hd1 hcZ)

theorem j2Syl_comm_mem
    {X : Type} [Group X] [Finite X]
    (h415 : CFSG.RankThree.PartTwo.Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {d y c : X}
    (hdZ : d ∈ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X))
    (hd1 : d ≠ 1) (hE : IsExtraspecialPGroup 3 (P : Subgroup X))
    (hyP : y ∈ (P : Subgroup X)) (hcP : c ∈ (P : Subgroup X)) :
    y * c * y⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := by
  have hw : y * c * y⁻¹ * c⁻¹ ∈
      (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hyP hcP) (inv_mem hyP)) (inv_mem hcP),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    exact j2Syl_comm_central hE hyP hcP h hh
  exact CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof.j2_mem_zpowers_of_mem_center
    h415 hX P hdZ hd1 hw

theorem exists_conj_eq_mul_of_j2
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {d c : X} (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1) (h27 : 27 ∣ Nat.card (Subgroup.centralizer ({d} : Set X)))
    (hc3 : c ^ 3 = 1) (hcd : c * d = d * c) (hcnd : c ∉ Subgroup.zpowers d) :
    ∃ y : X, y * d = d * y ∧ (y * c * y⁻¹ = d * c ∨ y * c * y⁻¹ = d ^ 2 * c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : CFSG.RankThree.PartTwo.Sec4.Item4_15 :=
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
  have hB9 : Nat.card ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers c) = 9 :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148J.card_zpowers_sup_zpowers_eq_nine hcd.symm hd3 hd1 hc3
      hcnd
  obtain ⟨P, hBP⟩ := j2Syl_exists_sylow hB9
  obtain ⟨⟨hH, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨hExt, hP27, -⟩ := hH
  have hdB : d ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hcB : c ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hdZ := CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof.j2_mem_center_of_dvd h415 hX P hBP
    hB9 hdB h27
  have hdC : d ∈ Subgroup.centralizer ((P : Subgroup X) : Set X) :=
    (Subgroup.mem_inf.mp hdZ).2
  have hcP : c ∈ (P : Subgroup X) := hBP hcB
  obtain ⟨y, hyP, hyB⟩ := j2Syl_exists_mem_not_mem hP27 hB9
  have hyc : y * c ≠ c * y :=
    j2Syl_not_comm h415 hX P hd1 hcd hcnd hBP hP27 hB9 hdZ hcP hyP hyB
  have hw := j2Syl_comm_mem h415 hX P hdZ hd1 hExt hyP hcP
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hk3 : d ^ (k % 3) = d ^ k := by
    have h := zpow_mod_orderOf d k
    simpa [hord] using h
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  refine ⟨y, (Subgroup.mem_centralizer_iff.mp hdC) y hyP, ?_⟩
  rcases hr with hr | hr | hr
  · exfalso
    apply hyc
    have h1 : y * c * y⁻¹ * c⁻¹ = 1 := by
      rw [← hk, ← hk3, hr, zpow_zero]
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · left
    have h1 : y * c * y⁻¹ * c⁻¹ = d := by
      rw [← hk, ← hk3, hr, zpow_one]
    calc y * c * y⁻¹ = y * c * y⁻¹ * c⁻¹ * c := by group
      _ = d * c := by rw [h1]
  · right
    have h1 : y * c * y⁻¹ * c⁻¹ = d ^ 2 := by
      rw [← hk, ← hk3, hr]
      norm_num
    calc y * c * y⁻¹ = y * c * y⁻¹ * c⁻¹ * c := by group
      _ = d ^ 2 * c := by rw [h1]

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
