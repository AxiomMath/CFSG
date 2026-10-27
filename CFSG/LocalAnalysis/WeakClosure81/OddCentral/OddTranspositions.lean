module
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Timmesfeld.Bridge.Asc72

theorem conj_not_mem_fusionZStar {Y : Type} [Group Y] {s : Y}
    (hs : normalClosure ({s} : Set Y) = ⊤) (hZ : fusionZStar Y ≠ ⊤) (g : Y) :
    g * s * g⁻¹ ∉ fusionZStar Y := by
  intro hg
  have hN : (fusionZStar Y).Normal := by
    unfold fusionZStar
    exact Subgroup.Normal.comap inferInstance _
  have hsZ : s ∈ fusionZStar Y := by
    have := hN.conj_mem _ hg g⁻¹
    simpa [mul_assoc] using this
  apply hZ
  rw [eq_top_iff, ← hs]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hsZ)

theorem oddTransp_no_common_inversion {X : Type} [Group X] {D : Set X} (hD : IsOddTransp D)
    (hDc : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (hde : d ≠ e) (hc : Commute d e) {y : X}
    (hy : Odd (orderOf y)) (hy1 : y ≠ 1) (hdy : d * y * d⁻¹ = y⁻¹) (hey : e * y * e⁻¹ = y⁻¹) :
    False := by
  have hd2 : orderOf d = 2 := hD.1 d hd
  have he2 : orderOf e = 2 := hD.1 e he
  have hdd : d * d = 1 := by
    have := pow_orderOf_eq_one d
    rw [hd2] at this
    simpa [pow_two] using this
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hdy' : d * y = y⁻¹ * d := by
    rw [mul_inv_eq_iff_eq_mul] at hdy
    exact hdy
  have hey' : e * y = y⁻¹ * e := by
    rw [mul_inv_eq_iff_eq_mul] at hey
    exact hey
  have h1 : d * y⁻¹ = y * d := by
    have h4 : y * d * y = d := by rw [mul_assoc, hdy']; simp
    exact (eq_mul_inv_of_mul_eq h4).symm
  have hf : y * d * y⁻¹ ∈ D := hDc d hd y
  have hfe : y * d * y⁻¹ * e = y ^ 2 * (d * e) := by
    calc y * d * y⁻¹ * e = y * (d * y⁻¹) * e := by simp [mul_assoc]
      _ = y * (y * d) * e := by rw [h1]
      _ = y ^ 2 * (d * e) := by simp [pow_two, mul_assoc]
  have hyc : Commute y (d * e) := by
    show y * (d * e) = d * e * y
    calc y * (d * e) = y * d * e := by simp [mul_assoc]
      _ = d * y⁻¹ * e := by rw [h1]
      _ = d * (y⁻¹ * e) := by simp [mul_assoc]
      _ = d * (e * y) := by rw [hey']
      _ = d * e * y := by simp [mul_assoc]
  have hde1 : d * e ≠ 1 := by
    intro h
    apply hde
    have : e = d⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, hdinv]
  have hde2 : orderOf (d * e) = 2 := by
    apply orderOf_eq_prime _ hde1
    rw [hc.mul_pow]
    have hee : e * e = 1 := by
      have := pow_orderOf_eq_one e
      rw [he2] at this
      simpa [pow_two] using this
    simp [pow_two, hdd, hee]
  have hord2 : orderOf (y ^ 2) = orderOf y := Nat.Coprime.orderOf_pow (Odd.coprime_two_right hy)
  have hco : (orderOf (y ^ 2)).Coprime (orderOf (d * e)) := by
    rw [hord2, hde2]
    exact Odd.coprime_two_right hy
  have hcomm : Commute (y ^ 2) (d * e) := hyc.pow_left 2
  have hord : orderOf (y ^ 2 * (d * e)) = orderOf y * 2 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hord2, hde2]
  rcases hD.2 _ hf e he with h | h
  · rw [hfe, hord] at h
    have h3 : orderOf y * 2 ∣ 1 * 2 := by simpa using h
    have h4 : orderOf y ∣ 1 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
    exact hy1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4))
  · rw [hfe, hord] at h
    obtain ⟨k, hk⟩ := h
    omega

theorem commute_of_commute_mul {X : Type} [Group X] [Finite X] {D : Set X}
    (hD : IsOddTransp D) (hDc : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D) {d e : X} (hd : d ∈ D)
    (he : e ∈ D) (hde : d ≠ e) (hc : Commute d e) {P : Subgroup X}
    (hP : Odd (Nat.card P)) (hPd : ∀ x ∈ P, d * x * d⁻¹ ∈ P) {q : X}
    (hq : q ∈ P) (hqc : Commute q (d * e)) : Commute q d := by
  have hd2 : orderOf d = 2 := hD.1 d hd
  have hdd : d * d = 1 := by
    have := pow_orderOf_eq_one d
    rw [hd2] at this
    simpa [pow_two] using this
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  set y : X := q⁻¹ * (d * q * d⁻¹) with hydef
  have hyP : y ∈ P := P.mul_mem (P.inv_mem hq) (hPd q hq)
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat hP (Subgroup.orderOf_dvd_natCard P hyP)
  have hdc : Commute d (d * e) := (Commute.refl d).mul_right hc
  have hyc : Commute y (d * e) :=
    hqc.inv_left.mul_left ((hdc.mul_left hqc).mul_left hdc.inv_left)
  have hdy : d * y * d⁻¹ = y⁻¹ := by
    rw [hydef]
    simp [mul_assoc, hdinv, hdd]
  have hey : e * y * e⁻¹ = y⁻¹ := by
    have h1 : e * y * e⁻¹ = d⁻¹ * ((d * e) * y * (d * e)⁻¹) * d := by group
    rw [h1, hyc.symm.eq]
    simp only [mul_inv_cancel_right]
    rw [hdinv]
    rw [hdinv] at hdy
    exact hdy
  by_cases hy1 : y = 1
  · rw [hydef, inv_mul_eq_one] at hy1
    exact (mul_inv_eq_iff_eq_mul.1 hy1.symm).symm
  · exact (oddTransp_no_common_inversion hD hDc hd he hde hc hyodd hy1 hdy hey).elim

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
