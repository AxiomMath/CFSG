module

public import CFSG.Timmesfeld.Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72

variable {K : Type*} [Group K]

private theorem orderOf_mul_ne_of_not_commute {a b : K} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : ¬ Commute a b) : ¬ orderOf (a * b) ∣ 2 := by
  intro hd
  apply hab
  have h2 : (a * b) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  have ha2 : a * a = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp ha.dvd
  have hb2 : b * b = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hb.dvd
  have h3 : a * b * (a * b) = 1 := by rw [← pow_two]; exact h2
  have h4 : a * b = b * a := by
    calc a * b = a * b * (a * b * (a * b)⁻¹) := by group
      _ = (a * b * (a * b)) * (a * b)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [h3]; group
      _ = b * a := by
        have : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
        rw [this, inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]
  exact h4

private theorem false_of_commute_left {D : Set K} (hodd : IsOddTransp D) {u v f : K}
    (hu : u ∈ D) (hv : v ∈ D) (hf : f ∈ D) (hcomm : Commute u v) (hw : u * v ∈ D)
    (hfu : Commute f u) (hfv : ¬ Commute f v) : False := by
  have hfv' : ¬ orderOf (f * v) ∣ 2 :=
    orderOf_mul_ne_of_not_commute (hodd.1 f hf) (hodd.1 v hv) hfv
  have hodd_fv : Odd (orderOf (f * v)) := (hodd.2 f hf v hv).resolve_left hfv'
  have hm1 : orderOf (f * v) ≠ 1 := fun h => hfv' (by rw [h]; exact one_dvd _)
  have hcu : Commute u (f * v) := (hfu.symm).mul_right hcomm
  have hco : (orderOf u).Coprime (orderOf (f * v)) := by
    rw [hodd.1 u hu]
    exact Nat.coprime_two_left.mpr hodd_fv
  have hord : orderOf (u * (f * v)) = 2 * orderOf (f * v) := by
    rw [hcu.orderOf_mul_eq_mul_orderOf_of_coprime hco, hodd.1 u hu]
  have hfw : f * (u * v) = u * (f * v) := by
    calc f * (u * v) = (f * u) * v := by group
      _ = (u * f) * v := by rw [hfu.eq]
      _ = u * (f * v) := by group
  rcases hodd.2 f hf (u * v) hw with h | h
  · rw [hfw, hord] at h
    have : orderOf (f * v) ∣ 1 := by
      have h' : 2 * orderOf (f * v) ∣ 2 * 1 := by simpa using h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h'
    exact hm1 (Nat.dvd_one.mp this)
  · rw [hfw, hord] at h
    exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) h

theorem mem_rootSet_of_mul_mem {D : Set K} (hodd : IsOddTransp D) {u v : K} (hu : u ∈ D)
    (hv : v ∈ D) (hcomm : Commute u v) (hw : u * v ∈ D) : v ∈ rootSet D u := by
  have hw' : v * u ∈ D := by rw [← hcomm.eq]; exact hw
  refine ⟨hv, fun f hf => ⟨fun hvf => ?_, fun huf => ?_⟩⟩
  · by_contra hnu
    exact false_of_commute_left hodd hv hu hf hcomm.symm hw' hvf.symm (fun h => hnu h.symm)
  · by_contra hnv
    exact false_of_commute_left hodd hu hv hf hcomm hw huf.symm (fun h => hnv h.symm)

end CFSG.RankThree.GF2n.Tim79a
