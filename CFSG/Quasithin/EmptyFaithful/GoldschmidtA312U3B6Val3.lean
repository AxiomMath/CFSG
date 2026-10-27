module

public import CFSG.RankThree.PartOne.A6N.Trace
public import CFSG.RankThree.SubgroupLists.CentralThreeLift
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Aux

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.RankThree.SubgroupLists

section Lift

variable {H : Type*} [Group H] [Finite H]

theorem exists_conj_pow_lift (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1)
    (hP : ¬ 5 ^ 2 ∣ Nat.card (H ⧸ Subgroup.center H)) {u v : H} (hu5 : u ^ 5 = 1)
    (hu : u ∉ Subgroup.center H) (hv5 : v ^ 5 = 1) (hv1 : v ≠ 1) :
    ∃ k : ℕ, IsConj v (u ^ k) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h53 : Nat.Coprime 5 3 := by norm_num
  have hu1 : (u : H ⧸ Subgroup.center H) ≠ 1 := fun h =>
    hu ((QuotientGroup.eq_one_iff u).mp h)
  have hv : (v : H ⧸ Subgroup.center H) ≠ 1 := by
    intro h
    have hvc : v ∈ Subgroup.center H := (QuotientGroup.eq_one_iff v).mp h
    have h3 := hZ3 v hvc
    have hd : orderOf v ∣ Nat.gcd 5 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hv5) (orderOf_dvd_of_pow_eq_one h3)
    rw [show Nat.gcd 5 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hv1 hd
  have hou : orderOf (u : H ⧸ Subgroup.center H) = 5 :=
    orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hu5, QuotientGroup.mk_one]) hu1
  have hov : orderOf (v : H ⧸ Subgroup.center H) = 5 :=
    orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hv5, QuotientGroup.mk_one]) hv
  obtain ⟨g, k, hk⟩ := exists_conj_pow_of_orderOf hP hou hov
  refine ⟨k, isConj_of_isConj_mk le_rfl hZ3 h53 hv5 ?_ ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hu5, one_pow]
  · rw [QuotientGroup.mk_pow]
    exact isConj_iff.mpr ⟨g, hk⟩

end Lift

section Trace

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)}

@[expose] def trH (x : H) : K := Matrix.trace ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem trH_conj {a b : H} (h : IsConj a b) : trH a = trH b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  simp only [trH, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  exact (trace_conj_gl (c : GL (Fin 3) K) _).symm

theorem isConj_of_trace_eq (h5 : (5 : K) ≠ 0)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) {u v : H} (hu5 : u ^ 5 = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hinv : IsConj u u⁻¹) {k : ℕ} (hk : IsConj v (u ^ k))
    (htr : trH v = trH u) : IsConj v u := by
  have hsq : trH (u ^ 2) ≠ trH u := by
    have hu5' : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 5 = 1 := by
      have := congrArg (fun x : H => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hu5
      simpa using this
    have hu1' : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := fun h =>
      hu1 (Subtype.ext (Units.ext (by simpa using h)))
    have htr' : (((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)⁻¹).trace =
        ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
      have := trH_conj hinv
      simpa [trH, Matrix.coe_units_inv] using this.symm
    have := CFSG.RankThree.PartOne.A6N.tr_sq_ne h5 (hdet u u.2) hu5' hu1' htr'
    simpa [trH, pow_two] using this
  have hu5k : ∀ n : ℕ, u ^ n = u ^ (n % 5) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, hu5, one_pow, one_mul]
  rw [hu5k k] at hk
  have hk5 : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : k % 5
  · rw [pow_zero] at hk
    exact absurd (isConj_one_left.mp hk) hv1
  · simpa using hk
  · exact absurd ((trH_conj hk).symm.trans htr) hsq
  · obtain ⟨c, hc⟩ := isConj_iff.mp hinv
    have h23 : IsConj (u ^ 2) (u ^ 3) := by
      refine isConj_iff.mpr ⟨c, ?_⟩
      have hu3 : (u ^ 2)⁻¹ = u ^ 3 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, hu5]
      calc c * u ^ 2 * c⁻¹ = (c * u * c⁻¹) ^ 2 := conj_pow.symm
        _ = (u⁻¹) ^ 2 := by rw [hc]
        _ = u ^ 3 := by rw [inv_pow, hu3]
    exact absurd (((trH_conj h23).trans (trH_conj hk).symm).trans htr) hsq
  · have hu4 : u ^ 4 = u⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hu5]
    rw [hu4] at hk
    exact hk.trans hinv.symm

end Trace

end CFSG.Quasithin.A312U3
