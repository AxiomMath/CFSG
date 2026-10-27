module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MA
public import CFSG.Quasithin.Vol2.Ch10SecB3Facts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem factCommNatSL_holds : FactCommNatSL := by
  intro V _ _ H A Z d a p hd hD hp hp2 hpH hA hcomm hZ x hx v
  obtain ⟨K, _, _, -, π, hD⟩ := hD
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  obtain ⟨B, hBs, hBk, hBe⟩ := C10P34.exists_natHom hD
  obtain ⟨Y, hY⟩ := C10P34.exists_induced B hBs x.toMonoidHom
    (fun w hw => (hBk _).mpr (hZ x hx w ((hBk w).mp hw)))
  have hY' : ∀ w, Y (B w) = B (x w) := hY
  have hxπ : ∀ (γ : ↥(StatedSL (m + 2) K)) (w : V),
      x (((π γ : ↥H) : MulAut V) w) = ((π γ : ↥H) : MulAut V) (x w) := by
    intro γ w
    have := congrArg (fun g : MulAut V => g w) (hcomm x hx _ (π γ).2)
    simpa [MulAut.mul_apply] using this
  have hYc : ∀ (γ : ↥(StatedSL (m + 2) K)) (y : Multiplicative (Fin (m + 2) → K)),
      Y (natAct _ γ y) = natAct _ γ (Y y) := by
    intro γ y
    obtain ⟨w, rfl⟩ := hBs y
    rw [← hBe, hY', hY', ← hBe]
    exact congrArg B (hxπ γ w)
  obtain ⟨l, hl⟩ := C10P34.eq_smul_of_comm_trv (by omega) Y
    (fun i j hij c y => hYc (B5.trvSL i j hij c) y)
  have hit : ∀ (k : ℕ) (w : V), Y^[k] (B w) = B ((x ^ k) w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [Function.iterate_succ_apply, hY', ih, pow_succ, MulAut.mul_apply]
  have hitl : ∀ (k : ℕ) (y : Multiplicative (Fin (m + 2) → K)),
      Multiplicative.toAdd (Y^[k] y) = l ^ k • Multiplicative.toAdd y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply, ih, hl, smul_smul, pow_succ]
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨w₀, hw₀⟩ := hBs (Multiplicative.ofAdd (Pi.single 0 1))
  have hl1 : l ^ p ^ k = 1 := by
    have h1 := hit (p ^ k) w₀
    rw [hxk, MulAut.one_apply, hw₀] at h1
    have h2 := congrArg (fun y => y 0) (hitl (p ^ k) (Multiplicative.ofAdd (Pi.single 0 1)))
    simp only [h1, toAdd_ofAdd, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hl1' : l = 1 := by
    by_contra hne
    have hl0 : l ≠ 0 := by
      intro h0
      rw [h0, zero_pow (pow_ne_zero k hp.ne_zero)] at hl1
      exact zero_ne_one hl1
    set μ : Kˣ := Units.mk0 l hl0 with hμ
    have hμk : μ ^ p ^ k = 1 := Units.ext (by simp [hμ, hl1])
    have hμ1 : μ ≠ 1 := fun h => hne (by simpa [hμ] using congrArg Units.val h)
    have hpμ : p ∣ orderOf μ := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hμk)
      rcases j with _ | j
      · rw [pow_zero, orderOf_eq_one_iff] at hj
        exact absurd hj hμ1
      · rw [hj]
        exact dvd_pow_self p (Nat.succ_ne_zero j)
    set t := C10P34.torusSL m μ with ht
    have hBpow : ∀ (r : ℕ) (w : V), B ((((π t) ^ r : ↥H) : MulAut V) w) =
        (natAct (StatedSL (m + 2) K) t)^[r] (B w) := by
      intro r
      induction r with
      | zero => intro w; simp
      | succ r ih =>
        intro w
        calc B ((((π t) ^ (r + 1) : ↥H) : MulAut V) w)
            = B ((((π t) ^ r : ↥H) : MulAut V) (((π t : ↥H) : MulAut V) w)) := by
              rw [pow_succ, Subgroup.coe_mul, MulAut.mul_apply]
          _ = (natAct (StatedSL (m + 2) K) t)^[r] (B (((π t : ↥H) : MulAut V) w)) := ih _
          _ = (natAct (StatedSL (m + 2) K) t)^[r] (natAct (StatedSL (m + 2) K) t (B w)) :=
              congrArg _ (hBe t w)
          _ = (natAct (StatedSL (m + 2) K) t)^[r + 1] (B w) :=
              (Function.iterate_succ_apply _ _ _).symm
    have hTpow : ∀ (r : ℕ) (c : K), (natAct (StatedSL (m + 2) K) t)^[r]
        (Multiplicative.ofAdd (Pi.single 0 c)) =
          Multiplicative.ofAdd (Pi.single 0 ((μ : K) ^ r * c)) := by
      intro r
      induction r with
      | zero => intro c; simp
      | succ r ih =>
        intro c
        rw [Function.iterate_succ_apply', ih, ht, C10P34.natAct_torusSL, pow_succ', mul_assoc]
    have hord : orderOf μ ∣ orderOf (π t) := by
      apply orderOf_dvd_of_pow_eq_one
      have h1 : ((((π t) ^ orderOf (π t) : ↥H) : MulAut V) w₀) = w₀ := by
        rw [pow_orderOf_eq_one]
        rfl
      have h2 := (congrArg B h1).symm.trans (hBpow (orderOf (π t)) w₀)
      rw [hw₀, hTpow] at h2
      have h3 := congrArg (fun y : Multiplicative (Fin (m + 2) → K) => Multiplicative.toAdd y 0) h2
      simp only [toAdd_ofAdd, Pi.single_eq_same, mul_one] at h3
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h3, Units.val_one])
    exact hpH ((hpμ.trans hord).trans (orderOf_dvd_natCard _))
  have h := hl (B v)
  rw [hY', hl1', one_smul] at h
  have h2 : B (x v * v⁻¹) = 1 := by
    rw [map_mul, map_inv, Multiplicative.toAdd.injective h, mul_inv_cancel]
  exact (hBk _).mp h2

end CFSG.Quasithin.Vol2.Ch10.SecB
