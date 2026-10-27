module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MD
public import CFSG.Quasithin.Vol2.Ch10SecB3Facts
public import CFSG.Quasithin.Vol2.Ch10SecQ34MA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint Matrix

theorem factCommSz_holds : FactCommSz := by
  intro V _ _ H A Z f p hD hp hp2 hpH hA hcomm hZ x hx v
  obtain ⟨a, -, rfl, K, _, _, -, π, hD⟩ := hD
  obtain ⟨B, hBs, hBk, hBe⟩ := C10P34.exists_natHom hD
  obtain ⟨Y, hY⟩ := C10P34.exists_induced B hBs x.toMonoidHom
    (fun w hw => (hBk _).mpr (hZ x hx w ((hBk w).mp hw)))
  have hY' : ∀ w, Y (B w) = B (x w) := hY
  have hxπ : ∀ (γ : ↥(suzukiGroup a K)) (w : V),
      x (((π γ : ↥H) : MulAut V) w) = ((π γ : ↥H) : MulAut V) (x w) := by
    intro γ w
    have := congrArg (fun g : MulAut V => g w) (hcomm x hx _ (π γ).2)
    simpa [MulAut.mul_apply] using this
  have hYc : ∀ (γ : ↥(suzukiGroup a K)) (m : Multiplicative (Fin 4 → K)),
      Y (natAct _ γ m) = natAct _ γ (Y m) := by
    intro γ m
    obtain ⟨w, rfl⟩ := hBs m
    rw [← hBe, hY', hY', ← hBe]
    exact congrArg B (hxπ γ w)
  set y : (Fin 4 → K) →+ (Fin 4 → K) := AddMonoidHom.toMultiplicative.symm Y with hydef
  have hyM : ∀ (γ : ↥(suzukiGroup a K)) (w : Fin 4 → K),
      y (((γ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w) =
        ((γ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ y w :=
    fun γ w => congrArg Multiplicative.toAdd (hYc γ (Multiplicative.ofAdd w))
  obtain ⟨μ, hμ⟩ := C10P34.eq_smul_of_comm_suzuki a y (fun w => hyM (C10P34.sElt a 1 0) w)
    (fun v w => hyM (C10P34.sElt a 0 v) w) (fun w => hyM (C10P34.wElt a K) w)
  have hYμ : ∀ m, Multiplicative.toAdd (Y m) = μ • Multiplicative.toAdd m := fun m =>
    hμ (Multiplicative.toAdd m)
  have hit : ∀ (k : ℕ) (w : V), Y^[k] (B w) = B ((x ^ k) w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [Function.iterate_succ_apply, hY', ih, pow_succ, MulAut.mul_apply]
  have hitμ : ∀ (k : ℕ) (m : Multiplicative (Fin 4 → K)),
      Multiplicative.toAdd (Y^[k] m) = μ ^ k • Multiplicative.toAdd m := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [Function.iterate_succ_apply, ih, hYμ, smul_smul, pow_succ]
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨w₀, hw₀⟩ := hBs (Multiplicative.ofAdd (Pi.single 1 1))
  have hμ1 : μ ^ p ^ k = 1 := by
    have h1 := hit (p ^ k) w₀
    rw [hxk, MulAut.one_apply, hw₀] at h1
    have h2 := congrArg (fun z => z 1) (hitμ (p ^ k) (Multiplicative.ofAdd (Pi.single 1 1)))
    simp only [h1, toAdd_ofAdd, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hμ' : μ = 1 := by
    by_contra hne
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, zero_pow (pow_ne_zero k hp.ne_zero)] at hμ1
      exact zero_ne_one hμ1
    set l : Kˣ := Units.mk0 μ hμ0 with hl
    have hlk : l ^ p ^ k = 1 := Units.ext (by simp [hl, hμ1])
    have hl1 : l ≠ 1 := fun h => hne (by simpa [hl] using congrArg Units.val h)
    have hpl : p ∣ orderOf l := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hlk)
      rcases j with _ | j
      · rw [pow_zero, orderOf_eq_one_iff] at hj
        exact absurd hj hl1
      · rw [hj]
        exact dvd_pow_self p (Nat.succ_ne_zero j)
    set t := C10P34.dElt a l with ht
    have hBpow : ∀ (r : ℕ) (w : V), B ((((π t) ^ r : ↥H) : MulAut V) w) =
        (natAct (suzukiGroup a K) t)^[r] (B w) := by
      intro r
      induction r with
      | zero => intro w; simp
      | succ r ih =>
        intro w
        calc B ((((π t) ^ (r + 1) : ↥H) : MulAut V) w)
            = B ((((π t) ^ r : ↥H) : MulAut V) (((π t : ↥H) : MulAut V) w)) := by
              rw [pow_succ, Subgroup.coe_mul, MulAut.mul_apply]
          _ = (natAct (suzukiGroup a K) t)^[r] (B (((π t : ↥H) : MulAut V) w)) := ih _
          _ = (natAct (suzukiGroup a K) t)^[r] (natAct (suzukiGroup a K) t (B w)) :=
              congrArg _ (hBe t w)
          _ = (natAct (suzukiGroup a K) t)^[r + 1] (B w) :=
              (Function.iterate_succ_apply _ _ _).symm
    have hTpow : ∀ (r : ℕ) (c : K), (natAct (suzukiGroup a K) t)^[r]
        (Multiplicative.ofAdd (Pi.single 1 c)) =
          Multiplicative.ofAdd (Pi.single 1 ((((l ^ (2 ^ a : ℤ)) ^ r : Kˣ)) * c)) := by
      intro r
      induction r with
      | zero => intro c; simp
      | succ r ih =>
        intro c
        rw [Function.iterate_succ_apply', ih]
        change Multiplicative.ofAdd (suzukiD a l *ᵥ Pi.single 1 _) = _
        rw [C10P34.mulVec_D_one, pow_succ', Units.val_mul, mul_assoc]
    have hord : p ∣ orderOf (π t) := by
      have h1 : ((((π t) ^ orderOf (π t) : ↥H) : MulAut V) w₀) = w₀ := by
        rw [pow_orderOf_eq_one]
        rfl
      have h2 := (congrArg B h1).symm.trans (hBpow (orderOf (π t)) w₀)
      rw [hw₀, hTpow] at h2
      have h3 := congrArg (fun z : Multiplicative (Fin 4 → K) => Multiplicative.toAdd z 1) h2
      simp only [toAdd_ofAdd, Pi.single_eq_same, mul_one] at h3
      have h4 : (l ^ (2 ^ a : ℤ)) ^ orderOf (π t) = 1 := Units.ext (by rw [← h3, Units.val_one])
      have h5 : l ^ (2 ^ a * orderOf (π t)) = 1 := by
        rw [pow_mul, ← h4]
        congr 1
      have h6 := (hpl.trans (orderOf_dvd_of_pow_eq_one h5))
      rcases (Nat.Prime.dvd_mul hp).mp h6 with h7 | h7
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h7))
          hp2
      · exact h7
    exact hpH (hord.trans (orderOf_dvd_natCard _))
  have h := hYμ (B v)
  rw [hY', hμ', one_smul] at h
  have h2 : B (x v * v⁻¹) = 1 := by
    rw [map_mul, map_inv, Multiplicative.toAdd.injective h, mul_inv_cancel]
  exact (hBk _).mp h2

end CFSG.Quasithin.Vol2.Ch10.SecB
