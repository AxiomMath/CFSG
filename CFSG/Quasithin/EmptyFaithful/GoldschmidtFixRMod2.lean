module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRMod1

public section

namespace CFSG.Quasithin.FixR

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem inv_eq_self_of_sq (hW : ∀ w : W, w ^ 2 = 1) (w : W) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hW w)

@[expose] def phiHom (a : MulAut W) : W →* W where
  toFun w := w * a w
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _

theorem phiHom_apply (a : MulAut W) (w : W) : phiHom a w = w * a w := rfl

theorem mem_ker_phiHom (hW : ∀ w : W, w ^ 2 = 1) (a : MulAut W) {w : W} :
    w ∈ (phiHom a).ker ↔ a w = w := by
  rw [MonoidHom.mem_ker, phiHom_apply]
  constructor
  · intro h
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_self_of_sq hW]
  · intro h
    rw [h, ← sq]
    exact hW w

theorem fixed_phiHom (a : MulAut W) (haa : a * a = 1) (w : W) :
    a (phiHom a w) = phiHom a w := by
  have h : a (a w) = w := by
    have := congrArg (fun f : MulAut W => f w) haa
    simpa [MulAut.mul_apply] using this
  rw [phiHom_apply, map_mul, h, mul_comm]

@[expose] def nuQ (q : MulAut W) (w : W) : W := w * q w * (q ^ 2) w * (q ^ 3) w * (q ^ 4) w

theorem nuQ_mul (q : MulAut W) (x y : W) : nuQ q (x * y) = nuQ q x * nuQ q y := by
  simp only [nuQ, map_mul]
  ac_rfl

@[expose] def nuHom (q : MulAut W) : W →* W where
  toFun := nuQ q
  map_one' := by simp [nuQ]
  map_mul' := nuQ_mul q

theorem nuHom_apply (q : MulAut W) (w : W) : nuHom q w = nuQ q w := rfl

theorem qpow_succ_apply (q : MulAut W) (n : ℕ) (w : W) : q ((q ^ n) w) = (q ^ (n + 1)) w := by
  rw [pow_succ']; rfl

theorem qpow_apply_five (q : MulAut W) (hq : q ^ 5 = 1) (w : W) : q ((q ^ 4) w) = w := by
  rw [qpow_succ_apply, hq]; rfl

theorem qpow_two_apply (q : MulAut W) (w : W) : (q ^ 2) w = q (q w) := by
  rw [pow_two]; rfl

theorem q_nuQ (q : MulAut W) (hq : q ^ 5 = 1) (w : W) : q (nuQ q w) = nuQ q w := by
  have e2 : q (q w) = (q ^ 2) w := (qpow_two_apply q w).symm
  have e3 : q ((q ^ 2) w) = (q ^ 3) w := qpow_succ_apply q 2 w
  have e4 : q ((q ^ 3) w) = (q ^ 4) w := qpow_succ_apply q 3 w
  have e5 : q ((q ^ 4) w) = w := qpow_apply_five q hq w
  simp only [nuQ, map_mul, e2, e3, e4, e5]
  ac_rfl

theorem comm_nuQ (q c : MulAut W) (h : c * q = q * c) (w : W) : c (nuQ q w) = nuQ q (c w) := by
  have hk : ∀ k : ℕ, c * q ^ k = q ^ k * c := fun k =>
    (Commute.pow_right (show Commute c q from h) k).eq
  have hk' : ∀ (k : ℕ) (v : W), c ((q ^ k) v) = (q ^ k) (c v) := fun k v => by
    have := congrArg (fun f : MulAut W => f v) (hk k)
    simpa [MulAut.mul_apply] using this
  have h1 : c (q w) = q (c w) := by simpa using hk' 1 w
  simp only [nuQ, map_mul, hk', h1]

theorem a_mul_qpow (a q : MulAut W) (hq5 : q ^ 5 = 1) (hqa : a * q = q ^ 4 * a) :
    a * q ^ 2 = q ^ 3 * a ∧ a * q ^ 3 = q ^ 2 * a ∧ a * q ^ 4 = q * a := by
  have h2 : a * q ^ 2 = q ^ 3 * a := by
    calc a * q ^ 2 = a * q * q := by rw [pow_two, mul_assoc]
      _ = q ^ 4 * a * q := by rw [hqa]
      _ = q ^ 4 * (a * q) := by rw [mul_assoc]
      _ = q ^ 4 * (q ^ 4 * a) := by rw [hqa]
      _ = q ^ (5 + 3) * a := by rw [← mul_assoc, ← pow_add]
      _ = q ^ 3 * a := by rw [pow_add, hq5, one_mul]
  have h3 : a * q ^ 3 = q ^ 2 * a := by
    calc a * q ^ 3 = a * q ^ 2 * q := by rw [pow_succ, mul_assoc]
      _ = q ^ 3 * a * q := by rw [h2]
      _ = q ^ 3 * (a * q) := by rw [mul_assoc]
      _ = q ^ 3 * (q ^ 4 * a) := by rw [hqa]
      _ = q ^ (5 + 2) * a := by rw [← mul_assoc, ← pow_add]
      _ = q ^ 2 * a := by rw [pow_add, hq5, one_mul]
  have h4 : a * q ^ 4 = q * a := by
    calc a * q ^ 4 = a * q ^ 3 * q := by rw [pow_succ _ 3, mul_assoc]
      _ = q ^ 2 * a * q := by rw [h3]
      _ = q ^ 2 * (a * q) := by rw [mul_assoc]
      _ = q ^ 2 * (q ^ 4 * a) := by rw [hqa]
      _ = q ^ (5 + 1) * a := by rw [← mul_assoc, ← pow_add]
      _ = q * a := by rw [pow_add, hq5, one_mul, pow_one]
  exact ⟨h2, h3, h4⟩

theorem a_nuQ (a q : MulAut W) (hq5 : q ^ 5 = 1) (hqa : a * q = q ^ 4 * a) (y : W) :
    a (nuQ q y) = nuQ q (a y) := by
  obtain ⟨h2, h3, h4⟩ := a_mul_qpow a q hq5 hqa
  have k1 : a (q y) = (q ^ 4) (a y) := congrArg (fun φ : MulAut W => φ y) hqa
  have k2 : a ((q ^ 2) y) = (q ^ 3) (a y) := congrArg (fun φ : MulAut W => φ y) h2
  have k3 : a ((q ^ 3) y) = (q ^ 2) (a y) := congrArg (fun φ : MulAut W => φ y) h3
  have k4 : a ((q ^ 4) y) = q (a y) := congrArg (fun φ : MulAut W => φ y) h4
  simp only [nuQ, map_mul, k1, k2, k3, k4]
  ac_rfl

theorem hilbert_ninety (hW : ∀ w : W, w ^ 2 = 1) (a q : MulAut W) (hq5 : q ^ 5 = 1)
    (hqa : a * q = q ^ 4 * a) {y : W} (hay : a y = y) (hy : nuQ q y = 1) :
    ∃ u : W, nuQ q u = 1 ∧ u * a u = y := by
  obtain ⟨h2, -, -⟩ := a_mul_qpow a q hq5 hqa
  refine ⟨q y * (q ^ 2) y, ?_, ?_⟩
  · rw [nuQ_mul]
    have h1 : nuQ q (q y) = 1 := by
      have := comm_nuQ q q rfl y
      rw [← this, hy, map_one]
    have h2' : nuQ q ((q ^ 2) y) = 1 := by
      have := comm_nuQ q (q ^ 2) (by rw [← pow_succ, ← pow_succ']) y
      rw [← this, hy, map_one]
    rw [h1, h2', one_mul]
  · have k1 : a (q y) = (q ^ 4) y := by
      have := congrArg (fun φ : MulAut W => φ y) hqa
      simpa [hay] using this
    have k2 : a ((q ^ 2) y) = (q ^ 3) y := by
      have := congrArg (fun φ : MulAut W => φ y) h2
      simpa [hay] using this
    have hc : y * (q y * (q ^ 2) y * (q ^ 3) y * (q ^ 4) y) = 1 := by
      have h := hy
      simp only [nuQ] at h
      rw [← h]
      ac_rfl
    have hc' : q y * (q ^ 2) y * (q ^ 3) y * (q ^ 4) y = y := by
      rw [eq_inv_of_mul_eq_one_right hc, inv_eq_self_of_sq hW]
    rw [map_mul, k1, k2]
    calc q y * (q ^ 2) y * ((q ^ 4) y * (q ^ 3) y)
        = q y * (q ^ 2) y * (q ^ 3) y * (q ^ 4) y := by ac_rfl
      _ = y := hc'

theorem apply_mem_ker_nuHom (a q : MulAut W) (hq5 : q ^ 5 = 1) (hqa : a * q = q ^ 4 * a) {y : W}
    (hy : y ∈ (nuHom q).ker) : a y ∈ (nuHom q).ker := by
  rw [MonoidHom.mem_ker, nuHom_apply] at hy ⊢
  rw [← a_nuQ a q hq5 hqa, hy, map_one]

theorem inf_ker_phiHom_eq (hW : ∀ w : W, w ^ 2 = 1) (a q : MulAut W) (haa : a * a = 1)
    (hq5 : q ^ 5 = 1) (hqa : a * q = q ^ 4 * a) :
    (phiHom a).ker ⊓ (nuHom q).ker = (nuHom q).ker.map (phiHom a) := by
  ext y
  constructor
  · rintro ⟨hy1, hy2⟩
    have hay : a y = y := (mem_ker_phiHom hW a).mp hy1
    obtain ⟨u, hu1, hu2⟩ := hilbert_ninety hW a q hq5 hqa hay hy2
    exact ⟨u, MonoidHom.mem_ker.mpr hu1, hu2⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(mem_ker_phiHom hW a).mpr (fixed_phiHom a haa u), ?_⟩
    exact (nuHom q).ker.mul_mem hu (apply_mem_ker_nuHom a q hq5 hqa hu)

theorem card_ker_nuHom [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (a q : MulAut W) (haa : a * a = 1)
    (hq5 : q ^ 5 = 1) (hqa : a * q = q ^ 4 * a) :
    Nat.card ((nuHom q).ker.map (phiHom a)) * Nat.card ((nuHom q).ker.map (phiHom a)) =
      Nat.card (nuHom q).ker := by
  have h1 := Subgroup.relIndex_mul_card (H := (phiHom a).ker) (K := (nuHom q).ker)
  rw [Subgroup.relIndex_ker, inf_ker_phiHom_eq hW a q haa hq5 hqa] at h1
  exact h1

theorem card_fixV_mul_ge [Finite W] (a : MulAut W) (Y : Subgroup W) :
    Nat.card (phiHom a).ker * Nat.card (Y.map (phiHom a)) ≤ Nat.card W := by
  rw [← Subgroup.card_ker_mul_card_range (phiHom a)]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (Subgroup.map_le_range _ _))

theorem apply_mem_commV (P : Subgroup (MulAut W)) {γ : MulAut W}
    (hγ : γ ∈ Subgroup.normalizer (P : Set (MulAut W))) {w : W} (hw : w ∈ commV P) :
    γ w ∈ commV P :=
  map_commV_le P hγ ⟨w, hw, rfl⟩

theorem nuQ_mem_commV (P : Subgroup (MulAut W)) {q : MulAut W} (hq : q ∈ P) {w : W}
    (hw : w ∈ commV P) : nuQ q w ∈ commV P := by
  have hk : ∀ k : ℕ, (q ^ k) w ∈ commV P := fun k =>
    apply_mem_commV P (Subgroup.le_normalizer (P.pow_mem hq k)) hw
  have h1 : q w ∈ commV P := by simpa using hk 1
  unfold nuQ
  exact (commV P).mul_mem ((commV P).mul_mem ((commV P).mul_mem ((commV P).mul_mem hw h1)
    (hk 2)) (hk 3)) (hk 4)

theorem tp_le_ker_nuHom [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 25)
    {q : MulAut W} (hq : q ∈ P) (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1) {L : Subgroup (MulAut W)}
    (hL : L ≤ P) (hLc : Nat.card L = 5) (hne : Subgroup.zpowers q ≠ L) :
    tp P L ≤ (nuHom q).ker := by
  intro w hw
  rw [MonoidHom.mem_ker, nuHom_apply]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq5' : orderOf q = 5 := orderOf_eq_prime hq5 hq1
  have hMc : Nat.card (Subgroup.zpowers q) = 5 := by rw [Nat.card_zpowers, hq5']
  have hMP : Subgroup.zpowers q ≤ P := (Subgroup.zpowers_le).mpr hq
  have hsup : Subgroup.zpowers q ⊔ L = P := sup_eq_of_ne hP hMP hL hMc hLc hne
  have hzq : q (nuQ q w) = nuQ q w := q_nuQ q hq5 w
  have hzL : ∀ l ∈ L, l (nuQ q w) = nuQ q w := fun l hl => by
    have hcomm : l * q = q * l := hPc l (hL hl) q hq
    rw [comm_nuQ q l hcomm w, hw.1 l hl]
  have hzM : ∀ x ∈ Subgroup.zpowers q, x (nuQ q w) = nuQ q w := by
    have : Subgroup.zpowers q ≤ MulAction.stabilizer (MulAut W) (nuQ q w) :=
      (Subgroup.zpowers_le).mpr hzq
    exact fun x hx => this hx
  have hzP : ∀ x ∈ P, x (nuQ q w) = nuQ q w := by
    have := fix_of_le_sup hzM hzL
    rwa [hsup] at this
  exact eq_one_of_fixed_of_mem_commV hW P hP (nuQ_mem_commV P hq hw.2) hzP

end CFSG.Quasithin.FixR
