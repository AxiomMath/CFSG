module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresDefs

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}

variable (D d) in
abbrev PiMat : Type := ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)

variable (D d) in
abbrev piE (i : Fin r) : PiMat D d := Pi.single i 1

theorem single_mul_eq (i : Fin r) (m : Matrix (Fin (d i)) (Fin (d i)) (D i)) (x : PiMat D d) :
    (Pi.single i m : PiMat D d) * x = Pi.single i (m * x i) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Pi.single_eq_of_ne hk]

theorem mul_single_eq (i : Fin r) (m : Matrix (Fin (d i)) (Fin (d i)) (D i)) (x : PiMat D d) :
    x * (Pi.single i m : PiMat D d) = Pi.single i (x i * m) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Pi.single_eq_of_ne hk]

theorem piE_mul (i : Fin r) (x : PiMat D d) : piE D d i * x = Pi.single i (x i) := by
  rw [piE, single_mul_eq, Matrix.one_mul]

theorem mul_piE (i : Fin r) (x : PiMat D d) : x * piE D d i = Pi.single i (x i) := by
  rw [piE, mul_single_eq, Matrix.mul_one]

theorem piE_ne_zero [∀ i, NeZero (d i)] (i : Fin r) : piE D d i ≠ 0 := by
  intro h
  have h1 := congrFun h i
  simp only [piE, Pi.single_eq_same, Pi.zero_apply] at h1
  exact one_ne_zero h1

theorem piE_injective [∀ i, NeZero (d i)] : Function.Injective (piE D d) := by
  intro i j h
  by_contra hij
  have h1 := congrFun h i
  simp only [piE, Pi.single_eq_same, Pi.single_eq_of_ne hij] at h1
  exact one_ne_zero h1

theorem exists_scalar_of_central {z : PiMat D d} (hz : ∀ x : PiMat D d, x * z = z * x) (j : Fin r) :
    ∃ c : D j, z j = Matrix.scalar (Fin (d j)) c := by
  have h : z j ∈ Set.center (Matrix (Fin (d j)) (Fin (d j)) (D j)) := by
    rw [Semigroup.mem_center_iff]
    intro m
    have h1 := congrFun (hz (Pi.single j m)) j
    simpa using h1
  rw [Matrix.center_eq_range] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

variable {τ : PiMat D d → PiMat D d}

theorem IsInvol.central (hτ : IsInvol τ) {z : PiMat D d} (hz : ∀ x : PiMat D d, x * z = z * x)
    (x : PiMat D d) : x * τ z = τ z * x := by
  obtain ⟨y, rfl⟩ := hτ.surjective x
  rw [← hτ.map_mul, ← hτ.map_mul, hz]

theorem central_idem_apply [∀ i, NeZero (d i)] {z : PiMat D d}
    (hz : ∀ x : PiMat D d, x * z = z * x) (hzz : z * z = z) (j : Fin r) : z j = 0 ∨ z j = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_central hz j
  have hcc : c * c = c := by
    have h1 := congrFun hzz j
    simp only [Pi.mul_apply, hc, ← map_mul] at h1
    have h0 : (0 : Fin (d j)) = ⟨0, Nat.pos_of_ne_zero (NeZero.ne (d j))⟩ := rfl
    have h2 := congrFun (congrFun h1 0) 0
    simpa [Matrix.scalar_apply] using h2
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with h | h
  · left
    rw [hc, h, map_zero]
  · right
    rw [hc, h, map_one]


section Perm

theorem piE_central (i : Fin r) (x : PiMat D d) : x * piE D d i = piE D d i * x := by
  rw [mul_piE, piE_mul]

theorem piE_mul_self (i : Fin r) : piE D d i * piE D d i = piE D d i := by
  rw [piE_mul]
  simp

theorem IsInvol.exists_tau_piE [∀ i, NeZero (d i)] (hτ : IsInvol τ) (i : Fin r) :
    ∃ j, τ (piE D d i) = piE D d j := by
  have hcτ := hτ.central (piE_central i)
  have hidem : τ (piE D d i) * τ (piE D d i) = τ (piE D d i) := by
    rw [← hτ.map_mul, piE_mul_self]
  obtain ⟨j, hj⟩ : ∃ j, τ (piE D d i) j ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : τ (piE D d i) = 0 := funext h
    exact piE_ne_zero i (hτ.injective (h0.trans hτ.map_zero.symm))
  have hj1 : τ (piE D d i) j = 1 := (central_idem_apply hcτ hidem j).resolve_left hj
  refine ⟨j, ?_⟩
  have hf : piE D d j * τ (piE D d i) = piE D d j := by
    rw [piE_mul, hj1]
  have h2 : piE D d i * τ (piE D d j) = τ (piE D d j) := by
    have h := congrArg τ hf
    rwa [hτ.map_mul, hτ.invol] at h
  have hcj := hτ.central (piE_central j)
  have hidemj : τ (piE D d j) * τ (piE D d j) = τ (piE D d j) := by
    rw [← hτ.map_mul, piE_mul_self]
  rcases central_idem_apply hcj hidemj i with h0 | h1
  · exfalso
    rw [piE_mul, h0, Pi.single_zero] at h2
    exact piE_ne_zero j (hτ.injective (h2.symm.trans hτ.map_zero.symm))
  · rw [piE_mul, h1] at h2
    have h3 : piE D d i = τ (piE D d j) := h2
    rw [h3, hτ.invol]

theorem IsInvol.exists_perm [∀ i, NeZero (d i)] (hτ : IsInvol τ) :
    ∃ π : Fin r → Fin r, ∀ i, τ (piE D d i) = piE D d (π i) :=
  ⟨fun i => (hτ.exists_tau_piE i).choose, fun i => (hτ.exists_tau_piE i).choose_spec⟩

variable {π : Fin r → Fin r}

theorem perm_perm [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) (i : Fin r) : π (π i) = i := by
  apply piE_injective (D := D) (d := d)
  rw [← hπ, ← hπ, hτ.invol]

theorem tau_single_apply_of_ne (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (i : Fin r) (m : Matrix (Fin (d i)) (Fin (d i)) (D i)) {k : Fin r} (hk : k ≠ π i) :
    τ (Pi.single i m) k = 0 := by
  have h : τ (Pi.single i m : PiMat D d) = piE D d (π i) * τ (Pi.single i m) := by
    conv_lhs => rw [show (Pi.single i m : PiMat D d) = Pi.single i m * piE D d i by
      rw [mul_piE, Pi.single_eq_same]]
    rw [hτ.map_mul, hπ]
  rw [h, piE_mul, Pi.single_eq_of_ne hk]

theorem apply_tau_eq [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) (x : PiMat D d) {j k : Fin r} (hjk : π k = j) :
    τ x k = τ (Pi.single j (x j)) k := by
  have h1 : τ (piE D d j) = piE D d k := by rw [hπ, ← hjk, perm_perm hτ hπ]
  have h2 : τ x * piE D d k = τ (Pi.single j (x j)) := by
    rw [← h1, ← hτ.map_mul, piE_mul]
  have h3 := congrFun h2 k
  rw [mul_piE, Pi.single_eq_same] at h3
  exact h3

variable (τ) in
@[expose] def tauFix (b : Fin r) (m : Matrix (Fin (d b)) (Fin (d b)) (D b)) :
    Matrix (Fin (d b)) (Fin (d b)) (D b) :=
  τ (Pi.single b m) b

theorem tau_single_eq_tauFix (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b : Fin r} (hb : π b = b) (m : Matrix (Fin (d b)) (Fin (d b)) (D b)) :
    τ (Pi.single b m) = Pi.single b (tauFix τ b m) := by
  funext k
  by_cases hk : k = b
  · subst hk
    rw [Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne hk, tau_single_apply_of_ne hτ hπ b m (by rwa [hb])]

theorem isInvol_tauFix (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b : Fin r} (hb : π b = b) : IsInvol (tauFix τ b) where
  map_add x y := by
    simp only [tauFix]
    rw [Pi.single_add, hτ.map_add, Pi.add_apply]
  map_mul x y := by
    simp only [tauFix]
    rw [Pi.single_mul, hτ.map_mul, Pi.mul_apply]
  map_one := by
    simp only [tauFix]
    rw [show (Pi.single b (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) : PiMat D d) = piE D d b from
      rfl, hπ, hb, piE, Pi.single_eq_same]
  invol x := by
    show τ (Pi.single b (tauFix τ b x)) b = x
    rw [← tau_single_eq_tauFix hτ hπ hb, hτ.invol, Pi.single_eq_same]

theorem apply_tau_eq_tauFix [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b : Fin r} (hb : π b = b) (x : PiMat D d) : τ x b = tauFix τ b (x b) :=
  apply_tau_eq hτ hπ x hb

end Perm

end LayerCores

end CFSG.StandardType
