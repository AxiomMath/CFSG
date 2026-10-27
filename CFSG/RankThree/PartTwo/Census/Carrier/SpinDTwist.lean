module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDPoints

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame.Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {bm : Matrix ι ι ℤ} {qd : ι → ℤ}
  {N : Type} [Fintype N] [DecidableEq N] (F : Frame bm qd N)

theorem gamA_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : ι) :
    (F.gamA A a).map f = F.gamA B a := by
  ext r c
  simp [gamA]

theorem rho_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : GL N A) :
    F.rho B (Matrix.GeneralLinearGroup.map f g) = (F.rho A g).map f := by
  ext b a
  have e : ((Matrix.GeneralLinearGroup.map f g : GL N B) : Matrix N N B) * F.gamA B a *
      (↑(Matrix.GeneralLinearGroup.map f g)⁻¹ : Matrix N N B) =
      ((g : Matrix N N A) * F.gamA A a * (↑g⁻¹ : Matrix N N A)).map f := by
    have hc : ∀ h : GL N A, ((Matrix.GeneralLinearGroup.map f h : GL N B) : Matrix N N B) =
        (h : Matrix N N A).map f := fun h => rfl
    rw [← Matrix.GeneralLinearGroup.map_inv, hc, hc, ← F.gamA_map f, ← Matrix.map_mul,
      ← Matrix.map_mul]
  simp only [rho, coord, e, Matrix.map_apply]

theorem rho_conj {A : Type*} [CommRing A] (P : GL N A) (τ : Equiv.Perm ι)
    (hτ : ∀ a, τ (τ a) = a)
    (hP : ∀ a, (P : Matrix N N A) * F.gamA A a * (↑P⁻¹ : Matrix N N A) = -F.gamA A (τ a))
    {g : GL N A} (hg : g ∈ F.normGroup A) (b a : ι) :
    F.rho A (P * g * P⁻¹) b a = F.rho A g (τ b) (τ a) := by
  have hPP : (↑P⁻¹ : Matrix N N A) * (P : Matrix N N A) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hP' : (↑P⁻¹ : Matrix N N A) * F.gamA A a * (P : Matrix N N A) = -F.gamA A (τ a) := by
    have h := hP (τ a)
    rw [hτ] at h
    calc (↑P⁻¹ : Matrix N N A) * F.gamA A a * (P : Matrix N N A)
        = (↑P⁻¹ : Matrix N N A) * (-((P : Matrix N N A) * F.gamA A (τ a) *
            (↑P⁻¹ : Matrix N N A))) * (P : Matrix N N A) := by rw [h, neg_neg]
      _ = -(((↑P⁻¹ : Matrix N N A) * (P : Matrix N N A)) * F.gamA A (τ a) *
            ((↑P⁻¹ : Matrix N N A) * (P : Matrix N N A))) := by noncomm_ring
      _ = -F.gamA A (τ a) := by rw [hPP, one_mul, mul_one]
  have e : ((P * g * P⁻¹ : GL N A) : Matrix N N A) * F.gamA A a *
      (↑(P * g * P⁻¹)⁻¹ : Matrix N N A) =
      -((P : Matrix N N A) * ((g : Matrix N N A) * F.gamA A (τ a) * (↑g⁻¹ : Matrix N N A)) *
        (↑P⁻¹ : Matrix N N A)) := by
    have e1 : ((P * g * P⁻¹ : GL N A) : Matrix N N A) * F.gamA A a *
        (↑(P * g * P⁻¹)⁻¹ : Matrix N N A) =
        (P : Matrix N N A) * (g : Matrix N N A) * ((↑P⁻¹ : Matrix N N A) * F.gamA A a *
          (P : Matrix N N A)) * (↑g⁻¹ : Matrix N N A) * (↑P⁻¹ : Matrix N N A) := by
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
      noncomm_ring
    rw [e1, hP']
    noncomm_ring
  have hsum : (P : Matrix N N A) * (∑ c, F.rho A g c (τ a) • F.gamA A c) *
      (↑P⁻¹ : Matrix N N A) = ∑ c, F.rho A g c (τ a) • -F.gamA A (τ c) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hP]
  show F.coord A b _ = F.rho A g (τ b) (τ a)
  rw [e, conj_gamA hg, hsum]
  simp only [coord, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (τ b)]
  · have h1 := F.coord_gamA A b b
    rw [ite_eq_left rfl] at h1
    rw [hτ, show F.gamA A b (F.pos b).1 (F.pos b).2 = 1 from h1]
    ring
  · intro c _ hc
    have h1 := F.coord_gamA A b (τ c)
    have hbc : b ≠ τ c := fun h => hc (by rw [h, hτ])
    rw [ite_eq_right hbc] at h1
    rw [show F.gamA A (τ c) (F.pos b).1 (F.pos b).2 = 0 from h1]
    ring
  · simp

end CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame.Frame

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier SpinFrame
open CFSG.RankThree.PartTwo.Census.Spin.CarrierD (Cl IsIntOp crD anD)

variable (n : ℕ) (hn : 4 ≤ n)

abbrev lastD : Fin n := ⟨n - 1, by omega⟩

abbrev tauD : Equiv.Perm (DI n) :=
  Equiv.swap (.inl (lastD n hn)) (.inr (lastD n hn))

@[expose] noncomputable def graphIntMatrix : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  fun i j => if i = graphBasisPerm n (by omega) j then graphBasisScale n (by omega) j else 0

theorem isIntOp_graphIntMatrix :
    IsIntOp n (crD n (lastD n hn) - anD n (lastD n hn)) (graphIntMatrix n hn) := by
  intro s
  have h := graphOperator_latticeBasis n (by omega) s
  rw [graphOperator, TauCeti.SpinPolarizationData.typeDGraphOperator_apply,
    TauCeti.SpinPolarizationData.typeDGraphVector_def, map_sub] at h
  rw [h, AddSubgroup.coe_zsmul, Finset.sum_eq_single (graphBasisPerm n (by omega) s)]
  · rw [graphIntMatrix, ite_eq_left rfl]
  · intro r _ hr
    rw [graphIntMatrix, ite_eq_right hr, zero_smul]
  · simp

theorem graphAutMatrix_eq (A : Type) [CommRing A] :
    ((graphAutMatrix n hn A : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      (frame n).gamA A (.inl (lastD n hn)) - (frame n).gamA A (.inr (lastD n hn)) := by
  have heq : graphIntMatrix n hn = gamD n (.inl (lastD n hn)) - gamD n (.inr (lastD n hn)) :=
    (isIntOp_graphIntMatrix n hn).eq ((isIntOp_gen n (.inl (lastD n hn))).sub
      (isIntOp_gen n (.inr (lastD n hn))))
  ext i j
  rw [coe_graphAutMatrix_apply, Matrix.sub_apply, Frame.gamA, Frame.gamA, frame_gam,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    ← map_sub, ← Matrix.sub_apply, ← heq, graphIntMatrix]
  split_ifs <;> simp

theorem sub_mul_mul_sub_eq {R : Type*} [Ring R] {X Y : R} (hX : X * X = 0) (hY : Y * Y = 0)
    (hXY : X * Y + Y * X = 1) :
    (X - Y) * X * (X - Y) = Y ∧ (X - Y) * Y * (X - Y) = X ∧
      ∀ Z, X * Z = -(Z * X) → Y * Z = -(Z * Y) → (X - Y) * Z * (X - Y) = Z := by
  refine ⟨?_, ?_, fun Z hXZ hYZ => ?_⟩
  · calc (X - Y) * X * (X - Y)
        = X * X * X - X * X * Y - Y * (X * X) + Y * (X * Y + Y * X) - Y * Y * X := by
          noncomm_ring
      _ = Y := by rw [hX, hXY, hY]; noncomm_ring
  · calc (X - Y) * Y * (X - Y)
        = X * (X * Y + Y * X) - X * X * Y - X * (Y * Y) - Y * Y * X + Y * (Y * Y) := by
          noncomm_ring
      _ = X := by rw [hX, hXY, hY]; noncomm_ring
  · calc (X - Y) * Z * (X - Y)
        = X * Z * X - X * Z * Y - Y * Z * X + Y * Z * Y := by noncomm_ring
      _ = -(Z * (X * X)) + Z * (X * Y + Y * X) - Z * (Y * Y) := by
          rw [hXZ, hYZ]
          noncomm_ring
      _ = Z := by rw [hX, hXY, hY]; noncomm_ring

theorem graphAutMatrix_inv (A : Type) [CommRing A] :
    (graphAutMatrix n hn A)⁻¹ = -graphAutMatrix n hn A :=
  inv_eq_of_mul_eq_one_right (by rw [mul_neg, graphAutMatrix_mul_self, neg_neg])

theorem graphAutMatrix_conj (A : Type) [CommRing A] (a : DI n) :
    ((graphAutMatrix n hn A : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) * (frame n).gamA A a *
      (↑(graphAutMatrix n hn A)⁻¹ : Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      -(frame n).gamA A (tauD n hn a) := by
  rw [graphAutMatrix_inv, Units.val_neg, graphAutMatrix_eq, mul_neg]
  congr 1
  set X := (frame n).gamA A (.inl (lastD n hn))
  set Y := (frame n).gamA A (.inr (lastD n hn))
  have hX : X * X = 0 := by
    rw [Frame.gamA_sq, qdD_apply, Int.cast_zero, map_zero]
  have hY : Y * Y = 0 := by
    rw [Frame.gamA_sq, qdD_apply, Int.cast_zero, map_zero]
  have hXY : X * Y + Y * X = 1 := by
    rw [Frame.gamA_anticomm, bmD_inl_inr, ite_eq_left rfl, Int.cast_one, map_one]
  obtain ⟨h1, h2, h3⟩ := sub_mul_mul_sub_eq hX hY hXY
  by_cases hax : a = .inl (lastD n hn)
  · rw [hax, Equiv.swap_apply_left]
    exact h1
  · by_cases hay : a = .inr (lastD n hn)
    · rw [hay, Equiv.swap_apply_right]
      exact h2
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]
      have hanti : ∀ {x : DI n}, bmD n x a = 0 → (frame n).gamA A x * (frame n).gamA A a =
          -((frame n).gamA A a * (frame n).gamA A x) := fun {x} hxa => by
        have h := (frame n).gamA_anticomm A x a
        rw [hxa, Int.cast_zero, map_zero] at h
        exact eq_neg_of_add_eq_zero_left h
      have hxa : bmD n (.inl (lastD n hn)) a = 0 := by
        rcases a with j | j
        · rfl
        · rw [bmD_inl_inr, ite_eq_right]
          rintro rfl
          exact hay rfl
      have hya : bmD n (.inr (lastD n hn)) a = 0 := by
        rcases a with j | j
        · rw [bmD_inr_inl, ite_eq_right]
          rintro rfl
          exact hax rfl
        · rfl
      exact h3 _ (hanti hxa) (hanti hya)

variable {n}

theorem orthPoints_graphAutPoints {K : Type} [Field K] (g : points n hn K) :
    ((orthPoints n hn K (graphAutPoints n hn K g) : GL (DI n) K) : Matrix (DI n) (DI n) K) =
      ((orthPoints n hn K g : GL (DI n) K) : Matrix (DI n) (DI n) K).submatrix (tauD n hn)
        (tauD n hn) := by
  ext b a
  rw [coe_orthPoints, coe_orthPoints, Matrix.submatrix_apply, coe_graphAutPoints]
  exact (frame n).rho_conj (graphAutMatrix n hn K) (tauD n hn)
    (fun a => Equiv.swap_apply_self _ _ a) (graphAutMatrix_conj n hn K)
    (points_le_normGroup n hn K g.2) b a

theorem orthPoints_frobenius {K : Type} [Field K] (p k : ℕ) [ExpChar K p] (g : points n hn K) :
    ((orthPoints n hn K (frobenius n hn p k K g) : GL (DI n) K) : Matrix (DI n) (DI n) K) =
      ((orthPoints n hn K g : GL (DI n) K) : Matrix (DI n) (DI n) K).map
        (iterateFrobenius K p k) := by
  rw [coe_orthPoints, coe_orthPoints, coe_frobenius, Frame.rho_map]

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD
