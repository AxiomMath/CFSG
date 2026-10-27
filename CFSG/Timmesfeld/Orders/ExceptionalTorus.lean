module

public import CFSG.LieType.Chevalley.TorusCoordinates

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section ZpowMatrix

variable {G : Type*} [CommGroup G] {n : ℕ}

@[expose] def zpowMatrix (M : Matrix (Fin n) (Fin n) ℤ) : (Fin n → G) →* (Fin n → G) where
  toFun t j := ∏ i, t i ^ M i j
  map_one' := by
    funext j
    simp
  map_mul' t u := by
    funext j
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem zpowMatrix_apply (M : Matrix (Fin n) (Fin n) ℤ) (t : Fin n → G) (j : Fin n) :
    zpowMatrix M t j = ∏ i, t i ^ M i j :=
  rfl

theorem zpowMatrix_zpowMatrix (M N : Matrix (Fin n) (Fin n) ℤ) (t : Fin n → G) :
    zpowMatrix M (zpowMatrix N t) = zpowMatrix (N * M) t := by
  funext j
  simp only [zpowMatrix_apply, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => prod_zpow_eq_zpow_sum _ _ _

theorem zpowMatrix_one (t : Fin n → G) : zpowMatrix 1 t = t := by
  funext j
  simp only [zpowMatrix_apply, Matrix.one_apply]
  rw [Finset.prod_eq_single j (fun i _ hij => by rw [ite_eq_right hij, zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), ite_eq_left rfl, zpow_one]

theorem card_ker_zpowMatrix_eq {A P P' D Q Q' : Matrix (Fin n) (Fin n) ℤ} (hA : A = P * D * Q)
    (hP : P' * P = 1) (hP' : P * P' = 1) (hQ : Q * Q' = 1) :
    Nat.card (zpowMatrix (G := G) A).ker = Nat.card (zpowMatrix (G := G) D).ker := by
  have hcomp : ∀ t : Fin n → G,
      zpowMatrix A t = zpowMatrix Q (zpowMatrix D (zpowMatrix P t)) := fun t => by
    rw [zpowMatrix_zpowMatrix, zpowMatrix_zpowMatrix, hA, mul_assoc]
  have hQinj : ∀ x : Fin n → G, zpowMatrix Q x = 1 → x = 1 := fun x hx => by
    have h := congrArg (zpowMatrix Q') hx
    rwa [zpowMatrix_zpowMatrix, hQ, zpowMatrix_one, map_one] at h
  refine Nat.card_congr
    { toFun := fun t => ⟨zpowMatrix P t, (MonoidHom.mem_ker).2 (hQinj _ (by
        rw [← hcomp]
        exact (MonoidHom.mem_ker).1 t.2))⟩
      invFun := fun s => ⟨zpowMatrix P' s, (MonoidHom.mem_ker).2 (by
        rw [hcomp, zpowMatrix_zpowMatrix P P', hP, zpowMatrix_one, (MonoidHom.mem_ker).1 s.2,
          map_one])⟩
      left_inv := fun t => Subtype.ext (by
        change zpowMatrix P' (zpowMatrix P (t : Fin n → G)) = t
        rw [zpowMatrix_zpowMatrix, hP', zpowMatrix_one])
      right_inv := fun s => Subtype.ext (by
        change zpowMatrix P (zpowMatrix P' (s : Fin n → G)) = s
        rw [zpowMatrix_zpowMatrix, hP, zpowMatrix_one]) }

theorem card_ker_zpowMatrix_diagonal (d : Fin n → ℕ) :
    Nat.card (zpowMatrix (G := G) (Matrix.diagonal fun i => (d i : ℤ))).ker =
      ∏ i, Nat.card (powMonoidHom (d i) : G →* G).ker := by
  have hdiag : ∀ (t : Fin n → G) (j : Fin n),
      zpowMatrix (Matrix.diagonal fun i => (d i : ℤ)) t j = t j ^ d j := fun t j => by
    rw [zpowMatrix_apply, Finset.prod_eq_single j (fun i _ hij => by
      rw [Matrix.diagonal_apply_ne _ hij, zpow_zero]) (fun h => absurd (Finset.mem_univ j) h),
      Matrix.diagonal_apply_eq, zpow_natCast]
  rw [← Nat.card_pi]
  refine Nat.card_congr
    { toFun := fun t i => ⟨(t : Fin n → G) i, (MonoidHom.mem_ker).2 (by
        rw [powMonoidHom_apply, ← hdiag]
        exact congrFun ((MonoidHom.mem_ker).1 t.2) i)⟩
      invFun := fun s => ⟨fun i => s i, (MonoidHom.mem_ker).2 (funext fun j => by
        rw [hdiag, Pi.one_apply]
        exact (MonoidHom.mem_ker).1 (s j).2)⟩
      left_inv := fun t => rfl
      right_inv := fun s => rfl }

end ZpowMatrix

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem list_prod_torusElt_hVec (l : List (Fin τ.rank × Kˣ)) (j : Fin τ.rank) :
    (((l.map fun p => torusElt τ K p.1 p.2).prod : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) (hVec τ K j) = hVec τ K j := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, torusElt_hVec]

theorem list_ofFn_torusElt (t : Fin τ.rank → Kˣ) :
    (List.ofFn fun i => torusElt τ K i (t i)) =
      (List.ofFn fun i => (i, t i)).map fun p => torusElt τ K p.1 p.2 := by
  rw [List.map_ofFn]
  rfl

theorem torusCoordHom_eq_one_iff (t : Fin τ.rank → Kˣ) :
    torusCoordHom τ K t = 1 ↔ zpowMatrix τ.cartan t = 1 := by
  constructor
  · intro ht
    funext j
    refine Units.ext ?_
    have h := torusCoordHom_apply_rootVec_single (R := K) t j
    rw [ht, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
      rootVec_eq_single_of_isRoot (isRoot_single τ j)] at h
    have h' := congrArg (fun v : RootModule τ K =>
      v (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) h
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
    rw [zpowMatrix_apply, Pi.one_apply, Units.val_one, ← h']
  · intro ht
    have hk : ∀ k, ∏ i, t i ^ τ.cartan i k = 1 := fun k => congrFun ht k
    refine Subtype.ext (Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_))
    · rw [OneMemClass.coe_one, Units.val_one, Module.End.one_apply, coe_torusCoordHom,
        list_ofFn_torusElt, list_prod_torusElt_hVec]
    · rw [OneMemClass.coe_one, Units.val_one, Module.End.one_apply, coe_torusCoordHom,
        list_ofFn_torusElt, list_prod_torusElt_rootVec hα, List.map_ofFn, List.prod_ofFn]
      have hscal : ∏ i : Fin τ.rank, t i ^ (∑ k, τ.cartan i k * α k) = 1 := by
        simp only [← prod_zpow_eq_zpow_sum, zpow_mul]
        rw [Finset.prod_comm]
        refine Finset.prod_eq_one fun k _ => ?_
        rw [Finset.prod_zpow, hk k, one_zpow]
      have e : ∏ i : Fin τ.rank, ((fun p : Fin τ.rank × Kˣ => p.2 ^ (∑ k, τ.cartan p.1 k * α k)) ∘
          (fun i => (i, t i))) i = 1 := hscal
      rw [e, Units.val_one, one_smul]

theorem card_torusGroup_mul [Finite K] :
    Nat.card (torusGroup τ K) * Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker =
      (Nat.card K - 1) ^ τ.rank := by
  have hker : (torusCoordHom τ K).ker = (zpowMatrix (G := Kˣ) τ.cartan).ker := by
    ext t
    simp only [MonoidHom.mem_ker]
    exact torusCoordHom_eq_one_iff t
  rw [← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    torusCoordHom_surjective).toEquiv, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_fun, Nat.card_units, Nat.card_fin]

theorem card_torusGroup_of_mul_eq_one [Finite K] {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hB : τ.cartan * B = 1) : Nat.card (torusGroup τ K) = (Nat.card K - 1) ^ τ.rank := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _ ⟨torusCoordHom_injective_of_mul_eq_one hB,
    torusCoordHom_surjective⟩).toEquiv, Nat.card_fun, Nat.card_units, Nat.card_fin]

end Torus

@[expose] def cartanInvE8 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

theorem cartan_mul_cartanInvE8 : Tag.E8.cartan * cartanInvE8 = 1 := by
  decide

@[expose] def smithE6P : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![-1, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0; 2, -1, 0, 0, -1, 0; -1, 2, -1, 0, 0, 0;
    0, -1, 2, -1, 0, 0; 0, 0, -1, 2, 4, -1]

@[expose] def smithE6P' : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![-1, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0; 1, -2, 0, -1, 0, 0; 2, -3, 0, -2, -1, 0;
    -2, 1, -1, 0, 0, 0; -5, 0, -4, -3, -2, -1]

@[expose] def smithE6Q : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![-2, 0, 1, 0, 0, 0; 0, -2, 0, 1, 0, 0; 2, -3, 0, 0, 1, 0; 4, -4, 0, 0, 0, 1;
    -3, 2, 0, 0, 0, 0; -2, 1, 0, 0, 0, 0]

@[expose] def smithE6Q' : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![0, 0, 0, 0, 1, -2; 0, 0, 0, 0, 2, -3; 1, 0, 0, 0, 2, -4; 0, 1, 0, 0, 4, -6;
    0, 0, 1, 0, 4, -5; 0, 0, 0, 1, 4, -4]

@[expose] def smithE7P : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![-1, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0; 2, -1, 0, 0, 0, -1, 0; -1, 2, -1, 0, 0, 0, 0;
    0, -1, 2, -1, 0, 0, 0; 0, 0, -1, 2, -1, 0, 0; 0, 0, 0, -1, 2, 4, -1]

@[expose] def smithE7P' : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![-1, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0; 1, -2, 0, -1, 0, 0, 0; 2, -3, 0, -2, -1, 0, 0;
    3, -4, 0, -3, -2, -1, 0; -2, 1, -1, 0, 0, 0, 0; -4, -1, -4, -4, -3, -2, -1]

@[expose] def smithE7Q : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![-2, 0, 1, 0, 0, 0, 0; 0, -2, 0, 1, 0, 0, 0; 2, -3, 0, 0, 1, 0, 0; 4, -4, 0, 0, 0, 1, 0;
    6, -5, 0, 0, 0, 0, 1; -3, 2, 0, 0, 0, 0, 0; -2, 1, 0, 0, 0, 0, 0]

@[expose] def smithE7Q' : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![0, 0, 0, 0, 0, 1, -2; 0, 0, 0, 0, 0, 2, -3; 1, 0, 0, 0, 0, 2, -4; 0, 1, 0, 0, 0, 4, -6;
    0, 0, 1, 0, 0, 4, -5; 0, 0, 0, 1, 0, 4, -4; 0, 0, 0, 0, 1, 4, -3]

@[expose] def smithE6D : Fin Tag.E6.rank → ℕ := ![1, 1, 1, 1, 1, 3]

@[expose] def smithE7D : Fin Tag.E7.rank → ℕ := ![1, 1, 1, 1, 1, 1, 2]

theorem smithE6 :
    Tag.E6.cartan = smithE6P * Matrix.diagonal (fun i => (smithE6D i : ℤ)) * smithE6Q := by
  decide

theorem smithE6P'_mul : smithE6P' * smithE6P = 1 := by decide

theorem smithE6P_mul : smithE6P * smithE6P' = 1 := by decide

theorem smithE6Q_mul : smithE6Q * smithE6Q' = 1 := by decide

theorem smithE7 :
    Tag.E7.cartan = smithE7P * Matrix.diagonal (fun i => (smithE7D i : ℤ)) * smithE7Q := by
  decide

theorem smithE7P'_mul : smithE7P' * smithE7P = 1 := by decide

theorem smithE7P_mul : smithE7P * smithE7P' = 1 := by decide

theorem smithE7Q_mul : smithE7Q * smithE7Q' = 1 := by decide

variable {K : Type} [Field K] [Finite K]

theorem card_torusGroup_G2 : Nat.card (torusGroup .G2 K) = (Nat.card K - 1) ^ 2 :=
  card_torusGroup_of_mul_eq_one cartan_mul_cartanInv_G2

theorem card_torusGroup_F4 : Nat.card (torusGroup .F4 K) = (Nat.card K - 1) ^ 4 :=
  card_torusGroup_of_mul_eq_one cartan_mul_cartanInv_F4

theorem card_torusGroup_E8 : Nat.card (torusGroup .E8 K) = (Nat.card K - 1) ^ 8 :=
  card_torusGroup_of_mul_eq_one cartan_mul_cartanInvE8

theorem card_torusGroup_E6 :
    Nat.card (torusGroup .E6 K) * (Nat.card K - 1).gcd 3 = (Nat.card K - 1) ^ 6 := by
  have h := card_torusGroup_mul (τ := .E6) (K := K)
  rw [card_ker_zpowMatrix_eq smithE6 smithE6P'_mul smithE6P_mul smithE6Q_mul,
    card_ker_zpowMatrix_diagonal] at h
  simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units] at h
  rw [show ∏ i : Fin Tag.E6.rank, (Nat.card K - 1).gcd (smithE6D i) =
      (Nat.card K - 1).gcd 3 by
    change ∏ i : Fin 6, (Nat.card K - 1).gcd (smithE6D i) = _
    simp [smithE6D, Fin.prod_univ_succ]] at h
  exact h

theorem card_torusGroup_E7 :
    Nat.card (torusGroup .E7 K) * (Nat.card K - 1).gcd 2 = (Nat.card K - 1) ^ 7 := by
  have h := card_torusGroup_mul (τ := .E7) (K := K)
  rw [card_ker_zpowMatrix_eq smithE7 smithE7P'_mul smithE7P_mul smithE7Q_mul,
    card_ker_zpowMatrix_diagonal] at h
  simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units] at h
  rw [show ∏ i : Fin Tag.E7.rank, (Nat.card K - 1).gcd (smithE7D i) =
      (Nat.card K - 1).gcd 2 by
    change ∏ i : Fin 7, (Nat.card K - 1).gcd (smithE7D i) = _
    simp [smithE7D, Fin.prod_univ_succ]] at h
  exact h

end CFSG.Timmesfeld.ExceptionalOrders
