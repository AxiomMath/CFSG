module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinCent
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

section Pair

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}

@[expose] noncomputable def pairGL (hpq : p ≠ q) : GL (Fin 2) (ZMod 2) →* GL κ (ZMod 2) :=
  Units.map (CFSG.LieType.Steinberg.Sp.blockMatHom (ZMod 2) hpq)

theorem coe_pairGL (hpq : p ≠ q) (M : GL (Fin 2) (ZMod 2)) :
    (pairGL hpq M : Matrix κ κ (ZMod 2)) =
      CFSG.LieType.Steinberg.Sp.blockMat p q (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  rfl

theorem pairGL_injective (hpq : p ≠ q) : Function.Injective (pairGL (κ := κ) hpq) :=
  fun _ _ h => Units.ext (CFSG.LieType.Steinberg.Sp.blockMat_injective hpq (congrArg Units.val h))

end Pair

@[expose] def betaTwo : GL (Fin 2) (ZMod 2) :=
  ⟨!![1, 1; 1, 0], !![0, 1; 1, 1], by decide, by decide⟩

@[expose] def rhoTwo : GL (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 1], !![1, 1; 1, 0], by decide, by decide⟩

@[expose] def tauTwo : GL (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide, by decide⟩

theorem inl_ne_inr_inr (m : ℕ) : (Sum.inl 0 : BlkIdx 1 m) ≠ Sum.inr (Sum.inr 0) :=
  Sum.inl_ne_inr

@[expose] noncomputable def betaStd (m : ℕ) : GL (BlkIdx 1 m) (ZMod 2) :=
  pairGL (inl_ne_inr_inr m) betaTwo

@[expose] def leviOne (m : ℕ) : GL (Fin m) (ZMod 2) →* GL (BlkIdx 1 m) (ZMod 2) where
  toFun R := levi 1 R
  map_one' := Units.ext (by
    rw [coe_levi, Units.val_one, Units.val_one, Units.val_one]
    exact blk_one)
  map_mul' R R' := Units.ext (by simp [coe_levi, blk_mul])

@[expose] def leviB (m : ℕ) : Subgroup (GL (BlkIdx 1 m) (ZMod 2)) :=
  (leviOne m).range

theorem leviB_le_cent (m : ℕ) : leviB m ≤ Cent 1 m := by
  rintro _ ⟨R, rfl⟩
  exact levi_mem_cent 1 m 1 R

@[expose] noncomputable def lastTwo : (m : ℕ) → GL (Fin 2) (ZMod 2) →* GL (Fin m) (ZMod 2)
  | 0 => 1
  | 1 => 1
  | k + 2 => pairGL (Fin.castSucc_lt_last (Fin.last k)).ne

@[expose] noncomputable def endsTwo : (m : ℕ) → GL (Fin 2) (ZMod 2) →* GL (Fin m) (ZMod 2)
  | 0 => 1
  | 1 => 1
  | k + 2 => pairGL (p := (0 : Fin (k + 2))) (q := Fin.last (k + 1)) (by simp [Fin.ext_iff])

@[expose] noncomputable def bStar (m : ℕ) : GL (BlkIdx 1 m) (ZMod 2) :=
  leviOne m (lastTwo m rhoTwo)

@[expose] noncomputable def wStar (m : ℕ) : GL (BlkIdx 1 m) (ZMod 2) :=
  leviOne m (lastTwo m tauTwo)

@[expose] noncomputable def qStd (m : ℕ) : GL (BlkIdx 1 m) (ZMod 2) :=
  leviOne m (endsTwo m rhoTwo)

theorem bStar_mem_leviB (m : ℕ) : bStar m ∈ leviB m := ⟨_, rfl⟩

theorem wStar_mem_leviB (m : ℕ) : wStar m ∈ leviB m := ⟨_, rfl⟩

theorem qStd_mem_leviB (m : ℕ) : qStd m ∈ leviB m := ⟨_, rfl⟩

theorem qStd_mem_cent (m : ℕ) : qStd m ∈ Cent 1 m := leviB_le_cent m (qStd_mem_leviB m)

@[expose] def uOne (m : ℕ) : Subgroup (GL (BlkIdx 1 m) (ZMod 2)) where
  carrier := {g | ∃ (a : Matrix (Fin 1) (Fin m) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)),
    g = uGL a 0 c}
  one_mem' := ⟨0, 0, uGL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    exact ⟨a + a', c + c', by rw [uGL_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨a, c, rfl⟩
    exact ⟨-a, -c, by
      rw [uGL_inv]; congr 1 <;> ext i j <;> simp <;> exact (ZMod.neg_eq_self_mod_two _).symm⟩

@[expose] def uTwo (m : ℕ) : Subgroup (GL (BlkIdx 1 m) (ZMod 2)) where
  carrier := {g | ∃ (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)),
    g = uGL 0 b c}
  one_mem' := ⟨0, 0, uGL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
    exact ⟨b + b', c + c', by rw [uGL_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    exact ⟨-b, -c, by
      rw [uGL_inv]; congr 1 <;> ext i j <;> simp <;> exact (ZMod.neg_eq_self_mod_two _).symm⟩

theorem uOne_le_uSub (m : ℕ) : uOne m ≤ uSub 1 m := by
  rintro _ ⟨a, c, rfl⟩
  exact ⟨a, 0, c, rfl⟩

theorem uTwo_le_uSub (m : ℕ) : uTwo m ≤ uSub 1 m := by
  rintro _ ⟨b, c, rfl⟩
  exact ⟨0, b, c, rfl⟩

theorem jGL_mem_uOne (m : ℕ) : jGL 1 m ∈ uOne m := ⟨0, 1, rfl⟩

theorem jGL_mem_uTwo (m : ℕ) : jGL 1 m ∈ uTwo m := ⟨0, 1, rfl⟩

@[expose] def antiDiagPerm (m : ℕ) : Equiv.Perm (BlkIdx 1 m) where
  toFun
    | .inl i => .inr (.inr i)
    | .inr (.inl j) => .inr (.inl j.rev)
    | .inr (.inr i) => .inl i
  invFun
    | .inl i => .inr (.inr i)
    | .inr (.inl j) => .inr (.inl j.rev)
    | .inr (.inr i) => .inl i
  left_inv := by rintro (i | j | i) <;> simp
  right_inv := by rintro (i | j | i) <;> simp

@[expose] noncomputable def antiDiag (m : ℕ) : GL (BlkIdx 1 m) (ZMod 2) :=
  TauCeti.permutationGL (antiDiagPerm m)

@[expose] noncomputable def sigmaStd (m : ℕ) : MulAut (GL (BlkIdx 1 m) (ZMod 2)) :=
  MulAut.conj (antiDiag m) * Matrix.GeneralLinearGroup.inverseTranspose

theorem leviOne_injective (m : ℕ) : Function.Injective (leviOne m) := by
  intro R R' h
  refine Units.ext ?_
  have h' := congrArg Units.val h
  ext i j
  have := congrFun₂ h' (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j))
  simpa [leviOne, coe_levi, blk] using this

theorem glOne_eq_one (P : GL (Fin 1) (ZMod 2)) : P = 1 := by
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi
  subst hj
  have hu : IsUnit ((P : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0) := by
    have h := P.isUnit
    rwa [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one] at h
  have hne : (P : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0 ≠ 0 := isUnit_iff_ne_zero.mp hu
  have h2 : ∀ d : ZMod 2, d ≠ 0 → d = 1 := by decide
  rw [h2 _ hne]
  rfl

theorem orderOf_bStar {m : ℕ} (hm : 2 ≤ m) : orderOf (bStar m) = 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [bStar, orderOf_injective _ (leviOne_injective _)]
  simp only [lastTwo]
  rw [orderOf_injective _ (pairGL_injective _)]
  exact orderOf_eq_prime (by decide) (by decide)

private theorem caDefs_tau_conj : tauTwo * rhoTwo * tauTwo⁻¹ = rhoTwo⁻¹ := by decide

theorem wStar_conj_bStar (m : ℕ) : wStar m * bStar m * (wStar m)⁻¹ = (bStar m)⁻¹ := by
  rcases lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp [wStar, bStar, lastTwo]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [wStar, bStar]
    simp only [← map_inv, ← map_mul]
    rw [caDefs_tau_conj]

theorem orderOf_qStd {m : ℕ} (hm : 2 ≤ m) : orderOf (qStd m) = 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [qStd, orderOf_injective _ (leviOne_injective _)]
  simp only [endsTwo]
  rw [orderOf_injective _ (pairGL_injective _)]
  exact orderOf_eq_prime (by decide) (by decide)

theorem antiDiagPerm_inv (m : ℕ) : (antiDiagPerm m)⁻¹ = antiDiagPerm m := by
  ext x
  rcases x with i | j | i <;> simp [antiDiagPerm, Fin.rev_rev]

theorem antiDiag_inv (m : ℕ) : (antiDiag m)⁻¹ = antiDiag m := by
  rw [antiDiag, ← map_inv, antiDiagPerm_inv]

private theorem caDefs_conj_permGL_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (hσ : σ⁻¹ = σ) (g : GL ι (ZMod 2)) (i j : ι) :
    (((TauCeti.permutationGL σ * g * (TauCeti.permutationGL σ)⁻¹ : GL ι (ZMod 2)) :
      Matrix ι ι (ZMod 2)) i j) =
      (g : Matrix ι ι (ZMod 2)) (σ i) (σ j) := by
  have h := TauCeti.coe_permutationGL_inv_mul_mul_permutationGL_apply σ⁻¹ g i j
  have hQ : TauCeti.permutationGL (k := ZMod 2) σ⁻¹ =
      (TauCeti.permutationGL (k := ZMod 2) σ)⁻¹ := map_inv _ _
  have hQ' : (TauCeti.permutationGL (k := ZMod 2) σ⁻¹)⁻¹ =
      TauCeti.permutationGL (k := ZMod 2) σ := by rw [hQ, inv_inv]
  rw [hQ', hQ, hσ] at h
  exact h

private theorem caDefs_sigmaStd_apply (m : ℕ) (g : GL (BlkIdx 1 m) (ZMod 2))
    (i j : BlkIdx 1 m) :
    ((sigmaStd m g : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) i j =
      ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) (antiDiagPerm m j) (antiDiagPerm m i) := by
  rw [sigmaStd, MulAut.mul_apply, MulAut.conj_apply]
  change (((TauCeti.permutationGL (antiDiagPerm m) *
      Matrix.GeneralLinearGroup.inverseTranspose g *
      (TauCeti.permutationGL (antiDiagPerm m))⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) i j) = _
  rw [caDefs_conj_permGL_apply (antiDiagPerm m) (antiDiagPerm_inv m)
    (Matrix.GeneralLinearGroup.inverseTranspose g) i j]
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
  rfl

private theorem caDefs_jGL_antiDiag (m : ℕ) (i j : BlkIdx 1 m) :
    ((jGL 1 m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) (antiDiagPerm m j) (antiDiagPerm m i) =
      ((jGL 1 m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) i j := by
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [jGL, coe_uGL, uMat, blk, antiDiagPerm, Matrix.of_apply, Matrix.one_apply,
    Fin.rev_inj, eq_comm]

theorem sigmaStd_jGL (m : ℕ) : sigmaStd m (jGL 1 m) = jGL 1 m := by
  refine Units.ext ?_
  ext i j
  rw [caDefs_sigmaStd_apply]
  have hinv : (jGL 1 m : GL (BlkIdx 1 m) (ZMod 2))⁻¹ = jGL 1 m :=
    inv_eq_of_mul_eq_one_right (jGL_mul_self (r := 1) (m := m))
  rw [hinv]
  exact caDefs_jGL_antiDiag m i j

private theorem caDefs_antiDiagPerm_apply_apply (m : ℕ) (x : BlkIdx 1 m) :
    antiDiagPerm m (antiDiagPerm m x) = x := by
  rcases x with i | j | i <;> simp [antiDiagPerm, Fin.rev_rev]

theorem sigmaStd_sigmaStd (m : ℕ) (g : GL (BlkIdx 1 m) (ZMod 2)) :
    sigmaStd m (sigmaStd m g) = g := by
  refine Units.ext ?_
  ext i j
  rw [caDefs_sigmaStd_apply]
  rw [← map_inv]
  rw [caDefs_sigmaStd_apply]
  rw [inv_inv]
  simp only [caDefs_antiDiagPerm_apply_apply]

private theorem caDefs_sigmaStd_uGL_uOne (m : ℕ) (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    sigmaStd m (uGL a 0 c) =
      uGL 0 (Matrix.of fun j _ => a 0 j.rev) c := by
  refine Units.ext ?_
  ext i j
  rw [caDefs_sigmaStd_apply]
  have hinv : (uGL a 0 c : GL (BlkIdx 1 m) (ZMod 2))⁻¹ = uGL a 0 c := by
    rw [uGL_inv]
    congr 1
    · ext x y; simp [ZMod.neg_eq_self_mod_two]
    · ext x y; simp [ZMod.neg_eq_self_mod_two]
    · ext x y; simp [Matrix.mul_zero, ZMod.neg_eq_self_mod_two]
  rw [hinv]
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [uGL, coe_uGL, uMat, blk, antiDiagPerm, Matrix.of_apply, Matrix.one_apply,
    Fin.rev_inj, eq_comm]

theorem sigmaStd_map_uOne (m : ℕ) : (uOne m).map (sigmaStd m).toMonoidHom = uTwo m := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, c, rfl⟩ := hg
    exact ⟨Matrix.of fun j _ => a 0 j.rev, c, caDefs_sigmaStd_uGL_uOne m a c⟩
  · rintro _ ⟨b, c, rfl⟩
    let a' : Matrix (Fin 1) (Fin m) (ZMod 2) := Matrix.of fun _ j => b j.rev 0
    refine Subgroup.mem_map.mpr ⟨uGL a' 0 c, ⟨a', c, rfl⟩, ?_⟩
    change sigmaStd m (uGL a' 0 c) = uGL 0 b c
    rw [caDefs_sigmaStd_uGL_uOne]
    congr 1
    ext j i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    simp [a', Matrix.of_apply, Fin.rev_rev]

private theorem caDefs_sigmaStd_uGL_uTwo (m : ℕ) (b : Matrix (Fin m) (Fin 1) (ZMod 2))
    (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    sigmaStd m (uGL 0 b c) =
      uGL (Matrix.of fun _ j => b j.rev 0) 0 c := by
  refine Units.ext ?_
  ext i j
  rw [caDefs_sigmaStd_apply]
  have hinv : (uGL 0 b c : GL (BlkIdx 1 m) (ZMod 2))⁻¹ = uGL 0 b c := by
    rw [uGL_inv]
    congr 1
    · ext x y; simp [ZMod.neg_eq_self_mod_two]
    · ext x y; simp [ZMod.neg_eq_self_mod_two]
    · ext x y; simp [Matrix.mul_zero, ZMod.neg_eq_self_mod_two]
  rw [hinv]
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [uGL, coe_uGL, uMat, blk, antiDiagPerm, Matrix.of_apply, Matrix.one_apply,
    Fin.rev_inj, eq_comm]

theorem sigmaStd_map_uTwo (m : ℕ) : (uTwo m).map (sigmaStd m).toMonoidHom = uOne m := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨b, c, rfl⟩ := hg
    exact ⟨Matrix.of fun _ j => b j.rev 0, c, caDefs_sigmaStd_uGL_uTwo m b c⟩
  · rintro _ ⟨a, c, rfl⟩
    let b' : Matrix (Fin m) (Fin 1) (ZMod 2) := Matrix.of fun j _ => a 0 j.rev
    refine Subgroup.mem_map.mpr ⟨uGL 0 b' c, ⟨b', c, rfl⟩, ?_⟩
    change sigmaStd m (uGL 0 b' c) = uGL a 0 c
    rw [caDefs_sigmaStd_uGL_uTwo]
    congr 1
    ext j i
    have hj : j = 0 := Subsingleton.elim j 0
    rw [hj]
    simp [b', Matrix.of_apply, Fin.rev_rev]

private theorem caDefs_endsTwo_sigma (k : ℕ) (i j : Fin (k + 2)) :
    ((endsTwo (k + 2) rhoTwo⁻¹ : GL (Fin (k + 2)) (ZMod 2)) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) (Fin.rev j) (Fin.rev i) =
      ((endsTwo (k + 2) rhoTwo : GL (Fin (k + 2)) (ZMod 2)) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) i j := by
  simp only [endsTwo]
  rw [coe_pairGL, coe_pairGL]
  have hlast0 : Fin.last (k + 1) ≠ (0 : Fin (k + 2)) :=
    Fin.last_ne_zero (Nat.succ_ne_zero k)
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_zero, Fin.rev_last, hlast0, rhoTwo]
    · by_cases hjl : j = Fin.last (k + 1)
      · subst hjl
        simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_zero, Fin.rev_last, hlast0, rhoTwo]
      · have hrj0 : Fin.rev j ≠ (0 : Fin (k + 2)) := by
          simpa [Fin.rev_eq_iff, Fin.rev_zero] using hjl
        have hrjl : Fin.rev j ≠ Fin.last (k + 1) := by
          simpa [Fin.rev_eq_iff, Fin.rev_last] using hj0
        simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_zero, hlast0, hrj0, hrjl, hj0, hjl,
          Matrix.one_apply]
  · by_cases hil : i = Fin.last (k + 1)
    · subst hil
      by_cases hj0 : j = 0
      · subst hj0
        simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_zero, Fin.rev_last, hlast0, rhoTwo]
      · by_cases hjl : j = Fin.last (k + 1)
        · subst hjl
          simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_zero, Fin.rev_last, hlast0, rhoTwo]
        · have hrj0 : Fin.rev j ≠ (0 : Fin (k + 2)) := by
            simpa [Fin.rev_eq_iff, Fin.rev_zero] using hjl
          have hrjl : Fin.rev j ≠ Fin.last (k + 1) := by
            simpa [Fin.rev_eq_iff, Fin.rev_last] using hj0
          simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_last, hlast0, hrj0, hrjl, hj0, hjl,
            Matrix.one_apply]
    · have hri0 : Fin.rev i ≠ (0 : Fin (k + 2)) := by
        simpa [Fin.rev_eq_iff, Fin.rev_zero] using hil
      have hril : Fin.rev i ≠ Fin.last (k + 1) := by
        simpa [Fin.rev_eq_iff, Fin.rev_last] using hi0
      by_cases hj0 : j = 0
      · subst hj0
        simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_zero, hlast0, hri0, hril, hi0, hil,
          Matrix.one_apply]
      · by_cases hjl : j = Fin.last (k + 1)
        · subst hjl
          simp [CFSG.LieType.Steinberg.Sp.blockMat, Fin.rev_last, hlast0, hri0, hril, hi0, hil,
            Matrix.one_apply]
        · have hrj0 : Fin.rev j ≠ (0 : Fin (k + 2)) := by
            simpa [Fin.rev_eq_iff, Fin.rev_zero] using hjl
          have hrjl : Fin.rev j ≠ Fin.last (k + 1) := by
            simpa [Fin.rev_eq_iff, Fin.rev_last] using hj0
          simp [CFSG.LieType.Steinberg.Sp.blockMat, hlast0, hri0, hril, hrj0, hrjl, hi0, hil,
            hj0, hjl, Matrix.one_apply]
          simp [eq_comm]

theorem sigmaStd_qStd (m : ℕ) : sigmaStd m (qStd m) = qStd m := by
  rcases lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp [qStd, endsTwo]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    refine Units.ext ?_
    ext i j
    rw [caDefs_sigmaStd_apply]
    have hqinv : (qStd (k + 2))⁻¹ =
        leviOne (k + 2) (endsTwo (k + 2) rhoTwo⁻¹) := by
      rw [qStd]
      simp only [endsTwo, ← map_inv]
    rw [hqinv, qStd]
    rcases i with i | i | i <;> rcases j with j | j | j
    · fin_cases i; fin_cases j
      simp [leviOne, coe_levi, blk, antiDiagPerm]
    · simp [leviOne, coe_levi, blk, antiDiagPerm]
    · simp [leviOne, coe_levi, blk, antiDiagPerm]
    · simp [leviOne, coe_levi, blk, antiDiagPerm]
    · simpa [leviOne, coe_levi, blk, antiDiagPerm] using caDefs_endsTwo_sigma k i j
    · simp [leviOne, coe_levi, blk, antiDiagPerm]
    · simp [leviOne, coe_levi, blk, antiDiagPerm]
    · simp [leviOne, coe_levi, blk, antiDiagPerm]
    · fin_cases i; fin_cases j
      simp [leviOne, coe_levi, blk, antiDiagPerm]

end CFSG.StandardType.FF81.CentA

end
