module

public import CFSG.LocalAnalysis.ZStar.ClassSums
public import Mathlib.NumberTheory.Padics.RingHoms
public import CFSG.LocalAnalysis.ZStar.Helpers

public section

namespace CFSG

namespace ZStar.PadicBlockLift

open ZStar.Helpers
open ZStar.ClassSums

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

abbrev ModularGroupAlgebra (n : ℕ) := MonoidAlgebra (ZMod (2 ^ n)) G

@[expose] noncomputable def reduceLevel (n : ℕ) :
    ModularGroupAlgebra (G := G) (n + 1) →+* ModularGroupAlgebra (G := G) n :=
  MonoidAlgebra.mapRingHom G
    (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)))

@[simp]
theorem reduceLevel_coeff (n : ℕ) (x : ModularGroupAlgebra (G := G) (n + 1))
    (g : G) :
    (reduceLevel n x).coeff g =
      ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))
        (x.coeff g) := by
  exact MonoidAlgebra.coeff_mapRingHom _ _ _

private theorem scalar_mul_eq_zero_of_reduce_eq_zero
    (n : ℕ) (hn : 1 ≤ n) {a b : ZMod (2 ^ (n + 1))}
    (ha : ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)) a = 0)
    (hb : ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)) b = 0) :
    a * b = 0 := by
  have hna : 2 ^ n ∣ a.val := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at ha
    exact (ZMod.natCast_eq_zero_iff a.val (2 ^ n)).mp ha
  have hnb : 2 ^ n ∣ b.val := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hb
    exact (ZMod.natCast_eq_zero_iff b.val (2 ^ n)).mp hb
  obtain ⟨ka, hka⟩ := hna
  obtain ⟨kb, hkb⟩ := hnb
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hka, hkb]
  push_cast
  rw [mul_assoc, mul_left_comm (ka : ZMod (2 ^ (n + 1)))]
  have hp : ((2 ^ n : ℕ) : ZMod (2 ^ (n + 1))) * (2 ^ n : ℕ) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rw [← pow_add]
    exact pow_dvd_pow 2 (by omega)
  have hpRing : (2 : ZMod (2 ^ (n + 1))) ^ n *
      (2 : ZMod (2 ^ (n + 1))) ^ n = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hp
  calc
    (2 ^ n : ZMod (2 ^ (n + 1))) *
        ((2 ^ n : ZMod (2 ^ (n + 1))) * ((ka : ZMod (2 ^ (n + 1))) * kb)) =
        ((2 ^ n : ZMod (2 ^ (n + 1))) * (2 ^ n : ZMod (2 ^ (n + 1)))) *
          ((ka : ZMod (2 ^ (n + 1))) * kb) := by ring
    _ = 0 := by rw [hpRing, zero_mul]

private theorem sq_eq_zero_of_reduceLevel_eq_zero
    (n : ℕ) (hn : 1 ≤ n) (x : ModularGroupAlgebra (G := G) (n + 1))
    (hx : reduceLevel n x = 0) : x * x = 0 := by
  classical
  have hcoeff (g : G) :
      ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))
        (x.coeff g) = 0 := by
    have := congrArg (fun y : ModularGroupAlgebra (G := G) n => y.coeff g) hx
    simpa using this
  ext g
  rw [MonoidAlgebra.coeff_mul_apply_left]
  calc
    x.coeff.sum (fun h r ↦ r * x.coeff (h⁻¹ * g)) =
        x.coeff.sum (fun _ _ ↦ 0) := by
      apply Finsupp.sum_congr
      intro h hh
      exact scalar_mul_eq_zero_of_reduce_eq_zero n hn
        (hcoeff h) (hcoeff (h⁻¹ * g))
    _ = 0 := Finsupp.sum_fun_zero x.coeff

theorem reduceLevel_surjective (n : ℕ) :
    Function.Surjective (reduceLevel (G := G) n) := by
  exact MonoidAlgebra.map_surjective _
    (ZMod.castHom_surjective (pow_dvd_pow 2 (Nat.le_succ n)))

@[expose] noncomputable def liftScalar (n : ℕ) (a : ZMod (2 ^ n)) : ZMod (2 ^ (n + 1)) :=
  Classical.choose
    (ZMod.castHom_surjective (pow_dvd_pow 2 (Nat.le_succ n)) a)

@[simp]
theorem reduce_liftScalar (n : ℕ) (a : ZMod (2 ^ n)) :
    ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))
      (liftScalar n a) = a :=
  Classical.choose_spec
    (ZMod.castHom_surjective (pow_dvd_pow 2 (Nat.le_succ n)) a)

@[simp]
theorem reduceLevel_classSum (n : ℕ) (C : ConjClasses G) :
    reduceLevel n (classSum (ZMod (2 ^ (n + 1))) C) =
      classSum (ZMod (2 ^ n)) C := by
  classical
  ext g
  simp [reduceLevel_coeff, classSum_coeff]

@[expose] noncomputable def centralPreimage (n : ℕ) (e : ModularGroupAlgebra (G := G) n) :
    ModularGroupAlgebra (G := G) (n + 1) := by
  classical
  exact ∑ C : ConjClasses G,
    liftScalar n (e.coeff (classRep C)) • classSum (ZMod (2 ^ (n + 1))) C

private theorem centralPreimage_central (n : ℕ) (e : ModularGroupAlgebra (G := G) n) :
    centralPreimage n e ∈
      Submonoid.center (ModularGroupAlgebra (G := G) (n + 1)) := by
  classical
  rw [Submonoid.mem_center_iff]
  intro z
  unfold centralPreimage
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C hC
  simpa only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm] using
    congrArg (liftScalar n (e.coeff (classRep C)) • ·)
      (classSum_commute (ZMod (2 ^ (n + 1))) C z)

private theorem reduceLevel_centralPreimage
    (n : ℕ) (e : ModularGroupAlgebra (G := G) n)
    (he : e ∈ Submonoid.center (ModularGroupAlgebra (G := G) n)) :
    reduceLevel n (centralPreimage n e) = e := by
  classical
  rw [centralPreimage, map_sum]
  have heq := central_eq_sum_classSums (ZMod (2 ^ n)) he
  conv_rhs => rw [heq]
  apply Finset.sum_congr rfl
  intro C hC
  ext g
  simp only [reduceLevel_coeff, MonoidAlgebra.coeff_smul_apply, classSum_coeff]
  by_cases h : ConjClasses.mk g = C
  · simp only [h, ite_eq_left]
    simpa only [smul_eq_mul, mul_one, ZMod.castHom_apply] using
      reduce_liftScalar n (e.coeff (classRep C))
  · simp [h]

@[expose] noncomputable def liftCentralIdempotent
    (n : ℕ) (e : ModularGroupAlgebra (G := G) n) :
    ModularGroupAlgebra (G := G) (n + 1) :=
  let a := centralPreimage n e
  1 - (1 - a ^ 2) ^ 2

private theorem liftCentralIdempotent_idempotent
    (n : ℕ) (hn : 1 ≤ n) (e : ModularGroupAlgebra (G := G) n)
    (hecentral : e ∈ Submonoid.center (ModularGroupAlgebra (G := G) n))
    (heidem : e * e = e) :
    liftCentralIdempotent n e * liftCentralIdempotent n e =
      liftCentralIdempotent n e := by
  let a := centralPreimage n e
  have ha : reduceLevel n a = e := reduceLevel_centralPreimage n e hecentral
  have herr : reduceLevel n (a - a ^ 2) = 0 := by
    rw [map_sub, map_pow, ha, pow_two, heidem, sub_self]
  have herr2 : (a - a ^ 2) * (a - a ^ 2) = 0 :=
    sq_eq_zero_of_reduceLevel_eq_zero n hn (a - a ^ 2) herr
  have hidem : IsIdempotentElem (1 - (1 - a ^ 2) ^ 2) :=
    isIdempotentElem_one_sub_one_sub_pow_pow a 2 (by simpa [pow_two] using herr2)
  exact hidem.eq

private theorem reduceLevel_liftCentralIdempotent
    (n : ℕ) (e : ModularGroupAlgebra (G := G) n)
    (hecentral : e ∈ Submonoid.center (ModularGroupAlgebra (G := G) n))
    (heidem : e * e = e) :
    reduceLevel n (liftCentralIdempotent n e) = e := by
  simp only [liftCentralIdempotent, map_sub, map_one, map_mul,
    reduceLevel_centralPreimage n e hecentral, pow_two]
  rw [heidem]
  rw [one_sub_idempotent heidem]
  abel

private theorem liftCentralIdempotent_central
    (n : ℕ) (e : ModularGroupAlgebra (G := G) n) :
    liftCentralIdempotent n e ∈
      Submonoid.center (ModularGroupAlgebra (G := G) (n + 1)) := by
  let a := centralPreimage n e
  have haM : a ∈ Submonoid.center (ModularGroupAlgebra (G := G) (n + 1)) :=
    centralPreimage_central n e
  have haR : a ∈ Subring.center (ModularGroupAlgebra (G := G) (n + 1)) := by
    rw [Subring.mem_center_iff]
    exact Submonoid.mem_center_iff.mp haM
  have hliftR : (1 - (1 - a ^ 2) ^ 2) ∈
      Subring.center (ModularGroupAlgebra (G := G) (n + 1)) := by
    exact (Subring.center _).sub_mem (Subring.center _).one_mem
      ((Subring.center _).pow_mem
        ((Subring.center _).sub_mem (Subring.center _).one_mem
          ((Subring.center _).pow_mem haR 2)) 2)
  rw [Submonoid.mem_center_iff]
  exact Subring.mem_center_iff.mp hliftR

@[expose] noncomputable def principalBlockLevel (G : Type u) [Group G] [Fintype G] :
    (n : ℕ) → ModularGroupAlgebra (G := G) (n + 1)
  | 0 => principalBlockCandidate G
  | n + 1 => liftCentralIdempotent (n + 1) (principalBlockLevel G n)

private theorem principalBlockLevel_central (n : ℕ) :
    principalBlockLevel G n ∈
      Submonoid.center (ModularGroupAlgebra (G := G) (n + 1)) := by
  induction n with
  | zero =>
      rw [Submonoid.mem_center_iff]
      intro z
      exact (principalBlockCandidate_central G).commute G z |>.eq.symm
  | succ n ih =>
      exact liftCentralIdempotent_central (n + 1) (principalBlockLevel G n)

private theorem principalBlockLevel_idempotent (n : ℕ) :
    principalBlockLevel G n * principalBlockLevel G n =
      principalBlockLevel G n := by
  induction n with
  | zero => exact principalBlockCandidate_idempotent G
  | succ n ih =>
      exact liftCentralIdempotent_idempotent (n + 1) (by omega)
        (principalBlockLevel G n) (principalBlockLevel_central n) ih

@[simp]
theorem reduceLevel_principalBlockLevel (n : ℕ) :
    reduceLevel (n + 1) (principalBlockLevel G (n + 1)) =
      principalBlockLevel G n := by
  exact reduceLevel_liftCentralIdempotent (n + 1) (principalBlockLevel G n)
    (principalBlockLevel_central n) (principalBlockLevel_idempotent n)

@[expose] noncomputable def principalBlockMod (G : Type u) [Group G] [Fintype G] :
    (n : ℕ) → ModularGroupAlgebra (G := G) n
  | 0 => 0
  | n + 1 => principalBlockLevel G n

@[simp]
theorem reduceLevel_principalBlockMod (n : ℕ) :
    reduceLevel n (principalBlockMod G (n + 1)) = principalBlockMod G n := by
  cases n with
  | zero =>
      ext g
      change _ = (0 : ZMod 1)
      exact Subsingleton.elim _ _
  | succ n =>
      exact reduceLevel_principalBlockLevel n

@[expose] noncomputable def reduceTo (m n : ℕ) (h : m ≤ n) :
    ModularGroupAlgebra (G := G) n →+* ModularGroupAlgebra (G := G) m :=
  MonoidAlgebra.mapRingHom G
    (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m)))

@[simp]
theorem reduceTo_coeff (m n : ℕ) (h : m ≤ n)
    (x : ModularGroupAlgebra (G := G) n) (g : G) :
    (reduceTo m n h x).coeff g =
      ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m)) (x.coeff g) := by
  exact MonoidAlgebra.coeff_mapRingHom _ _ _

private theorem reduceTo_self (n : ℕ) (x : ModularGroupAlgebra (G := G) n) :
    reduceTo n n le_rfl x = x := by
  classical
  ext g
  simp [reduceTo_coeff]

private theorem reduceTo_comp_reduceLevel (m n : ℕ) (h : m ≤ n) :
    (reduceTo (G := G) m n h).comp (reduceLevel (G := G) n) =
      reduceTo (G := G) m (n + 1) (h.trans (Nat.le_succ n)) := by
  rw [reduceTo, reduceLevel, reduceTo]
  rw [← MonoidAlgebra.mapRingHom_comp]
  rw [ZMod.castHom_comp]

private theorem reduceTo_principalBlockMod {m n : ℕ} (h : m ≤ n) :
    reduceTo m n h (principalBlockMod G n) = principalBlockMod G m := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst m
      exact reduceTo_self 0 (principalBlockMod G 0)
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact reduceTo_self (n + 1) (principalBlockMod G (n + 1))
      · have hmn : m ≤ n := by omega
        calc
          reduceTo m (n + 1) h (principalBlockMod G (n + 1)) =
              reduceTo m n hmn
                (reduceLevel n (principalBlockMod G (n + 1))) := by
            have hc := congrArg
              (fun q : ModularGroupAlgebra (G := G) (n + 1) →+*
                  ModularGroupAlgebra (G := G) m =>
                q (principalBlockMod G (n + 1)))
              (reduceTo_comp_reduceLevel m n hmn)
            exact hc.symm
          _ = reduceTo m n hmn (principalBlockMod G n) := by
            rw [reduceLevel_principalBlockMod]
          _ = principalBlockMod G m := ih hmn

theorem principalBlockMod_idempotent (n : ℕ) :
    principalBlockMod G n * principalBlockMod G n = principalBlockMod G n := by
  cases n with
  | zero => simp [principalBlockMod]
  | succ n => exact principalBlockLevel_idempotent n

theorem principalBlockMod_central (n : ℕ) :
    principalBlockMod G n ∈
      Submonoid.center (ModularGroupAlgebra (G := G) n) := by
  cases n with
  | zero =>
      rw [Submonoid.mem_center_iff]
      intro z
      simp [principalBlockMod]
  | succ n => exact principalBlockLevel_central n

private theorem principalBlockCoeff_compatible (g : G)
    (m n : ℕ) (h : m ≤ n) :
    ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m))
        ((principalBlockMod G n).coeff g) =
      (principalBlockMod G m).coeff g := by
  have hc := congrArg
    (fun x : ModularGroupAlgebra (G := G) m => x.coeff g)
    (reduceTo_principalBlockMod (G := G) h)
  simpa only [reduceTo_coeff] using hc

@[expose] noncomputable def blockCoeffEval (g : G) (n : ℕ) :
    Polynomial ℤ →+* ZMod (2 ^ n) :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod (2 ^ n)))
    ((principalBlockMod G n).coeff g)

theorem blockCoeffEval_compatible (g : G) (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m))).comp
        (blockCoeffEval (G := G) g n) = blockCoeffEval (G := G) g m := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [blockCoeffEval]
  · simpa [blockCoeffEval] using principalBlockCoeff_compatible g m n h

@[expose] noncomputable def principalBlockPadicCoeff (g : G) : ℤ_[2] :=
  PadicInt.lift (blockCoeffEval_compatible (G := G) g) Polynomial.X

@[simp]
theorem toZModPow_principalBlockPadicCoeff (n : ℕ) (g : G) :
    PadicInt.toZModPow n (principalBlockPadicCoeff (G := G) g) =
      (principalBlockMod G n).coeff g := by
  have hs := congrArg (fun f : Polynomial ℤ →+* ZMod (2 ^ n) => f Polynomial.X)
    (PadicInt.lift_spec (blockCoeffEval_compatible (G := G) g) n)
  simpa [principalBlockPadicCoeff, blockCoeffEval] using hs

@[expose] noncomputable def principalBlockPadic : MonoidAlgebra ℤ_[2] G :=
  ∑ g : G, MonoidAlgebra.single g (principalBlockPadicCoeff (G := G) g)

@[simp]
theorem principalBlockPadic_coeff (g : G) :
    (principalBlockPadic (G := G)).coeff g = principalBlockPadicCoeff (G := G) g := by
  classical
  simp [principalBlockPadic, Finsupp.finsetSum_apply, Finsupp.single_apply]

@[expose] noncomputable def reducePadic (n : ℕ) :
    MonoidAlgebra ℤ_[2] G →+* ModularGroupAlgebra (G := G) n :=
  MonoidAlgebra.mapRingHom G (PadicInt.toZModPow n)

@[simp]
theorem reducePadic_coeff (n : ℕ) (x : MonoidAlgebra ℤ_[2] G) (g : G) :
    (reducePadic n x).coeff g = PadicInt.toZModPow n (x.coeff g) := by
  exact MonoidAlgebra.coeff_mapRingHom _ _ _

@[simp]
theorem reducePadic_principalBlockPadic (n : ℕ) :
    reducePadic n (principalBlockPadic (G := G)) = principalBlockMod G n := by
  ext g
  simp

end

end ZStar.PadicBlockLift

end CFSG
