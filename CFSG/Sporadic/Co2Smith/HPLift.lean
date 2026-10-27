module

public import CFSG.Sporadic.Co2Smith.S0Enum
public import CFSG.Sporadic.Co2Smith.Spin8Cover

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def aHat : PGcov := PresentedGroup.mk _ (FreeGroup.mk Native.sp6Wa)

@[expose] noncomputable def bHat : PGcov := PresentedGroup.mk _ (FreeGroup.mk Native.sp6Wb)

theorem covMap_aHat :
    (covMap aHat : K) = aE := by
  rw [aHat, covMap_mk]
  exact (lift_sp6Gen_mix (Or.inl rfl) sp6Check_parts.2.2.2.1).trans mWord_two

theorem covMap_bHat :
    (covMap bHat : K) = bE := by
  rw [bHat, covMap_mk]
  exact (lift_sp6Gen_mix (Or.inr rfl) sp6Check_parts.2.2.2.2).trans mWord_three

theorem spinHom_aHat :
    (spinHom aHat : Matrix (Fin 8) (Fin 8) ℤ) = toMatZ Native.aSpinN :=
  lift_spinUnit_mk Native.sp6Wa

theorem spinHom_bHat :
    (spinHom bHat : Matrix (Fin 8) (Fin 8) ℤ) = toMatZ Native.bSpinN :=
  lift_spinUnit_mk Native.sp6Wb

@[expose] noncomputable def genLift (w : List ℕ) : PGcov :=
  w.foldr (fun x acc => (if x = 2 then aHat else bHat) * acc) 1

theorem covMap_genLift :
    ∀ w : List ℕ, (∀ x ∈ w, x = 2 ∨ x = 3) →
    (covMap (genLift w) : K) = mWord w
  | [], _ => by rw [genLift, List.foldr_nil, map_one, mWord_nil]; rfl
  | x :: w, hw => by
    rw [genLift, List.foldr_cons, map_mul, Subgroup.coe_mul, ← genLift,
      covMap_genLift w fun y hy => hw y (List.mem_cons_of_mem _ hy), mWord_cons]
    congr 1
    rcases hw x List.mem_cons_self with rfl | rfl
    · rw [ite_eq_left rfl, covMap_aHat]; rfl
    · rw [ite_eq_right (by norm_num), covMap_bHat]; rfl

theorem mixSpinN_cons (x : ℕ) (w : List ℕ) : Native.mixSpinN (x :: w) =
    Native.mulZ (if x == 2 then Native.aSpinN else Native.bSpinN) (Native.mixSpinN w) := rfl

theorem spinHom_genLift : ∀ w : List ℕ,
    (spinHom (genLift w) : Matrix (Fin 8) (Fin 8) ℤ) = toMatZ (Native.mixSpinN w)
  | [] => by rw [genLift, List.foldr_nil, map_one, Units.val_one, Native.mixSpinN,
      List.foldr_nil, toMatZ_idZ]
  | x :: w => by
    rw [genLift, List.foldr_cons, map_mul, Units.val_mul, ← genLift, spinHom_genLift w,
      mixSpinN_cons, toMatZ_mulZ]
    congr 1
    by_cases hx : x = 2
    · subst hx
      rw [ite_eq_left rfl, spinHom_aHat]
      rfl
    · rw [ite_eq_right hx, spinHom_bHat, show (x == 2) = false from by simpa using hx]
      rfl

@[expose] noncomputable def tLift (k i : ℕ) : PGcov :=
  if i = 0 then 1
  else if _hp : (chainRec k).2.1[i]! < i then
    genLift (Native.chainGens[k]!)[(chainRec k).2.2[i]!]! * tLift k (chainRec k).2.1[i]!
  else 1
termination_by i

theorem tLift_zero (k : ℕ) : tLift k 0 = 1 := by
  rw [tLift, ite_eq_left rfl]

theorem tLift_of_lt {k i : ℕ} (hi : i ≠ 0) (hp : (chainRec k).2.1[i]! < i) :
    tLift k i = genLift (Native.chainGens[k]!)[(chainRec k).2.2[i]!]! *
      tLift k (chainRec k).2.1[i]! := by
  rw [tLift, ite_eq_right hi, dite_eq_left hp]

theorem tSpinN_zero (r : Array ℕ × Array ℕ × Array ℕ) (G : Array (Array ℤ)) :
    Native.tSpinN r G 0 = Native.idZ := by
  rw [Native.tSpinN, ite_eq_left rfl]

theorem tSpinN_of_lt {r : Array ℕ × Array ℕ × Array ℕ} {G : Array (Array ℤ)} {i : ℕ}
    (hi : i ≠ 0) (hp : r.2.1[i]! < i) :
    Native.tSpinN r G i = Native.mulZ G[r.2.2[i]!]! (Native.tSpinN r G r.2.1[i]!) := by
  rw [Native.tSpinN, ite_eq_right hi, dite_eq_left hp]

theorem tLift_spec
    {k : ℕ} (hk : k < 6) : ∀ i < Native.chainOrb[k]!,
    (covMap (tLift k i) : K) = tElt k i ∧
      (spinHom (tLift k i) : Matrix (Fin 8) (Fin 8) ℤ) =
        toMatZ (Native.tSpinN (chainRec k) (Array.map Native.mixSpinN Native.chainGens[k]!) i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, h⟩ := chain_spec hk
    rcases (h i hi).2 with rfl | ⟨hp, hl, -⟩
    · rw [tLift_zero, tElt_zero, tSpinN_zero, map_one, map_one, Units.val_one, toMatZ_idZ]
      exact ⟨rfl, rfl⟩
    · have hi0 : i ≠ 0 := by omega
      have hl' : (chainRec k).2.2[i]! < (Native.chainGens[k]!).size := by
        rwa [← chainRows_size]
      obtain ⟨ihc, ihs⟩ := ih _ hp (hp.trans hi)
      refine ⟨?_, ?_⟩
      · rw [tLift_of_lt hi0 hp, tElt_of_lt hi0 hp, map_mul, Subgroup.coe_mul, ihc,
          covMap_genLift _ (chainGens_letters k hk _ hl')]
        rfl
      · rw [tLift_of_lt hi0 hp, map_mul, Units.val_mul, ihs, spinHom_genLift, tSpinN_of_lt hi0 hp,
          toMatZ_mulZ, getElem!_pos (Array.map Native.mixSpinN Native.chainGens[k]!) _
            (by simpa using hl'), Array.getElem_map, getElem!_pos (Native.chainGens[k]!) _ hl']

@[expose] noncomputable def pLift (n : ℕ) : PGcov :=
  tLift 0 (n % 63) * (tLift 1 (n / 63 % 32) * (tLift 2 (n / 2016 % 15) *
    (tLift 3 (n / 30240 % 8) * (tLift 4 (n / 241920 % 3) * tLift 5 (n / 725760 % 2)))))

theorem covMap_pLift
    (n : ℕ) : (covMap (pLift n) : K) = sElt n := by
  rw [pLift, sElt]
  simp only [map_mul, Subgroup.coe_mul]
  rw [(tLift_spec (k := 0) (by norm_num) (n % 63) (Nat.mod_lt _ (by norm_num))).1,
    (tLift_spec (k := 1) (by norm_num) (n / 63 % 32) (Nat.mod_lt _ (by norm_num))).1,
    (tLift_spec (k := 2) (by norm_num) (n / 2016 % 15) (Nat.mod_lt _ (by norm_num))).1,
    (tLift_spec (k := 3) (by norm_num) (n / 30240 % 8) (Nat.mod_lt _ (by norm_num))).1,
    (tLift_spec (k := 4) (by norm_num) (n / 241920 % 3) (Nat.mod_lt _ (by norm_num))).1,
    (tLift_spec (k := 5) (by norm_num) (n / 725760 % 2) (Nat.mod_lt _ (by norm_num))).1]

end CFSG.Sporadic.Co2Smith
