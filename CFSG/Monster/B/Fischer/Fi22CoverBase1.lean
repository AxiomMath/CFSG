
module

public import CFSG.Monster.B.Fischer.Fi22CoverBase

public import CFSG.Monster.B.Fischer.Fi22Local
public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public import CFSG.Monster.B.Fischer.Fi22Outer

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem rep_fi22OuterField {f j : ℕ} (hf : f < 10)
    (hj : j < (fi22OuterLines3510.getD f (0, 0)).2) :
    Rep 3510 (fi22OuterStrong3510 f)[j]! (fi22OuterField f j) := by
  have hL : fi22OuterLine3510 f j < 151 := by
    have := fi22OuterLines3510_bound f hf
    rw [fi22OuterLine3510]
    omega
  rw [fi22OuterStrong3510, getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj),
    Array.getElem_ofFn]
  exact rep_fi22OuterPerm3510 hL

theorem rep_fi22OuterU {j : ℕ} (hj : j < 54) :
    Rep 3510 (fi22OuterStrong3510 7)[j]! (fi22OuterU j) :=
  rep_fi22OuterField (by norm_num) hj

theorem rep_fi22OuterH {j : ℕ} (hj : j < 54) :
    Rep 3510 (fi22OuterStrong3510 8)[j]! (fi22OuterH j) :=
  rep_fi22OuterField (by norm_num) hj

theorem rep_fi22OuterXRep {i : ℕ} (hi : i < 3) :
    Rep 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterXRep i) :=
  rep_fi22OuterField (by norm_num) hi

theorem rep_fi22OuterZ :
    Rep 3510 (fi22OuterStrong3510 1)[0]! fi22OuterZ :=
  rep_fi22OuterField (by norm_num) (by decide)

theorem fi22OuterTPointsNat_lt :
    ∀ x ∈ fi22OuterTPointsNat, x < 3510 :=
  fi22Outer_check.2.2.2.2.2.2.2.1

theorem fi22T_facts : ChainCheckFacts 3510
    ((fi22OuterStrong3510 4).extract 0 fi22OuterTGenCount) (fi22OuterStrong3510 4)
    #[0, 1, 2, 3, 6, 4] (fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations) 4 :=
  chainCheckFacts fi22Local_check.2.2.1

theorem fi22TLev_size {i : ℕ} (hi : i < 6) :
    (lev 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] i).pts.size =
      [1024, 32, 4, 1, 1, 1][i]! := by
  have h := fi22Local_check.2.2.2.1
  rw [rawOrbitSizes] at h
  rw [← h, lev]
  have hi' : i < (rawLevels 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4]).size := by
    rw [ChainArrays.chainLevels_size]
    exact hi
  rw [getElem!_pos _ i hi', getElem!_pos _ i (by simpa using hi')]
  simp

theorem fi22TProd_bounds (x : Fin 1024 × Fin 32 × Fin 4) :
    (x.1 : ℕ) < (lev 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] 0).pts.size ∧
      (x.2.1 : ℕ) < (lev 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] 1).pts.size ∧
      (x.2.2 : ℕ) < (lev 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] 2).pts.size := by
  rw [fi22TLev_size (i := 0) (by norm_num), fi22TLev_size (i := 1) (by norm_num),
    fi22TLev_size (i := 2) (by norm_num)]
  exact ⟨x.1.2, x.2.1.2, x.2.2.2⟩

theorem fi22TProd_apply
    (x : Fin 1024 × Fin 32 × Fin 4) (p : Fin 3510) :
    (fi22TProd x p : ℕ) = tr3 fi22TLevels x.1 x.2.1 x.2.2 p :=
  fi22OuterChainT_arrays.prod3_apply fi22T_facts (by rw [fi22OuterChainT_baseCount]; norm_num)
    (fi22TProd_bounds x).1 (fi22TProd_bounds x).2.1 (fi22TProd_bounds x).2.2 p

theorem fi22TProd_mem
    (x : Fin 1024 × Fin 32 × Fin 4) : fi22TProd x ∈ fi22OuterT := by
  have h0 := fi22OuterChainT.levelSubgroup_zero_eq_original fi22OuterChainT_valid
  have hmem : ∀ i < 3, ∀ k < (lev 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] i).pts.size,
      levT 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] i k ∈ fi22OuterT := by
    intro i hi k hk
    rw [fi22OuterT, ← h0]
    exact fi22OuterChainT.levelSubgroup_antitone 0 i (Nat.zero_le _)
      (fi22OuterChainT_arrays.levT_mem fi22T_facts (by rw [fi22OuterChainT_baseCount]; omega) hk)
  obtain ⟨ha, hb, hc⟩ := fi22TProd_bounds x
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem 0 (by norm_num) _ ha)
    (hmem 1 (by norm_num) _ hb)) (hmem 2 (by norm_num) _ hc)

theorem fi22TProd_surj
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22OuterT) :
    ∃ x, fi22TProd x = g := by
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := fi22OuterChainT_arrays.exists_prod3 (by norm_num)
    fi22Local_check.2.2.1 (by rw [fi22OuterChainT_baseCount]; norm_num) (fun i hi3 hi6 => by
      rw [fi22OuterChainT_baseCount] at hi6
      rw [fi22TLev_size hi6]
      interval_cases i <;> rfl) hg
  rw [fi22TLev_size (i := 0) (by norm_num)] at ha
  rw [fi22TLev_size (i := 1) (by norm_num)] at hb
  rw [fi22TLev_size (i := 2) (by norm_num)] at hc
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩), h⟩

theorem fi22TProd_injective : Function.Injective fi22TProd := by
  let Ψ : Fin 1024 × Fin 32 × Fin 4 → fi22OuterT := fun x => ⟨fi22TProd x, fi22TProd_mem x⟩
  have hsurj : Function.Surjective Ψ := fun g => by
    obtain ⟨x, hx⟩ := fi22TProd_surj g.2
    exact ⟨x, Subtype.ext hx⟩
  have hcard : Nat.card (Fin 1024 × Fin 32 × Fin 4) ≤ Nat.card fi22OuterT := by
    rw [card_fi22OuterT, Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin, Nat.card_fin]
  have hbij := hsurj.bijective_of_nat_card_le hcard
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

theorem fi22TProd_zero : fi22TProd (0, 0, 0) = 1 := by
  have h : ∀ i < 6, levT 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] i 0 = 1 := fun i hi =>
    fi22OuterChainT_arrays.levT_zero fi22T_facts (by rw [fi22OuterChainT_baseCount]; exact hi)
  rw [fi22TProd]
  simp only [Fin.val_zero]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), one_mul, one_mul]

theorem fi22TProd_eq_one_iff (x : Fin 1024 × Fin 32 × Fin 4) :
    (allLt 3510 fun p => tr3 fi22TLevels x.1 x.2.1 x.2.2 p == p) = true ↔ fi22TProd x = 1 := by
  rw [allLt_iff]
  constructor
  · intro h
    refine Equiv.ext fun p => Fin.ext ?_
    rw [Equiv.Perm.one_apply, fi22TProd_apply x p]
    exact beq_iff_eq.1 (h p p.2)
  · intro h p hp
    have e : ((fi22TProd x) ⟨p, hp⟩ : ℕ) = p := by
      rw [h]
      rfl
    rw [fi22TProd_apply x ⟨p, hp⟩] at e
    exact beq_iff_eq.2 e

theorem fi22TProd_sq_eq_one_iff (x : Fin 1024 × Fin 32 × Fin 4) :
    (allLt 3510 fun p =>
      tr3 fi22TLevels x.1 x.2.1 x.2.2 (tr3 fi22TLevels x.1 x.2.1 x.2.2 p) == p) = true ↔
      fi22TProd x * fi22TProd x = 1 := by
  rw [allLt_iff]
  constructor
  · intro h
    refine Equiv.ext fun p => Fin.ext ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, fi22TProd_apply x (fi22TProd x p),
      fi22TProd_apply x p]
    exact beq_iff_eq.1 (h p p.2)
  · intro h p hp
    have e : ((fi22TProd x * fi22TProd x) ⟨p, hp⟩ : ℕ) = p := by
      rw [h]
      rfl
    rw [Equiv.Perm.mul_apply, fi22TProd_apply x (fi22TProd x ⟨p, hp⟩),
      fi22TProd_apply x ⟨p, hp⟩] at e
    exact beq_iff_eq.2 e

theorem isInv3_iff (x : Fin 1024 × Fin 32 × Fin 4) :
    isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true ↔ orderOf (fi22TProd x) = 2 := by
  rw [orderOf_eq_prime_iff, pow_two, ne_eq, ← fi22TProd_eq_one_iff, ← fi22TProd_sq_eq_one_iff,
    isInv3]
  cases allLt 3510 (fun p => tr3 fi22TLevels x.1 x.2.1 x.2.2 p == p) <;>
    cases allLt 3510 (fun p => tr3 fi22TLevels x.1 x.2.1 x.2.2
      (tr3 fi22TLevels x.1 x.2.1 x.2.2 p) == p) <;> simp

theorem mem_fi22OuterR_iff (x : Fin 3510) :
    x ∈ fi22OuterR ↔ fi22OuterTPointsNat.contains (x : ℕ) = true := by
  have hlt := fi22OuterTPointsNat_lt
  rw [List.contains_iff_mem, fi22OuterR, fi22FinList, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show y % 3510 ∈ fi22OuterTPointsNat
    rw [Nat.mod_eq_of_lt (hlt y hy)]
    exact hy
  · intro hx
    exact ⟨x, hx, Fin.ext (Nat.mod_eq_of_lt x.2)⟩

theorem conjOK3_spec {x y : Fin 1024 × Fin 32 × Fin 4} {u : Array ℕ}
    {U : Equiv.Perm (Fin 3510)} (hu : Rep 3510 u U)
    (h : conjOK3 fi22TLevels 3510 u x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 = true) :
    fi22TProd y * U * (fi22TProd y)⁻¹ = fi22TProd x := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Equiv.ext fun p => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, fi22TProd_apply y (U p),
    fi22TProd_apply x (fi22TProd y p), fi22TProd_apply y p, ← hu p]
  exact beq_iff_eq.1 (allLt_spec h p.2)

theorem filter_fixed_fi22OuterXRep {i : ℕ} (hi : i < 3) :
    (Finset.univ.filter fun p => fi22OuterXRep i p = p) =
      Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[i]!)[p.val]! = p.val :=
  Finset.filter_congr fun p _ => by rw [(rep_fi22OuterXRep hi) p, Fin.val_inj]

end CFSG.Monster.B.Fischer
