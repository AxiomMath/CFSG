module

public import CFSG.Monster.B.Final.Basic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Certificates.Kernel.BabyMonster.RegRun
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Cbar.SimpleBase
public import CFSG.Monster.B.Max2.Pinned
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace CFSG.Monster.B

open CFSG.Blueprint CFSG.SectionRank.LocalWitness

local notation "SB" => NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
  NativeSporadic.BSeed2

@[expose] noncomputable def seedUnit {X : Matrix (Fin 4370) (Fin 4370) (ZMod 2)} (hX : X ∈ SB)
    {n : ℕ} (hn : n ≠ 0) (h : X ^ n = 1) : NativeSporadic.B :=
  unitOf SB hX hn h

theorem bMat_seedUnit {X : Matrix (Fin 4370) (Fin 4370) (ZMod 2)} (hX : X ∈ SB) {n : ℕ}
    (hn : n ≠ 0) (h : X ^ n = 1) : bMat (seedUnit hX hn h) = X :=
  valHom_unitOf SB hX hn h

theorem bMat_runG_of_regsOK {prog : List Primes.Native.Ins}
    {A B : List ℕ} {regs : List ℕ} {tgt : List (List ℕ)}
    (hA : genA₁ = CFSG.KC.BM.stripMat A) (hB : genA₂ = CFSG.KC.BM.stripMat B)
    (h : CFSG.KC.BM.Reg.RegsOK prog [(1, some A), (2, some B)] true regs tgt) :
    ∀ k < regs.length, bMat (Pinned.runG prog bA₁ bA₂ (regs.getD k 0)) =
      CFSG.KC.BM.stripMat (tgt.getD k []) := by
  intro k hk
  refine h bMat (progInit bA₁ bA₂) ?_ ?_ k hk
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simpa [progInit, bMat_bA₁] using hA
    · simpa [progInit, bMat_bA₂] using hB
  · intro _ r hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    simp [progInit, hr.1, hr.2]

variable {g h k : NativeSporadic.B}

theorem comm_of_bMat (e : bMat g * bMat h = bMat h * bMat g) : g * h = h * g :=
  bMat_injective (by rw [map_mul, map_mul]; exact e)

theorem mul_self_of_bMat (e : bMat g * bMat g = 1) : g * g = 1 :=
  bMat_injective (by rw [map_mul, map_one]; exact e)

theorem pow_of_bMat {n : ℕ} (e : bMat g ^ n = 1) : g ^ n = 1 :=
  bMat_injective (by rw [map_pow, map_one]; exact e)

theorem ne_of_bMat (e : bMat g ≠ bMat h) : g ≠ h := fun h' => e (congrArg bMat h')

theorem ne_one_of_bMat (e : bMat g ≠ 1) : g ≠ 1 := fun h' => e (by rw [h', map_one])

theorem orderOf_of_bMat {p : ℕ} (hp : p.Prime) (e : bMat g ^ p = 1) (e1 : bMat g ≠ 1) :
    orderOf g = p :=
  haveI : Fact p.Prime := ⟨hp⟩
  orderOf_eq_prime (pow_of_bMat e) (ne_one_of_bMat e1)

end CFSG.Monster.B
