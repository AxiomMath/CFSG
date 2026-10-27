module

public import Certificates.Certificate810301
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Cent
public import CFSG.Sporadic.Co2Schreier.SixGroup
public import CFSG.Sporadic.Co2Schreier.Centralizers
public import CFSG.Sporadic.Co2I301.SpecAux

public noncomputable section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Dickson.I271

@[expose] def hP : Equiv.Perm (Fin 2300) := permOfArr 2300 (i301H ())

@[expose] def dP : Equiv.Perm (Fin 2300) := permOfArr 2300 (i301D ())

@[expose] def sP : Equiv.Perm (Fin 2300) := permOfArr 2300 (i301S ())

@[expose] def b2P : Equiv.Perm (Fin 2300) := permOfArr 2300 (i301B2 ())

@[expose] def b3P : Equiv.Perm (Fin 2300) := permOfArr 2300 (i301B3 ())

@[expose] def k1P : Equiv.Perm (Fin 2300) := permOfArr 2300 (i301K1 ())

@[expose] def k2P : Equiv.Perm (Fin 2300) := permOfArr 2300 (i301K2 ())

@[expose] def K0 : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {k1P, k2P}

@[expose] def U0 : Subgroup (Equiv.Perm (Fin 2300)) := Lsub.map (MulAut.conj hP).toMonoidHom

@[expose] def B1 : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {dP, b2P, b3P}

@[expose] def o6P (j : Fin 6) : Fin 2300 := ⟨o6.getD j 0 % 2300, Nat.mod_lt _ (by norm_num)⟩

@[expose] def sigma1P : Equiv.Perm (Fin 6) :=
  ⟨![3, 2, 1, 0, 4, 5], ![3, 2, 1, 0, 4, 5], by decide, by decide⟩

@[expose] def sigma2P : Equiv.Perm (Fin 6) :=
  ⟨![5, 3, 4, 0, 2, 1], ![3, 5, 4, 1, 2, 0], by decide, by decide⟩

@[expose] def wordVal {M : Type*} [Monoid M] (g : List M) (w : List ℕ) : M :=
  (w.map fun i => g.getD i 1).prod

instance smallCheck_fact : Fact (smallCheck () = true) :=
  ⟨Certificates.certificate810301.1⟩

section Facts


theorem hP_mem : hP ∈ co2P := SpecAux.hP_mem (h := hP) rfl

theorem dP_eq : dP = hP * co2XB * hP⁻¹ := SpecAux.dP_eq (h := hP) (d := dP) rfl rfl

theorem gens_mem_locC : dP ∈ locC ∧ sP ∈ locC ∧ b2P ∈ locC ∧ b3P ∈ locC ∧ k1P ∈ locC ∧
    k2P ∈ locC :=
  SpecAux.gens_mem_locC (d := dP) (s := sP) (b2 := b2P) (b3 := b3P) (k1 := k1P) (k2 := k2P) rfl rfl
    rfl rfl rfl rfl

theorem gens_mem_U0 : k1P ∈ U0 ∧ k2P ∈ U0 ∧ sP ∈ U0 :=
  SpecAux.gens_mem_U0 (h := hP) (s := sP) (k1 := k1P) (k2 := k2P) (U := U0) rfl rfl rfl rfl rfl

theorem mem_K0_facts : b2P ∈ K0 ∧ b3P ∈ K0 ∧ sP * k1P * sP⁻¹ ∈ K0 ∧ sP * k2P * sP⁻¹ ∈ K0 :=
  SpecAux.mem_K0_facts (s := sP) (b2 := b2P) (b3 := b3P) (k1 := k1P) (k2 := k2P) (K := K0) rfl rfl
    rfl rfl rfl rfl

theorem commute_facts : Commute dP sP ∧ Commute dP b2P ∧ Commute dP b3P ∧ Commute dP k1P ∧
    Commute dP k2P ∧ Commute b2P b3P ∧ Commute locZ dP ∧ Commute locZ sP ∧ Commute locZ b2P ∧
    Commute locZ b3P ∧ Commute locZ k1P ∧ Commute locZ k2P :=
  SpecAux.commute_facts (d := dP) (s := sP) (b2 := b2P) (b3 := b3P) (k1 := k1P) (k2 := k2P) rfl rfl
    rfl rfl rfl rfl

theorem pow_facts : dP ^ 3 = 1 ∧ dP ≠ 1 ∧ b2P ^ 3 = 1 ∧ b3P ^ 3 = 1 ∧ sP ^ 2 = 1 :=
  SpecAux.pow_facts (d := dP) (s := sP) (b2 := b2P) (b3 := b3P) rfl rfl rfl rfl

theorem indep_facts : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → dP ^ i * b2P ^ j * b3P ^ k = 1 →
    i = 0 ∧ j = 0 ∧ k = 0 :=
  SpecAux.indep_facts (d := dP) (b2 := b2P) (b3 := b3P) rfl rfl rfl

theorem card_K0 : Nat.card K0 = 360 := SpecAux.card_K0 (k1 := k1P) (k2 := k2P) (K := K0) rfl rfl rfl

theorem o6P_injective : Function.Injective o6P := by decide

theorem k1P_o6P (j : Fin 6) : k1P (o6P j) = o6P (sigma1P j) := by
  have hlt : ∀ j : Fin 6, o6.getD j 0 < 2300 := by decide
  apply Fin.ext
  rw [(SpecAux.k_o6 (k1 := k1P) (k2 := k2P) rfl rfl j (o6P j) (Nat.mod_eq_of_lt (hlt j))).1]
  revert j
  decide

theorem k2P_o6P (j : Fin 6) : k2P (o6P j) = o6P (sigma2P j) := by
  have hlt : ∀ j : Fin 6, o6.getD j 0 < 2300 := by decide
  apply Fin.ext
  rw [(SpecAux.k_o6 (k1 := k1P) (k2 := k2P) rfl rfl j (o6P j) (Nat.mod_eq_of_lt (hlt j))).2]
  revert j
  decide

theorem eq_one_of_fix_o6P : ∀ g ∈ K0, (∀ j, g (o6P j) = o6P j) → g = 1 := by
  intro g hg hfix
  refine SpecAux.eq_one_of_fix_base (k1 := k1P) (k2 := k2P) (K := K0) rfl rfl rfl g hg
    fun b hb => ?_
  have hbase : finBase2300 k0Base = [o6P 0, o6P 1, o6P 2, o6P 3] := by decide
  rw [hbase] at hb
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact hfix _

theorem centralizer_facts : ∀ g ∈ co2P, Commute g dP → Commute g locZ →
    (∃ i j k : ℕ, i < 3 ∧ j < 2 ∧ k < 2 ∧ g * (dP ^ i * locZ ^ j * sP ^ k)⁻¹ ∈ K0) ∧
    (Commute g k1P → Commute g k2P → ∃ i j : ℕ, i < 3 ∧ j < 2 ∧ g = dP ^ i * locZ ^ j) :=
  fun g hg hgd hgz => by
    have h : RowCentFacts := Certificates.certificate810301.2.1
    exact h g hg hgd hgz

theorem pow512_ne_one : ∀ i j : ℕ, 0 < i → i < 3 → j < 2 → (dP ^ i * locZ ^ j) ^ 512 ≠ 1 :=
  SpecAux.pow512_ne_one (d := dP) rfl

end Facts

end CFSG.Sporadic.Co2I301
