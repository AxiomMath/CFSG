module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Contain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Gl
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Orbit

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.Quasithin.F134.Sp4
open CFSG.QuasithinUnique.Lin2.Five (tauEquiv)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem le_borelSubgroup_of_le_stabilizer_two_odd [Finite K] [CharP K 2]
    {P : Subgroup (StatedSp 2 K)} {p a : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hPa : Nat.card P = p ^ a) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) :
    P ≤ borelSubgroup 2 K ∧ p ∣ Nat.card K - 1 := by
  have h3 := dvd_pred_of_le_stabilizer_two hp2 ha hPF hPa hexp
  exact ⟨fun y hy => mem_borelSubgroup_iff.mpr
    ⟨le_stabilizer_one_of_le_stabilizer_two_of_dvd hp.out hp2 hPU hPF hPa h3 hy, hPF hy⟩, h3⟩

theorem le_borelSubgroup_of_mul_odd [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {P : Subgroup (StatedSp 2 K)} {p a : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (ha : a = 2 ∨ a = 3) (hPa : Nat.card P = p ^ a) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s) :
    P ≤ borelSubgroup 2 K ∧ p ∣ Nat.card K - 1 := by
  have ha2 : 2 ≤ a := by omega
  obtain ⟨d, hd, hPd⟩ := exists_le_stabilizer_flag_of_card hK hp.out hp2 (by omega) hPa hPU
  rcases hd with rfl | rfl
  ·
    set τ := (tauEquiv (F := K)).toMonoidHom with hτ
    have hτF : P.map τ ≤ stabilizer 2 K (flag 2 K 2) := by
      rintro _ ⟨y, hy, rfl⟩
      exact tauSp_mem_stabilizer_two (hPd hy)
    have hτa : Nat.card (P.map τ) = p ^ a := by
      rw [Subgroup.card_map_of_injective (f := τ) (tauEquiv (F := K)).injective, hPa]
    have hτexp : ∀ x ∈ P.map τ, x ^ p = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hexp y hy, map_one]
    have hτU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P.map τ, ∃ y ∈ P.map τ, ∃ s ∈ unipotent 2 K,
        u * x = y * s := by
      intro u hu x hx
      rw [← map_tauEquiv_unipotent] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, s, hs, hzs⟩ := hPU u' hu' y hy
      refine ⟨τ z, ⟨z, hz, rfl⟩, τ s, ?_, by rw [← map_mul, hzs, map_mul]⟩
      rw [← map_tauEquiv_unipotent]
      exact ⟨s, hs, rfl⟩
    obtain ⟨hB, h3⟩ := le_borelSubgroup_of_le_stabilizer_two_odd hp2 ha2 hτU hτa hτexp hτF
    refine ⟨fun y hy => ?_, h3⟩
    have hy' : τ y ∈ borelSubgroup 2 K := hB ⟨y, hy, rfl⟩
    rw [← map_tauEquiv_borelSubgroup] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    rwa [(tauEquiv (F := K)).injective hzy] at hz
  · exact le_borelSubgroup_of_le_stabilizer_two_odd hp2 ha2 hPU hPa hexp hPd

theorem mul_comm_of_le_borelSubgroup [Finite K] [CharP K 2] {P : Subgroup (StatedSp 2 K)}
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hPB : P ≤ borelSubgroup 2 K) {x y : StatedSp 2 K} (hx : x ∈ P) (hy : y ∈ P) :
    x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_unipotent (K := K) 2 2
  have hU2 : IsPGroup 2 (unipotent 2 K) := hS ▸ S.isPGroup'
  set X : borelSubgroup 2 K := ⟨x, hPB hx⟩
  set Y : borelSubgroup 2 K := ⟨y, hPB hy⟩
  have hker : ⁅X, Y⁆ ∈ (diagHom 2 K).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at hker
  have hc : x * y * x⁻¹ * y⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 :=
    Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne p 2 hp2 P (unipotent 2 K) hP hU2) hc hker
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

end CFSG.Quasithin.H13.NQCore.Psp4
