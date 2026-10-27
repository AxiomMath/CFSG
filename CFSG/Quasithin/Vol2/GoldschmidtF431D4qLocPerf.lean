module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocZsq
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open scoped commutatorElement
open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin
  CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false


section Generic

variable {G : Type*} [Group G]

theorem perfectCore_eq_of_commutator_le {H M : Subgroup G} (hHM : H ≤ M) (hMH : ⁅M, M⁆ ≤ H) :
    perfectCore M = perfectCore H := by
  refine le_antisymm ?_ (perfectCore_mono hHM)
  have key : ∀ n, derivedSeriesOf M (n + 1) ≤ derivedSeriesOf H n := by
    intro n
    induction n with
    | zero => exact hMH
    | succ n ih =>
      rw [derivedSeriesOf_succ M (n + 1), derivedSeriesOf_succ H n]
      exact Subgroup.commutator_mono ih ih
  exact le_iInf fun n => (perfectCore_le_derivedSeriesOf M (n + 1)).trans (key n)

end Generic

section Transport

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  (Kb : Subgroup (MulAut (Cm σ))) (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

include hf hK hσq in
theorem commutator_MbSt_le {P : Subgroup (Cm σ)}
    (hP : ∀ g : Cm σ, MulAut.conj g ∈ autStab P → g ∈ P) :
    ⁅MbSt σ Kb P, MbSt σ Kb P⁆ ≤ P.map (conjK σ Kb hinn) := by
  refine Subgroup.commutator_le.2 fun φ hφ ψ hψ => ?_
  have hθ : theta σ hf hK hσq ⁅(φ : MulAut (Cm σ)), (ψ : MulAut (Cm σ))⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (ringAut_mul_comm K _ _)
  have hker : ⁅(φ : MulAut (Cm σ)), (ψ : MulAut (Cm σ))⁆ ∈
      (MulAut.conj : Cm σ →* MulAut (Cm σ)).range := by
    rw [← theta_ker σ hf hK hσq]
    exact hθ
  obtain ⟨g, hg⟩ := hker
  have hmem : (⁅φ, ψ⁆ : ↥Kb) ∈ MbSt σ Kb P := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hφ hψ) (inv_mem hφ)) (inv_mem hψ)
  have hcoe : ((⁅φ, ψ⁆ : ↥Kb) : MulAut (Cm σ)) = ⁅(φ : MulAut (Cm σ)), (ψ : MulAut (Cm σ))⁆ := by
    simp [commutatorElement_def]
  have hstab : MulAut.conj g ∈ autStab P := by
    rw [hg, ← hcoe]
    exact (mem_MbSt σ).1 hmem
  exact ⟨g, hP g hstab, Subtype.ext ((coe_conjK σ Kb hinn g).trans (hg.trans hcoe.symm))⟩

include hf hK hσq in
theorem perfectCore_MbSt {P : Subgroup (Cm σ)}
    (hP : ∀ g : Cm σ, MulAut.conj g ∈ autStab P → g ∈ P) :
    perfectCore (MbSt σ Kb P) = (perfectCore P).map (conjK σ Kb hinn) := by
  have hle : P.map (conjK σ Kb hinn) ≤ MbSt σ Kb P := by
    rintro _ ⟨g, hg, rfl⟩
    exact (mem_MbSt σ).2 (conj_mem_autStab_of_mem hg)
  rw [perfectCore_eq_of_commutator_le hle (commutator_MbSt_le σ hf hK hσq Kb hinn hP)]
  exact F431.perfectCore_map_of_injective (conjK σ Kb hinn) (conjK_injective σ Kb hinn) P

include hf hK hσq in
theorem centerOf_perfectCore_MbSt {P : Subgroup (Cm σ)}
    (hP : ∀ g : Cm σ, MulAut.conj g ∈ autStab P → g ∈ P) :
    centerOf (perfectCore (MbSt σ Kb P)) = (centerOf (perfectCore P)).map (conjK σ Kb hinn) := by
  rw [perfectCore_MbSt σ hf hK hσq Kb hinn hP]
  exact F431.centerOf_map_of_injective (conjK σ Kb hinn) (conjK_injective σ Kb hinn) _

end Transport

section Fields

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
  (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  (Kb : Subgroup (MulAut (Cm σ))) (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

theorem four_le_card (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 ≤ 2 ^ 3 := by norm_num
    _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3

include hσ hf hK hσq in
theorem zK_mem_centerOf_perfectCore :
    zK σ Kb hinn ∈ centerOf (perfectCore (MbSt σ Kb (Pst0 σ))) := by
  rw [centerOf_perfectCore_MbSt σ hf hK hσq Kb hinn fun g hg =>
    mem_Pst0_of_conj_mem_autStab σ hf hK hσq hg]
  exact Subgroup.mem_map_of_mem _ (zC_mem_centerOf σ hσ hf hK)

include hσ hf hK hσq hinn in
theorem sq_of_mem_centerOf_MbSt {x : ↥Kb}
    (hx : x ∈ centerOf (perfectCore (MbSt σ Kb (Pst0 σ)))) : x ^ 2 = 1 := by
  rw [centerOf_perfectCore_MbSt σ hf hK hσq Kb hinn fun g hg =>
    mem_Pst0_of_conj_mem_autStab σ hf hK hσq hg] at hx
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
  rw [sq, ← map_mul, sq_of_mem_centerOf σ hσ (four_le_card hf hK) hw, map_one]

include hσ hf hK hσq hinn in
theorem centerOf_S_le :
    centerOf ((Tsub σ ⊥).subgroupOf Kb) ≤ centerOf (perfectCore (MbSt σ Kb (Pst0 σ))) := by
  rintro x ⟨hxS, hxc⟩
  obtain ⟨u, hu, δ, hδ, hxu⟩ := (mem_Tsub_iff σ ⊥ _).1 (Subgroup.mem_subgroupOf.1 hxS)
  rw [Subgroup.mem_bot.1 hδ, fieldActor_one, mul_one] at hxu
  have hxe : x = conjK σ Kb hinn u := Subtype.ext hxu
  have hcu : ∀ v ∈ Ust σ, u * v = v * u := fun v hv => by
    have hvS : conjK σ Kb hinn v ∈ (Tsub σ ⊥).subgroupOf Kb :=
      Subgroup.mem_subgroupOf.2 ((mem_Tsub_iff σ ⊥ _).2
        ⟨v, hv, 1, Subgroup.one_mem _, by rw [fieldActor_one, mul_one]; rfl⟩)
    have h := Subgroup.mem_centralizer_iff.1 hxc _ hvS
    rw [hxe, ← map_mul, ← map_mul] at h
    exact (conjK_injective σ Kb hinn h).symm
  rw [centerOf_perfectCore_MbSt σ hf hK hσq Kb hinn fun g hg =>
    mem_Pst0_of_conj_mem_autStab σ hf hK hσq hg, hxe]
  exact Subgroup.mem_map_of_mem _ (centerOf_Ust_le σ hσ (four_le_card hf hK) hu hcu)

end Fields

end CFSG.Quasithin.H13.F431.D4q.Loc
