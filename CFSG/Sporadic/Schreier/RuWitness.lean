module

public import CFSG.Sporadic.Schreier.RuCertData
public import CFSG.Sporadic.Schreier.RuCheckWit

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem ruLGens_eq : ruLGens = [ruLGen 1, ruLGen 2, ruLGen 3] := by
  simp [ruLGen, ruLGens, ruLMWords]

theorem ruM_mem : ruM1 ∈ ruP ∧ ruM2 ∈ ruP := slotRun_mem ruMProg ruA0_mem ruA1_mem

theorem ruWw_mem : ruWw ∈ ruP := evalSigned_mem (pair_mem ruA0_mem ruA1_mem) _

theorem ruRw_mem : ruRw ∈ ruP := evalSigned_mem (pair_mem ruM_mem.1 ruM_mem.2) _

theorem ruUw_mem : ruUw ∈ ruP :=
  ruP.mul_mem (ruP.mul_mem (ruP.mul_mem ruWw_mem ruRw_mem) (ruP.inv_mem ruWw_mem)) ruA0_mem

theorem ruHw_mem : ruHw ∈ ruP := ruP.mul_mem (ruP.pow_mem ruUw_mem 7) ruWw_mem

theorem ruLGens_mem : ∀ g ∈ ruLGens, g ∈ ruP := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact ruP.mul_mem (ruP.mul_mem ruHw_mem (evalSigned_mem (pair_mem ruM_mem.1 ruM_mem.2) w))
    (ruP.inv_mem ruHw_mem)

theorem getD_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {l : List G}
    (h : ∀ g ∈ l, g ∈ H) (i : ℕ) : l.getD i 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact H.one_mem
  | some g => exact h g (List.mem_of_getElem? hi)

theorem ruLGen_mem (i : ℕ) : ruLGen i ∈ ruP := getD_mem_of_mem ruLGens_mem _

theorem ruLGen_memL (i : ℕ) : ruLGen i ∈ ruL :=
  getD_mem_of_mem (fun _ hg => Subgroup.subset_closure hg) _

theorem ruL_le : ruL ≤ ruP := closure_list_le ruLGens_mem

theorem ruFusX_mem (i : ℕ) : ruFusX i ∈ ruS :=
  evalSigned_mem (fun _ hg => Subgroup.subset_closure hg) _

theorem ruFusG_mem (i : ℕ) : ruFusG i ∈ ruP := evalSigned_mem (pair_mem ruA0_mem ruA1_mem) _

theorem ruFusH_mem (i : ℕ) : ruFusH i ∈ ruP :=
  ruP.mul_mem (ruP.pow_mem (ruP.mul_mem (ruP.mul_mem (ruP.mul_mem (ruFusG_mem i) ruA0_mem)
    (ruP.inv_mem (ruFusG_mem i))) (ruS_le (ruFusX_mem i))) _) (ruFusG_mem i)

theorem ruYp_memL (p : ℕ) : ruYp p ∈ ruL :=
  evalSigned_mem (fun _ hg => Subgroup.subset_closure hg) _

theorem CTUC_Ru_centralizer_and_fusion_witness_data :
    (ruM1, ruM2) = slotRun ruMProg ruA0 ruA1 ∧ ruRw = evalSigned [ruM1, ruM2] ruRMWord ∧
    ruWw = evalSigned [ruA0, ruA1] ruAlignmentSeedWord ∧ ruUw = ruWw * ruRw * ruWw⁻¹ * ruA0 ∧
    ruHw = ruUw ^ 7 * ruWw ∧
    (∀ i ∈ [1, 2, 3], ruLGen i =
      ruHw * evalSigned [ruM1, ruM2] (ruLMWords.getD (i - 1) []) * ruHw⁻¹) ∧
    ruL = Subgroup.closure {ruLGen 1, ruLGen 2, ruLGen 3} ∧
    (∀ i ∈ [1, 2, 3], ruFusX i = evalSigned ruSGens (ruSylowFusion.getD (i - 1) ([], [], 1)).1 ∧
      ruFusG i = evalSigned [ruA0, ruA1] (ruSylowFusion.getD (i - 1) ([], [], 1)).2.1 ∧
      ruFusD i = (ruSylowFusion.getD (i - 1) ([], [], 1)).2.2 ∧
      ruFusH i = (ruFusG i * ruA0 * (ruFusG i)⁻¹ * ruFusX i) ^ ((ruFusD i - 1) / 2) * ruFusG i) ∧
    [ruFusD 1, ruFusD 2, ruFusD 3] = [7, 5, 7] ∧
    ruOddNormalObstructions.map (fun r => r.1) = [5, 7, 13] ∧
    (∀ p ∈ [5, 7, 13], ruYp p = evalSigned [ruLGen 1, ruLGen 2, ruLGen 3] (ruObsRec p).1 ∧
      ruObsConj p = 3) ∧
    ruM1 ∈ ruP ∧ ruM2 ∈ ruP ∧ ruRw ∈ ruP ∧ ruWw ∈ ruP ∧ ruUw ∈ ruP ∧ ruHw ∈ ruP ∧
    (∀ i, ruLGen i ∈ ruP) ∧ ruL ≤ ruP ∧ (∀ i, ruFusX i ∈ ruS) ∧ (∀ i, ruFusG i ∈ ruP) ∧
    (∀ i, ruFusH i ∈ ruP) ∧ ∀ p, ruYp p ∈ ruL := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hp, -⟩ := ruWit_check
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun i _ => ⟨rfl, rfl, rfl, rfl⟩, ?_, hp, ?_,
    ruM_mem.1, ruM_mem.2, ruRw_mem, ruWw_mem, ruUw_mem, ruHw_mem, ruLGen_mem, ruL_le,
    ruFusX_mem, ruFusG_mem, ruFusH_mem, ruYp_memL⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  · rw [ruL, ruLGens_eq]
    congr 1
    ext g
    simp
  · simp [ruFusD, ruFusRec, ruSylowFusion]
  · intro p hp'
    refine ⟨by rw [ruYp, ruLGens_eq], ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> rfl

end CFSG.Sporadic.RuSchreier
