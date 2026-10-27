module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Spec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6DataAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A6AutOrder8Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

namespace AutModel

theorem T_eq : AutData.T = Core.p0Lit := by decide +kernel

theorem desc_T : Desc P0 AutData.T := by
  rw [T_eq]
  exact ⟨mem_P0_iff, fun _ hc => exists_P0_of_code hc⟩

theorem isPGroup_T : IsPGroup 2 P0 :=
  IsPGroup.of_card (n := 5) (by rw [card_P0]; norm_num)

theorem decode_autL : ∀ c ∈ Core.autL, ∃ x ∈ A6Models.autA6, code x = c := by
  intro c hc
  unfold Core.autL at hc
  obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
  rw [← autRepsP_code] at hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  refine ⟨y' * r', mul_mem (psl29_le_autA6 hy') ?_, by rw [code_mul]⟩
  rw [autA6_eq]
  exact autReps_mem_closure r' hr'

theorem Ks_ok : ∀ D ∈ AutData.Ks, D.check AutData.T = true := by
  intro D hD
  simp only [AutData.Ks, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl
  · exact AutData.K0_ok
  · exact AutData.K1_ok
  · exact AutData.K2_ok
  · exact AutData.K3_ok

theorem Ks_gens : ∀ D ∈ AutData.Ks, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.autA6 : Set P10), code x = c :=
  fun D hD c hc => decode_autL c (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp AutData.gens_ok) D hD) c hc))

theorem factorization_1440 : (1440 : ℕ).factorization 2 = 5 := by
  norm_num [Nat.factorization]

theorem sylow : IsSylowIn 2 P0 A6Models.autA6 :=
  isSylowIn_of_card_eq P0_le_autA6 (by rw [card_P0, card_autA6, factorization_1440]; norm_num)

theorem sup_eq : A6Models.psl29 ⊔ P0 = A6Models.autA6 :=
  sup_eq_of_card psl29_le_autA6 P0_le_autA6 card_psl29 card_P0 card_autA6 (by norm_num)

theorem tFrob_sq : A6Models.tFrob * A6Models.tFrob = 1 := by decide +kernel

theorem sq_mem : ∀ x ∈ A6Models.autA6, x * x ∈ A6Models.psl29 :=
  sq_mem_of_reps (reps := autRepsP) (by
      intro r hr
      simp only [autRepsP, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨one_mem _, by simp⟩
      · exact ⟨Out21.A6.tMul_mem_autA6, Out21.A6.tMul_sq_mem⟩
      · exact ⟨Out21.A6.tFrob_mem_autA6, by
          rw [tFrob_sq]; exact one_mem _⟩
      · exact ⟨mul_mem Out21.A6.tMul_mem_autA6 Out21.A6.tFrob_mem_autA6, by
          rw [← Out21.A6.tMulFrob_eq]; exact Out21.A6.tMulFrob_sq_mem⟩)
    fun x hx => (mem_autA6_iff_exists x).mp hx

theorem T_max : ∀ H : Subgroup P10, P0 ≤ H → H ≤ A6Models.autA6 → H = P0 ∨ H = A6Models.autA6 :=
  max_of_overgroup sylow sq_mem sup_eq
    fun _ hTH _ hk hkT hkH => P0_overgroup (fun _ hp => hTH hp) hk hkT hkH

theorem modelFacts : ModelFacts A6Models.autA6 A6Models.psl29 P0 where
  T₀_le := P0_le_autA6
  L₀_le := psl29_le_autA6
  sylow := sylow
  sup_eq := sup_eq
  normal := psl29_normal
  three_dvd := by rw [card_psl29]; norm_num
  le_of_normal := le_of_normal_psl le_rfl psl29_le_autA6
  cent := fun _ hg h => centralizer_psl29 hg h
  sq_mem := sq_mem
  pair := pair_spec desc_T decode_autL AutData.pair_ok
  table := table_spec desc_T isPGroup_T AutData.inv_ok Ks_ok Ks_gens AutData.entries_ok
    AutData.seed_ok fun _ _ => Or.inr T_max
  close := fun _ hET hTE hEe hE4 => close_star desc_T isPGroup_T P0_le_autA6 AutData.inv_ok
    Ks_ok Ks_gens AutData.entries_ok AutData.seed_ok AutData.nonNormal_ok AutData.close_ok T_max
    hET hTE hEe hE4

end AutModel

theorem nonempty_mulEquiv_autA6_of_isAutOf {X : Type} [Group X]
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsAutOf X
      (alternatingGroup (Fin 6))) : Nonempty (X ≃* ↥A6Models.autA6) := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.isAutOf_autA6
  exact ⟨e.trans f.symm⟩

end CFSG.LocalAnalysis.WeakClosure81.NFA6

