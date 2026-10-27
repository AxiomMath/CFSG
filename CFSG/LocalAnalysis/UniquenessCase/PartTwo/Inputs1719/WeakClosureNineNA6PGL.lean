module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Spec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6DataPGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A6AutOrder8Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

namespace PGLModel

abbrev T₀ : Subgroup P10 := P0 ⊓ A6Models.pgl29

theorem T_eq : PGLData.T = Out21.A6.qpL := by decide +kernel

theorem desc_T : Desc T₀ PGLData.T := by
  rw [T_eq]
  exact ⟨Out21.A6.mem_Qp_iff, Out21.A6.surj_Qp⟩

theorem isPGroup_T : IsPGroup 2 T₀ :=
  IsPGroup.of_card (n := 4) (by rw [Out21.A6.card_Qp]; norm_num)

theorem tMul_code : code A6Models.tMul = [0, 4, 8, 5, 6, 1, 7, 2, 3, 9] := by decide +kernel

theorem decode_gens : ∀ c ∈ pslLit ++ pslLit.map (fun c => cmul c [0, 4, 8, 5, 6, 1, 7, 2, 3, 9]),
    ∃ x ∈ (A6Models.pgl29 : Set P10), code x = c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hc
    exact ⟨x, Out21.A6.psl29_le_pgl29 hx, rfl⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hd
    exact ⟨x * A6Models.tMul, mul_mem (Out21.A6.psl29_le_pgl29 hx) Out21.A6.tMul_mem_pgl29,
      by rw [code_mul, tMul_code]⟩

theorem decode_pair : ∀ c ∈ pslLit ++ PGLData.T, ∃ x ∈ A6Models.pgl29, code x = c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hc
    exact ⟨x, Out21.A6.psl29_le_pgl29 hx, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := desc_T.surj c hc
    exact ⟨x, hx.2, rfl⟩

theorem Ks_ok : ∀ D ∈ PGLData.Ks, D.check PGLData.T = true := by
  intro D hD
  simp only [PGLData.Ks, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl
  · exact PGLData.K0_ok
  · exact PGLData.K1_ok
  · exact PGLData.K2_ok
  · exact PGLData.K3_ok

theorem Ks_gens : ∀ D ∈ PGLData.Ks, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.pgl29 : Set P10), code x = c :=
  fun D hD c hc => decode_gens c (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp PGLData.gens_ok) D hD) c hc))

theorem sylow : IsSylowIn 2 T₀ A6Models.pgl29 :=
  isSylowIn_of_card_eq inf_le_right (by
    rw [Out21.A6.card_Qp, Out21.A6.card_pgl29, Out21.A6.factorization_720]
    norm_num)

theorem sup_eq : A6Models.psl29 ⊔ T₀ = A6Models.pgl29 :=
  sup_eq_of_card Out21.A6.psl29_le_pgl29 inf_le_right card_psl29 Out21.A6.card_Qp
    Out21.A6.card_pgl29 (by norm_num)

theorem sq_mem : ∀ x ∈ A6Models.pgl29, x * x ∈ A6Models.psl29 :=
  sq_mem_of_reps (reps := Out21.A6.pglReps) (by
      intro r hr
      simp only [Out21.A6.pglReps, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨one_mem _, by simp⟩
      · exact ⟨Out21.A6.tMul_mem_autA6, Out21.A6.tMul_sq_mem⟩)
    fun x hx => (Out21.A6.mem_pgl29_iff x).mp hx

theorem T_max : ∀ H : Subgroup P10, T₀ ≤ H → H ≤ A6Models.pgl29 → H = T₀ ∨ H = A6Models.pgl29 :=
  max_of_overgroup sylow sq_mem sup_eq
    fun _ hTH _ hk hkT hkH => ov_spec desc_T PGLData.ov_ok hTH hk hkT hkH

theorem modelFacts : ModelFacts A6Models.pgl29 A6Models.psl29 T₀ where
  T₀_le := inf_le_right
  L₀_le := Out21.A6.psl29_le_pgl29
  sylow := sylow
  sup_eq := sup_eq
  normal := fun g hg x hx => psl29_normal g (Out21.A6.pgl29_le_autA6 hg) x hx
  three_dvd := by rw [card_psl29]; norm_num
  le_of_normal := le_of_normal_psl Out21.A6.pgl29_le_autA6 Out21.A6.psl29_le_pgl29
  cent := fun g hg h => centralizer_psl29 (Out21.A6.pgl29_le_autA6 hg) h
  sq_mem := sq_mem
  pair := pair_spec desc_T decode_pair PGLData.pair_ok
  table := table_spec desc_T isPGroup_T PGLData.inv_ok Ks_ok Ks_gens PGLData.entries_ok
    PGLData.seed_ok fun _ _ => Or.inr T_max
  close := fun _ hET hTE hEe hE4 => (close_vacuous desc_T PGLData.inv_ok PGLData.entries_ok
    PGLData.seed_ok PGLData.nonNormal_ok hET hTE hEe hE4).elim

end PGLModel

theorem nonempty_mulEquiv_pgl29_of_isPGL2 {X : Type} [Group X]
    (h : CFSG.Quasithin.F6.IsPGL2 9 X) : Nonempty (X ≃* ↥A6Models.pgl29) := by
  obtain ⟨F, hF, hFf, hF9, ⟨e⟩⟩ := h
  obtain ⟨F', hF', hF'f, hF'9, ⟨e'⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.isPGL2_nine_pgl29
  let := hF
  let := hF'
  let := Fintype.ofFinite F
  let := Fintype.ofFinite F'
  let φ : F ≃+* F' := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF9, hF'9])
  exact ⟨e.trans ((CFSG.Quasithin.F6.PGL2Res.statedEquiv F).trans
    ((CFSG.ShultStronglyClosedTI.pglFieldEquiv (ι := Fin 2) φ).trans
      ((CFSG.Quasithin.F6.PGL2Res.statedEquiv F').symm.trans e'.symm)))⟩

end CFSG.LocalAnalysis.WeakClosure81.NFA6

