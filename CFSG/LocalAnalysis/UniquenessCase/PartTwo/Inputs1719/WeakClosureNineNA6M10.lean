module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Spec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6DataM10
public import CFSG.Quasithin.Recognition.RuTypeM10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

namespace M10Model

abbrev T₀ : Subgroup P10 := P0 ⊓ A6Models.m10

theorem T_eq : M10Data.T = Out21.A6.qmL := by decide +kernel

theorem desc_T : Desc T₀ M10Data.T := by
  rw [T_eq]
  exact ⟨Out21.A6.mem_Qm_iff, Out21.A6.surj_Qm⟩

theorem isPGroup_T : IsPGroup 2 T₀ :=
  IsPGroup.of_card (n := 4) (by rw [Out21.A6.card_Qm]; norm_num)

theorem m10_le_autA6 : A6Models.m10 ≤ A6Models.autA6 := by
  rw [Out21.A6.m10_eq, closure_le]
  intro g hg
  have hg' : g ∈ Out21.A6.m10Gens := hg
  simp only [Out21.A6.m10Gens, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl
  · exact psl29_le_autA6 Out21.A6.tAdd_mem_psl29
  · exact psl29_le_autA6 Out21.A6.tSq_mem_psl29
  · exact psl29_le_autA6 Out21.A6.tInv_mem_psl29
  · exact Out21.A6.tMulFrob_mem_autA6

theorem tMulFrob_code : code A6Models.tMulFrob = [0, 4, 8, 7, 2, 3, 5, 6, 1, 9] := by
  decide +kernel

theorem decode_gens : ∀ c ∈ pslLit ++ pslLit.map (fun c => cmul c [0, 4, 8, 7, 2, 3, 5, 6, 1, 9]),
    ∃ x ∈ (A6Models.m10 : Set P10), code x = c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hc
    exact ⟨x, Out21.A6.psl29_le_m10 hx, rfl⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hd
    exact ⟨x * A6Models.tMulFrob, mul_mem (Out21.A6.psl29_le_m10 hx) Out21.A6.tMulFrob_mem_m10,
      by rw [code_mul, tMulFrob_code]⟩

theorem decode_pair : ∀ c ∈ pslLit ++ M10Data.T, ∃ x ∈ A6Models.m10, code x = c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hc
    exact ⟨x, Out21.A6.psl29_le_m10 hx, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := desc_T.surj c hc
    exact ⟨x, hx.2, rfl⟩

theorem Ks_ok : ∀ D ∈ M10Data.Ks, D.check M10Data.T = true := by
  intro D hD
  simp only [M10Data.Ks, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl
  · exact M10Data.K0_ok
  · exact M10Data.K1_ok

theorem Ks_gens : ∀ D ∈ M10Data.Ks, ∀ c ∈ D.K.gc, ∃ x ∈ (A6Models.m10 : Set P10), code x = c :=
  fun D hD c hc => decode_gens c (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp M10Data.gens_ok) D hD) c hc))

theorem Ks_p : ∀ D ∈ M10Data.Ks, D.p = 3 := by
  intro D hD
  simp only [M10Data.Ks, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl <;> rfl

theorem modelFacts : ModelFacts A6Models.m10 A6Models.psl29 T₀ where
  T₀_le := inf_le_right
  L₀_le := Out21.A6.psl29_le_m10
  sylow := isSylowIn_of_card_eq inf_le_right (by
    rw [Out21.A6.card_Qm, Out21.A6.card_m10, Out21.A6.factorization_720]
    norm_num)
  sup_eq := sup_eq_of_card Out21.A6.psl29_le_m10 inf_le_right card_psl29 Out21.A6.card_Qm
    Out21.A6.card_m10 (by norm_num)
  normal := fun g hg x hx => psl29_normal g (m10_le_autA6 hg) x hx
  three_dvd := by rw [card_psl29]; norm_num
  le_of_normal := le_of_normal_psl m10_le_autA6 Out21.A6.psl29_le_m10
  cent := fun g hg h => centralizer_psl29 (m10_le_autA6 hg) h
  sq_mem := sq_mem_of_reps (reps := Out21.A6.m10Reps) (by
      intro r hr
      simp only [Out21.A6.m10Reps, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨one_mem _, by simp⟩
      · exact ⟨Out21.A6.tMulFrob_mem_autA6, Out21.A6.tMulFrob_sq_mem⟩)
    fun x hx => (Out21.A6.mem_m10_iff x).mp hx
  pair := pair_spec desc_T decode_pair M10Data.pair_ok
  table := table_spec desc_T isPGroup_T M10Data.inv_ok Ks_ok Ks_gens M10Data.entries_ok
    M10Data.seed_ok fun D hD => Or.inl (Ks_p D hD)
  close := fun _ hET hTE hEe hE4 => (close_vacuous desc_T M10Data.inv_ok M10Data.entries_ok
    M10Data.seed_ok M10Data.nonNormal_ok hET hTE hEe hE4).elim

end M10Model

theorem nonempty_mulEquiv_m10_of_isM10 {X : Type} [Group X]
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsM10 X) :
    Nonempty (X ≃* ↥A6Models.m10) := by
  obtain ⟨φ, hφ, ⟨e⟩, hinv⟩ := h
  refine CFSG.Quasithin.RuType.nonempty_mulEquiv_m10 φ.ker ?_ ?_ e
  · rw [index_ker, MonoidHom.range_eq_top.mpr hφ, card_top, Nat.card_eq_fintype_card]
    rfl
  · intro x hx
    by_contra hk
    exact hinv x hk hx

end CFSG.LocalAnalysis.WeakClosure81.NFA6

