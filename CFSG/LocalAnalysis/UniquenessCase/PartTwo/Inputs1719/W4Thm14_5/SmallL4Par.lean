module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSL
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinFlag
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.LeviBlock CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.Blueprint (LieModel)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nonempty_bar2_hinf_slFlagStab_four_empty :
    Nonempty (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K ∅)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) K) := by
  have h0 : linBlockLen 4 ∅ 0 = 4 :=
    linBlockLen_eq (by simp) (Or.inl rfl) (Or.inl (by simp))
      (fun c hc => absurd hc (Set.notMem_empty c)) (by norm_num)
  have hB : ∀ j, j ≠ 0 → linBlockSL K 4 ∅ j = ⊥ := by
    intro j hj0
    refine linBlockSL_eq_bot_of_not_start ?_
    rintro (h | h)
    · exact hj0 (Fin.ext h)
    · exact Set.notMem_empty _ h
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (linLeviHom K 4 ∅)
    (isPGroup_ker_linLeviHom (by norm_num)) 0 (linBlockSL K 4 ∅) hB (fun y hy => ?_)
    commutator_range_linLeviHom_le (linBlockSLEquiv h0)
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num))
    (pCore_specialLinearGroup_eq_bot 4)
  exact pi_le_range_linLeviHom ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_slFlagStab_four_one :
    Nonempty (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K {1})) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) := by
  have h0 : linBlockLen 4 {1} 0 = 1 :=
    linBlockLen_eq (by simp) (Or.inl rfl) (Or.inr (by simp))
      (fun c hc => by rw [Set.mem_singleton_iff] at hc; simp [hc]) le_rfl
  have h1 : linBlockLen 4 {1} 1 = 3 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inl (by simp))
      (fun c hc => by rw [Set.mem_singleton_iff] at hc; simp [hc]) (by norm_num)
  have hB : ∀ j, j ≠ 1 → linBlockSL K 4 {1} j = ⊥ := by
    intro j hj1
    by_cases hj0 : j = 0
    · subst hj0
      exact linBlockSL_eq_bot (by rw [h0]; norm_num)
    refine linBlockSL_eq_bot_of_not_start ?_
    rintro (h | h)
    · exact hj0 (Fin.ext h)
    · exact hj1 (Fin.ext (by simpa using h))
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (linLeviHom K 4 {1})
    (isPGroup_ker_linLeviHom (by norm_num)) 1 (linBlockSL K 4 {1}) hB (fun y hy => ?_)
    commutator_range_linLeviHom_le (linBlockSLEquiv h1)
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl)
    (pCore_specialLinearGroup_eq_bot 3)
  exact pi_le_range_linLeviHom ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_slFlagStab_four_one_two (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K {1, 2})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hmem : ∀ c, c ∈ ({1, 2} : Set ℕ) ↔ c = 1 ∨ c = 2 := fun c => by simp
  have h0 : linBlockLen 4 {1, 2} 0 = 1 :=
    linBlockLen_eq (by simp) (Or.inl rfl) (Or.inr (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) le_rfl
  have h1 : linBlockLen 4 {1, 2} 1 = 1 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inr (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) le_rfl
  have h2 : linBlockLen 4 {1, 2} 2 = 2 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inl (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) (by norm_num)
  have hB : ∀ j, j ≠ 2 → linBlockSL K 4 {1, 2} j = ⊥ := by
    intro j hj2
    by_cases hj0 : j = 0
    · subst hj0
      exact linBlockSL_eq_bot (by rw [h0]; norm_num)
    by_cases hj1 : j = 1
    · subst hj1
      exact linBlockSL_eq_bot (by rw [h1]; norm_num)
    refine linBlockSL_eq_bot_of_not_start ?_
    rintro (h | h)
    · exact hj0 (Fin.ext h)
    · rcases (hmem _).mp h with h | h
      · exact hj1 (Fin.ext (by simpa using h))
      · exact hj2 (Fin.ext (by simpa using h))
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (linLeviHom K 4 {1, 2})
    (isPGroup_ker_linLeviHom (by norm_num)) 2 (linBlockSL K 4 {1, 2}) hB (fun y hy => ?_)
    commutator_range_linLeviHom_le (linBlockSLEquiv h2)
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
    (pCore_specialLinearGroup_eq_bot 2)
  exact pi_le_range_linLeviHom ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_slFlagStab_four_one_three (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K {1, 3})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hmem : ∀ c, c ∈ ({1, 3} : Set ℕ) ↔ c = 1 ∨ c = 3 := fun c => by simp
  have h0 : linBlockLen 4 {1, 3} 0 = 1 :=
    linBlockLen_eq (by simp) (Or.inl rfl) (Or.inr (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) le_rfl
  have h1 : linBlockLen 4 {1, 3} 1 = 2 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inr (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) (by norm_num)
  have h3 : linBlockLen 4 {1, 3} 3 = 1 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inl (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) le_rfl
  have hB : ∀ j, j ≠ 1 → linBlockSL K 4 {1, 3} j = ⊥ := by
    intro j hj1
    by_cases hj0 : j = 0
    · subst hj0
      exact linBlockSL_eq_bot (by rw [h0]; norm_num)
    by_cases hj3 : j = 3
    · subst hj3
      exact linBlockSL_eq_bot (by rw [h3]; norm_num)
    refine linBlockSL_eq_bot_of_not_start ?_
    rintro (h | h)
    · exact hj0 (Fin.ext h)
    · rcases (hmem _).mp h with h | h
      · exact hj1 (Fin.ext (by simpa using h))
      · exact hj3 (Fin.ext (by simpa using h))
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (linLeviHom K 4 {1, 3})
    (isPGroup_ker_linLeviHom (by norm_num)) 1 (linBlockSL K 4 {1, 3}) hB (fun y hy => ?_)
    commutator_range_linLeviHom_le (linBlockSLEquiv h1)
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
    (pCore_specialLinearGroup_eq_bot 2)
  exact pi_le_range_linLeviHom ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_slFlagStab_four_two_three (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K {2, 3})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hmem : ∀ c, c ∈ ({2, 3} : Set ℕ) ↔ c = 2 ∨ c = 3 := fun c => by simp
  have h0 : linBlockLen 4 {2, 3} 0 = 2 :=
    linBlockLen_eq (by simp) (Or.inl rfl) (Or.inr (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) (by norm_num)
  have h2 : linBlockLen 4 {2, 3} 2 = 1 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inr (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) le_rfl
  have h3 : linBlockLen 4 {2, 3} 3 = 1 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inl (by simp))
      (fun c hc => by rcases (hmem c).mp hc with rfl | rfl <;> simp) le_rfl
  have hB : ∀ j, j ≠ 0 → linBlockSL K 4 {2, 3} j = ⊥ := by
    intro j hj0
    by_cases hj2 : j = 2
    · subst hj2
      exact linBlockSL_eq_bot (by rw [h2]; norm_num)
    by_cases hj3 : j = 3
    · subst hj3
      exact linBlockSL_eq_bot (by rw [h3]; norm_num)
    refine linBlockSL_eq_bot_of_not_start ?_
    rintro (h | h)
    · exact hj0 (Fin.ext h)
    · rcases (hmem _).mp h with h | h
      · exact hj2 (Fin.ext (by simpa using h))
      · exact hj3 (Fin.ext (by simpa using h))
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (linLeviHom K 4 {2, 3})
    (isPGroup_ker_linLeviHom (by norm_num)) 0 (linBlockSL K 4 {2, 3}) hB (fun y hy => ?_)
    commutator_range_linLeviHom_le (linBlockSLEquiv h0)
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
    (pCore_specialLinearGroup_eq_bot 2)
  exact pi_le_range_linLeviHom ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

omit [Finite K] [CharP K 2] in
theorem flagStabilizer_four_one_two_three :
    LinearFlag.flagStabilizer 4 K {1, 2, 3} = LinearFlag.upperTriangular 4 K := by
  have hcuts : LinearFlag.borelOvergroupCuts (LinearFlag.upperTriangular 4 K) = {1, 2, 3} := by
    ext i
    constructor
    · rintro ⟨hi, hin, -⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · intro hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      have h1 : 1 ≤ i := by omega
      have h4 : i < 4 := by omega
      exact ⟨h1, h4, by
        rw [← LinearFlag.reflElt_of_lt h1 h4]
        exact CFSG.QuasithinUnique.Setup.X7a.reflElt_not_mem_upperTriangular h1 h4⟩
  have h := (LinearFlag.borel_overgroups (LinearFlag.upperTriangular 4 K) le_rfl).1
  rw [hcuts] at h
  exact h.symm

omit [CharP K 2] in
theorem isSL3_of_mulEquiv_sl3_of_card_two {X : Type} [Group X] (hK : Nat.card K = 2)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) : IsSL3 X 1 := by
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two hK le_rfl
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two hK le_rfl
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  obtain ⟨⟨hq1, hq2⟩, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have h : IsSLn X 3 1 :=
    ⟨K, inferInstance, inferInstance, by rw [hK, pow_one],
      ⟨e.trans (specialLinearGroupEquivStatedSL 3 K)⟩⟩
  exact ⟨⟨Group.isPerfect_def.mp hq1, hq2.1⟩, isLn_quot_center_of_isSLn h le_rfl le_rfl⟩

theorem ordA_two_ne_ordA_three_two {f : ℕ} (hf : 2 < f) : ordA 2 (2 ^ f) ≠ ordA 3 (2 ^ 1) := by
  intro hm
  have h1 := profile_ordA (n := 2) (by norm_num) (by omega : 1 ≤ f)
  rw [hm] at h1
  have hN := (h1.transfer (profile_ordA (n := 3) (f := 1) (by norm_num) le_rfl)).1
  norm_num at hN
  omega

theorem not_nParamSingle_of_isSLn_four_one {X : Type} [Group X] {n : ℕ} (h : IsSLn X 4 1)
    (hn : 2 < n) : ¬ NParamSingle X n := by
  have hlow := lowOrder_of_isSLn_four le_rfl h
  have hZ : CFSG.Open.IsQuasisimple X → Odd (Nat.card (center X)) := fun _ =>
    odd_card_center_of_isSLn h
  rintro (hSz | hL2 | hSU3 | hSL3 | hSp4)
  · exact false_of_rankOne (Or.inr (Or.inl hSz)) hlow hZ
  · exact false_of_rankOne (Or.inl hL2) hlow hZ
  · exact false_of_rankOne (Or.inr (Or.inr (Or.inr hSU3))) hlow hZ
  · have hquot : Nat.card (X ⧸ Subgroup.center X) = ordA 3 (2 ^ 1) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using
        (isLn_quot_center_of_isSLn h (by norm_num) le_rfl).card_eq_lieOrd (by norm_num)
    have hX : Nat.card (X ⧸ Subgroup.center X) = ordA 2 (2 ^ n) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hSL3.2.card_eq_lieOrd (by norm_num)
    exact ordA_two_ne_ordA_three_two hn (hX.symm.trans hquot)
  · have hX : Nat.card X = ordBC 2 (2 ^ n) := by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hSp4.card_eq_lieOrd (by norm_num)
    exact ordA_ne_ordBC_two (n := 3) (by norm_num) le_rfl (by omega)
      ((card_eq_ordA_three_of_isSLn_four h le_rfl).symm.trans hX)

theorem not_nParam_of_isSLn_four_one {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
    (h : IsSLn (Bar2 L) 4 1) (hn : 2 < n) : ¬ NParam L n := by
  intro hN
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  let e' : Bar2 L ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
    e.trans (specialLinearGroupEquivStatedSL 4 F).symm
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) F) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two hF2 (by norm_num)
  haveI : IsSimpleGroup (Bar2 L) := e'.isSimpleGroup
  have hnab : ∃ a b : Bar2 L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two (m := 4) hF2 (by norm_num)
    exact ⟨e'.symm a, e'.symm b, fun h => hab (by simpa using congrArg e' h)⟩
  obtain ⟨⟨hq1, hq2⟩, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  exact not_nParamSingle_of_isSLn_four_one ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩ hn
    (nParamSingle_of_nParam_of_isQuasisimple hN ⟨Group.isPerfect_def.mp hq1, hq2.1⟩)

theorem hinf_flagStabilizer_four_eq_bot_of_card_two (hK : Nat.card K = 2) {I : Set ℕ}
    (hI : I = {2} ∨ I = {1, 2} ∨ I = {1, 3} ∨ I = {2, 3} ∨ I = {1, 2, 3}) :
    Hinf (LinearFlag.flagStabilizer 4 K I) = ⊥ := by
  rw [Hinf_eq_perfectCore]
  refine CFSG.QuasithinUnique.Vol2Native.A312L.perfectCore_eq_bot_of_small hK (by norm_num) ?_
  intro a m h ha hb hno
  have hc : ∀ c ∈ I, ¬ a < c ∨ ¬ c < a + m := fun c hc => not_and_or.mp (hno c hc)
  rcases hI with rfl | rfl | rfl | rfl | rfl
  · have := hc 2 (by simp)
    simp only [Set.mem_singleton_iff] at ha hb
    omega
  · have := hc 1 (by simp)
    have := hc 2 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    omega
  · have := hc 1 (by simp)
    have := hc 3 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    omega
  · have := hc 2 (by simp)
    have := hc 3 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    omega
  · have := hc 1 (by simp)
    have := hc 2 (by simp)
    have := hc 3 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    omega

theorem cuts_four_cases {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 4) :
    I = ∅ ∨ I = {1} ∨ I = {2} ∨ I = {3} ∨ I = {1, 2} ∨ I = {1, 3} ∨ I = {2, 3} ∨
      I = {1, 2, 3} := by
  classical
  have key : ∀ i, i ∈ I ↔ (i = 1 ∧ 1 ∈ I) ∨ (i = 2 ∧ 2 ∈ I) ∨ (i = 3 ∧ 3 ∈ I) := by
    intro i
    constructor
    · intro hi
      obtain ⟨h1, h4⟩ := hI i hi
      interval_cases i <;> simp [hi]
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact h
  have hext : ∀ J : Set ℕ, (∀ i, i ∈ J ↔ (i = 1 ∧ 1 ∈ I) ∨ (i = 2 ∧ 2 ∈ I) ∨ (i = 3 ∧ 3 ∈ I)) →
      I = J := fun J hJ => Set.ext fun i => (key i).trans (hJ i).symm
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I <;> by_cases h3 : 3 ∈ I
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (hext _ fun i => by simp [h1, h2, h3])))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hext _ fun i => by simp [h1, h2, h3])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hext _ fun i => by simp [h1, h2, h3]))))))
  · exact Or.inr (Or.inl (hext _ fun i => by simp [h1, h2, h3]))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hext _ fun i => by simp [h1, h2, h3])))))))
  · exact Or.inr (Or.inr (Or.inl (hext _ fun i => by simp [h1, h2, h3])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hext _ fun i => by simp [h1, h2, h3]))))
  · exact Or.inl (hext _ fun i => by simp [h1, h2, h3])

theorem nParam_eq_of_lieModel_psl4_parabolic {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} {e n : ℕ} (hS : LieModel ↥L .PSL 4 2 e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n)
    (hn : 2 < n) : n = e := by
  obtain ⟨⟨-, he1, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ := by
    rw [← LinearFlag.scalars_eq_center, eq_bot_iff]
    rintro A ⟨c, hc, hA⟩
    rw [Subgroup.mem_bot]
    have hc1 : (c : K) = 1 := by
      have h4 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      have h : ((c : K) + 1) ^ 4 = 0 := by
        have hexp : ((c : K) + 1) ^ 4 = ((c : K) ^ 4 + 1) + 2 * (2 * (c : K) ^ 3 +
            3 * (c : K) ^ 2 + 2 * (c : K)) := by ring
        rw [hexp, h4, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
      exact CharTwo.add_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.mp h)
    apply Subtype.ext
    change (A : Matrix (Fin 4) (Fin 4) K) = 1
    rw [hA, hc1, map_one]
  let ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
    φ.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot))
  obtain ⟨S, hSN⟩ := IsParabolicTwo.comap ψ.symm.toMonoidHom ψ.symm.surjective hpar
  obtain ⟨c, hcS⟩ := uc22sp207_exists_conj_cover (m := 4) (by norm_num) (MonoidHom.id _)
    Function.surjective_id S
  obtain ⟨hcut, hQ⟩ := uc22sp207_comap_eq_flagStabilizer (by norm_num) _ hcS hSN
  set I := LinearFlag.borelOvergroupCuts (((P.subgroupOf L).comap ψ.symm.toMonoidHom).comap
    ((MulAut.conj c).toMonoidHom.comp (MonoidHom.id _)))
  clear_value I
  let φ' : Matrix.SpecialLinearGroup (Fin 4) K ≃* ↥L := (MulAut.conj c).trans ψ.symm
  have hPQ : P.subgroupOf L = (LinearFlag.flagStabilizer 4 K I).map φ'.toMonoidHom := by
    rw [← hQ, Subgroup.comap_comap]
    exact (Subgroup.map_comap_eq_self_of_surjective φ'.surjective _).symm
  obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPL φ' hPQ
  have hQne : Hinf (LinearFlag.flagStabilizer 4 K I) ≠ ⊥ := by
    intro h
    apply hinf
    have hPeq : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
    rw [← hPeq, ← Hinf_map L.subtype, hPQ, Hinf_map_eq_bot φ' _ h, Subgroup.map_bot]
  have he : e = 1 ∨ 2 ≤ e := by omega
  have hK4 : 2 ≤ e → 4 ≤ Nat.card K := fun he2 => by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  have hK2 : e = 1 → Nat.card K = 2 := fun he1 => by rw [hK, he1, pow_one]
  have hsl2 : 2 ≤ e → (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K I)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) → n = e := fun he2 ε =>
    kNshape_holds _ _ n e hN (Or.inl (KTabD.isL2_of_mulEquiv_sl2 he2 hK (χ.trans ε)))
  have hsl3 : (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K I)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) → n = e := fun ε => by
    rcases he with rfl | he2
    · exact nParam_eq_of_isSL3 hN (isSL3_of_mulEquiv_sl3_of_card_two (hK2 rfl) (χ.trans ε))
    · exact nParam_eq_of_mulEquiv_sl3 he2 hK hN (χ.trans ε)
  have hsmall : e = 1 → (I = {2} ∨ I = {1, 2} ∨ I = {1, 3} ∨ I = {2, 3} ∨ I = {1, 2, 3}) →
      False := fun he1 hI => hQne (hinf_flagStabilizer_four_eq_bot_of_card_two (hK2 he1) hI)
  rcases cuts_four_cases hcut with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exfalso
    obtain ⟨ε⟩ := nonempty_bar2_hinf_slFlagStab_four_empty (K := K)
    have h4 : IsSLn (Bar2 (Hinf P)) 4 e :=
      ⟨K, inferInstance, inferInstance, hK,
        ⟨(χ.trans ε).trans (specialLinearGroupEquivStatedSL 4 K)⟩⟩
    rcases he with rfl | he2
    · exact not_nParam_of_isSLn_four_one h4 hn hN
    · exact not_nParam_of_isSLn_four h4 he2 hN
  ·
    obtain ⟨ε⟩ := nonempty_bar2_hinf_slFlagStab_four_one (K := K)
    exact hsl3 ε
  ·
    rcases he with rfl | he2
    · exact (hsmall rfl (Or.inl rfl)).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_slFlagStab_four_two (hK4 he2)
      exact nParam_eq_of_mulEquiv_sl2_prod he2 hK hN (χ.trans ε)
  ·
    obtain ⟨ε⟩ := nonempty_bar2_hinf_slFlagStab_four_three (K := K)
    exact hsl3 ε
  ·
    rcases he with rfl | he2
    · exact (hsmall rfl (Or.inr (Or.inl rfl))).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_slFlagStab_four_one_two (hK4 he2)
      exact hsl2 he2 ε
  ·
    rcases he with rfl | he2
    · exact (hsmall rfl (Or.inr (Or.inr (Or.inl rfl)))).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_slFlagStab_four_one_three (hK4 he2)
      exact hsl2 he2 ε
  ·
    rcases he with rfl | he2
    · exact (hsmall rfl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_slFlagStab_four_two_three (hK4 he2)
      exact hsl2 he2 ε
  ·
    exfalso
    apply hQne
    rw [Hinf_eq_perfectCore, flagStabilizer_four_one_two_three]
    exact (isSolvable_iff_perfectCore_eq_bot _).mp
      (CFSG.QuasithinUnique.Setup.X7a.isSolvable_upperTriangular ⟨e, hK⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
