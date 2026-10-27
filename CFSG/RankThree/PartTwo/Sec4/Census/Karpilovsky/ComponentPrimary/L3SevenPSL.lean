module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.Kit
public import Certificates.Certificate291420
public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

open CFSG.CosetTable CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

abbrev F7 := ZMod 7

@[expose] def mA : Matrix (Fin 3) (Fin 3) F7 := !![1, 0, 0; 0, 6, 0; 0, 0, 6]
@[expose] def mB : Matrix (Fin 3) (Fin 3) F7 := !![6, 0, 0; 0, 1, 0; 0, 0, 6]
@[expose] def mC : Matrix (Fin 3) (Fin 3) F7 := !![2, 1, 3; 2, 2, 2; 3, 1, 2]
@[expose] def mD : Matrix (Fin 3) (Fin 3) F7 := !![2, 4, 6; 4, 2, 1; 5, 2, 2]

@[expose] def mOf (i : ℕ) : Matrix (Fin 3) (Fin 3) F7 := [mA, mB, mC, mD].getD i 1

theorem det_mOf : ∀ i < 4, (mOf i).det = 1 := by decide +kernel

theorem rel_ok : ∀ w ∈ relCodes, ∃ c : F7, c ≠ 0 ∧
    (w.map fun x => mOf (x % 4)).prod = c • (1 : Matrix (Fin 3) (Fin 3) F7) := by
  decide +kernel

@[expose] def gSL (i : Fin 4) : Matrix.SpecialLinearGroup (Fin 3) F7 := ⟨mOf i, det_mOf i i.2⟩

theorem coe_list_prod_gSL (w : List ℕ) :
    ((w.map fun x => gSL ⟨x % 4, Nat.mod_lt _ (by norm_num)⟩).prod :
      Matrix.SpecialLinearGroup (Fin 3) F7).1 = (w.map fun x => mOf (x % 4)).prod := by
  induction w with
  | nil => rfl
  | cons x w ih => simp only [List.map_cons, List.prod_cons, Matrix.SpecialLinearGroup.coe_mul, ih]; rfl

theorem hrel_central : ∀ w ∈ l37Rels, FreeGroup.lift gSL (FreeGroup.mk w) ∈
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F7) := by
  intro w hw
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
  rw [FreeGroup.lift_mk]
  obtain ⟨c, hc, hprod⟩ := rel_ok w0 hw0
  have e : ((List.map (fun x : Fin 4 × Bool => cond x.2 (gSL x.1) (gSL x.1)⁻¹)
      (w0.map fun x => ((⟨x % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4), true))).prod :
      Matrix.SpecialLinearGroup (Fin 3) F7) =
      (w0.map fun x => gSL ⟨x % 4, Nat.mod_lt _ (by norm_num)⟩).prod := by
    simp [List.map_map, Function.comp_def]
  rw [e, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨c, ?_, ?_⟩
  · have hdet := (w0.map fun x => gSL ⟨x % 4, Nat.mod_lt _ (by norm_num)⟩).prod.2
    rw [coe_list_prod_gSL, hprod, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
    simpa using hdet
  · rw [coe_list_prod_gSL, hprod]
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

@[expose] def tData : List (ℕ × ℕ × List ℕ) :=
  [(0, 1, [2, 0, 3, 0, 1, 2, 1, 3, 0, 3, 1, 2, 3, 0, 2]),
   (0, 2, [3, 0, 3, 0, 2, 0, 1, 2, 0, 2, 3, 1, 2, 0, 3]),
   (1, 0, [2, 3, 0, 2, 1, 3, 0, 3, 1, 2, 3, 0, 1, 3, 0, 2, 3]),
   (1, 2, [2, 0, 1, 3, 1, 2, 1, 3, 0, 2, 1, 3, 1, 2, 0, 2, 1]),
   (2, 0, [3, 1, 2, 0, 2, 1, 3, 0, 3, 1, 2, 0, 2, 1, 3, 0]),
   (2, 1, [1, 3, 0, 1, 2, 1, 3, 1, 2, 0, 3, 1, 2, 1, 3, 0, 3])]

theorem tData_ok : ∀ e ∈ tData, ∀ i j : Fin 3, e.1 = i.val → e.2.1 = j.val →
    ((e.2.2.map fun x => mOf (x % 4)).prod : Matrix (Fin 3) (Fin 3) F7) =
      1 + Matrix.single i j (1 : F7) := by
  decide +kernel

theorem tData_find : ∀ i j : Fin 3, i ≠ j → ∃ e ∈ tData, e.1 = i.val ∧ e.2.1 = j.val := by
  decide +kernel

theorem htr_mem : ∀ (i j : Fin 3) (hij : i ≠ j),
    Matrix.SpecialLinearGroup.transvection hij (1 : F7) ∈ Subgroup.closure (Set.range gSL) := by
  intro i j hij
  obtain ⟨⟨i0, j0, w⟩, he, h1, h2⟩ := tData_find i j hij
  simp only at h1 h2
  have hprod := tData_ok _ he i j h1 h2
  simp only at hprod
  have : Matrix.SpecialLinearGroup.transvection hij (1 : F7) =
      (w.map fun x => gSL ⟨x % 4, Nat.mod_lt _ (by norm_num)⟩).prod := by
    apply Subtype.ext
    rw [coe_list_prod_gSL, hprod]
    rfl
  rw [this]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem card_pg_le :
    Finite (PG 4 l37Rels) ∧ Nat.card (PG 4 l37Rels) ≤ 1876896 :=
  Certificates.certificate291420

theorem nonempty_pg_equiv :
    Nonempty (PG 4 l37Rels ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) := by
  obtain ⟨hfin, hcard⟩ := card_pg_le
  exact Coordinator.L37.nonempty_mulEquiv_psl_of_presented l37Rels gSL hrel_central htr_mem hcard

theorem quot_projSL {G : Type*} [Group G] (h : Fin 4 → G)
    (hh : ∀ w ∈ l37Rels, FreeGroup.lift h (FreeGroup.mk w) = 1) {H : Subgroup G}
    (hH : Subgroup.closure (Set.range h) = H) (hne : H ≠ ⊥) :
    ∃ _ : Fact (Nat.Prime 7), Nonempty (↥H ⧸ aschbacherSolvableCore 3 ↥H ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
  Coordinator.L37.exists_quot_mulEquiv_projSL_of_presented l37Rels nonempty_pg_equiv h hh hH hne

theorem lift_eq_one_of_relCodes {G : Type*} [Group G] (y : Fin 4 → G)
    (hy : ∀ w ∈ relCodes, (w.map fun x => y ⟨x % 4, Nat.mod_lt _ (by norm_num)⟩).prod = 1) :
    ∀ w ∈ l37Rels, FreeGroup.lift y (FreeGroup.mk w) = 1 := by
  intro w hw
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
  rw [FreeGroup.lift_mk]
  simpa [List.map_map, Function.comp_def] using hy w0 hw0

theorem nonempty_equiv_closure {G : Type*} [Group G]
    (h : Fin 4 → G) (hh : ∀ w ∈ l37Rels, FreeGroup.lift h (FreeGroup.mk w) = 1)
    {H : Subgroup G} (hH : Subgroup.closure (Set.range h) = H) (hne : H ≠ ⊥) :
    Nonempty (↥H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) := by
  obtain ⟨e⟩ := nonempty_pg_equiv
  set φ : PG 4 l37Rels →* G := PresentedGroup.toGroup (f := h) (by
    intro r hr
    have hr' : r ∈ l37Rels.map FreeGroup.mk := hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr'
    exact hh w hw)
  have hrange : φ.range = H := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure, ← hH,
      ← Set.range_comp]
    congr 2
    funext i
    exact PresentedGroup.toGroup.of _
  have := Coordinator.L37.isSimpleGroup_psl_three_seven
  have hntPG : Nontrivial (PG 4 l37Rels) := e.toEquiv.nontrivial
  have hsimp : IsSimpleGroup (PG 4 l37Rels) :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hker : φ.ker = ⊥ := by
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · exact hk
    · exfalso
      apply hne
      rw [← hrange, eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact (MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top x)) ▸ Subgroup.one_mem ⊥
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  set eH : PG 4 l37Rels ≃* ↥H := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨eH.symm.trans e⟩

theorem card_closure_eq {G : Type*} [Group G] (h : Fin 4 → G)
    (hh : ∀ w ∈ l37Rels, FreeGroup.lift h (FreeGroup.mk w) = 1) {H : Subgroup G}
    (hH : Subgroup.closure (Set.range h) = H) (hne : H ≠ ⊥) : Nat.card H = 1876896 := by
  obtain ⟨e⟩ := nonempty_equiv_closure h hh hH hne
  rw [Nat.card_congr e.toEquiv, Coordinator.L37.card_psl_three_seven]

theorem isSimpleGroup_closure {G : Type*} [Group G]
    (h : Fin 4 → G) (hh : ∀ w ∈ l37Rels, FreeGroup.lift h (FreeGroup.mk w) = 1)
    {H : Subgroup G} (hH : Subgroup.closure (Set.range h) = H) (hne : H ≠ ⊥) :
    IsSimpleGroup ↥H := by
  obtain ⟨e⟩ := nonempty_equiv_closure h hh hH hne
  have := Coordinator.L37.isSimpleGroup_psl_three_seven
  have : Nontrivial ↥H := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
