module

public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharStab
public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  Matrix

variable {Ω : Type} [Field Ω]

variable (Ω) in
@[expose] def v0Stab : Subgroup (ModGL Tag.D4 Ω) where
  carrier := {g | ∀ m ∈ d4A2Module Ω,
    (g : Module.End Ω (RootModule Tag.D4 Ω)) m ∈ d4A2Module Ω ∧
      ((g⁻¹ : ModGL Tag.D4 Ω) : Module.End Ω (RootModule Tag.D4 Ω)) m ∈ d4A2Module Ω}
  mul_mem' {g h} hg hh m hm := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Module.End.mul_apply]
      exact (hg _ (hh m hm).1).1
    · rw [_root_.mul_inv_rev, Units.val_mul, Module.End.mul_apply]
      exact (hh _ (hg m hm).2).2
  one_mem' m hm := by
    rw [inv_one, Units.val_one, Module.End.one_apply]
    exact ⟨hm, hm⟩
  inv_mem' {g} hg m hm := by
    rw [inv_inv]
    exact ⟨(hg m hm).2, (hg m hm).1⟩

theorem apply_d4A2Vec_of_mem {g : ModGL Tag.D4 Ω} (hg : g ∈ v0Stab Ω) (j : Fin 3) :
    (g : Module.End Ω (RootModule Tag.D4 Ω)) (d4A2Vec Ω j) = ∑ i, d4A2Mat g i j • d4A2Vec Ω i :=
  eq_sum_of_mem_d4A2Module ((hg _ (d4A2Vec_mem j)).1)

theorem d4A2Mat_mul_of_mem {g h : ModGL Tag.D4 Ω} (hh : h ∈ v0Stab Ω) :
    d4A2Mat (g * h) = d4A2Mat g * d4A2Mat h := by
  ext i j
  rw [d4A2Mat, Matrix.of_apply, Units.val_mul, Module.End.mul_apply, apply_d4A2Vec_of_mem hh,
    map_sum, Finsupp.finsetSum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

variable (Ω) in
@[expose] def v0Rep : v0Stab Ω →* GL (Fin 3) Ω where
  toFun g := ⟨d4A2Mat (g : ModGL Tag.D4 Ω), d4A2Mat ((g⁻¹ : v0Stab Ω) : ModGL Tag.D4 Ω),
    by rw [← d4A2Mat_mul_of_mem (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, d4A2Mat_one],
    by rw [← d4A2Mat_mul_of_mem g.2, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, d4A2Mat_one]⟩
  map_one' := Units.ext d4A2Mat_one
  map_mul' g h := Units.ext (d4A2Mat_mul_of_mem h.2)

theorem rootDiag_d4A2Vec (b : Fin Tag.D4.rank → Ωˣ) (k : Fin 3) :
    rootDiag b (d4A2Vec Ω k) = ((rootChar b (d4A2Weight k) : Ωˣ) : Ω) • d4A2Vec Ω k :=
  rootDiag_single b (d4A2Label k)

theorem rootDiag_mem_d4A2Module (b : Fin Tag.D4.rank → Ωˣ) {m : RootModule Tag.D4 Ω}
    (hm : m ∈ d4A2Module Ω) : rootDiag b m ∈ d4A2Module Ω := by
  rw [eq_sum_of_mem_d4A2Module hm, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul, rootDiag_d4A2Vec]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (d4A2Vec_mem k))

theorem rootDiagUnit_mem_v0Stab (b : Fin Tag.D4.rank → Ωˣ) : rootDiagUnit Tag.D4 b ∈ v0Stab Ω :=
  fun _ hm => ⟨rootDiag_mem_d4A2Module b hm, rootDiag_mem_d4A2Module b⁻¹ hm⟩

theorem subsystemGroup_le_v0Stab : subsystemGroup Tag.D4 Ω d4SuppA2 ≤ v0Stab Ω := fun _ hg _ hm =>
  ⟨mem_d4A2Module_of_mem hg hm, mem_d4A2Module_of_mem (inv_mem hg) hm⟩

theorem d4A2Mat_rootDiagUnit (b : Fin Tag.D4.rank → Ωˣ) :
    d4A2Mat (rootDiagUnit Tag.D4 b) =
      Matrix.diagonal fun k => ((rootChar b (d4A2Weight k) : Ωˣ) : Ω) := by
  ext i j
  rw [d4A2Mat, Matrix.of_apply, show ((rootDiagUnit Tag.D4 b : ModGL Tag.D4 Ω) :
    Module.End Ω (RootModule Tag.D4 Ω)) = rootDiag b from rfl, rootDiag_d4A2Vec,
    Finsupp.smul_apply, d4A2Vec_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

theorem exists_d4A2TorusElt_of_diagonal {u : ModGL Tag.D4 Ω}
    (hu : u ∈ subsystemGroup Tag.D4 Ω d4SuppA2) {d : Fin 3 → Ω}
    (hd : d4A2Mat u = Matrix.diagonal d) : ∃ t s : Ωˣ, u = d4A2TorusElt t s := by
  have hdet : d 0 * d 1 * d 2 = 1 := by
    have h := det_d4A2Mat hu
    rw [hd, Matrix.det_diagonal, Fin.prod_univ_three] at h
    exact h
  have h0 : d 0 ≠ 0 := fun h => by rw [h, zero_mul, zero_mul] at hdet; exact zero_ne_one hdet
  have h1 : d 1 ≠ 0 := fun h => by rw [h, mul_zero, zero_mul] at hdet; exact zero_ne_one hdet
  have h2 : d 2 ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  set t : Ωˣ := Units.mk0 (d 0) h0
  set s : Ωˣ := Units.mk0 (d 0 * d 1) (mul_ne_zero h0 h1)
  refine ⟨t, s, ?_⟩
  have hmem := d4A2TorusElt_mem (K := Ω) t s
  have hrep : d4A2Rep Ω ⟨u, hu⟩ = d4A2Rep Ω ⟨d4A2TorusElt t s, hmem⟩ := by
    apply Subtype.ext
    rw [coe_d4A2Rep, coe_d4A2Rep, hd, d4A2Mat_d4A2TorusElt]
    congr 1
    funext k
    fin_cases k
    · rfl
    · change d 1 = ((t⁻¹ * s : Ωˣ) : Ω)
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
      field_simp
    · change d 2 = ((s⁻¹ : Ωˣ) : Ω)
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
      linear_combination hdet
  exact congrArg Subtype.val (d4A2Rep_injective hrep)

theorem exists_rootDiagUnit_eq_d4A2TorusElt (t s : Ωˣ) :
    ∃ c : Fin Tag.D4.rank → Ωˣ, d4A2TorusElt t s = rootDiagUnit Tag.D4 c := by
  refine ⟨(fun j => t ^ Tag.D4.cartan 0 j) * (fun j => s ^ Tag.D4.cartan 2 j), ?_⟩
  rw [d4A2TorusElt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, rootDiagUnit_mul]

theorem exists_rootDiagUnit_of_d4A2Mat_scalar (b : Fin Tag.D4.rank → Ωˣ) {u : ModGL Tag.D4 Ω}
    (hu : u ∈ subsystemGroup Tag.D4 Ω d4SuppA2) {r : Ω}
    (hr : d4A2Mat (rootDiagUnit Tag.D4 b * u) = Matrix.scalar (Fin 3) r) :
    ∃ c : Fin Tag.D4.rank → Ωˣ, rootDiagUnit Tag.D4 b * u = rootDiagUnit Tag.D4 c ∧
      c 0 = 1 ∧ c 2 = 1 := by
  have hdiag : d4A2Mat u = Matrix.diagonal fun k =>
      r * (((rootChar b (d4A2Weight k))⁻¹ : Ωˣ) : Ω) := by
    have h := hr
    rw [d4A2Mat_mul_of_mem (subsystemGroup_le_v0Stab hu), d4A2Mat_rootDiagUnit] at h
    have hinv : Matrix.diagonal (fun k => (((rootChar b (d4A2Weight k))⁻¹ : Ωˣ) : Ω)) *
        Matrix.diagonal (fun k => ((rootChar b (d4A2Weight k) : Ωˣ) : Ω)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one using 2
      funext k
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc d4A2Mat u = Matrix.diagonal (fun k => (((rootChar b (d4A2Weight k))⁻¹ : Ωˣ) : Ω)) *
          (Matrix.diagonal (fun k => ((rootChar b (d4A2Weight k) : Ωˣ) : Ω)) * d4A2Mat u) := by
          rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = _ := by
          rw [h, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
          congr 1
          funext k
          ring
  obtain ⟨t, s, rfl⟩ := exists_d4A2TorusElt_of_diagonal hu hdiag
  obtain ⟨c₀, hc₀⟩ := exists_rootDiagUnit_eq_d4A2TorusElt t s
  refine ⟨b * c₀, by rw [hc₀, rootDiagUnit_mul], ?_⟩
  rw [hc₀, ← rootDiagUnit_mul, d4A2Mat_rootDiagUnit, Matrix.scalar_apply] at hr
  have hk : ∀ k, ((rootChar (b * c₀) (d4A2Weight k) : Ωˣ) : Ω) = r := fun k => by
    have := congrFun (congrFun hr k) k
    rwa [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at this
  obtain ⟨e0, e2⟩ := single_eq_d4A2Weight_sub
  refine ⟨?_, ?_⟩
  · rw [← rootChar_single_D4 (b * c₀) 0, e0, rootChar_sub]
    exact Units.ext (by rw [Units.val_mul, Units.val_inv_eq_inv_val, hk, hk, mul_inv_cancel₀ (by
      intro h0
      have := hk 0
      rw [h0] at this
      exact (Units.ne_zero _) this), Units.val_one])
  · rw [← rootChar_single_D4 (b * c₀) 2, e2, rootChar_sub]
    exact Units.ext (by rw [Units.val_mul, Units.val_inv_eq_inv_val, hk, hk, mul_inv_cancel₀ (by
      intro h0
      have := hk 0
      rw [h0] at this
      exact (Units.ne_zero _) this), Units.val_one])

theorem rootDiagUnit_commute_of_mem_subsystemGroup {c : Fin Tag.D4.rank → Ωˣ} (h0 : c 0 = 1)
    (h2 : c 2 = 1) {u : ModGL Tag.D4 Ω} (hu : u ∈ subsystemGroup Tag.D4 Ω d4SuppA2) :
    rootDiagUnit Tag.D4 c * u = u * rootDiagUnit Tag.D4 c := by
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation Tag.D4 Ω c
  have hc : ∀ i ∈ d4SuppA2, c i = 1 := fun i hi => by
    rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
    · exact h0
    · exact h2
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, a, rfl | rfl⟩ := hg
    · have := hx i a
      rw [hc i hi, Units.val_one, one_mul] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    · have := hy i a
      rw [hc i hi, inv_one, Units.val_one, one_mul] at this
      exact mul_inv_eq_iff_eq_mul.mp this
  | one => rw [mul_one, one_mul]
  | mul g g' _ _ ihg ihg' =>
    rw [← mul_assoc, ihg, mul_assoc, ihg', mul_assoc]
  | inv g _ ihg =>
    exact ((show Commute _ _ from ihg).inv_right).eq

theorem rootDiagUnit_commute_of_mem {c : Fin Tag.D4.rank → Ωˣ} (h0 : c 0 = 1) (h2 : c 2 = 1)
    {t u : ModGL Tag.D4 Ω} (ht : t ∈ torusGroup Tag.D4 Ω)
    (hu : u ∈ subsystemGroup Tag.D4 Ω d4SuppA2) :
    rootDiagUnit Tag.D4 c * (t * u) = t * u * rootDiagUnit Tag.D4 c := by
  rw [← mul_assoc, rootDiagUnit_mul_comm_of_mem_torusGroup c ht, mul_assoc,
    rootDiagUnit_commute_of_mem_subsystemGroup h0 h2 hu, mul_assoc]

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
