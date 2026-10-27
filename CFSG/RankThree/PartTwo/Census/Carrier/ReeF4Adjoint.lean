module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Table
public import CFSG.LieType.Chevalley.RootOps.CertTools
import CFSG.LieType.Chevalley.RootOps.Cert.F4Simple
import CFSG.LieType.Chevalley.RootOps.Cert.F4Tab

public noncomputable section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

variable {A : Type*} [CommRing A]

theorem dim_F4 : dim .F4 = 52 :=
  rfl

@[expose] def lab (p : Fin 52) : Label .F4 :=
  posLabel p (by rw [dim_F4]; exact p.2)

theorem lab_bijective : Function.Bijective lab :=
  ⟨fun p q h => Fin.ext (posLabel_injective _ _ h), fun b => by
    obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
    exact ⟨⟨p, by rwa [dim_F4] at hp⟩, rfl⟩⟩

@[expose] def labEquiv : Fin 52 ≃ Label .F4 :=
  Equiv.ofBijective lab lab_bijective

theorem posVec_eq_single_lab (p : Fin 52) :
    posVec .F4 A p = Finsupp.single (labEquiv p) 1 :=
  posVec_eq_single (by rw [dim_F4]; exact p.2)

@[expose] def nodeF (i : Fin 4) : Fin Tag.F4.rank :=
  ⟨i, i.2⟩

@[expose] def adOp (g h : Matrix (Fin 26) (Fin 26) A) : Module.End A (RootModule .F4 A) :=
  Finsupp.linearCombination A fun b =>
    ∑ u : Fin 52, coord u (g * bMatR A (labEquiv.symm b) * h) • posVec .F4 A u

theorem adOp_posVec (g h : Matrix (Fin 26) (Fin 26) A) (s : Fin 52) :
    adOp g h (posVec .F4 A s) =
      ∑ u : Fin 52, coord u (g * bMatR A s * h) • posVec .F4 A u := by
  rw [posVec_eq_single_lab, adOp, Finsupp.linearCombination_single, one_smul,
    Equiv.symm_apply_apply]

theorem rootModule_ext {f f' : Module.End A (RootModule .F4 A)}
    (h : ∀ s : Fin 52, f (posVec .F4 A s) = f' (posVec .F4 A s)) : f = f' :=
  ext_posVec fun p hp => h ⟨p, by rwa [dim_F4] at hp⟩

theorem sum_coord_bMatR_smul (s : Fin 52) :
    ∑ u : Fin 52, coord u (bMatR A s) • posVec .F4 A u = posVec .F4 A s := by
  rw [Finset.sum_eq_single s]
  · rw [coord_bMatR s.2 s.2, ite_eq_left rfl, one_smul]
  · intro u _ hu
    rw [coord_bMatR u.2 s.2, ite_eq_right (fun h => hu (Fin.ext h)), zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem coord_combR (v : List (ℕ × ℤ)) (u : Fin 52) :
    coord u (combR A v) = (v.map fun x => (x.2 : A) * coord u (bMatR A x.1)).sum := by
  rw [combR]
  induction v with
  | nil => simp [coord_zero]
  | cons x v ih => rw [List.map_cons, List.sum_cons, coord_add, coord_smul, ih, List.map_cons,
      List.sum_cons]

theorem sum_coord_combR_smul {v : List (ℕ × ℤ)} (hv : ValidVec .F4 v) :
    ∑ u : Fin 52, coord u (combR A v) • posVec .F4 A u = vecOf .F4 A v := by
  induction v with
  | nil => simp [combR, coord_zero]
  | cons x v ih =>
    have hx : x.1 < 52 := by
      have := hv x (List.mem_cons_self ..)
      rwa [dim_F4] at this
    rw [vecOf_cons, ← ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [combR, List.map_cons, List.sum_cons, coord_add, coord_smul, add_smul,
      Finset.sum_add_distrib, ← smul_smul, ← Finset.smul_sum]
    congr 1
    have := sum_coord_bMatR_smul (A := A) ⟨x.1, hx⟩
    exact congrArg ((x.2 : A) • ·) this

abbrev spanW (A : Type*) [CommRing A] : Submodule A (Matrix (Fin 26) (Fin 26) A) :=
  Submodule.span A (Set.range fun u : Fin 52 => bMatR A u)

theorem inSpan_iff_mem {Y : Matrix (Fin 26) (Fin 26) A} : InSpan Y ↔ Y ∈ spanW A := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

theorem bMatR_mem_spanW {p : ℕ} (hp : p < 52) : bMatR A p ∈ spanW A :=
  Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩

theorem combR_mem_spanW {v : List (ℕ × ℤ)} (hv : ValidVec .F4 v) : combR A v ∈ spanW A := by
  induction v with
  | nil => exact Submodule.zero_mem _
  | cons x v ih =>
    have hx : x.1 < 52 := by
      have := hv x (List.mem_cons_self ..)
      rwa [dim_F4] at this
    rw [combR, List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (bMatR_mem_spanW hx))
      (ih fun y hy => hv y (List.mem_cons_of_mem _ hy))

abbrev conjL (g h : Matrix (Fin 26) (Fin 26) A) :
    Matrix (Fin 26) (Fin 26) A →ₗ[A] Matrix (Fin 26) (Fin 26) A :=
  (LinearMap.mulLeft A g).comp (LinearMap.mulRight A h)

theorem conjL_apply (g h Y : Matrix (Fin 26) (Fin 26) A) : conjL g h Y = g * Y * h := by
  rw [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, Matrix.mul_assoc]

theorem mem_spanW_of_basis {g h : Matrix (Fin 26) (Fin 26) A}
    (hb : ∀ u : Fin 52, InSpan (g * bMatR A u * h)) {Y : Matrix (Fin 26) (Fin 26) A}
    (hY : Y ∈ spanW A) : g * Y * h ∈ spanW A := by
  have hle : (spanW A).map (conjL g h) ≤ spanW A := by
    rw [Submodule.map_span_le]
    rintro _ ⟨u, rfl⟩
    rw [conjL_apply, ← inSpan_iff_mem]
    exact hb u
  rw [← conjL_apply]
  exact hle ⟨Y, hY, rfl⟩

@[expose] def normGroup (A : Type*) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 26) A) where
  carrier := {g | ∀ u : Fin 52, InSpan ((g : Matrix (Fin 26) (Fin 26) A) * bMatR A u *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) ∧
    InSpan (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) *
      bMatR A u * (g : Matrix (Fin 26) (Fin 26) A))}
  mul_mem' := by
    intro g h hg hh u
    simp only [Set.mem_ofPred_eq, mul_inv_rev, Units.val_mul] at hg hh ⊢
    constructor
    · rw [inSpan_iff_mem]
      have e : (g : Matrix (Fin 26) (Fin 26) A) * h * bMatR A u *
          (((h⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) =
          g * (h * bMatR A u * (h⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A)) *
            (g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) := by
        simp only [Matrix.mul_assoc]
      rw [e]
      exact mem_spanW_of_basis (fun v => (hg v).1) (inSpan_iff_mem.1 (hh u).1)
    · rw [inSpan_iff_mem]
      have e : ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) *
            bMatR A u * (g * h) =
          (h⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) * bMatR A u * g) * h := by
        simp only [Matrix.mul_assoc]
      rw [e]
      exact mem_spanW_of_basis (fun v => (hh v).2) (inSpan_iff_mem.1 (hg u).2)
  one_mem' := fun u => by
    simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    exact ⟨inSpan_bMatR u, inSpan_bMatR u⟩
  inv_mem' := fun {g} hg u => by
    simp only [Set.mem_ofPred_eq, inv_inv] at hg ⊢
    exact ⟨(hg u).2, (hg u).1⟩

theorem conj_mem_spanW {g : Matrix.GeneralLinearGroup (Fin 26) A} (hg : g ∈ normGroup A)
    {Y : Matrix (Fin 26) (Fin 26) A} (hY : Y ∈ spanW A) :
    (g : Matrix (Fin 26) (Fin 26) A) * Y *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) ∈ spanW A :=
  mem_spanW_of_basis (fun u => (hg u).1) hY

abbrev adConj (g : Matrix.GeneralLinearGroup (Fin 26) A) : Module.End A (RootModule .F4 A) :=
  adOp (g : Matrix (Fin 26) (Fin 26) A)
    ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)

theorem adConj_one : adConj (1 : Matrix.GeneralLinearGroup (Fin 26) A) = 1 := by
  refine rootModule_ext fun s => ?_
  rw [adOp_posVec]
  simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  rw [sum_coord_bMatR_smul, Module.End.one_apply]

theorem adConj_mul (g : Matrix.GeneralLinearGroup (Fin 26) A)
    {h : Matrix.GeneralLinearGroup (Fin 26) A} (hh : h ∈ normGroup A) :
    adConj (g * h) = adConj g * adConj h := by
  refine rootModule_ext fun s => ?_
  rw [Module.End.mul_apply, adOp_posVec (h : Matrix (Fin 26) (Fin 26) A), map_sum]
  simp only [map_smul, adOp_posVec]
  set c : Fin 52 → A := fun u => coord u ((h : Matrix (Fin 26) (Fin 26) A) * bMatR A s *
    ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) with hc
  have hspan := ((hh s).1).eq_sum
  have e : ((g * h : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) *
      bMatR A s * (((g * h)⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) =
      ∑ u, c u • ((g : Matrix (Fin 26) (Fin 26) A) * bMatR A u *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) := by
    rw [mul_inv_rev, Units.val_mul, Units.val_mul]
    have e1 : (g : Matrix (Fin 26) (Fin 26) A) * h * bMatR A s *
        (((h⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) =
        g * (h * bMatR A s * (h⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A)) *
          (g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) := by
      simp only [Matrix.mul_assoc]
    rw [e1, hspan, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  simp only [coord_sum, coord_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [smul_smul]

@[expose] def adHom (A : Type*) [CommRing A] : normGroup A →* Module.End A (RootModule .F4 A) where
  toFun g := adConj (g : Matrix.GeneralLinearGroup (Fin 26) A)
  map_one' := adConj_one
  map_mul' g h := adConj_mul (g : Matrix.GeneralLinearGroup (Fin 26) A) h.2

theorem adHom_apply (g : normGroup A) :
    adHom A g = adConj (g : Matrix.GeneralLinearGroup (Fin 26) A) :=
  rfl

@[expose] def adUnits (K : Type*) [Field K] : normGroup K →* ModGL .F4 K :=
  (adHom K).toHomUnits

theorem coe_adUnits {K : Type*} [Field K] (g : normGroup K) :
    ((adUnits K g : ModGL .F4 K) : Module.End K (RootModule .F4 K)) =
      adConj (g : Matrix.GeneralLinearGroup (Fin 26) K) :=
  rfl

abbrev rootPoint (k : Fin 4 ⊕ Fin 4) (t : A) : Matrix.GeneralLinearGroup (Fin 26) A :=
  (TauCeti.F4ShortRoot.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
    Matrix.GeneralLinearGroup (Fin 26) A)

theorem validVec_colOf (k : Fin 4 ⊕ Fin 4) (j : ℕ) (hj : j ∈ [1, 2, 3]) (s : ℕ) :
    ValidVec .F4 (colOf (entries .F4 (genRoot k) j) s) := by
  have hlt : genRoot k < Tag.F4.rootCertificate.roots.length := by
    rcases k with i | i <;> fin_cases i <;> decide
  exact (validEntries_of_validB (validB_of_allValid f4_allValid hlt hj)).colOf s

theorem conj_rootPoint_inSpan (k : Fin 4 ⊕ Fin 4) (t : A) (s : Fin 52) :
    InSpan (rootPointMat k t * bMatR A s * rootPointMat k (-t)) := by
  rw [inSpan_iff_mem, conj_rootPoint k t s.2]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (bMatR_mem_spanW s.2)
    (Submodule.smul_mem _ _ (combR_mem_spanW (validVec_colOf k 1 (by simp) s))))
    (Submodule.smul_mem _ _ (combR_mem_spanW (validVec_colOf k 2 (by simp) s))))
    (Submodule.smul_mem _ _ (combR_mem_spanW (validVec_colOf k 3 (by simp) s)))

theorem rootPoint_mem_normGroup (k : Fin 4 ⊕ Fin 4) (t : A) : rootPoint k t ∈ normGroup A := by
  intro u
  rw [coe_rootPoint_inv]
  refine ⟨conj_rootPoint_inSpan k t u, ?_⟩
  have h := conj_rootPoint_inSpan k (-t) u
  rwa [neg_neg] at h

theorem adConj_rootPoint_posVec (k : Fin 4 ⊕ Fin 4) (t : A) (s : Fin 52) :
    adConj (rootPoint k t) (posVec .F4 A s) =
      posVec .F4 A s + t • vecOf .F4 A (colOf (entries .F4 (genRoot k) 1) s) +
        t ^ 2 • vecOf .F4 A (colOf (entries .F4 (genRoot k) 2) s) +
        t ^ 3 • vecOf .F4 A (colOf (entries .F4 (genRoot k) 3) s) := by
  rw [adOp_posVec, coe_rootPoint_inv, conj_rootPoint k t s.2]
  simp only [coord_add, coord_smul, add_smul, Finset.sum_add_distrib, ← smul_smul,
    ← Finset.smul_sum]
  rw [sum_coord_bMatR_smul, sum_coord_combR_smul (validVec_colOf k 1 (by simp) s),
    sum_coord_combR_smul (validVec_colOf k 2 (by simp) s),
    sum_coord_combR_smul (validVec_colOf k 3 (by simp) s)]

theorem simpleRow_F4 (i : Fin 4) : simpleRow .F4 (nodeF i) = true := by
  fin_cases i
  exacts [f4_simpleRow_0, f4_simpleRow_1, f4_simpleRow_2, f4_simpleRow_3]

theorem adConj_rootPoint_inl (i : Fin 4) (t : A) :
    adConj (rootPoint (.inl i) t) = xOp .F4 A (nodeF i) t := by
  refine rootModule_ext fun s => ?_
  rw [adConj_rootPoint_posVec, xOp_eq_sum_xCoeff]
  have hs : (s : ℕ) < dim .F4 := by rw [dim_F4]; exact s.2
  have hx : ∀ j, 1 ≤ j → j ≤ 3 → xCoeff .F4 A (nodeF i) j (posVec .F4 A s) =
      vecOf .F4 A (colOf (entries .F4 (genRoot (.inl i)) j) s) := fun j h1 h3 => by
    rw [← entriesOp_eq_xCoeff (simpleRow_spec (simpleRow_F4 i) h1 h3).1, entriesOp_posVec _ hs]
    rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, LinearMap.add_apply,
    LinearMap.smul_apply, zero_add, pow_zero, one_smul, pow_one, xCoeff_zero,
    Module.End.one_apply]
  rw [hx 1 le_rfl (by norm_num), hx 2 (by norm_num) (by norm_num), hx 3 (by norm_num) le_rfl]

theorem adConj_rootPoint_inr (i : Fin 4) (t : A) :
    adConj (rootPoint (.inr i) t) = yOp .F4 A (nodeF i) t := by
  refine rootModule_ext fun s => ?_
  rw [adConj_rootPoint_posVec, yOp_eq_sum_yCoeff]
  have hs : (s : ℕ) < dim .F4 := by rw [dim_F4]; exact s.2
  have hy : ∀ j, 1 ≤ j → j ≤ 3 → yCoeff .F4 A (nodeF i) j (posVec .F4 A s) =
      vecOf .F4 A (colOf (entries .F4 (genRoot (.inr i)) j) s) := fun j h1 h3 => by
    rw [← entriesOp_eq_yCoeff (simpleRow_spec (simpleRow_F4 i) h1 h3).2, entriesOp_posVec _ hs]
    rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, LinearMap.add_apply,
    LinearMap.smul_apply, zero_add, pow_zero, one_smul, pow_one, yCoeff_zero,
    Module.End.one_apply]
  rw [hy 1 le_rfl (by norm_num), hy 2 (by norm_num) (by norm_num), hy 3 (by norm_num) le_rfl]

end CFSG.TauCetiBridge.ReeF4
