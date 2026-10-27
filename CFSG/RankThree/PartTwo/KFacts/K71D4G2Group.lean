module

public import CFSG.RankThree.PartTwo.KFacts.K71D4G2Intertwiner
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.BabyPrereqPerfectAwayFromTwo

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (BaseChange)

@[expose] def d4FoldCartan : Matrix (Fin TwistTag.D4.foldedTag.rank)
    (Fin TwistTag.D4.foldedTag.rank) ℤ :=
  !![2, -1; -3, 2]

@[expose] def d4FoldCartanInv : Matrix (Fin TwistTag.D4.foldedTag.rank)
    (Fin TwistTag.D4.foldedTag.rank) ℤ :=
  !![2, 1; 3, 2]

theorem d4FoldCartan_mul_inv : d4FoldCartan * d4FoldCartanInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem d4_cartan_orbit_sum (a b : Fin TwistTag.D4.foldedTag.rank) :
    ∑ j ∈ Finset.univ.filter (fun j => TwistTag.D4.orbitIndex j = b),
      TwistTag.D4.tag.cartan j (TwistTag.D4.orbitMin a) = d4FoldCartan a b := by
  fin_cases a <;> fin_cases b <;> decide

variable {K : Type} [Field K]

@[expose] def d4TorusParam (e : Fin TwistTag.D4.foldedTag.rank → Kˣ) :
    Fin TwistTag.D4.foldedTag.rank → Kˣ :=
  fun b => ∏ c, e c ^ d4FoldCartanInv b c

theorem cartanChar_d4TorusParam (e : Fin TwistTag.D4.foldedTag.rank → Kˣ)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    cartanChar (fun i => d4TorusParam e (TwistTag.D4.orbitIndex i)) (TwistTag.D4.orbitMin a) =
      e a := by
  unfold cartanChar
  rw [← Finset.prod_fiberwise Finset.univ TwistTag.D4.orbitIndex]
  have h : ∀ c : Fin TwistTag.D4.foldedTag.rank,
      ∏ j ∈ Finset.univ.filter (fun j => TwistTag.D4.orbitIndex j = c),
        d4TorusParam e (TwistTag.D4.orbitIndex j) ^
          TwistTag.D4.tag.cartan j (TwistTag.D4.orbitMin a) =
      d4TorusParam e c ^ d4FoldCartan a c := fun c => by
    rw [← d4_cartan_orbit_sum a c, ← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl fun c _ => h c]
  exact prod_zpow_prod_zpow_of_mul_eq_one d4FoldCartan_mul_inv e a

variable (K)

theorem d4_graphFixedTorus_le_graphFixedRootGroup :
    graphFixedTorus TwistTag.D4 K (RingHom.id K) ≤
      graphFixedRootGroup TwistTag.D4 K (RingHom.id K) := by
  intro h hh
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hl := compat_of_twistHom_rootDiagUnit
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K (RingHom.id K)).1 hhΓ).2
  set W := d4TorusParam (fun c => l (TwistTag.D4.orbitMin c))
  have hb : ∀ i, (fun i => W (TwistTag.D4.orbitIndex i)) (TwistTag.D4.perm i) =
      Units.map (RingHom.id K).toMonoidHom ((fun i => W (TwistTag.D4.orbitIndex i)) i) :=
    fun i => by
      simp only [TwistTag.orbitIndex_perm]
      rfl
  obtain ⟨w, hw⟩ := exists_compatDiag_eq (t := TwistTag.D4) (σ := RingHom.id K)
    (b := fun i => W (TwistTag.D4.orbitIndex i)) hb
  have key : cartanChar (compatDiag TwistTag.D4 (RingHom.id K) w) = l := by
    rw [hw]
    exact eq_of_compat_of_orbitMin (cartanChar_perm hb) hl fun a => cartanChar_d4TorusParam _ a
  rw [← key, ← list_prod_orbitH_eq_rootDiagUnit]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup _ _ _ _

theorem d4_twistedFixedGroup_id_eq_graphFixedRootGroup :
    twistedFixedGroup TwistTag.D4 K (RingHom.id K) =
      graphFixedRootGroup TwistTag.D4 K (RingHom.id K) := by
  refine le_antisymm (fun g hg => ?_) (graphFixedRootGroup_le _ _ _)
  have hg' : g ∈ (twistedFixedGroup TwistTag.D4 K (RingHom.id K) :
      Set (ModGL TwistTag.D4.tag K)) := hg
  rw [coe_twistedFixedGroup_eq_mul (fun x => ⟨x, rfl⟩)] at hg'
  obtain ⟨h, hh, c, hc, rfl⟩ := hg'
  exact mul_mem (d4_graphFixedTorus_le_graphFixedRootGroup K hh) hc

theorem g2LabelRep_injective : Function.Injective g2LabelRep :=
  Function.LeftInverse.injective d4LabelToG2_g2LabelRep

section Inverse

variable (R : Type*) [CommRing R]

@[expose] def d4ToG2Module : RootModule Tag.D4 R →ₗ[R] RootModule Tag.G2 R :=
  Finsupp.lcomapDomain g2LabelRep g2LabelRep_injective

variable {R} in
theorem d4ToG2Module_apply (v : RootModule Tag.D4 R) (a : Label Tag.G2) :
    d4ToG2Module R v a = v (g2LabelRep a) :=
  rfl

theorem d4ToG2Module_comp_g2ToD4Module :
    d4ToG2Module R ∘ₗ g2ToD4Module R = LinearMap.id := by
  ext w a
  simp only [LinearMap.comp_apply, d4ToG2Module_apply, g2ToD4Module_apply,
    d4LabelToG2_g2LabelRep, LinearMap.id_apply]

end Inverse

theorem g2ToD4Module_mem (w : RootModule Tag.G2 K) :
    g2ToD4Module K w ∈ d4GraphFixedModule K := by
  rw [← range_g2ToD4Module]
  exact LinearMap.mem_range_self _ w

variable {K} in
theorem g2ToD4Module_d4ToG2Module {v : RootModule Tag.D4 K} (hv : v ∈ d4GraphFixedModule K) :
    g2ToD4Module K (d4ToG2Module K v) = v := by
  have hv' := apply_d4LabelPerm_of_mem hv
  ext b
  rw [g2ToD4Module_apply, d4ToG2Module_apply]
  rcases g2LabelRep_d4LabelToG2 b with h | h | h
  · rw [h]
  · rw [h, hv']
  · rw [h, hv', hv']

@[expose] def d4RestrictEnd (A : Module.End K (RootModule Tag.D4 K)) :
    Module.End K (RootModule Tag.G2 K) :=
  d4ToG2Module K ∘ₗ A ∘ₗ g2ToD4Module K

variable {K} in
theorem g2ToD4Module_comp_d4RestrictEnd {A : Module.End K (RootModule Tag.D4 K)}
    (hA : ∀ v ∈ d4GraphFixedModule K, A v ∈ d4GraphFixedModule K) :
    g2ToD4Module K ∘ₗ d4RestrictEnd K A = A ∘ₗ g2ToD4Module K :=
  LinearMap.ext fun w => g2ToD4Module_d4ToG2Module (hA _ (g2ToD4Module_mem K w))

theorem d4RestrictEnd_one : d4RestrictEnd K 1 = 1 := by
  change d4ToG2Module K ∘ₗ LinearMap.id ∘ₗ g2ToD4Module K = LinearMap.id
  rw [LinearMap.id_comp, d4ToG2Module_comp_g2ToD4Module]

variable {K} in
theorem d4RestrictEnd_mul (A : Module.End K (RootModule Tag.D4 K))
    {B : Module.End K (RootModule Tag.D4 K)}
    (hB : ∀ v ∈ d4GraphFixedModule K, B v ∈ d4GraphFixedModule K) :
    d4RestrictEnd K (A * B) = d4RestrictEnd K A * d4RestrictEnd K B := by
  refine LinearMap.ext fun w => ?_
  simp only [d4RestrictEnd, LinearMap.comp_apply, Module.End.mul_apply]
  rw [g2ToD4Module_d4ToG2Module (hB _ (g2ToD4Module_mem K w))]

variable {K} in
theorem apply_mem_d4GraphFixedModule_of_commute {A : Module.End K (RootModule Tag.D4 K)}
    (hA : d4DiagramEnd K * A = A * d4DiagramEnd K) {v : RootModule Tag.D4 K}
    (hv : v ∈ d4GraphFixedModule K) : A v ∈ d4GraphFixedModule K := by
  rw [mem_d4GraphFixedModule] at hv ⊢
  rw [← Module.End.mul_apply, hA, Module.End.mul_apply, hv]

@[expose] def d4EndHom : ModGL TwistTag.D4.tag K →* Module.End K (RootModule Tag.D4 K) :=
  Units.coeHom _

theorem d4EndHom_diagramMap : d4EndHom K (diagramMap TwistTag.D4 K) = d4DiagramEnd K :=
  rfl

variable {K} in
theorem d4_diagramMap_mul_of_mem_twistedFixedGroup {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    diagramMap TwistTag.D4 K * g = g * diagramMap TwistTag.D4 K := by
  have h := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K (RingHom.id K)).1 hg).2
  rw [twistHom_apply, show Units.map (entrywiseHom (RingHom.id K)) g = g from
    Units.ext (entrywise_id _)] at h
  calc diagramMap TwistTag.D4 K * g =
        diagramMap TwistTag.D4 K * g * (diagramMap TwistTag.D4 K)⁻¹ * diagramMap TwistTag.D4 K := by
        group
    _ = g * diagramMap TwistTag.D4 K := by rw [h]

variable {K} in
theorem d4_mem_twistedFixedGroup_id_iff {g : ModGL TwistTag.D4.tag K} :
    g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) ↔
      g ∈ adjointGroup TwistTag.D4.tag K ∧
        diagramMap TwistTag.D4 K * g = g * diagramMap TwistTag.D4 K := by
  refine ⟨fun hg => ⟨hg.1, d4_diagramMap_mul_of_mem_twistedFixedGroup hg⟩,
    fun ⟨hC, hP⟩ => ⟨hC, ?_⟩⟩
  change twistHom TwistTag.D4 K (RingHom.id K) g = g
  rw [twistHom_apply, show Units.map (entrywiseHom (RingHom.id K)) g = g from
    Units.ext (entrywise_id _), hP, mul_inv_cancel_right]

variable {K} in
theorem d4DiagramEnd_mul_d4EndHom {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    d4DiagramEnd K * d4EndHom K g = d4EndHom K g * d4DiagramEnd K := by
  have h := congrArg (d4EndHom K) (d4_diagramMap_mul_of_mem_twistedFixedGroup hg)
  rwa [map_mul, map_mul, d4EndHom_diagramMap] at h

variable {K} in
theorem d4EndHom_apply_mem {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K)) {v : RootModule Tag.D4 K}
    (hv : v ∈ d4GraphFixedModule K) : d4EndHom K g v ∈ d4GraphFixedModule K :=
  apply_mem_d4GraphFixedModule_of_commute (d4DiagramEnd_mul_d4EndHom hg) hv

variable {K} in
theorem d4RestrictEnd_mul_inv (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    d4RestrictEnd K (d4EndHom K g) * d4RestrictEnd K (d4EndHom K (g⁻¹ :
      twistedFixedGroup TwistTag.D4 K (RingHom.id K))) = 1 := by
  rw [← d4RestrictEnd_mul _ fun v hv => d4EndHom_apply_mem (g⁻¹).2 hv, ← map_mul,
    ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one, d4RestrictEnd_one]

@[expose] def d4FixedToG2 : twistedFixedGroup TwistTag.D4 K (RingHom.id K) →* ModGL Tag.G2 K where
  toFun g :=
    { val := d4RestrictEnd K (d4EndHom K g)
      inv := d4RestrictEnd K (d4EndHom K (g⁻¹ : twistedFixedGroup TwistTag.D4 K (RingHom.id K)))
      val_inv := d4RestrictEnd_mul_inv g
      inv_val := by
        have h := d4RestrictEnd_mul_inv g⁻¹
        rwa [inv_inv] at h }
  map_one' := Units.ext (by
    change d4RestrictEnd K (d4EndHom K ((1 : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
      ModGL TwistTag.D4.tag K)) = 1
    rw [Subgroup.coe_one, map_one, d4RestrictEnd_one])
  map_mul' g h := Units.ext (by
    change d4RestrictEnd K (d4EndHom K ((g * h : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
      ModGL TwistTag.D4.tag K)) = d4RestrictEnd K (d4EndHom K g) * d4RestrictEnd K (d4EndHom K h)
    rw [Subgroup.coe_mul, map_mul]
    exact d4RestrictEnd_mul _ fun v hv => d4EndHom_apply_mem h.2 hv)

variable {K} in
theorem coe_d4FixedToG2 (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    (d4FixedToG2 K g : Module.End K (RootModule Tag.G2 K)) = d4RestrictEnd K (d4EndHom K g) :=
  rfl

variable {K} in
theorem g2ToD4Module_comp_d4FixedToG2 (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    g2ToD4Module K ∘ₗ (d4FixedToG2 K g : Module.End K (RootModule Tag.G2 K)) =
      d4EndHom K g ∘ₗ g2ToD4Module K :=
  g2ToD4Module_comp_d4RestrictEnd fun _ hv => d4EndHom_apply_mem g.2 hv

@[expose] def g2FoldedIndex : Fin Tag.G2.rank → Fin TwistTag.D4.foldedTag.rank :=
  (![⟨1, by decide⟩, ⟨0, by decide⟩] : Fin 2 → Fin TwistTag.D4.foldedTag.rank)

@[expose] def g2UnfoldIndex : Fin TwistTag.D4.foldedTag.rank → Fin Tag.G2.rank :=
  (![⟨1, by decide⟩, ⟨0, by decide⟩] : Fin 2 → Fin Tag.G2.rank)

theorem g2FoldedIndex_g2UnfoldIndex (a : Fin TwistTag.D4.foldedTag.rank) :
    g2FoldedIndex (g2UnfoldIndex a) = a := by
  fin_cases a <;> rfl

@[expose] def g2OrbitXUnit (j : Fin Tag.G2.rank) (c : K) : ModGL TwistTag.D4.tag K :=
  ((TwistTag.D4.orbitWord (g2FoldedIndex j)).map fun i => xUnit TwistTag.D4.tag K i c).prod

@[expose] def g2OrbitYUnit (j : Fin Tag.G2.rank) (c : K) : ModGL TwistTag.D4.tag K :=
  ((TwistTag.D4.orbitWord (g2FoldedIndex j)).map fun i => yUnit TwistTag.D4.tag K i c).prod

variable {K} in
theorem d4EndHom_g2OrbitXUnit (j : Fin Tag.G2.rank) (c : K) :
    d4EndHom K (g2OrbitXUnit K j c) = g2OrbitX K j c := by
  rw [g2OrbitXUnit, map_list_prod, List.map_map]
  fin_cases j <;> rfl

variable {K} in
theorem d4EndHom_g2OrbitYUnit (j : Fin Tag.G2.rank) (c : K) :
    d4EndHom K (g2OrbitYUnit K j c) = g2OrbitY K j c := by
  rw [g2OrbitYUnit, map_list_prod, List.map_map]
  fin_cases j <;> rfl

variable {K} in
theorem d4_mem_orbitField_id (a : Fin TwistTag.D4.foldedTag.rank) (c : K) :
    c ∈ orbitField TwistTag.D4 K (RingHom.id K) a :=
  mem_orbitField.2 (ringHom_id_pow_apply _ c)

variable {K} in
theorem d4_coe_orbitX_id_eq_prod (a : Fin TwistTag.D4.foldedTag.rank)
    (c : orbitField TwistTag.D4 K (RingHom.id K) a) :
    (orbitX TwistTag.D4 K (RingHom.id K) a c : ModGL TwistTag.D4.tag K) =
      ((TwistTag.D4.orbitWord a).map fun i => xUnit TwistTag.D4.tag K i c).prod := by
  rw [coe_orbitX, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, ringHom_id_pow_apply]

variable {K} in
theorem d4_coe_orbitY_id_eq_prod (a : Fin TwistTag.D4.foldedTag.rank)
    (c : orbitField TwistTag.D4 K (RingHom.id K) a) :
    (orbitY TwistTag.D4 K (RingHom.id K) a c : ModGL TwistTag.D4.tag K) =
      ((TwistTag.D4.orbitWord a).map fun i => yUnit TwistTag.D4.tag K i c).prod := by
  rw [coe_orbitY, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, ringHom_id_pow_apply]

variable {K} in
theorem d4_coe_orbitX_id (a : Fin TwistTag.D4.foldedTag.rank)
    (c : orbitField TwistTag.D4 K (RingHom.id K) a) :
    (orbitX TwistTag.D4 K (RingHom.id K) a c : ModGL TwistTag.D4.tag K) =
      g2OrbitXUnit K (g2UnfoldIndex a) c := by
  rw [d4_coe_orbitX_id_eq_prod, g2OrbitXUnit, g2FoldedIndex_g2UnfoldIndex]

variable {K} in
theorem d4_coe_orbitY_id (a : Fin TwistTag.D4.foldedTag.rank)
    (c : orbitField TwistTag.D4 K (RingHom.id K) a) :
    (orbitY TwistTag.D4 K (RingHom.id K) a c : ModGL TwistTag.D4.tag K) =
      g2OrbitYUnit K (g2UnfoldIndex a) c := by
  rw [d4_coe_orbitY_id_eq_prod, g2OrbitYUnit, g2FoldedIndex_g2UnfoldIndex]

variable {K} in
theorem g2OrbitXUnit_eq_orbitX (j : Fin Tag.G2.rank) (c : K) :
    g2OrbitXUnit K j c = (orbitX TwistTag.D4 K (RingHom.id K) (g2FoldedIndex j)
      ⟨c, d4_mem_orbitField_id _ c⟩ : ModGL TwistTag.D4.tag K) := by
  rw [d4_coe_orbitX_id_eq_prod, g2OrbitXUnit]

variable {K} in
theorem g2OrbitYUnit_eq_orbitY (j : Fin Tag.G2.rank) (c : K) :
    g2OrbitYUnit K j c = (orbitY TwistTag.D4 K (RingHom.id K) (g2FoldedIndex j)
      ⟨c, d4_mem_orbitField_id _ c⟩ : ModGL TwistTag.D4.tag K) := by
  rw [d4_coe_orbitY_id_eq_prod, g2OrbitYUnit]

variable {K} in
theorem g2OrbitXUnit_mem (j : Fin Tag.G2.rank) (c : K) :
    g2OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) := by
  rw [g2OrbitXUnit_eq_orbitX]
  exact graphFixedPosUnipotent_le _ _ _ (orbitX_mem_graphFixedPosUnipotent _ _ _ _)

variable {K} in
theorem g2OrbitYUnit_mem (j : Fin Tag.G2.rank) (c : K) :
    g2OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) := by
  rw [g2OrbitYUnit_eq_orbitY]
  exact graphFixedNegUnipotent_le _ _ _ (orbitY_mem_graphFixedNegUnipotent _ _ _ _)

variable {K}

theorem d4FixedToG2_g2OrbitXUnit (h2 : (2 : K) = 0) (j : Fin Tag.G2.rank) (c : K) :
    d4FixedToG2 K ⟨g2OrbitXUnit K j c, g2OrbitXUnit_mem j c⟩ = xUnit Tag.G2 K j c := by
  refine Units.ext ?_
  rw [coe_d4FixedToG2, coe_xUnit, d4RestrictEnd]
  change d4ToG2Module K ∘ₗ d4EndHom K (g2OrbitXUnit K j c) ∘ₗ g2ToD4Module K = _
  rw [d4EndHom_g2OrbitXUnit, g2OrbitX_comp_g2ToD4Module K h2 j c, ← LinearMap.comp_assoc,
    d4ToG2Module_comp_g2ToD4Module, LinearMap.id_comp]

theorem d4FixedToG2_g2OrbitYUnit (h2 : (2 : K) = 0) (j : Fin Tag.G2.rank) (c : K) :
    d4FixedToG2 K ⟨g2OrbitYUnit K j c, g2OrbitYUnit_mem j c⟩ = yUnit Tag.G2 K j c := by
  refine Units.ext ?_
  rw [coe_d4FixedToG2, coe_yUnit, d4RestrictEnd]
  change d4ToG2Module K ∘ₗ d4EndHom K (g2OrbitYUnit K j c) ∘ₗ g2ToD4Module K = _
  rw [d4EndHom_g2OrbitYUnit, g2OrbitY_comp_g2ToD4Module K h2 j c, ← LinearMap.comp_assoc,
    d4ToG2Module_comp_g2ToD4Module, LinearMap.id_comp]

theorem d4_twistedFixedGroup_id_eq_closure :
    twistedFixedGroup TwistTag.D4 K (RingHom.id K) = Subgroup.closure
      {g | ∃ (j : Fin Tag.G2.rank) (c : K), g = g2OrbitXUnit K j c ∨ g = g2OrbitYUnit K j c} := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [d4_twistedFixedGroup_id_eq_graphFixedRootGroup,
      graphFixedRootGroup_eq_iSup_orbitRankOneGroup (σ := RingHom.id K) (fun x => ⟨x, rfl⟩)]
    refine iSup_le fun a => (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.subset_closure ⟨g2UnfoldIndex a, c, Or.inl (d4_coe_orbitX_id a c)⟩
    · exact Subgroup.subset_closure ⟨g2UnfoldIndex a, c, Or.inr (d4_coe_orbitY_id a c)⟩
  · rintro _ ⟨j, c, rfl | rfl⟩
    exacts [g2OrbitXUnit_mem j c, g2OrbitYUnit_mem j c]

theorem d4FixedToG2_mem_adjointGroup (h2 : (2 : K) = 0)
    (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    d4FixedToG2 K g ∈ adjointGroup Tag.G2 K := by
  set H := (adjointGroup Tag.G2 K).comap (d4FixedToG2 K)
  have hle : twistedFixedGroup TwistTag.D4 K (RingHom.id K) ≤
      H.map (twistedFixedGroup TwistTag.D4 K (RingHom.id K)).subtype := by
    conv_lhs => rw [d4_twistedFixedGroup_id_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, c, rfl | rfl⟩
    · refine ⟨⟨_, g2OrbitXUnit_mem j c⟩, ?_, rfl⟩
      change d4FixedToG2 K ⟨_, g2OrbitXUnit_mem j c⟩ ∈ adjointGroup Tag.G2 K
      rw [d4FixedToG2_g2OrbitXUnit h2]
      exact xUnit_mem_adjointGroup j c
    · refine ⟨⟨_, g2OrbitYUnit_mem j c⟩, ?_, rfl⟩
      change d4FixedToG2 K ⟨_, g2OrbitYUnit_mem j c⟩ ∈ adjointGroup Tag.G2 K
      rw [d4FixedToG2_g2OrbitYUnit h2]
      exact yUnit_mem_adjointGroup j c
  obtain ⟨h, hh, hgh⟩ := hle g.2
  rw [show g = h from Subtype.ext hgh.symm]
  exact hh

theorem adjointGroup_le_range_d4FixedToG2 (h2 : (2 : K) = 0) :
    adjointGroup Tag.G2 K ≤ (d4FixedToG2 K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨j, c, hg | hg⟩
  · rw [show g = xUnit Tag.G2 K j c from Units.ext hg]
    exact ⟨_, d4FixedToG2_g2OrbitXUnit h2 j c⟩
  · rw [show g = yUnit Tag.G2 K j c from Units.ext hg]
    exact ⟨_, d4FixedToG2_g2OrbitYUnit h2 j c⟩

variable (K) in
@[expose] def d4FixedToG2Group (h2 : (2 : K) = 0) :
    twistedFixedGroup TwistTag.D4 K (RingHom.id K) →* adjointGroup Tag.G2 K :=
  (d4FixedToG2 K).codRestrict _ (d4FixedToG2_mem_adjointGroup h2)

theorem d4FixedToG2Group_surjective (h2 : (2 : K) = 0) :
    Function.Surjective (d4FixedToG2Group K h2) := fun g => by
  obtain ⟨x, hx⟩ := adjointGroup_le_range_d4FixedToG2 h2 g.2
  exact ⟨x, Subtype.ext hx⟩

section BaseChange

variable {L : Type} [Field L] (f : K →+* L)

theorem g2ToD4Module_mapRange (w : RootModule Tag.G2 K) :
    g2ToD4Module L (Finsupp.mapRange f f.map_zero w) =
      Finsupp.mapRange f f.map_zero (g2ToD4Module K w) := by
  ext b
  simp only [g2ToD4Module_apply, Finsupp.mapRange_apply]

theorem d4ToG2Module_mapRange (v : RootModule Tag.D4 K) :
    d4ToG2Module L (Finsupp.mapRange f f.map_zero v) =
      Finsupp.mapRange f f.map_zero (d4ToG2Module K v) := by
  ext a
  simp only [d4ToG2Module_apply, Finsupp.mapRange_apply]

theorem baseChange_d4RestrictEnd {A : Module.End K (RootModule Tag.D4 K)}
    {B : Module.End L (RootModule Tag.D4 L)} (h : BaseChange f A B) :
    BaseChange f (d4RestrictEnd K A) (d4RestrictEnd L B) := fun a => by
  simp only [d4RestrictEnd, LinearMap.comp_apply]
  rw [← d4ToG2Module_mapRange, h.apply, ← g2ToD4Module_mapRange, Finsupp.mapRange_single,
    map_one]

theorem baseChange_d4EndHom (g : ModGL TwistTag.D4.tag K) :
    BaseChange f (d4EndHom K g) (d4EndHom L (baseChangeGL f g)) :=
  baseChange_baseChangeEnd f _

theorem d4_baseChangeGL_mem_twistedFixedGroup {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    baseChangeGL f g ∈ twistedFixedGroup TwistTag.D4 L (RingHom.id L) := by
  obtain ⟨hC, hP⟩ := d4_mem_twistedFixedGroup_id_iff.1 hg
  refine d4_mem_twistedFixedGroup_id_iff.2
    ⟨CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup f hC, ?_⟩
  rw [← baseChangeGL_diagramMap f, ← map_mul, hP, map_mul]

theorem d4FixedToG2_baseChangeGL (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    d4FixedToG2 L ⟨baseChangeGL f g, d4_baseChangeGL_mem_twistedFixedGroup f g.2⟩ =
      baseChangeGL f (d4FixedToG2 K g) :=
  Units.ext ((baseChange_d4RestrictEnd f (baseChange_d4EndHom f _)).unique
    (baseChange_baseChangeEnd f _))

end BaseChange

theorem nontrivial_adjointGroup_G2 : Nontrivial (adjointGroup Tag.G2 K) := by
  refine ⟨⟨⟨xUnit Tag.G2 K ⟨0, by decide⟩ 1, xUnit_mem_adjointGroup _ _⟩, 1, fun h => ?_⟩⟩
  have h' : xOp Tag.G2 K ⟨0, by decide⟩ 1 = xOp Tag.G2 K ⟨0, by decide⟩ 0 := by
    rw [xOp_zero]
    exact congrArg (fun g : adjointGroup Tag.G2 K =>
      ((g : ModGL Tag.G2 K) : Module.End K (RootModule Tag.G2 K))) h
  exact one_ne_zero (xOp_injective _ h')

theorem d4FixedToG2Group_injective_of_three_le (h2 : (2 : K) = 0)
    (hK3 : (3 : ℕ∞) ≤ ENat.card K) : Function.Injective (d4FixedToG2Group K h2) := by
  have hC0 : graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom ≤
      twistedFixedGroup TwistTag.D4 K (RingHom.id K) := graphFixedRootGroup_le _ _ _
  set ψ := (d4FixedToG2Group K h2).comp (Subgroup.inclusion hC0)
  have hΓ : ∀ g : twistedFixedGroup TwistTag.D4 K (RingHom.id K),
      (g : ModGL TwistTag.D4.tag K) ∈
        graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom := fun g =>
    (d4_twistedFixedGroup_id_eq_graphFixedRootGroup K).le g.2
  have hψ : Function.Surjective ψ := fun x => by
    obtain ⟨g, rfl⟩ := d4FixedToG2Group_surjective h2 x
    exact ⟨⟨g, hΓ g⟩, rfl⟩
  have hker : ψ.ker = ⊥ := by
    by_contra hne
    have hM : ¬ ψ.ker ≤ Subgroup.center
        (graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom) := by
      rw [center_graphFixedRootGroup_eq_bot (σ := (RingEquiv.refl K).toRingHom)
        (RingEquiv.refl K).surjective]
      exact fun h => hne (le_bot_iff.1 h)
    have := fixed_noncentral_normal_solvable_quotient TwistTag.D4 K (RingEquiv.refl K) ψ.ker hM
    have : Group.IsSolvable (adjointGroup Tag.G2 K) :=
      Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toMonoidHom)
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).surjective
    have := nontrivial_adjointGroup_G2 (K := K)
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (adjointGroup Tag.G2 K)
    rw [generated_group_perfect_away_from_two Tag.G2 K hK3] at hlt
    exact lt_irrefl _ hlt
  intro g g' hgg'
  have hinj := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  have h : (⟨g, hΓ g⟩ : graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom) =
      ⟨g', hΓ g'⟩ := hinj hgg'
  have h' := congrArg (fun x : graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom =>
    (x : ModGL TwistTag.D4.tag K)) h
  exact Subtype.ext h'

theorem d4FixedToG2Group_injective (h2 : (2 : K) = 0) :
    Function.Injective (d4FixedToG2Group K h2) := by
  by_cases hK3 : (3 : ℕ∞) ≤ ENat.card K
  · exact d4FixedToG2Group_injective_of_three_le h2 hK3
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  have hL2 : (2 : L) = 0 := by rw [← map_ofNat f 2, h2, map_zero]
  have hL3 : (3 : ℕ∞) ≤ ENat.card L := by
    rw [ENat.card_eq_top_of_infinite]
    exact le_top
  have hinjL := d4FixedToG2Group_injective_of_three_le hL2 hL3
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hg1 : d4FixedToG2 K g = 1 := congrArg Subtype.val hg
  have hgL : d4FixedToG2Group L hL2
      ⟨baseChangeGL f g, d4_baseChangeGL_mem_twistedFixedGroup f g.2⟩ = 1 := by
    refine Subtype.ext ?_
    change d4FixedToG2 L ⟨baseChangeGL f g, d4_baseChangeGL_mem_twistedFixedGroup f g.2⟩ = 1
    rw [d4FixedToG2_baseChangeGL, hg1, map_one]
  have h1 := hinjL (hgL.trans (map_one _).symm)
  have h1' : baseChangeGL f (g : ModGL TwistTag.D4.tag K) = baseChangeGL f 1 := by
    rw [map_one]
    exact congrArg Subtype.val h1
  exact (Subgroup.mem_bot).2 (Subtype.ext (baseChangeGL_injective f h1'))

variable (K) in
@[expose] def d4FixedG2Equiv (h2 : (2 : K) = 0) :
    twistedFixedGroup TwistTag.D4 K (RingHom.id K) ≃* adjointGroup Tag.G2 K :=
  MulEquiv.ofBijective (d4FixedToG2Group K h2)
    ⟨d4FixedToG2Group_injective h2, d4FixedToG2Group_surjective h2⟩

theorem coe_d4FixedG2Equiv (h2 : (2 : K) = 0)
    (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    (d4FixedG2Equiv K h2 g : ModGL Tag.G2 K) = d4FixedToG2 K g :=
  rfl

theorem even_D4_pure_graph_fixed_group_exact_G2 (hK : ringChar K = 2) :
    twistedFixedGroup TwistTag.D4 K (RingHom.id K) =
      graphFixedRootGroup TwistTag.D4 K (RingHom.id K) ∧
    (∀ g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K), ∀ v ∈ d4GraphFixedModule K,
      (g : Module.End K (RootModule TwistTag.D4.tag K)) v ∈ d4GraphFixedModule K) ∧
    (∀ g : twistedFixedGroup TwistTag.D4 K (RingHom.id K),
      g2ToD4Module K ∘ₗ (d4FixedToG2 K g : Module.End K (RootModule Tag.G2 K)) =
        ((g : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K)) ∘ₗ
          g2ToD4Module K) ∧
    (∀ (j : Fin Tag.G2.rank) (c : K),
      g2OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) ∧
      g2OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K)) ∧
    (∃ Ψ : twistedFixedGroup TwistTag.D4 K (RingHom.id K) ≃* adjointGroup Tag.G2 K,
      (∀ g, (Ψ g : ModGL Tag.G2 K) = d4FixedToG2 K g) ∧
      (∀ (j : Fin Tag.G2.rank) (c : K)
        (hx : g2OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K)),
        (Ψ ⟨_, hx⟩ : ModGL Tag.G2 K) = xUnit Tag.G2 K j c) ∧
      ∀ (j : Fin Tag.G2.rank) (c : K)
        (hy : g2OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K)),
        (Ψ ⟨_, hy⟩ : ModGL Tag.G2 K) = yUnit Tag.G2 K j c) ∧
    ∀ (L : Type) [Field L] (f : K →+* L),
      (∀ g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K),
        baseChangeGL f g ∈ twistedFixedGroup TwistTag.D4 L (RingHom.id L)) ∧
      ∀ (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K))
        (g' : twistedFixedGroup TwistTag.D4 L (RingHom.id L)),
        (g' : ModGL TwistTag.D4.tag L) = baseChangeGL f g →
          d4FixedToG2 L g' = baseChangeGL f (d4FixedToG2 K g) := by
  have : CharP K 2 := ringChar.of_eq hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  refine ⟨d4_twistedFixedGroup_id_eq_graphFixedRootGroup K,
    fun g hg v hv => d4EndHom_apply_mem hg hv, g2ToD4Module_comp_d4FixedToG2,
    fun j c => ⟨g2OrbitXUnit_mem j c, g2OrbitYUnit_mem j c⟩,
    ⟨d4FixedG2Equiv K h2, coe_d4FixedG2Equiv h2, fun j c _ => d4FixedToG2_g2OrbitXUnit h2 j c,
      fun j c _ => d4FixedToG2_g2OrbitYUnit h2 j c⟩,
    fun L _ f => ⟨fun g hg => d4_baseChangeGL_mem_twistedFixedGroup f hg, fun g g' hg' => ?_⟩⟩
  rw [show g' = ⟨baseChangeGL f g, d4_baseChangeGL_mem_twistedFixedGroup f g.2⟩ from
    Subtype.ext hg']
  exact d4FixedToG2_baseChangeGL f g

end CFSG.RankThree.PartTwo.KFacts
