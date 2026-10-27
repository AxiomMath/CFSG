module

public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup
public import CFSG.LieType.SemisimpleCentralizers.LinearCommutant

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.ClassicalPosition

theorem ggE0Concl_centralizer_generalLinear {N : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (s : GL (Fin N) F) (hs : Odd (orderOf s)) {C : Subgroup (GL (Fin N) F)}
    (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    GGE0Concl (Subgroup.centralizer {s}) C := by
  have hA : (Nat.card (Subgroup.zpowers s) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    intro h
    rw [CharP.cast_eq_zero_iff F 2] at h
    exact (Nat.not_even_iff_odd.mpr hs) (even_iff_two_dvd.mpr h)
  obtain ⟨r, D, hD, hDf, d, hchar, -, ⟨e⟩⟩ :=
    CFSG.LieType.SemisimpleCentralizers.centralizer_mulEquiv_pi_generalLinearGroup
      (Subgroup.zpowers s) hA
  have hcent : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (GL (Fin N) F)) :
      Set (GL (Fin N) F)) = Subgroup.centralizer {s} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hD2 : ∀ k, CharP (D k) 2 := fun k => ringChar.of_eq ((hchar k).trans (ringChar.eq F 2))
  refine ggE0Concl_of_mulEquiv ((MulEquiv.subgroupCongr hcent.symm).trans
    (e.trans Subgroup.topEquiv.symm)) (fun C' hC' => ggE0Concl_pi
      (fun k C'' hC'' => ggE0Concl_top_generalLinear C'' hC'') hC') hC

theorem largeEvenMarking_of_isComponentOf_centralizer_generalLinear {N : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (s : GL (Fin N) F) (hs : Odd (orderOf s)) {C : Subgroup (GL (Fin N) F)}
    (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  have hA : (Nat.card (Subgroup.zpowers s) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    intro h
    rw [CharP.cast_eq_zero_iff F 2] at h
    exact (Nat.not_even_iff_odd.mpr hs) (even_iff_two_dvd.mpr h)
  obtain ⟨r, D, hD, hDf, d, hchar, -, ⟨e⟩⟩ :=
    CFSG.LieType.SemisimpleCentralizers.centralizer_mulEquiv_pi_generalLinearGroup
      (Subgroup.zpowers s) hA
  have hcent : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (GL (Fin N) F)) :
      Set (GL (Fin N) F)) = Subgroup.centralizer {s} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hD2 : ∀ k, CharP (D k) 2 := fun k => ringChar.of_eq ((hchar k).trans (ringChar.eq F 2))
  refine largeEvenMarking_of_isComponentOf_mulEquiv ((MulEquiv.subgroupCongr hcent.symm).trans
    (e.trans Subgroup.topEquiv.symm)) (fun C' hC' => largeEvenMarking_of_isComponentOf_pi
      (fun k C'' hC'' => largeEvenMarking_of_isComponentOf_top_generalLinear hC'') hC') hC

private theorem isGLLift_zpow {U X ι F : Type} [Group U] [Group X] [Finite U] [Fintype ι]
    [DecidableEq ι] [Field F] {j : U →* GL ι F} {ψ : U →* X} (hj : Function.Injective j)
    {s : GL ι F} {b : X} (hs : IsGLLift j ψ s b) (k : ℤ) :
    IsGLLift j ψ (s ^ k) (b ^ k) := by
  induction k using Int.induction_on with
  | zero => simpa using isGLLift_one (j := j) (ψ := ψ)
  | succ i ih =>
      rw [zpow_add_one s (i : ℤ), ← mul_self_zpow b (i : ℤ)]
      exact hs.mul ih
  | pred i ih =>
      have hb : b ^ (-(i : ℤ) - 1) = b⁻¹ * b ^ (-(i : ℤ)) := by
        rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by ring, zpow_add]
        simp
      rw [zpow_sub_one s (-(i : ℤ)), hb]
      exact (hs.inv_of_injective hj).mul ih

private theorem setOf_isGLLift_zpowers_eq {U X ι F : Type} [Group U] [Group X] [Finite U]
    [Fintype ι] [DecidableEq ι] [Field F] {j : U →* GL ι F} {ψ : U →* X}
    (hj : Function.Injective j) {s : GL ι F} {b : X} (hs : IsGLLift j ψ s b) :
    {x : GL ι F | x ∈ Subgroup.zpowers s ∧
      ∃ d ∈ Subgroup.zpowers b, IsGLLift j ψ x d} = (Subgroup.zpowers s : Set (GL ι F)) := by
  ext x
  constructor
  · rintro ⟨hx, -⟩
    exact hx
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨Subgroup.zpow_mem_zpowers s k, b ^ k, Subgroup.zpow_mem_zpowers b k,
      isGLLift_zpow hj hs k⟩

theorem ggE0Comp_PSL (m : ℕ) {F : Type} [Field F] [Finite F] {X : Type} [Group X] [Finite X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X} {s : GL (Fin (m + 1)) F}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b) {C₀ : Subgroup X}
    (hC₀ : IsComponentOf C₀ (ψ.range ⊓ Subgroup.centralizer {b})) :
    ∃ J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F),
      CFSG.Assembly.IsQuasisimple ↥J' ∧
      IsComponentOf (J'.map Matrix.SpecialLinearGroup.toGL) (Subgroup.centralizer {s}) ∧
      J'.map ψ = C₀ := by
  classical
  have hcent : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X) =
      Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hJ : IsComponentOf C₀ (ψ.range ⊓
      Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X)) := by
    rw [hcent]
    exact hC₀
  have hlift : ∀ d ∈ Subgroup.zpowers b, ∃ s' : GL (Fin (m + 1)) F,
      s' ∈ Subgroup.zpowers s ∧ IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' d := by
    intro d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ⟨s ^ k, Subgroup.zpow_mem_zpowers s k,
      isGLLift_zpow Matrix.SpecialLinearGroup.toGL_injective hs k⟩
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective ψ hψ (fun s' => s' ∈ Subgroup.zpowers s) hJ hlift
  have hcentS : Subgroup.centralizer {x : GL (Fin (m + 1)) F | x ∈ Subgroup.zpowers s ∧
      ∃ d ∈ Subgroup.zpowers b, IsGLLift Matrix.SpecialLinearGroup.toGL ψ x d} =
      Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) F)) := by
    rw [setOf_isGLLift_zpowers_eq Matrix.SpecialLinearGroup.toGL_injective hs,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcentS] at hJ'comp
  have hJ'GL : IsComponentOf (J'.map Matrix.SpecialLinearGroup.toGL)
      (((Subgroup.centralizer {s}).comap Matrix.SpecialLinearGroup.toGL).map
        Matrix.SpecialLinearGroup.toGL) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ'comp
      Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
  rw [Subgroup.map_comap_eq] at hJ'GL
  refine ⟨J', hJ'comp.2.2, ?_, hJ'map⟩
  refine (isComponentOf_iff_of_normal_of_commutator_le inf_le_right ?_).mpr hJ'GL
  intro a ha b' hb'
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (Matrix.GeneralLinearGroup.det a) (Matrix.GeneralLinearGroup.det b')]
    group
  · exact mul_mem (mul_mem (mul_mem ha hb') (inv_mem ha)) (inv_mem hb')

theorem isComponentOf_centralizer_statedSL_iff {N : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (s : ↥(CFSG.Open.StatedSL N F)) {C : Subgroup (GL (Fin N) F)} :
    IsComponentOf C (Subgroup.centralizer ({(s : GL (Fin N) F)} : Set (GL (Fin N) F))) ↔
      IsComponentOf C
        ((Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSL N F))).map (CFSG.Open.StatedSL N F).subtype) := by
  have hmap : (Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSL N F))).map (CFSG.Open.StatedSL N F).subtype =
      CFSG.Open.StatedSL N F ⊓ Subgroup.centralizer ({(s : GL (Fin N) F)} : Set (GL (Fin N) F)) := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective (CFSG.Open.StatedSL N F).subtype
      (Subtype.val_injective) (⊤ : Subgroup ↥(CFSG.Open.StatedSL N F)) s
    simpa only [Subgroup.map_top, Subgroup.range_subtype, top_inf_eq, Subgroup.coe_subtype] using h
  rw [hmap]
  exact isComponentOf_iff_of_normal_of_commutator_le inf_le_right (fun a ha b hb => by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_comm (Matrix.GeneralLinearGroup.det a) (Matrix.GeneralLinearGroup.det b)]
      group
    · exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))

theorem largeEvenMarking_of_isComponentOf_centralizer_statedSL {N : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] (s : ↥(CFSG.Open.StatedSL N F)) (hs : Odd (orderOf s))
    {C : Subgroup ↥(CFSG.Open.StatedSL N F)} (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  let e : ↥(Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSL N F))) ≃*
      ↥((Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSL N F))).map (CFSG.Open.StatedSL N F).subtype) :=
    Subgroup.equivMapOfInjective _ _ (Subtype.val_injective)
  refine largeEvenMarking_of_isComponentOf_mulEquiv e ?_ hC
  intro C' hC'
  have hC'' : IsComponentOf C'
      (Subgroup.centralizer ({(s : GL (Fin N) F)} : Set (GL (Fin N) F))) :=
    (isComponentOf_centralizer_statedSL_iff s).mpr hC'
  exact largeEvenMarking_of_isComponentOf_centralizer_generalLinear (s : GL (Fin N) F)
    (by rwa [Subgroup.orderOf_coe]) hC''

theorem ggE0Concl_centralizer_statedSL {N : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (s : ↥(CFSG.Open.StatedSL N F)) (hs : Odd (orderOf s))
    {C : Subgroup ↥(CFSG.Open.StatedSL N F)} (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    GGE0Concl (Subgroup.centralizer {s}) C := by
  have hC' : IsComponentOf (C.map (CFSG.Open.StatedSL N F).subtype)
      ((Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSL N F))).map (CFSG.Open.StatedSL N F).subtype) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (Subtype.val_injective)).mpr hC
  have hC_GL : IsComponentOf (C.map (CFSG.Open.StatedSL N F).subtype)
      (Subgroup.centralizer ({(s : GL (Fin N) F)} : Set (GL (Fin N) F))) :=
    (isComponentOf_centralizer_statedSL_iff s).mpr hC'
  have hGL : GGE0Concl (Subgroup.centralizer ({(s : GL (Fin N) F)} : Set (GL (Fin N) F)))
      (C.map (CFSG.Open.StatedSL N F).subtype) :=
    ggE0Concl_centralizer_generalLinear (s : GL (Fin N) F)
      (by rwa [Subgroup.orderOf_coe]) hC_GL
  have hmono : GGE0Concl ((Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSL N F))).map
      (CFSG.Open.StatedSL N F).subtype) (C.map (CFSG.Open.StatedSL N F).subtype) := by
    refine ggE0Concl_mono ?_ hGL
    rintro x ⟨y, hy, rfl⟩
    have hy' : y * s = s * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (by simpa using hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy'
  exact (ggE0Concl_map_iff (CFSG.Open.StatedSL N F).subtype (Subtype.val_injective)
    (Subgroup.centralizer {s}) C).1 hmono

theorem ggE0Concl_centralizer_statedSL_strong {N : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (s : ↥(CFSG.Open.StatedSL N F)) (hs : Odd (orderOf s))
    {C : Subgroup ↥(CFSG.Open.StatedSL N F)} (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    Subgroup.centralizer {s} ≤ Subgroup.normalizer (C : Set ↥(CFSG.Open.StatedSL N F)) ∧
      LargeEvenMarking ↥C (fun lab _R _ I _F θ => GGChevStTag lab ∧
        ∀ ε ∈ Subgroup.centralizer {s}, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C => (l' : ↥(CFSG.Open.StatedSL N F)) = ε⁻¹ * l * ε) φ) := by
  obtain ⟨hnorm, hact⟩ := ggE0Concl_centralizer_statedSL s hs hC
  exact ⟨hnorm, hact (largeEvenMarking_of_isComponentOf_centralizer_statedSL s hs hC)⟩

end CFSG.StandardType
