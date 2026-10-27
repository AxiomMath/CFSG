module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

section Tail

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  {r : ℕ} {qA : QuadraticForm K A}

theorem tail_overgroup_stabilizers (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))}
    (hMG : M ≤ orthElementaryGroup (quadTail r qA)) (hBM : tailBorel r qA ≤ M) :
    M = orthElementaryGroup (quadTail r qA) ⊓
      ⨅ i ∈ {i : Fin r | tailWeylElt r qA a₀ i ∉ M},
        MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
          (tailFlag K A r (i + 1)) := by
  set J : Set (Fin r) := {i : Fin r | tailWeylElt r qA a₀ i ∉ M} with hJ
  set M' := orthElementaryGroup (quadTail r qA) ⊓
      ⨅ i ∈ J, MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
        (tailFlag K A r (i + 1)) with hM'
  have hM'G : M' ≤ orthElementaryGroup (quadTail r qA) := inf_le_left
  have hBM' : tailBorel r qA ≤ M' := by
    intro b hb
    refine Subgroup.mem_inf.2 ⟨tailBorel_le hb, ?_⟩
    simp only [Subgroup.mem_iInf]
    intro i _
    exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
      ((mem_tailBorel.1 hb).2 _ (by omega) (by have := i.isLt; omega))
  refine le_antisymm ?_ ?_
  ·
    rw [eq_closure_of_tailBorel_le hani ha₀ hMG hBM, Subgroup.closure_le]
    rintro _ (hb | ⟨j, hj, rfl⟩)
    · exact hBM' hb
    · refine Subgroup.mem_inf.2 ⟨tailWeylElt_mem a₀ j, ?_⟩
      simp only [Subgroup.mem_iInf]
      intro i hi
      refine MulAction.mem_stabilizer_iff.2 ((tailWeylElt_smul_tailFlag hani ha₀ i j).2 ?_)
      rintro rfl
      exact hi hj
  ·
    rw [eq_closure_of_tailBorel_le hani ha₀ hM'G hBM', Subgroup.closure_le]
    rintro _ (hb | ⟨i, hi, rfl⟩)
    · exact hBM hb
    · by_contra hni
      have hiJ : i ∈ J := hni
      have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hi).2 i)
      have h2 := Subgroup.mem_iInf.1 h1 hiJ
      exact ((tailWeylElt_smul_tailFlag hani ha₀ i i).1 (MulAction.mem_stabilizer_iff.1 h2)) rfl

theorem tail_overgroup_ne_iff (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))}
    (hMG : M ≤ orthElementaryGroup (quadTail r qA)) (hBM : tailBorel r qA ≤ M) :
    M ≠ orthElementaryGroup (quadTail r qA) ↔ ∃ i : Fin r, tailWeylElt r qA a₀ i ∉ M := by
  constructor
  · intro hne
    by_contra h
    push Not at h
    apply hne
    refine le_antisymm hMG ?_
    rw [orthogonal_geometry_tail_Borel_Weyl_generation hani ha₀, Subgroup.closure_le]
    rintro _ (hb | ⟨j, rfl⟩)
    · exact hBM hb
    · exact h j
  · rintro ⟨i, hi⟩ hMeq
    exact hi (hMeq ▸ tailWeylElt_mem a₀ i)

end Tail

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise
open Matrix

section Helpers

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem map_symm_map_equiv {V' : Type*} [AddCommGroup V'] [Module K V'] (e : V ≃ₗ[K] V')
    (X : Submodule K V) : (X.map e.toLinearMap).map e.symm.toLinearMap = X := by
  rw [← Submodule.map_comp]
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id :=
    LinearMap.ext fun v => e.symm_apply_apply v
  rw [h, Submodule.map_id]

theorem map_map_symm_equiv {V' : Type*} [AddCommGroup V'] [Module K V'] (e : V ≃ₗ[K] V')
    (X : Submodule K V') : (X.map e.symm.toLinearMap).map e.toLinearMap = X := by
  rw [← Submodule.map_comp]
  have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun v => e.apply_symm_apply v
  rw [h, Submodule.map_id]

theorem map_fix_conj (G T : V ≃ₗ[K] V) (F : Submodule K V) :
    F.map ((G⁻¹ * T * G : V ≃ₗ[K] V) : V →ₗ[K] V) = F ↔
      (F.map G.toLinearMap).map T.toLinearMap = F.map G.toLinearMap := by
  have hmul : ((G⁻¹ * T * G : V ≃ₗ[K] V) : V →ₗ[K] V) =
      G.symm.toLinearMap.comp (T.toLinearMap.comp G.toLinearMap) := LinearMap.ext fun v => rfl
  have h1 : F.map ((G⁻¹ * T * G : V ≃ₗ[K] V) : V →ₗ[K] V) =
      ((F.map G.toLinearMap).map T.toLinearMap).map G.symm.toLinearMap := by
    rw [hmul, Submodule.map_comp, Submodule.map_comp]
  rw [h1]
  constructor
  · intro h
    calc (F.map G.toLinearMap).map T.toLinearMap
        = (((F.map G.toLinearMap).map T.toLinearMap).map G.symm.toLinearMap).map G.toLinearMap :=
          (map_map_symm_equiv G _).symm
      _ = F.map G.toLinearMap := by rw [h]
  · intro h
    rw [h, map_symm_map_equiv]

theorem map_eq_iff_forall [FiniteDimensional K V] (e : V ≃ₗ[K] V) (W : Submodule K V) :
    W.map e.toLinearMap = W ↔ ∀ w ∈ W, e w ∈ W := by
  constructor
  · intro h w hw
    rw [← h]
    exact Submodule.mem_map_of_mem hw
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.2 fun w hw => h w hw) ?_
    exact LinearEquiv.finrank_map_eq e W

end Helpers

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] (b c : K)

abbrev omegaV0 (K : Type) [Field K] : Type := (Fin (4 - 1) ⊕ Fin (4 - 1) → K) × (Fin 2 → K)

noncomputable abbrev omegaG0 (K : Type) [Field K] (b c : K) :
    Subgroup (omegaV0 K ≃ₗ[K] omegaV0 K) :=
  orthElementaryGroup (quadTail (4 - 1) (minusTailForm K b c))

theorem exists_stab_family_omega (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {Γ : Subgroup (GL (Fin (2 * 4)) K)}
    (hΓ : Γ = StatedOmega ⇑(coordinateQuadMinus 4 K (by norm_num) b c))
    (S₀ : Sylow 2 Γ) (N : Subgroup Γ) (hN : Subgroup.normalizer ((S₀ : Subgroup Γ) : Set Γ) ≤ N)
    (hne : N ≠ ⊤) :
    ∃ 𝒲 : Set (Submodule K (Fin (2 * 4) → K)), 𝒲.Nonempty ∧
      (∀ W ∈ 𝒲, W ≠ ⊥ ∧ ∀ x ∈ W, coordinateQuadMinus 4 K (by norm_num) b c x = 0) ∧
      ∀ y : Γ, y ∈ N ↔ ∀ W ∈ 𝒲, ∀ w ∈ W,
        (((y : Γ) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w ∈ W := by
  subst hΓ
  classical
  have h14 : (1 : ℕ) ≤ 4 := by norm_num
  have hE := commutator_coordinateQuadMinus 4 K b c (le_refl 4) hirr
  let ψ : (quadTail (4 - 1) (minusTailForm K b c)).IsometryEquiv
      (coordinateQuadMinus 4 K (by norm_num) b c) :=
    (minusTailIsometry 4 K b c).trans (coordinateMinusIsometry 4 K (by norm_num) b c)
  let Φ : StatedOmega ⇑(coordinateQuadMinus 4 K (by norm_num) b c) ≃* omegaG0 K b c :=
    tailOmegaEquiv ψ rfl hE
  have hani := anisotropic_minusTailForm hirr
  have hreg := nondegenerate_minusTailForm hirr
  have hm : Module.finrank K (Fin 2 → K) = 1 ∨ Module.finrank K (Fin 2 → K) = 2 :=
    Or.inr finrank_fin_two_fun
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨U, hU⟩, hNU, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2)
    (by norm_num : 3 ≤ 4 - 1) hani hreg hm
  have hFinΓ : Finite (StatedOmega ⇑(coordinateQuadMinus 4 K (by norm_num) b c)) := inferInstance
  have hFinG : Finite ↥(omegaG0 K b c) := Finite.of_equiv _ Φ.toEquiv
  let S₀' : Sylow 2 ↥(omegaG0 K b c) := Sylow.mapSurjective (f := Φ.toMonoidHom) Φ.surjective S₀
  have hS₀' : (S₀' : Subgroup ↥(omegaG0 K b c)) = (S₀ : Subgroup _).map Φ.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(omegaG0 K b c) U S₀'
  have hgU : (S₀' : Subgroup ↥(omegaG0 K b c)) =
      (U : Subgroup ↥(omegaG0 K b c)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hN₀ : Subgroup.normalizer ((S₀' : Subgroup ↥(omegaG0 K b c)) : Set ↥(omegaG0 K b c)) ≤
      N.map Φ.toMonoidHom := by
    rw [hS₀', ← Subgroup.map_equiv_normalizer_eq (S₀ : Subgroup _) Φ]
    exact Subgroup.map_mono hN
  let N'' : Subgroup ↥(omegaG0 K b c) := (N.map Φ.toMonoidHom).comap (MulAut.conj g).toMonoidHom
  have hB'' : (tailBorel (4 - 1) (minusTailForm K b c)).subgroupOf (omegaG0 K b c) ≤ N'' := by
    intro x hx
    rw [← hNU, ← hU] at hx
    have h1 : (MulAut.conj g).toMonoidHom x ∈
        Subgroup.normalizer ((S₀' : Subgroup ↥(omegaG0 K b c)) : Set ↥(omegaG0 K b c)) := by
      rw [hgU, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.mem_map_of_mem _ hx
    exact hN₀ h1
  let M : Subgroup (omegaV0 K ≃ₗ[K] omegaV0 K) := N''.map (omegaG0 K b c).subtype
  have hMG : M ≤ omegaG0 K b c := Subgroup.map_subtype_le N''
  have hBM : tailBorel (4 - 1) (minusTailForm K b c) ≤ M := by
    intro x hx
    exact ⟨⟨x, tailBorel_le hx⟩, hB'' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hMne : M ≠ omegaG0 K b c := by
    intro hMeq
    apply hne
    have hN''top : N'' = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      have hx : (x : omegaV0 K ≃ₗ[K] omegaV0 K) ∈ M := by
        rw [hMeq]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [← this]
    have hN₀top : N.map Φ.toMonoidHom = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      have hz : (MulAut.conj g⁻¹).toMonoidHom z ∈ N'' := by
        rw [hN''top]
        exact Subgroup.mem_top _
      have h2 : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom z) ∈
          N.map Φ.toMonoidHom := hz
      have h3 : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom z) = z := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [h3] at h2
    refine eq_top_iff.2 fun y _ => ?_
    have hy : Φ y ∈ N.map Φ.toMonoidHom := by
      rw [hN₀top]
      exact Subgroup.mem_top _
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Φ.injective hyy
    rwa [← this]
  have ha₀ : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hM' := tail_overgroup_stabilizers hani ha₀ hMG hBM
  obtain ⟨i₁, hi₁⟩ := (tail_overgroup_ne_iff hani ha₀ hMG hBM).1 hMne
  let J : Set (Fin (4 - 1)) :=
    {i | tailWeylElt (4 - 1) (minusTailForm K b c) (Pi.single 0 1) i ∉ M}
  let Wi : Fin (4 - 1) → Submodule K (Fin (2 * 4) → K) := fun i =>
    ((tailFlag K (Fin 2 → K) (4 - 1) (i + 1)).map g.val.toLinearMap).map ψ.toLinearMap
  have hmemM : ∀ x : omegaV0 K ≃ₗ[K] omegaV0 K, x ∈ M ↔ x ∈ omegaG0 K b c ∧ ∀ i ∈ J,
      x ∈ MulAction.stabilizer (omegaV0 K ≃ₗ[K] omegaV0 K)
        (tailFlag K (Fin 2 → K) (4 - 1) (i + 1)) :=
    fun x => by
    have h := SetLike.ext_iff.1 hM' x
    rw [Subgroup.mem_inf] at h
    simp only [Subgroup.mem_iInf] at h
    exact h
  have key : ∀ y : ↥(StatedOmega ⇑(coordinateQuadMinus 4 K h14 b c)), y ∈ N ↔
      ∀ i ∈ J, (Wi i).map (toLinEquiv (Fin (2 * 4)) K y.val).toLinearMap = Wi i := by
    intro y
    have hconj : (MulAut.conj g).toMonoidHom (g⁻¹ * Φ y * g) = Φ y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h1 : y ∈ N ↔ g⁻¹ * Φ y * g ∈ N'' := by
      constructor
      · intro hy
        show (MulAut.conj g).toMonoidHom (g⁻¹ * Φ y * g) ∈ N.map Φ.toMonoidHom
        rw [hconj]
        exact Subgroup.mem_map_of_mem _ hy
      · intro hy
        have h2 : (MulAut.conj g).toMonoidHom (g⁻¹ * Φ y * g) ∈ N.map Φ.toMonoidHom := hy
        rw [hconj] at h2
        obtain ⟨y', hy', hyy⟩ := h2
        have : y' = y := Φ.injective hyy
        rwa [← this]
    have h2 : g⁻¹ * Φ y * g ∈ N'' ↔
        (((g⁻¹ * Φ y * g : ↥(omegaG0 K b c)) : omegaV0 K ≃ₗ[K] omegaV0 K)) ∈ M :=
      (Subgroup.mem_map_iff_mem (omegaG0 K b c).subtype_injective).symm
    rw [h1, h2, hmemM]
    rw [and_iff_right (g⁻¹ * Φ y * g).2]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    have hstab : ((((g⁻¹ * Φ y * g : ↥(omegaG0 K b c)) : omegaV0 K ≃ₗ[K] omegaV0 K)) ∈
        MulAction.stabilizer (omegaV0 K ≃ₗ[K] omegaV0 K)
          (tailFlag K (Fin 2 → K) (4 - 1) (i + 1))) ↔
        (tailFlag K (Fin 2 → K) (4 - 1) (i + 1)).map
          ((g.val⁻¹ * (Φ y).val * g.val : omegaV0 K ≃ₗ[K] omegaV0 K) :
            omegaV0 K →ₗ[K] omegaV0 K) = tailFlag K (Fin 2 → K) (4 - 1) (i + 1) := by
      rw [Submodule.mem_stabilizer_submodule_iff_map_eq]
      rfl
    rw [hstab, map_fix_conj]
    have := map_tailOmegaEquiv_iff ψ rfl hE y (Wi i)
    have hWi : (Wi i).map ψ.symm.toLinearMap =
        (tailFlag K (Fin 2 → K) (4 - 1) (i + 1)).map g.val.toLinearMap :=
      map_symm_map_isometry ψ
    rw [hWi] at this
    exact this
  refine ⟨Wi '' J, ⟨Wi i₁, i₁, hi₁, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    refine ⟨?_, ?_⟩
    · intro h0
      have h1 : Module.finrank K (Wi i) = i + 1 := by
        show Module.finrank K (((tailFlag K (Fin 2 → K) (4 - 1) (i + 1)).map g.val.toLinearMap).map
          ψ.toLinearEquiv.toLinearMap) = _
        rw [LinearEquiv.finrank_map_eq ψ.toLinearEquiv, LinearEquiv.finrank_map_eq g.val,
          finrank_tailFlag (by have := i.isLt; omega)]
      rw [h0, finrank_bot] at h1
      omega
    · rintro _ ⟨u, ⟨v, hv, rfl⟩, rfl⟩
      show coordinateQuadMinus 4 K h14 b c (ψ (g.val v)) = 0
      rw [ψ.map_app]
      have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (orthElementaryGroup_le _ g.2) v
      change quadTail (4 - 1) (minusTailForm K b c) (g.val v) = 0
      rw [h1]
      exact quadTail_eq_zero_of_mem_tailFlag hv
  · intro y
    rw [key]
    constructor
    · intro h W hW
      obtain ⟨i, hi, rfl⟩ := hW
      have := (map_eq_iff_forall (toLinEquiv (Fin (2 * 4)) K y.val) (Wi i)).1 (h i hi)
      simpa only [toLinEquiv_apply] using this
    · intro h i hi
      refine (map_eq_iff_forall (toLinEquiv (Fin (2 * 4)) K y.val) (Wi i)).2 fun w hw => ?_
      simpa only [toLinEquiv_apply] using h (Wi i) ⟨i, hi, rfl⟩ w hw

end Model

end CFSG.RankThree.PartOne.AUTSL
