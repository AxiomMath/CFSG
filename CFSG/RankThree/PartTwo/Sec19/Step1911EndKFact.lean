module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1911EndProof

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

@[expose] def glConj (g : GL (Fin 3) F) :
    SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F where
  toFun s := ⟨(g : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), by
    rw [det_mul, det_mul, s.2, mul_one, ← det_mul, Units.mul_inv, det_one]⟩
  map_one' := by
    apply Subtype.ext
    change (g : Matrix (Fin 3) (Fin 3) F) * 1 * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1
    rw [Matrix.mul_one, Units.mul_inv]
  map_mul' s t := by
    apply Subtype.ext
    change (g : Matrix (Fin 3) (Fin 3) F) * ((s : Matrix (Fin 3) (Fin 3) F) * t) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * s * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : Matrix (Fin 3) (Fin 3) F) * t * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), Units.inv_mul,
      Matrix.one_mul]

theorem coe_glConj (g : GL (Fin 3) F) (s : SpecialLinearGroup (Fin 3) F) :
    ((glConj g s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem toGL_glConj (g : GL (Fin 3) F) (s : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.toGL (glConj g s) = g * SpecialLinearGroup.toGL s * g⁻¹ :=
  Units.ext rfl

theorem glConj_toGL (y s : SpecialLinearGroup (Fin 3) F) :
    glConj (SpecialLinearGroup.toGL y) s = y * s * y⁻¹ :=
  SpecialLinearGroup.toGL_injective (by rw [toGL_glConj, map_mul, map_mul, map_inv])

theorem glConj_inv_glConj (g : GL (Fin 3) F) (s : SpecialLinearGroup (Fin 3) F) :
    glConj g⁻¹ (glConj g s) = s :=
  SpecialLinearGroup.toGL_injective (by rw [toGL_glConj, toGL_glConj]; group)

theorem glConj_injective (g : GL (Fin 3) F) : Function.Injective (glConj g) := fun s t h => by
  rw [← glConj_inv_glConj g s, h, glConj_inv_glConj]

theorem glConj_inv_mem [Finite F] {Q : Subgroup (SpecialLinearGroup (Fin 3) F)}
    {g : GL (Fin 3) F} (h : ∀ s ∈ Q, glConj g s ∈ Q) : ∀ s ∈ Q, glConj g⁻¹ s ∈ Q := by
  have hle : Q.map (glConj g) ≤ Q := by
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  have heq : Q.map (glConj g) = Q :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (glConj_injective g)).ge
  intro s hs
  rw [← heq] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rwa [glConj_inv_glConj]

theorem finrank_map_flagSpace (g : GL (Fin 3) F) {i : ℕ} (hi : i ≤ 3) :
    Module.finrank F ((flagSpace 3 F i).map
      (mulVecLin (g : Matrix (Fin 3) (Fin 3) F))) = i := by
  have hinj : Function.Injective (mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) := by
    rw [coe_mulVecLin]
    exact mulVec_injective_iff_isUnit.mpr g.isUnit
  rw [← (Submodule.equivMapOfInjective _ hinj (flagSpace 3 F i)).finrank_eq, finrank_flagSpace hi]

theorem mulVec_mem_flagSpace {I : Set ℕ} (hI : ∀ j ∈ I, j < 3) {i : ℕ} (hi : i ∈ I)
    (hi1 : 1 ≤ i) {g : GL (Fin 3) F}
    (hg : ∀ s ∈ flagStabilizer 3 F I, glConj g⁻¹ s ∈ flagStabilizer 3 F I) :
    ∀ v ∈ flagSpace 3 F i, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ flagSpace 3 F i := by
  set W' := (flagSpace 3 F i).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) with hW'
  have hi3 : i < 3 := hI i hi
  have hinv : ∀ s ∈ flagStabilizer 3 F I, ∀ v ∈ W',
      (s : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W' := by
    rintro s hs _ ⟨w, hw, rfl⟩
    have hs' := hg s hs
    have hstab := mem_stabilizer.mp (mem_flagStabilizer.mp hs' i hi)
    have hmem : ((glConj g⁻¹ s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈
        flagSpace 3 F i := by
      rw [← hstab]
      exact ⟨w, hw, rfl⟩
    refine ⟨_, hmem, ?_⟩
    rw [mulVecLin_apply, mulVecLin_apply, coe_glConj, mulVec_mulVec, inv_inv,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, ← mulVec_mulVec]
  have hdim : Module.finrank F W' = i := finrank_map_flagSpace g hi3.le
  rcases ((subflag_stabilizer_generation (K := F) (n := 3) I).2.1 W').mp hinv with
    h | h | ⟨j, hj, h⟩
  · rw [h, finrank_bot] at hdim
    omega
  · rw [h, finrank_top, Module.finrank_fin_fun] at hdim
    omega
  · have hj3 := hI j hj
    rw [h, finrank_flagSpace hj3.le] at hdim
    intro v hv
    rw [← hdim, ← h]
    exact ⟨v, hv, rfl⟩

theorem pow_finrank_eq_one {A B : Matrix (Fin 3) (Fin 3) F} (hA : IsUnit A) (hB : IsUnit B)
    {r : F} (hAB : A * B = r • (B * A)) {W : Submodule F (Fin 3 → F)}
    (hWA : ∀ v ∈ W, A *ᵥ v ∈ W) (hWB : ∀ v ∈ W, B *ᵥ v ∈ W) :
    r ^ Module.finrank F W = 1 := by
  set fA := (mulVecLin A).restrict (p := W) (q := W) (fun v hv => by
    rw [mulVecLin_apply]; exact hWA v hv) with hfA
  set fB := (mulVecLin B).restrict (p := W) (q := W) (fun v hv => by
    rw [mulVecLin_apply]; exact hWB v hv) with hfB
  have hcomp : fA ∘ₗ fB = r • (fB ∘ₗ fA) := by
    ext w
    simp only [hfA, hfB, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrict_apply,
      mulVecLin_apply, Submodule.coe_smul, mulVec_mulVec, hAB, smul_mulVec]
  have hunit : ∀ {C : Matrix (Fin 3) (Fin 3) F}, IsUnit C → ∀ (hC : ∀ v ∈ W, C *ᵥ v ∈ W),
      IsUnit (LinearMap.det ((mulVecLin C).restrict (p := W) (q := W) (fun v hv => by
        rw [mulVecLin_apply]; exact hC v hv))) := by
    intro C hC hCW
    rw [← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have h1 : C.mulVecLin (w : Fin 3 → F) = 0 := congrArg Subtype.val hw
    rw [mulVecLin_apply] at h1
    have h2 : (w : Fin 3 → F) = 0 :=
      mulVec_injective_iff_isUnit.mpr hC (by rw [h1, mulVec_zero])
    rw [Submodule.mem_bot]
    exact Subtype.ext h2
  have hdet := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_comp] at hdet
  have hu : IsUnit (LinearMap.det fA * LinearMap.det fB) :=
    (hunit hA hWA).mul (hunit hB hWB)
  rw [mul_comm (LinearMap.det fB) (LinearMap.det fA)] at hdet
  exact hu.mul_right_cancel (hdet.symm.trans (one_mul _).symm)

theorem false_of_normalizes_parabolic [Finite F] [CharP F 2]
    {P : Subgroup (SpecialLinearGroup (Fin 3) F)} (hP : P ≠ ⊤)
    {T : Sylow 2 (SpecialLinearGroup (Fin 3) F)}
    (hNT : Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin 3) F)) ≤ P)
    {g₁ g₂ : GL (Fin 3) F} (h₁ : ∀ s ∈ P, glConj g₁ s ∈ P) (h₂ : ∀ s ∈ P, glConj g₂ s ∈ P)
    {r : F} (hr1 : r ≠ 1) (hr3 : r ^ 3 = 1)
    (hcomm : ((g₁ * g₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      r • ((g₂ * g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SU, hSU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) SU T
  have hT : (T : Subgroup (SpecialLinearGroup (Fin 3) F)) =
      (unitriangular 3 F).map (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
        SpecialLinearGroup (Fin 3) F) := by
    rw [← hx, coe_sylow_smul, hSU]
  have hN : Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin 3) F)) =
      (upperTriangular 3 F).map (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
        SpecialLinearGroup (Fin 3) F) := by
    change Subgroup.normalizer (((T : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F))) = _
    rw [hT, normalizer_map_conj, normalizer_unitriangular]
  set P₀ := P.comap (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
    SpecialLinearGroup (Fin 3) F) with hP₀
  have hB : upperTriangular 3 F ≤ P₀ := fun b hb =>
    Subgroup.mem_comap.mpr (hNT (hN ▸ Subgroup.mem_map_of_mem _ hb))
  have hP₀top : P₀ ≠ ⊤ := by
    intro htop
    apply hP
    rw [eq_top_iff]
    intro s _
    have hs : x⁻¹ * s * x ∈ P₀ := by rw [htop]; exact Subgroup.mem_top _
    have := Subgroup.mem_comap.mp hs
    simpa [mul_assoc] using this
  set I := borelOvergroupCuts P₀ with hIdef
  have hQ : P₀ = flagStabilizer 3 F I := (borel_overgroups P₀ hB).1
  have hI3 : ∀ j ∈ I, j < 3 := fun j hj => by
    obtain ⟨_, hjn, _⟩ := hj
    exact hjn
  obtain ⟨i, hi⟩ : I.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hI
    apply hP₀top
    rw [hQ, hI, flagStabilizer_empty]
  obtain ⟨hi1, hi3, -⟩ := id hi
  set X := SpecialLinearGroup.toGL x with hX
  have hconj : ∀ g : GL (Fin 3) F, (∀ s ∈ P, glConj g s ∈ P) →
      ∀ s ∈ P₀, glConj (X⁻¹ * g * X) s ∈ P₀ := by
    intro g hg s hs
    rw [Subgroup.mem_comap] at hs ⊢
    have h1 : (MulAut.conj x : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F)
        (glConj (X⁻¹ * g * X) s) = glConj g ((MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
          SpecialLinearGroup (Fin 3) F) s) := by
      apply SpecialLinearGroup.toGL_injective
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul, map_inv, toGL_glConj, hX]
      group
    rw [h1]
    exact hg _ hs
  have hW : ∀ g : GL (Fin 3) F, (∀ s ∈ P, glConj g s ∈ P) →
      ∀ v ∈ flagSpace 3 F i, ((X⁻¹ * g * X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
        flagSpace 3 F i := by
    intro g hg
    refine mulVec_mem_flagSpace hI3 hi hi1 ?_
    rw [← hQ]
    exact glConj_inv_mem (hconj g hg)
  have hcomm' : ((X⁻¹ * g₁ * X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((X⁻¹ * g₂ * X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      r • (((X⁻¹ * g₂ * X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((X⁻¹ * g₁ * X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
    rw [← Units.val_mul, ← Units.val_mul,
      show X⁻¹ * g₁ * X * (X⁻¹ * g₂ * X) = X⁻¹ * (g₁ * g₂) * X by group,
      show X⁻¹ * g₂ * X * (X⁻¹ * g₁ * X) = X⁻¹ * (g₂ * g₁) * X by group,
      Units.val_mul (X⁻¹ * (g₁ * g₂)) X, Units.val_mul X⁻¹ (g₁ * g₂),
      Units.val_mul (X⁻¹ * (g₂ * g₁)) X, Units.val_mul X⁻¹ (g₂ * g₁), hcomm, Matrix.mul_smul,
      Matrix.smul_mul]
  have hpow := pow_finrank_eq_one (X⁻¹ * g₁ * X).isUnit (X⁻¹ * g₂ * X).isUnit hcomm'
    (hW g₁ h₁) (hW g₂ h₂)
  rw [finrank_flagSpace hi3.le] at hpow
  interval_cases i
  · rw [pow_one] at hpow
    exact hr1 hpow
  · apply hr1
    have h3 : r ^ 3 = r ^ 2 * r := by ring
    rw [hr3, hpow, one_mul] at h3
    exact h3.symm

end CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
