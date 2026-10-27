module

public import CFSG.RankThree.PartOne.KE6.Phi6Disc
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6First
public import CFSG.RankThree.PartOne.KE6.Phi6Shape

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KETw3 (exists_sl3_exchange_21 conj_rootSpan_le chainRoot56_add
  chainRoot13_add)
open Matrix
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω]

theorem specialLinearGroup_map_id (X : SL(3, Ω)) :
    Matrix.SpecialLinearGroup.map (RingHom.id Ω) X = X :=
  Subtype.ext (by simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem R_exch (ς Fr : Ω →+* Ω) (hς : Function.Bijective ς)
    (hFr : Function.Bijective Fr) (k₂ : Subfield Ω) (h₁ h₂ g₁ g₂ : SL(3, Ω))
    (E : ModGL Tag.E6 Ω) (T : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ)
    (hadd : ∀ x y, T (x + y) = T x + T y)
    (hEroot : ∀ β, IsRoot Tag.E6 β → ∃ μ : Ωˣ, ∀ c : Ω,
      E * pinnedX Tag.E6 Ω β c * E⁻¹ = pinnedX Tag.E6 Ω (T β) ((μ : Ω) * c))
    (hex : (∀ α ∈ parabolicRoots Tag.E6 support13, T α ∈ parabolicRoots Tag.E6 support56) ∧
      ∀ α ∈ parabolicRoots Tag.E6 support56, T α ∈ parabolicRoots Tag.E6 support13)
    (hfix : ∀ A : SL(3, k₂), (twoA2Mul Ω (g₁, g₂) * E) *
      Units.map (entrywiseHom ς) (twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹)) * (twoA2Mul Ω (g₁, g₂) * E)⁻¹ =
      twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹)) :
    ∀ t ∈ k₂, ς (Fr t) = t := by
  classical
  have hroots : ∀ i j : Fin 3, i ≠ j → ∃ a b : Fin 3, a ≠ b ∧
      T (chainRoot chain56 i j) = chainRoot chain13 a b := fun i j hij => by
    obtain ⟨a, b, hab, h⟩ := exists_chainRoot13_of_mem'
      (hex.2 _ (chainRoot56_mem_parabolicRoots hij))
    exact ⟨a, b, hab, h⟩
  have hQ12 : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      E * g * E⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 := by
    intro g hg
    rw [subsystemGroup_eq_rootSpan] at hg ⊢
    exact conj_rootSpan_le T (fun α hα => hEroot α hα.1) hex.1 g hg
  have hθ : ∀ (τ₁ τ₂ : Fin 3 → Fin 3 → Fin 3),
      (∀ i j : Fin 3, i ≠ j → T (chainRoot chain56 i j) = chainRoot chain13 (τ₁ i j) (τ₂ i j)) →
      ∀ i j : Fin 3, i ≠ j → ∃ μ : Ωˣ, ∀ c : Ω,
        (MulAut.conj E).toMonoidHom (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
          pinnedX Tag.E6 Ω (chainRoot chain13 (τ₁ i j) (τ₂ i j)) ((μ : Ω) * c) :=
    fun τ₁ τ₂ hT i j hij => by
      obtain ⟨μ, hμ⟩ := hEroot _ (isRoot_chainRoot56 hij)
      exact ⟨μ, fun c => by rw [← hT i j hij]; exact hμ c⟩
  have hmain : ∀ (τ₁ τ₂ : Fin 3 → Fin 3 → Fin 3) (hne : ∀ i j : Fin 3, i ≠ j → τ₁ i j ≠ τ₂ i j)
      (hT : ∀ i j : Fin 3, i ≠ j → T (chainRoot chain56 i j) =
        chainRoot chain13 (τ₁ i j) (τ₂ i j)),
      ∃ (N : SL(3, Ω) →* SL(3, Ω)) (bb : Fin 3 → Fin 3 → Ωˣ),
        (∀ X : SL(3, Ω), ((a2Equiv₁ Ω).symm (N X) : ModGL Tag.E6 Ω) =
          E * ((a2Equiv₂ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹) ∧
        ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
          ((N (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
            Matrix (Fin 3) (Fin 3) Ω) = 1 + single (τ₁ i j) (τ₂ i j) ((bb i j : Ω) * t) := by
    intro τ₁ τ₂ hne hT
    obtain ⟨hQ, bb, hshape⟩ := exists_sl3_exchange_21 (MulAut.conj E).toMonoidHom τ₁ τ₂ hne
      (hθ τ₁ τ₂ hT)
    let θ21 : subsystemGroup Tag.E6 Ω support56 →* subsystemGroup Tag.E6 Ω support13 :=
      { toFun := fun g => ⟨(MulAut.conj E).toMonoidHom (g : ModGL Tag.E6 Ω), hQ g g.2⟩
        map_one' := Subtype.ext (map_one (MulAut.conj E).toMonoidHom)
        map_mul' := fun x y => Subtype.ext (map_mul (MulAut.conj E).toMonoidHom
          (x : ModGL Tag.E6 Ω) y) }
    let N : SL(3, Ω) →* SL(3, Ω) :=
      (a2Equiv₁ Ω).toMonoidHom.comp (θ21.comp (a2Equiv₂ Ω).symm.toMonoidHom)
    refine ⟨N, bb, fun X => ?_, fun i j hij t => hshape i j hij t⟩
    change (((a2Equiv₁ Ω).symm ((a2Equiv₁ Ω) (θ21 ((a2Equiv₂ Ω).symm X))) :
      subsystemGroup Tag.E6 Ω support13) : ModGL Tag.E6 Ω) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hdisc : ∀ (N : SL(3, Ω) →* SL(3, Ω))
      (hN : ∀ X : SL(3, Ω), ((a2Equiv₁ Ω).symm (N X) : ModGL Tag.E6 Ω) =
        E * ((a2Equiv₂ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹),
      ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
          Ωˣ →* GL (Fin 3) Ω).range,
        Matrix.SpecialLinearGroup.toGL (g₁ * N (Matrix.SpecialLinearGroup.map ς
          (h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
            h₂⁻¹)) * g₁⁻¹) =
          z * Matrix.SpecialLinearGroup.toGL (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
            h₁⁻¹) := by
    intro N hN A
    refine fst_discrepancy ς g₁ g₂ E (fun _ Y => N Y)
      (fun X _ => a2Equiv₂ Ω ⟨E * ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹,
        hQ12 _ ((a2Equiv₁ Ω).symm X).2⟩) ?_ _ _ (hfix A)
    intro X Y
    have e1 : E * (((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω) *
        ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω)) * E⁻¹ =
        (E * ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹) *
          (E * ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω) * E⁻¹) := by group
    rw [twoA2Mul_apply, twoA2Mul_apply, e1, ← hN Y, MulEquiv.symm_apply_apply]
    exact (commute_Q₁_Q₂ ((a2Equiv₁ Ω).symm (N Y)).2
      (hQ12 _ ((a2Equiv₁ Ω).symm X).2)).eq.symm
  rcases transition_cases_gen chainRoot56_add hadd hroots with ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    obtain ⟨N, bb, hN, hshape⟩ := hmain (fun i _ => π i) (fun _ j => π j)
      (fun i j hij => π.injective.ne hij) (fun i j _ => hπ i j)
    obtain ⟨A₀, hA₀⟩ := exists_conj_map_of_root_permuting (n := 3) (le_refl 3) (RingHom.id Ω) π N
      bb (fun i j hij t => by
        rw [RingHom.id_apply]
        exact hshape i j hij t)
    have hGLN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
        A₀ * Matrix.SpecialLinearGroup.toGL X * A₀⁻¹ := fun X => by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA₀ X, Units.val_mul, Units.val_mul,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      simp
    exact rigid_first_pos ς Fr hς hFr k₂ g₁ h₁ h₂ A₀ N hGLN (hdisc N hN)
  ·
    obtain ⟨N, bb, hN, hshape⟩ := hmain (fun _ j => π j) (fun i _ => π i)
      (fun i j hij => (π.injective.ne hij).symm) (fun i j _ => hπ i j)
    obtain ⟨A₀, hA₀⟩ := exists_conj_map_inv_transpose_of_root_permuting (n := 3) (le_refl 3)
      (RingHom.id Ω) π N bb (fun i j hij t => by
        rw [RingHom.id_apply]
        exact hshape i j hij t)
    have hGLN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
        A₀ * invTransposeHom (Matrix.SpecialLinearGroup.toGL X) * A₀⁻¹ := fun X => by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA₀ X, Units.val_mul, Units.val_mul,
        coe_invTransposeHom]
      simp [Matrix.coe_units_inv]
    exact (rigid_first_neg ς Fr hς hFr k₂ g₁ h₁ h₂ A₀ N hGLN (hdisc N hN)).elim

theorem R_pres (ς Fr : Ω →+* Ω) (hς : Function.Bijective ς) (k₂ : Subfield Ω)
    (h₁ h₂ g₁ g₂ : SL(3, Ω)) (E : ModGL Tag.E6 Ω)
    (T : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ)
    (hadd : ∀ x y, T (x + y) = T x + T y)
    (hEroot : ∀ β, IsRoot Tag.E6 β → ∃ μ : Ωˣ, ∀ c : Ω,
      E * pinnedX Tag.E6 Ω β c * E⁻¹ = pinnedX Tag.E6 Ω (T β) ((μ : Ω) * c))
    (hpres : (∀ α ∈ parabolicRoots Tag.E6 support13, T α ∈ parabolicRoots Tag.E6 support13) ∧
      ∀ α ∈ parabolicRoots Tag.E6 support56, T α ∈ parabolicRoots Tag.E6 support56)
    (hfix : ∀ A : SL(3, k₂), (twoA2Mul Ω (g₁, g₂) * E) *
      Units.map (entrywiseHom ς) (twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹)) * (twoA2Mul Ω (g₁, g₂) * E)⁻¹ =
      twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹)) :
    ∀ t ∈ k₂, ς t = t := by
  classical
  have hroots : ∀ i j : Fin 3, i ≠ j → ∃ a b : Fin 3, a ≠ b ∧
      T (chainRoot chain13 i j) = chainRoot chain13 a b := fun i j hij => by
    obtain ⟨a, b, hab, h⟩ := exists_chainRoot13_of_mem'
      (hpres.1 _ (chainRoot13_mem_parabolicRoots hij))
    exact ⟨a, b, hab, h⟩
  have hQ22 : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      E * g * E⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 := by
    intro g hg
    rw [subsystemGroup_eq_rootSpan] at hg ⊢
    exact conj_rootSpan_le T (fun α hα => hEroot α hα.1) hpres.2 g hg
  have hθ : ∀ (τ₁ τ₂ : Fin 3 → Fin 3 → Fin 3),
      (∀ i j : Fin 3, i ≠ j → T (chainRoot chain13 i j) = chainRoot chain13 (τ₁ i j) (τ₂ i j)) →
      ∀ i j : Fin 3, i ≠ j → ∃ μ : Ωˣ, ∀ c : Ω,
        (MulAut.conj E).toMonoidHom (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
          pinnedX Tag.E6 Ω (chainRoot chain13 (τ₁ i j) (τ₂ i j)) ((μ : Ω) * c) :=
    fun τ₁ τ₂ hT i j hij => by
      obtain ⟨μ, hμ⟩ := hEroot _ (chainRoot13_mem_parabolicRoots hij).1
      exact ⟨μ, fun c => by rw [← hT i j hij]; exact hμ c⟩
  have hmain : ∀ (τ₁ τ₂ : Fin 3 → Fin 3 → Fin 3) (hne : ∀ i j : Fin 3, i ≠ j → τ₁ i j ≠ τ₂ i j)
      (hT : ∀ i j : Fin 3, i ≠ j → T (chainRoot chain13 i j) =
        chainRoot chain13 (τ₁ i j) (τ₂ i j)),
      ∃ (N : SL(3, Ω) →* SL(3, Ω)) (bb : Fin 3 → Fin 3 → Ωˣ),
        (∀ X : SL(3, Ω), ((a2Equiv₁ Ω).symm (N X) : ModGL Tag.E6 Ω) =
          E * ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹) ∧
        ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
          ((N (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
            Matrix (Fin 3) (Fin 3) Ω) = 1 + single (τ₁ i j) (τ₂ i j) ((bb i j : Ω) * t) := by
    intro τ₁ τ₂ hne hT
    obtain ⟨hQ, bb, hshape⟩ := exists_sl3_linear_11 (MulAut.conj E).toMonoidHom τ₁ τ₂ hne
      (hθ τ₁ τ₂ hT)
    let θ11 : subsystemGroup Tag.E6 Ω support13 →* subsystemGroup Tag.E6 Ω support13 :=
      { toFun := fun g => ⟨(MulAut.conj E).toMonoidHom (g : ModGL Tag.E6 Ω), hQ g g.2⟩
        map_one' := Subtype.ext (map_one (MulAut.conj E).toMonoidHom)
        map_mul' := fun x y => Subtype.ext (map_mul (MulAut.conj E).toMonoidHom
          (x : ModGL Tag.E6 Ω) y) }
    let N : SL(3, Ω) →* SL(3, Ω) :=
      (a2Equiv₁ Ω).toMonoidHom.comp (θ11.comp (a2Equiv₁ Ω).symm.toMonoidHom)
    refine ⟨N, bb, fun X => ?_, fun i j hij t => hshape i j hij t⟩
    change (((a2Equiv₁ Ω).symm ((a2Equiv₁ Ω) (θ11 ((a2Equiv₁ Ω).symm X))) :
      subsystemGroup Tag.E6 Ω support13) : ModGL Tag.E6 Ω) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hdisc : ∀ (N : SL(3, Ω) →* SL(3, Ω))
      (hN : ∀ X : SL(3, Ω), ((a2Equiv₁ Ω).symm (N X) : ModGL Tag.E6 Ω) =
        E * ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹),
      ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
          Ωˣ →* GL (Fin 3) Ω).range,
        Matrix.SpecialLinearGroup.toGL (g₁ * N (Matrix.SpecialLinearGroup.map ς
          (h₁ * Matrix.SpecialLinearGroup.map (RingHom.id Ω)
            (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₁⁻¹)) * g₁⁻¹) =
          z * Matrix.SpecialLinearGroup.toGL (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
            h₁⁻¹) := by
    intro N hN A
    simp only [specialLinearGroup_map_id]
    refine fst_discrepancy ς g₁ g₂ E (fun X _ => N X)
      (fun _ Y => a2Equiv₂ Ω ⟨E * ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω) * E⁻¹,
        hQ22 _ ((a2Equiv₂ Ω).symm Y).2⟩) ?_ _ _ (hfix A)
    intro X Y
    have e1 : E * (((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω) *
        ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω)) * E⁻¹ =
        (E * ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹) *
          (E * ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω) * E⁻¹) := by group
    rw [twoA2Mul_apply, twoA2Mul_apply, e1, ← hN X, MulEquiv.symm_apply_apply]
  rcases transition_cases_gen chainRoot13_add hadd hroots with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · obtain ⟨N, bb, hN, hshape⟩ := hmain (fun i _ => π i) (fun _ j => π j)
      (fun i j hij => π.injective.ne hij) (fun i j _ => hπ i j)
    obtain ⟨A₀, hA₀⟩ := exists_conj_map_of_root_permuting (n := 3) (le_refl 3) (RingHom.id Ω) π N
      bb (fun i j hij t => by
        rw [RingHom.id_apply]
        exact hshape i j hij t)
    have hGLN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
        A₀ * Matrix.SpecialLinearGroup.toGL X * A₀⁻¹ := fun X => by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA₀ X, Units.val_mul, Units.val_mul,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      simp
    intro t ht
    exact rigid_first_pos ς (RingHom.id Ω) hς Function.bijective_id k₂ g₁ h₁ h₁ A₀ N hGLN
      (hdisc N hN) t ht
  · obtain ⟨N, bb, hN, hshape⟩ := hmain (fun _ j => π j) (fun i _ => π i)
      (fun i j hij => (π.injective.ne hij).symm) (fun i j _ => hπ i j)
    obtain ⟨A₀, hA₀⟩ := exists_conj_map_inv_transpose_of_root_permuting (n := 3) (le_refl 3)
      (RingHom.id Ω) π N bb (fun i j hij t => by
        rw [RingHom.id_apply]
        exact hshape i j hij t)
    have hGLN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
        A₀ * invTransposeHom (Matrix.SpecialLinearGroup.toGL X) * A₀⁻¹ := fun X => by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA₀ X, Units.val_mul, Units.val_mul,
        coe_invTransposeHom]
      simp [Matrix.coe_units_inv]
    exact (rigid_first_neg ς (RingHom.id Ω) hς Function.bijective_id k₂ g₁ h₁ h₁ A₀ N hGLN
      (hdisc N hN)).elim

theorem exists_twoA2Mul_of_mem_rootSpan {q : ModGL Tag.E6 Ω}
    (hq : q ∈ rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 supportA2A2)) :
    ∃ g₁ g₂ : SL(3, Ω), twoA2Mul Ω (g₁, g₂) = q := by
  rw [rootSpan_supportA2A2] at hq
  have h1 : q ∈ (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) *
      (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
    rw [← coe_sup_subsystemGroup]
    exact hq
  rw [← range_twoA2Mul] at h1
  obtain ⟨⟨g₁, g₂⟩, hg⟩ := h1
  exact ⟨g₁, g₂, hg⟩

theorem R_main [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hpΩ : (p : Ω) ≠ 0) {y : ModGL Tag.E6 Ω} (hyH : y ∈ torusGroup Tag.E6 Ω) (hyp : y ^ p = 1)
    (hker : torusRootKernel y = parabolicRoots Tag.E6 supportA2A2)
    (Qε : ModGL Tag.E6 Ω) (πε : Equiv.Perm (Fin Tag.E6.rank))
    (hπc : ∀ i j, Tag.E6.cartan (πε i) (πε j) = Tag.E6.cartan i j)
    (hQd : ∀ c : Fin Tag.E6.rank → Ωˣ, Qε * rootDiagUnit Tag.E6 c * Qε⁻¹ =
      rootDiagUnit Tag.E6 (fun i => c (πε.symm i)))
    (hQroot : ∀ (w : WeylGroup Tag.E6) {t₀ : ModGL Tag.E6 Ω}, t₀ ∈ torusGroup Tag.E6 Ω →
      ∀ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β → ∃ μ : Ωˣ, ∀ c : Ω,
        (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * Qε) * pinnedX Tag.E6 Ω β c *
          (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * Qε)⁻¹ =
            pinnedX Tag.E6 Ω (w • permLattice πε β) ((μ : Ω) * c))
    (ς Fr : Ω →+* Ω) (hς : Function.Bijective ς) (hFr : Function.Bijective Fr)
    (k₂ : Subfield Ω) (h₁ h₂ : SL(3, Ω)) {G₃ : ModGL Tag.E6 Ω}
    (hG₃ : G₃ ∈ adjointGroup Tag.E6 Ω)
    (hfix : (G₃ * Qε) * Units.map (entrywiseHom ς) y * (G₃ * Qε)⁻¹ = y)
    (hlayer : ∀ A : SL(3, k₂), (G₃ * Qε) *
      Units.map (entrywiseHom ς) (twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹)) * (G₃ * Qε)⁻¹ =
      twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹)) :
    ∃ w : WeylGroup Tag.E6, (∀ b : Fin Tag.E6.rank → Ωˣ, y = rootDiagUnit Tag.E6 b →
        ∀ v : Fin Tag.E6.rank → ℤ,
          rootChar b (w • permLattice πε v) = Units.map ς.toMonoidHom (rootChar b v)) ∧
      ((((∀ α ∈ parabolicRoots Tag.E6 support13, w • permLattice πε α ∈
            parabolicRoots Tag.E6 support13) ∧
          ∀ α ∈ parabolicRoots Tag.E6 support56, w • permLattice πε α ∈
            parabolicRoots Tag.E6 support56) ∧ ∀ t ∈ k₂, ς t = t) ∨
        (((∀ α ∈ parabolicRoots Tag.E6 support13, w • permLattice πε α ∈
            parabolicRoots Tag.E6 support56) ∧
          ∀ α ∈ parabolicRoots Tag.E6 support56, w • permLattice πε α ∈
            parabolicRoots Tag.E6 support13) ∧ ∀ t ∈ k₂, ς (Fr t) = t)) := by
  classical
  obtain ⟨w, t₀, q'', ht₀, hq'', hdec, hrc⟩ := phi6_decomp hp5 hpΩ hyH hyp Qε πε hQd ς hG₃ hfix
  rw [hker] at hq''
  obtain ⟨g₁, g₂, hg⟩ := exists_twoA2Mul_of_mem_rootSpan hq''
  set E : ModGL Tag.E6 Ω := t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * Qε with hE
  set T : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ := fun v => w • permLattice πε v with hT
  have hadd : ∀ x y, T (x + y) = T x + T y := fun x y => by
    simp only [hT, permLattice_add, smul_add]
  have hEroot : ∀ β, IsRoot Tag.E6 β → ∃ μ : Ωˣ, ∀ c : Ω,
      E * pinnedX Tag.E6 Ω β c * E⁻¹ = pinnedX Tag.E6 Ω (T β) ((μ : Ω) * c) :=
    fun β hβ => hQroot w ht₀ β hβ
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hrcb := hrc b hb
  have hTmap : ∀ α ∈ parabolicRoots Tag.E6 supportA2A2, T α ∈ parabolicRoots Tag.E6 supportA2A2 := by
    intro α hα
    rw [← hker] at hα ⊢
    rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
    refine ⟨IsRoot.smul (IsRoot.permLattice hπc hα.1) w, ?_⟩
    have h1 := hrcb α
    rw [hα.2, map_one] at h1
    exact h1
  have hinj : Function.Injective T := fun x y hxy => by
    have h1 : permLattice πε x = permLattice πε y := smul_left_cancel w hxy
    have h2 := congrArg (permLattice πε.symm) h1
    rwa [permLattice_symm_permLattice, permLattice_symm_permLattice] at h2
  have hfixR : ∀ A : SL(3, k₂), (twoA2Mul Ω (g₁, g₂) * E) *
      Units.map (entrywiseHom ς) (twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹)) * (twoA2Mul Ω (g₁, g₂) * E)⁻¹ =
      twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹) := fun A => by
    rw [hg, ← hdec]
    exact hlayer A
  refine ⟨w, hrc, ?_⟩
  rcases T_cases hadd hinj hTmap with hpres | hexch
  · exact Or.inl ⟨hpres, R_pres ς Fr hς k₂ h₁ h₂ g₁ g₂ E T hadd hEroot hpres hfixR⟩
  · exact Or.inr ⟨hexch, R_exch ς Fr hς hFr k₂ h₁ h₂ g₁ g₂ E T hadd hEroot hexch hfixR⟩

end CFSG.RankThree.PartOne.KE6
