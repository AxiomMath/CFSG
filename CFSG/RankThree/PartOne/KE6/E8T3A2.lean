module

public import CFSG.RankThree.PartOne.KE.SigmaUnion
public import CFSG.RankThree.PartOne.KE.SLnShape

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped MatrixGroups

section BlockSL

variable {L : Type} [Field L]

theorem e8rhoJ_blockSL (Y : SL(2, L)) :
    e8rhoJ L (blockSL L 2 1 Y) = simpleRootSL2 Tag.E8 L (e8Index 0) Y := by
  have hx : ∀ c : L, e8rhoJ L (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) c) = xUnit Tag.E8 L (e8Index 0) c := by
    intro c
    have hmem : xUnit Tag.E8 L (e8Index 0) c ∈ subsystemGroup Tag.E8 L e8support13 :=
      xUnit_mem_subsystemGroup mem_e8support13_0 c
    have hrep : e8a2Rep L ⟨xUnit Tag.E8 L (e8Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
      apply Subtype.ext
      rw [coe_e8a2Rep, CFSG.LinearGroups.coe_transvection]
      exact e8a2Mat_x1 c
    rw [← hrep]
    exact e8rhoJ_e8a2Rep hmem
  have hy : ∀ c : L, e8rhoJ L (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) c) = yUnit Tag.E8 L (e8Index 0) c := by
    intro c
    have hmem : yUnit Tag.E8 L (e8Index 0) c ∈ subsystemGroup Tag.E8 L e8support13 :=
      yUnit_mem_subsystemGroup mem_e8support13_0 c
    have hrep : e8a2Rep L ⟨yUnit Tag.E8 L (e8Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
      apply Subtype.ext
      rw [coe_e8a2Rep, CFSG.LinearGroups.coe_transvection]
      exact e8a2Mat_y1 c
    rw [← hrep]
    exact e8rhoJ_e8a2Rep hmem
  have e0 : (finSumFinEquiv.symm (0 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inr 0 := rfl
  have hu : ∀ c : L, (blockSL L 2 1 (uSL c) : SL(3, L)) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
    intro c
    apply Subtype.ext
    rw [CFSG.LinearGroups.coe_transvection]
    have h : ((blockSL L 2 1 (uSL c) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (uSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
    rw [h]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [reindex_apply, submatrix_apply, e0, e1, e2, coe_uSL, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have hv : ∀ c : L, (blockSL L 2 1 (vSL c) : SL(3, L)) =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
    intro c
    apply Subtype.ext
    rw [CFSG.LinearGroups.coe_transvection]
    have h : ((blockSL L 2 1 (vSL c) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (vSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
    rw [h]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [reindex_apply, submatrix_apply, e0, e1, e2, coe_vSL, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have key : (e8rhoJ L).comp (blockSL L 2 1) = simpleRootSL2 Tag.E8 L (e8Index 0) :=
    eq_simpleRootSL2 (e8Index 0) (fun c => by rw [MonoidHom.comp_apply, hu, hx])
      (fun c => by rw [MonoidHom.comp_apply, hv, hy])
  exact DFunLike.congr_fun key Y

end BlockSL

section Core

variable {τ : Tag} {L : Type} [Field L]

theorem a2_factor_core [IsAlgClosed L] {S3 : Set (Fin τ.rank → ℤ)}
    (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(3, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(3, L) ≃* SL(3, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    [hfin : Finite (fixSubgroup Φ')] (hq : CFSG.IsQuasisimple (fixSubgroup Φ'))
    (hz : Subgroup.centralizer (((fixSubgroup Φ').map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 3) L)) : Set (GL (Fin 3) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 3)).range) :
    ∃ P : Subgroup (ModGL τ L),
      P = rootSpan τ L S3 ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      P = (fixSubgroup Φ').map ρ ∧
      SigmaFactor n Fr S3 (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan τ L S3 : Set (ModGL τ L))) := by
  classical
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set Rs := twistedFixedPoints n Φ with hRs
  set S := fixSubgroup Φ' with hS
  set P₀ : Subgroup (ModGL τ L) := ρ.range ⊓ Rs with hP₀
  have hP₀S : P₀ = S.map ρ := by
    ext u
    constructor
    · rintro ⟨⟨X, rfl⟩, hu2⟩
      refine ⟨X, ?_, rfl⟩
      have h : ρ (Φ' X) = ρ X := by rw [← hΦ' X]; exact hu2
      exact hρinj h
    · rintro ⟨X, hX, rfl⟩
      refine ⟨⟨X, rfl⟩, ?_⟩
      have h : Φ' X = X := hX
      change n * Φ (ρ X) * n⁻¹ = ρ X
      rw [hΦ' X, h]
  have hPe : S ≃* P₀ :=
    (Subgroup.equivMapOfInjective S ρ hρinj).trans (MulEquiv.subgroupCongr hP₀S.symm)
  have hPq : CFSG.IsQuasisimple P₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe hq
  have hPfin : Finite P₀ := Finite.of_equiv S hPe.toEquiv
  have hS3' : ∀ r ∈ S3, IsRoot τ r := hS3
  refine ⟨P₀, by rw [hP₀, hrange], hP₀S, ?_⟩
  refine ⟨fun _ => hPfin, fun _ => hPq, fun _ => ?_, fun _ => inf_le_right, fun _ => ?_,
    fun _ y hy hyR u hu => ?_, ?_⟩
  · rw [← hrange]
    exact inf_le_left
  · exact (inf_le_left : P₀ ≤ ρ.range).trans (by rw [hrange]; exact rootSpan_le_adjointGroup L S3)
  · have hu' : u ∈ P₀ := hu
    have hR : y * u * y⁻¹ ∈ Rs := mul_mem (mul_mem hyR hu'.2) (inv_mem hyR)
    have hyρ : y ∈ Subgroup.normalizer (ρ.range : Set (ModGL τ L)) := by
      rw [hrange]; exact hy
    exact ⟨(Subgroup.mem_normalizer_iff.1 hyρ u).1 hu'.1, hR⟩
  · intro y hy hcomm
    have hSf : ∀ X, X ∈ S ↔ Φ' X = X := fun X => Iff.rfl
    have hinj : Function.Injective
        (Matrix.SpecialLinearGroup.toGL : SL(3, L) →* GL (Fin 3) L) := fun B B' h =>
      Subtype.ext (congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h)
    have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
      (rootSpan τ L S3) (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS3')
    have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L S3 : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := hy
    rw [e] at hy'
    obtain ⟨t, ht, q, hq, rfl⟩ := hy'
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    rw [SetLike.mem_coe, ← hrange] at hq
    obtain ⟨A, rfl⟩ := hq
    obtain ⟨d, hd⟩ := htor b
    set M : GL (Fin 3) L := diagGL3 d * Matrix.SpecialLinearGroup.toGL A with hM
    have hconj : ∀ X : SL(3, L), X ∈ S → conjDiag3 d (A * X * A⁻¹) = X := by
      intro X hX
      apply hρinj
      rw [← hd]
      have hXP : ρ X ∈ P₀ := by
        rw [hP₀S]
        exact ⟨X, hX, rfl⟩
      have h := hcomm () _ hXP
      calc rootDiagUnit τ b * ρ (A * X * A⁻¹) * (rootDiagUnit τ b)⁻¹
          = (rootDiagUnit τ b * ρ A) * ρ X * (rootDiagUnit τ b * ρ A)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            group
        _ = ρ X := by rw [h, mul_inv_cancel_right]
    have hMcomm : ∀ X ∈ S, M * Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL X * M := by
      intro X hX
      have h := congrArg Matrix.SpecialLinearGroup.toGL (hconj X hX)
      rw [toGL_conjDiag3, map_mul, map_mul, map_inv] at h
      have h2 : M * Matrix.SpecialLinearGroup.toGL X * M⁻¹ = Matrix.SpecialLinearGroup.toGL X := by
        calc M * Matrix.SpecialLinearGroup.toGL X * M⁻¹
            = diagGL3 d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X *
              (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGL3 d)⁻¹ := by rw [hM]; group
          _ = Matrix.SpecialLinearGroup.toGL X := h
      exact mul_inv_eq_iff_eq_mul.1 h2
    have hMs : M ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
      rw [← hz, Subgroup.mem_centralizer_iff]
      rintro _ ⟨X, hX, rfl⟩
      exact (hMcomm X hX).symm
    obtain ⟨c, hc⟩ := hMs
    have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
      intro i j hij
      have h := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L) i j) hc
      simp only [hM, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, diagGL3,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.diagonal_mul, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ hij] at h
      have hdi : ((d i : Lˣ) : L) ≠ 0 := (d i).ne_zero
      exact (mul_eq_zero.1 h.symm).resolve_left hdi
    have hρA : ρ A ∈ torusGroup τ L := hdiag A hoff
    have hyH : rootDiagUnit τ b * ρ A ∈ torusGroup τ L := mul_mem ht hρA
    have hcZ : rootDiagUnit τ b * ρ A ∈ Subgroup.centralizer
        ((rootSpan τ L S3 : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [SetLike.mem_coe, ← hrange] at hg
      obtain ⟨X', rfl⟩ := hg
      have hsc : M * Matrix.SpecialLinearGroup.toGL X' = Matrix.SpecialLinearGroup.toGL X' * M := by
        rw [← hc]
        refine Units.ext ?_
        rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
        exact (Matrix.scalar_commute (c : L) (fun r => Commute.all _ r) _).eq
      have hc' : conjDiag3 d (A * X' * A⁻¹) = X' := by
        apply hinj
        rw [toGL_conjDiag3, map_mul, map_mul, map_inv]
        calc diagGL3 d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X' *
              (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGL3 d)⁻¹
            = M * Matrix.SpecialLinearGroup.toGL X' * M⁻¹ := by rw [hM]; group
          _ = Matrix.SpecialLinearGroup.toGL X' := by rw [hsc, mul_inv_cancel_right]
      have h4 : (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹ = ρ X' := by
        calc (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹
            = rootDiagUnit τ b * ρ (A * X' * A⁻¹) * (rootDiagUnit τ b)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
              group
          _ = ρ (conjDiag3 d (A * X' * A⁻¹)) := hd _
          _ = ρ X' := by rw [hc']
      exact (mul_inv_eq_iff_eq_mul.1 h4).symm
    exact ⟨hyH, hcZ⟩

end Core

section E8

variable {L : Type} [Field L]

theorem split_fixed_image_equiv {G : Type} [Group G] {k L : Type} [Field k] [Field L]
    [Algebra k L] (ρ : SL(3, L) →* G) (hρ : Function.Injective ρ)
    (Φ : SL(3, L) ≃* SL(3, L)) (H : SL(3, L))
    (hH : ∀ X : SL(3, L), X ∈ fixSubgroup Φ ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹)
    {P : Subgroup G} (hP : P = (fixSubgroup Φ).map ρ) : Nonempty (P ≃* SL(3, k)) := by
  let μ : SL(3, k) →* SL(3, L) :=
    (MulAut.conj H).toMonoidHom.comp (Matrix.SpecialLinearGroup.map (algebraMap k L))
  have hμ : Function.Injective μ := by
    intro a b hab
    have hmap : Matrix.SpecialLinearGroup.map (algebraMap k L) a =
        Matrix.SpecialLinearGroup.map (algebraMap k L) b := (MulAut.conj H).injective hab
    apply Subtype.ext
    ext i j
    apply (algebraMap k L).injective
    exact congrFun (congrFun (congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L)) hmap) i) j
  have hrange : μ.range = fixSubgroup Φ := by
    ext X
    constructor
    · rintro ⟨Y, rfl⟩
      exact (hH _).mpr ⟨Y, rfl⟩
    · intro hX
      obtain ⟨Y, hY⟩ := (hH X).mp hX
      exact ⟨Y, hY.symm⟩
  let eFix : SL(3, k) ≃* fixSubgroup Φ :=
    (MonoidHom.ofInjective hμ).trans (MulEquiv.subgroupCongr hrange)
  let eP : fixSubgroup Φ ≃* P :=
    (Subgroup.equivMapOfInjective (fixSubgroup Φ) ρ hρ).trans (MulEquiv.subgroupCongr hP.symm)
  exact ⟨(eFix.trans eP).symm⟩

theorem e8_a2_factor_with_model [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (v : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j : Fin 3, i ≠ j → weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • sigmaRootE8 v i j =
      if ε = 1 then sigmaRootE8 v (π i) (π j) else sigmaRootE8 v (π j) (π i)) :
    ∃ P : Subgroup (ModGL Tag.E8 L),
      P = rootSpan Tag.E8 L (sigmaSetE8 v) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      SigmaFactor n Fr (sigmaSetE8 v) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E8 L (sigmaSetE8 v) : Set (ModGL Tag.E8 L))) ∧
      (ε = 1 → Nonempty (P ≃* SL(3, k))) ∧
      ∃ h₀ : ModGL Tag.E8 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E8 L (e8Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! e he using fun (i j : Fin 3) (hij : i ≠ j) =>
    rhoSigmaE8_transvection (L := L) v i j hij
  have htor : ∀ b : Fin Tag.E8.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit Tag.E8 b * rhoSigmaE8 L v A * (rootDiagUnit Tag.E8 b)⁻¹ =
        rhoSigmaE8 L v (conjDiag3 d A) := fun b =>
    ⟨fun i => rootChar b (wbE8 v i), fun A => rhoSigmaE8_torus v b A⟩
  have hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      rhoSigmaE8 L v A ∈ torusGroup Tag.E8 L := fun A hA => rhoSigmaE8_diagonal v A hA
  have hrange := rhoSigmaE8_range (L := L) v
  have hS : ∀ r ∈ sigmaSetE8 v, IsRoot Tag.E8 r := fun r hr => by
    rw [sigmaSetE8_eq] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    exact isRoot_sigmaRootE8 v hij
  have hh₀ : ∀ (J : SL(3, L)) (Y : SL(2, k)),
      rhoSigmaE8 L v (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          J⁻¹) =
        (canonicalRep (coxeterSystem Tag.E8) L v * e8rhoJ L J) *
          simpleRootSL2 Tag.E8 L (e8Index 0)
            (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          (canonicalRep (coxeterSystem Tag.E8) L v * e8rhoJ L J)⁻¹ := by
    intro J Y
    have h1 : e8rhoJ L (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
        J⁻¹) = e8rhoJ L J * simpleRootSL2 Tag.E8 L (e8Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * (e8rhoJ L J)⁻¹ := by
      rw [map_mul, map_mul, map_inv, e8rhoJ_blockSL]
    change (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L v))
      (e8rhoJ L (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
        J⁻¹)) = _
    rw [h1, MulAut.conj_apply]
    group
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n * pinnedX Tag.E8 L (sigmaRootE8 v i j) c * n⁻¹ =
        pinnedX Tag.E8 L (weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • sigmaRootE8 v i j) ((b : L) * c) :=
    fun i j hij => monomial_conj_pinnedX hnm (isRoot_sigmaRootE8 v hij)
  rcases hε with rfl | rfl
  ·
    have hconj' : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX Tag.E8 L (sigmaRootE8 v i j) c * n⁻¹ =
          pinnedX Tag.E8 L (sigmaRootE8 v (π i) (π j)) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := hconj i j hij
      refine ⟨μ, fun c => ?_⟩
      rw [hμ c]
      have := hπ i j hij
      simp only [ite_true] at this
      rw [this]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E8) (ν := 3)
      (rhoSigmaE8 L v) (rhoSigmaE8_injective v) (sigmaRootE8 v) e he Fr hFrbij n
      (fun i j => (π i, π j)) (fun i j hij => π.injective.ne hij)
      (fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩) hconj'
    have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
          Matrix (Fin 3) (Fin 3) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f) :=
      fun i j hij t => by rw [hshape i j hij t, hFr]
    obtain ⟨-, ⟨H, hH⟩, ⟨J, hJ⟩, hfin, hq, -⟩ :=
      CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_split hℓ hf hk π Φ' b
        hshape'
    have := hfin
    obtain ⟨P, hP1, hP2, hfac⟩ := a2_factor_core hS (rhoSigmaE8 L v) (rhoSigmaE8_injective v)
      hrange htor hdiag Fr n Φ' hΦ' hq (centralizer_fix_split Φ' H hH)
    have hmodel : Nonempty (P ≃* SL(3, k)) :=
      split_fixed_image_equiv (rhoSigmaE8 L v) (rhoSigmaE8_injective v) Φ' H hH hP2
    refine ⟨P, hP1, hfac, fun _ => hmodel, canonicalRep (coxeterSystem Tag.E8) L v *
      e8rhoJ L J, fun Y => ?_⟩
    rw [hP2, ← hh₀ J Y]
    exact ⟨_, hJ Y, rfl⟩
  ·
    have hq2' := hq2 rfl
    have hconj' : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n * pinnedX Tag.E8 L (sigmaRootE8 v i j) c * n⁻¹ =
          pinnedX Tag.E8 L (sigmaRootE8 v (π j) (π i)) ((b : L) * c) := fun i j hij => by
      obtain ⟨μ, hμ⟩ := hconj i j hij
      refine ⟨μ, fun c => ?_⟩
      rw [hμ c]
      have := hπ i j hij
      simp only [show ¬ ((-1 : ℤ) = 1) by norm_num, ↓reduceIte] at this
      rw [this]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E8) (ν := 3)
      (rhoSigmaE8 L v) (rhoSigmaE8_injective v) (sigmaRootE8 v) e he Fr hFrbij n
      (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
      (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hconj'
    have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
          Matrix (Fin 3) (Fin 3) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f) :=
      fun i j hij t => by rw [hshape i j hij t, hFr]
    obtain ⟨-, ⟨H, hH⟩, ⟨J, hJ⟩, hfin, hbig⟩ :=
      CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary hℓ hf hk π Φ' b
        hshape'
    have := hfin
    obtain ⟨hq, -, -, -⟩ := hbig hq2'
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
    obtain ⟨P, hP1, hP2, hfac⟩ := a2_factor_core hS (rhoSigmaE8 L v) (rhoSigmaE8_injective v)
      hrange htor hdiag Fr n Φ' hΦ' hq (centralizer_fix_unitary hk Φ' H hH)
    have hmodel : (-1 : ℤ) = 1 → Nonempty (P ≃* SL(3, k)) := by
      intro hbad
      norm_num at hbad
    refine ⟨P, hP1, hfac, hmodel, canonicalRep (coxeterSystem Tag.E8) L v *
      e8rhoJ L J, fun Y => ?_⟩
    rw [hP2, ← hh₀ J Y]
    exact ⟨_, hJ Y, rfl⟩

end E8

end CFSG.RankThree.PartOne.KE6
