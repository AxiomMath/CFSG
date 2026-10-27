module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.E0Elements

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KF430

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding


@[expose] def cox : WeylGroup .G2 := rootReflection (vec 1 0) * rootReflection (vec 0 1)

theorem isRoot_vec10 : IsRoot .G2 (vec 1 0) := isRoot_of_mem_rootList (by decide)

theorem isRoot_vec01 : IsRoot .G2 (vec 0 1) := isRoot_of_mem_rootList (by decide)

theorem cox_smul (v : Fin Tag.G2.rank → ℤ) :
    cox • v = refl (vec 1 0) (refl (vec 0 1) v) := by
  rw [cox, mul_smul, QPlusModel.rootReflection_smul_eq_refl ℚ isRoot_vec01,
    QPlusModel.rootReflection_smul_eq_refl ℚ isRoot_vec10]

@[expose] def coxPre (v : Fin Tag.G2.rank → ℤ) : Fin Tag.G2.rank → ℤ :=
  refl (vec 0 1) (refl (vec 1 0) v)

theorem cox_coxPre10 : refl (vec 1 0) (refl (vec 0 1) (coxPre (vec 1 0))) = vec 1 0 := by decide

theorem cox_coxPre01 : refl (vec 1 0) (refl (vec 0 1) (coxPre (vec 0 1))) = vec 0 1 := by decide

theorem coxPre_mem_rootList : coxPre (vec 1 0) ∈ rootList ∧ coxPre (vec 0 1) ∈ rootList := by
  decide

@[expose] def coxAct (i j : ℤ) : ℤ × ℤ :=
  (cubeExp i j (coxPre (vec 1 0)), cubeExp i j (coxPre (vec 0 1)))

theorem coxAct_eq : ∀ i j : Fin 3,
    (toFin3 (coxAct i.val j.val).1, toFin3 (coxAct i.val j.val).2) = (2 * i, i + 2 * j) := by
  decide

variable {L : Type} [Field L]

theorem conj_cubeTuple3_cox {ζ : Lˣ} (hζ : orderOf ζ = 3) {n : ModGL .G2 L}
    (hn : n ∈ monomialSubgroup .G2 L) (hw : weylQuotientHom .G2 L ⟨n, hn⟩ = cox)
    (i j : Fin 3) :
    n * rootDiagUnit .G2 (cubeTuple3 ζ i j) * n⁻¹ =
      rootDiagUnit .G2 (cubeTuple3 ζ (2 * i) (i + 2 * j)) := by
  obtain ⟨a', h, hchar⟩ := exists_conj_rootDiagUnit hn (cubeTuple3 ζ i j)
  rw [h]
  congr 1
  have e0 : (vec 1 0 : Fin Tag.G2.rank → ℤ) = Pi.single ⟨0, by decide⟩ 1 := by
    funext k; fin_cases k <;> rfl
  have e1 : (vec 0 1 : Fin Tag.G2.rank → ℤ) = Pi.single ⟨1, by decide⟩ 1 := by
    funext k; fin_cases k <;> rfl
  have h0 := hchar _ (isRoot_of_mem_rootList coxPre_mem_rootList.1)
  have h1 := hchar _ (isRoot_of_mem_rootList coxPre_mem_rootList.2)
  have c0 : rootChar a' (vec 1 0) = a' ⟨0, by decide⟩ := by rw [e0, rootChar_single']
  have c1 : rootChar a' (vec 0 1) = a' ⟨1, by decide⟩ := by rw [e1, rootChar_single']
  rw [hw, cox_smul, cox_coxPre10, c0] at h0
  rw [hw, cox_smul, cox_coxPre01, c1] at h1
  have hfun : a' = cubeTuple ζ (coxAct i.val j.val).1 (coxAct i.val j.val).2 := by
    funext k
    fin_cases k
    · show a' ⟨0, _⟩ = _
      rw [h0, cubeTuple3, rootChar_cubeTuple]
      rfl
    · show a' ⟨1, _⟩ = _
      rw [h1, cubeTuple3, rootChar_cubeTuple]
      rfl
  rw [hfun, cubeTuple_eq_cubeTuple3 hζ]
  have := coxAct_eq i j
  rw [Prod.mk.injEq] at this
  rw [this.1, this.2]

theorem cox_sq_cube_move {ζ : Lˣ} (hζ : orderOf ζ = 3) {n : ModGL .G2 L}
    (hn : n ∈ monomialSubgroup .G2 L) (hw : weylQuotientHom .G2 L ⟨n, hn⟩ = cox) :
    n ^ 2 * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * (n ^ 2)⁻¹ ≠
        rootDiagUnit .G2 (cubeTuple3 ζ 1 0) ∧
      n ^ 3 * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * (n ^ 3)⁻¹ ≠
        rootDiagUnit .G2 (cubeTuple3 ζ 1 0) := by
  have step := conj_cubeTuple3_cox hζ hn hw
  have h2 : n ^ 2 * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * (n ^ 2)⁻¹ =
      rootDiagUnit .G2 (cubeTuple3 ζ 1 1) := by
    have e : n ^ 2 * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * (n ^ 2)⁻¹ =
        n * (n * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * n⁻¹) * n⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e, step, step]
    rfl
  have h3 : n ^ 3 * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * (n ^ 3)⁻¹ =
      rootDiagUnit .G2 (cubeTuple3 ζ 2 0) := by
    have e : n ^ 3 * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * (n ^ 3)⁻¹ =
        n * (n * (n * rootDiagUnit .G2 (cubeTuple3 ζ 1 0) * n⁻¹) * n⁻¹) * n⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e, step, step, step]
    rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h2] at h
    have := (cubeTuple3_injective hζ (rootDiagUnit_injective (τ := .G2) (K := L) h)).2
    exact absurd this (by decide)
  · rw [h3] at h
    have := (cubeTuple3_injective hζ (rootDiagUnit_injective (τ := .G2) (K := L) h)).1
    exact absurd this (by decide)

theorem rootWeyl_pair_mem_monomial (c₀ c₁ : Lˣ) :
    ∃ h : rootWeylSL2 .G2 L (vec 1 0) c₀ * rootWeylSL2 .G2 L (vec 0 1) c₁ ∈
        monomialSubgroup .G2 L,
      weylQuotientHom .G2 L ⟨_, h⟩ = cox := by
  obtain ⟨h₀, hw₀⟩ := (exceptional_Lang_root_rank_one_torus_transport .G2 L isRoot_vec10).2.2.1 c₀
  obtain ⟨h₁, hw₁⟩ := (exceptional_Lang_root_rank_one_torus_transport .G2 L isRoot_vec01).2.2.1 c₁
  refine ⟨mul_mem h₀ h₁, ?_⟩
  have : (⟨_, mul_mem h₀ h₁⟩ : monomialSubgroup .G2 L) = ⟨_, h₀⟩ * ⟨_, h₁⟩ := rfl
  rw [this, map_mul, hw₀, hw₁]
  rfl

theorem exists_conj_cube_one {n : ModGL .G2 L} (hn : n ∈ monomialSubgroup .G2 L)
    {a : Fin Tag.G2.rank → Lˣ} (ha : a ^ 3 = 1) :
    ∃ a' : Fin Tag.G2.rank → Lˣ, a' ^ 3 = 1 ∧
      n * rootDiagUnit .G2 a * n⁻¹ = rootDiagUnit .G2 a' := by
  obtain ⟨a', h, -⟩ := exists_conj_rootDiagUnit hn a
  refine ⟨a', ?_, h⟩
  apply rootDiagUnit_injective (τ := .G2) (K := L)
  change rootDiagUnitHom .G2 L (a' ^ 3) = rootDiagUnitHom .G2 L 1
  rw [map_pow, map_one]
  change rootDiagUnit .G2 a' ^ 3 = 1
  rw [← h, conj_pow]
  change n * rootDiagUnitHom .G2 L a ^ 3 * n⁻¹ = 1
  rw [← map_pow, ha, map_one, mul_one, mul_inv_cancel]

end CFSG.RankThree.PartTwo.KFacts.KF430
