module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

private theorem psl34c_sq_apply_eq_self {F : Type} [Field F] (hF : Nat.card F = 4)
    (σ : F ≃+* F) (a : F) : σ (σ a) = a := by
  obtain ⟨ω, hω0, hω1⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.exists_ne_zero_ne_one hF
  have hc : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  have hcases : ∀ x : F, x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1 := fun x =>
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.eq_zero_or_eq_one_or hF hω0 hω1 x
  have hσω0 : σ ω ≠ 0 := fun h => hω0 (σ.injective (by rw [h, map_zero]))
  have hσω1 : σ ω ≠ 1 := fun h => hω1 (σ.injective (by rw [h, map_one]))
  have hσσω : σ (σ ω) = ω := by
    rcases hcases (σ ω) with h | h | h | h
    · exact absurd h hσω0
    · exact absurd h hσω1
    · rw [h, h]
    · rw [h, map_add, map_one, h]
      linear_combination CharTwo.add_self_eq_zero (1 : F)
  rcases hcases a with rfl | rfl | rfl | rfl
  · rw [map_zero, map_zero]
  · rw [map_one, map_one]
  · exact hσσω
  · rw [map_add, map_one, map_add, map_one, hσσω]

private theorem psl34c_ringEquiv_mul_self {F : Type} [Field F] (hF : Nat.card F = 4)
    (σ : F ≃+* F) : σ * σ = 1 :=
  RingEquiv.ext fun a => psl34c_sq_apply_eq_self hF σ a

private theorem psl34c_sq_mem {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal) {c β : G}
    (hc : c ∈ N) (hβ : β * β = 1) : (c * β) ^ 2 ∈ N := by
  have hinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
  have h : (c * β) ^ 2 = c * (β * c * β⁻¹) := by
    rw [hinv, sq]
    simp only [mul_assoc]
  rw [h]
  exact N.mul_mem hc (hN.conj_mem c hc β)

private theorem psl34c_sq_mem_linear {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (β : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) :
    β ^ 2 ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F := by
  obtain ⟨-, hform⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation (K := F) (n := 3)
      (by norm_num)
  have hN : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F).Normal :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_normal_of_three_le (K := F)
      (n := 3) (by norm_num)
  have htrans :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport (K := F)
      (n := 3)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform β
  have hδf := htrans.2.2.2.2.2.1
  have hff : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ = 1 := by
    rw [htrans.2.1 σ σ, psl34c_ringEquiv_mul_self hF σ, map_one]
  rw [mul_assoc]
  refine psl34c_sq_mem hN
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_linearAutGroup A) ?_
  interval_cases ε
  · simpa using hff
  · rw [pow_one]
    calc _ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ *
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 3 F *
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ *
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 3 F) := by
          simp only [mul_assoc]
      _ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ := by
          rw [hδf σ]
      _ = 1 := hff

private theorem psl34c_card_linearAutGroup {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F) = 60480 := by
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 181440 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq 3, hF] <;>
      first | rfl | decide | norm_num [Finset.prod_Icc_succ_top]
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 3) : Fˣ →* Matrix.GeneralLinearGroup (Fin 3) F) := by
    intro u v huv
    have h := congrArg
      (fun g : Matrix.GeneralLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) huv
    exact Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h)
  have hker : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F).ker =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Fˣ →* Matrix.GeneralLinearGroup (Fin 3) F).range := by
    ext A
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
    exact CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_one_iff (by norm_num) A
  have hkc : Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F).ker = 3 := by
    rw [hker, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_units]
    omega
  have h1 :=
    Subgroup.card_ker_mul_card_range (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F)
  rw [hkc, hGL] at h1
  have hDeq : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F =
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F).range := by
    apply le_antisymm
    · unfold CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup
      rw [Subgroup.closure_le]
      rintro _ ⟨A, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨A, rfl⟩
    · rintro _ ⟨A, rfl⟩
      exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_linearAutGroup A
  rw [hDeq]
  omega

theorem psl34_aut_structure {K : Type} [Group K] [Finite K] (hK : IsPSL 3 2 2 K)
    (haut : Nat.card (MulAut K) = 241920) :
    ∃ P : Subgroup (MulAut K), P.Normal ∧ P.index = 4 ∧
      (MulAut.conj : K →* MulAut K).range ≤ P ∧ ∀ α : MulAut K, α ^ 2 ∈ P := by
  obtain ⟨-, F, hFld, hFfin, hF, ⟨e0⟩⟩ := hK
  have hF4 : Nat.card F = 4 := hF.trans (by norm_num)
  obtain ⟨e⟩ : Nonempty (K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    ⟨(e0.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F)⟩
  have hN : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F).Normal :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_normal_of_three_le (K := F)
      (n := 3) (by norm_num)
  have hφ : Function.Surjective (MulAut.congr e).toMonoidHom := (MulAut.congr e).surjective
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F).comap
    (MulAut.congr e).toMonoidHom, hN.comap _, ?_, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective
      (H := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F) hφ]
    have hD := psl34c_card_linearAutGroup hF4
    have hM : Nat.card (MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F))
        = 241920 :=
      (Nat.card_congr (MulAut.congr e).toEquiv).symm.trans haut
    have h := Subgroup.card_mul_index
      (H := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 F)
    rw [hD, hM] at h
    omega
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_comap]
    have hconj : (MulAut.congr e).toMonoidHom (MulAut.conj g) = MulAut.conj (e g) := by
      ext y
      simp [MulAut.conj_apply]
    rw [hconj]
    exact CFSG.RankThree.PartTwo.KFacts.innAut_le_linearAutGroup 3 F
      (MonoidHom.mem_range.mpr ⟨e g, rfl⟩)
  · intro α
    rw [Subgroup.mem_comap, map_pow]
    exact psl34c_sq_mem_linear hF4 _

end CFSG.Quasithin.H13.S126P31
