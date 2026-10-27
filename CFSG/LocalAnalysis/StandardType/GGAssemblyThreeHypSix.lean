module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Input

@[expose] def GGInnerDiagMpInputOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → ∀ G₀ : Subgroup G, ψ.range = G₀ →
    ∀ P : LargeEvenMarkProp ↥G₀,
      LargeEvenMarking ↥G₀ (fun lab R _ I F θ => S lab ∧ P lab R I F θ) →
      LargeEvenMarking ↥G₀ (fun lab R _ I F θ => P lab R I F θ ∧
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
          (∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) →
            GGPsiInnerDiag (ggU t n f).D ψ c)

theorem ggInnerDiagMpInput_of_on {S : LargeEvenLabel → Prop} (hS : GGInnerDiagMpInputOn S)
    (hT : GGInnerDiagMpInputOn fun lab => ¬ S lab) : GGInnerDiagMpInput := by
  intro G _ _ t n f ψ hadm hrk hker G₀ hrange P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  by_cases h : S lab
  · exact hS G t n f ψ hadm hrk hker G₀ hrange P ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, h, hθ⟩) hraw⟩
  · exact hT G t n f ψ hadm hrk hker G₀ hrange P ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, h, hθ⟩) hraw⟩

theorem ggInnerDiagMpInputOn_of_subset_inn {S : LargeEvenLabel → Prop}
    (hI : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R)) :
    GGInnerDiagMpInputOn S := by
  intro G _ _ t n f ψ _ _ _ G₀ hrange P hP
  subst hrange
  have hperf : commutator ↥ψ.range = ⊤ := hP.1
  exact largeEvenMarking_mono (fun _ _ _ _ _ θ h => ⟨h.1.2, fun c hc hc' =>
      ggPsiInnerDiag_of_induces_mem_inn _ ψ hperf θ h.2 hc hc'⟩)
    (largeEvenMarking_and_labelAll_simple hI (fun _ _ _ _ _ _ h => h.1) hP)

end Input

section Linear

variable {K : Type} [Field K]

theorem matConjImage_gl_subset_inn [Finite K] {d : ℕ} (hd : (Nat.card Kˣ).Coprime d) :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
  rintro φ ⟨A, -, hφ⟩
  set l : Kˣ := (powCoprime hd).symm (Matrix.GeneralLinearGroup.det A) with hl
  have hld : l ^ d = Matrix.GeneralLinearGroup.det A := by
    rw [hl, ← powCoprime_apply hd, Equiv.apply_symm_apply]
  set A' := Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ * A with hA'
  have hA'SL : A' ∈ LargeEvenSLGroup (Fin d) K := by
    rw [LargeEvenSLGroup, MonoidHom.mem_ker, hA', map_mul, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin, inv_pow, hld, inv_mul_cancel]
  have hconj : ∀ h : GL (Fin d) K, A' * h * A'⁻¹ = A * h * A⁻¹ := by
    intro h
    have hc := Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin d) l⁻¹)
    rw [hA', mul_inv_rev]
    set s := Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹
    calc s * A * h * (A⁻¹ * s⁻¹) = s * (A * h * A⁻¹) * s⁻¹ := by group
      _ = (A * h * A⁻¹) * s * s⁻¹ := by rw [hc (A * h * A⁻¹)]
      _ = A * h * A⁻¹ := by group
  obtain ⟨a, ha⟩ : ∃ a : LargeEvenSLGroup (Fin d) K, (a : GL (Fin d) K) = A' :=
    ⟨⟨A', hA'SL⟩, rfl⟩
  refine ⟨(a : LargeEvenProj (LargeEvenSLGroup (Fin d) K)), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hrel : ((a * h * a⁻¹ : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) = A * h * A⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      exact hconj h
    exact (hφ h (a * h * a⁻¹) hrel).symm

end Linear

theorem ggOdd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 * k + 2 := ⟨2 ^ (n - 1) - 1, by
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega⟩
  exact ⟨k, by omega⟩

section Labels

theorem recipeLinear_subsetInn {d N : ℕ} {Q : LargeEvenRawCont} (hd : (N - 1).Coprime d)
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have hcard : Nat.card Kˣ = N - 1 := by rw [Nat.card_units, hK]
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    matConjImage_gl_subset_inn (by rw [hcard]; exact hd)⟩

theorem recipeSymplectic_subsetInn {m n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ φ hφ => matConjImage_gsp_subset_inn m hφ⟩

theorem recipeOmegaPlus_subsetInn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => subset_rfl⟩

theorem recipeOmegaMinus_subsetInn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m q Q) :
    LargeEvenRecipeOmegaMinus m q fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, fun _ _ => subset_rfl⟩

theorem recipeSuzuki_subsetInn {a : ℕ} {Q : LargeEvenRawCont} (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => subset_rfl⟩

theorem recipeChevalley_subsetInn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ}
    {derived : Bool} {Q : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      LargeEvenChevIDImage A K (LargeEvenChevH A K derived) ⊆
        (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH A K derived) →*
          MulAut (LargeEvenCenterQuot (LargeEvenChevH A K derived))).range)
    (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => I ⊆ LargeEvenInnSet R) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ φ hφ => hA K hK hφ⟩

@[expose] def GGLinearInnLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ (2 ^ lab.n - 1).Coprime (lab.rank + 1)) ∨ (lab.tag = .D ∧ lab.rank = 3) ∨
    (lab.tag = .twD ∧ lab.rank = 2)

@[expose] def GGInnerDiagInnLabel (lab : LargeEvenLabel) : Prop :=
  GGInndiagInnLabel lab ∨ lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
    lab.tag = .G2der ∨ lab.tag = .twF4der ∨ GGLinearInnLabel lab

theorem largeEvenLabelAll_subset_inn
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGInnerDiagInnLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  intro Q hQ
  rcases h with (h | h | ⟨h, hl3⟩ | ⟨h, hl2, hl3⟩ | h) | h | h | h | h | h | h |
    ⟨h, hc⟩ | ⟨h, hl3⟩ | ⟨h, hl2⟩
  · dsimp only at h
    subst h
    exact recipeSymplectic_subsetInn hQ
  · dsimp only at h
    subst h
    exact recipeSymplectic_subsetInn hQ
  · dsimp only at h hl3
    subst h
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [hl3, ↓reduceIte] at hQ ⊢
    exact recipeOmegaPlus_subsetInn hQ
  · dsimp only at h hl2 hl3
    subst h
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [hl2, hl3, ↓reduceIte] at hQ ⊢
    exact recipeOmegaMinus_subsetInn hQ
  · dsimp only at h
    subst h
    exact recipeSuzuki_subsetInn hQ
  · dsimp only at h
    subst h
    exact recipeChevalley_subsetInn (fun K _ _ _ =>
      chevIDImage_subset_inn_of_top (τ := .G2) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)) hQ
  · dsimp only at h
    subst h
    exact recipeChevalley_subsetInn (fun K _ _ _ =>
      chevIDImage_subset_inn_of_top (τ := .F4) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩)) hQ
  · dsimp only at h
    subst h
    exact recipeChevalley_subsetInn (fun K _ _ hK => by
      have := charP_two_of_card hK
      exact chevIDImage_subset_inn_of_top (τ := .E7)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE7_adj
          (TableB.exists_sq_eq_of_charTwo K))) hQ
  · dsimp only at h
    subst h
    exact recipeChevalley_subsetInn (fun K _ _ _ =>
      chevIDImage_subset_inn_of_top (τ := .E8) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩)) hQ
  · dsimp only at h
    subst h
    exact recipeChevalley_subsetInn (fun K _ _ hK => by
      have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
      exact chevIDImage_subset_inn_of_subsingleton _) hQ
  · dsimp only at h
    subst h
    obtain ⟨-, hn1⟩ := hl
    subst hn1
    exact recipeTwF4_and (P := LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R)
      (fun K _ _ hK _ _ φ hφ => by
        have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two
          (K := K) (by simpa using hK)
        exact chevIDImage_subset_inn_of_subsingleton _ hφ) hQ
  · dsimp only at h hc
    subst h
    exact recipeLinear_subsetInn hc hQ
  · dsimp only at h hl3
    subst h hl3
    exact recipeLinear_subsetInn (by
      simpa using Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (ggOdd_two_pow_sub_one hn)))
      hQ
  · dsimp only at h hl2
    subst h hl2
    exact recipeLinear_subsetInn (Nat.coprime_two_right.mpr (by
      rw [← pow_mul]; exact ggOdd_two_pow_sub_one (by omega))) hQ

end Labels

section Rest

theorem ggInnerDiagMpInput_of_rest
    (h : GGInnerDiagMpInputOn fun lab => ¬ GGInnerDiagInnLabel lab) : GGInnerDiagMpInput :=
  ggInnerDiagMpInput_of_on (ggInnerDiagMpInputOn_of_subset_inn fun _ hlab hS =>
    largeEvenLabelAll_subset_inn hlab hS) h

end Rest

end CFSG.StandardType
