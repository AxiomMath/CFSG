module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
public import CFSG.LocalAnalysis.StandardType.GGLangModelIndex
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped commutatorElement

theorem charP_two_of_langSetup_q_eq_two_pow
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ f : ℕ} (S : LangSetup τ L p₀) (hq : S.D.q = 2 ^ f) : CharP L 2 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h := S.hqpow.1
    rw [hq, pow_zero] at h
    exact not_isPrimePow_one h
  have h2L : ((2 : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf0).1 h
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2L

theorem step_pinnedX_one_of_charTwo
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    S.D.step (pinnedX τ L γ 1) = pinnedX τ L (S.ρ γ) 1 := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨π, hπroot, -, -, hπ⟩ := exists_diagram_data (L := L) hP
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ε₁, hε₁, h₁⟩ := hπ γ hγ
  have hπγ : IsRoot τ (π γ) := (hπroot γ).2 hγ
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hπγ
  have e₁ := eq_one_of_mul_self_eq_one_of_charTwo hε₁
  have e₂ := eq_one_of_mul_self_eq_one_of_charTwo hε₂
  have hs : S.D.step (pinnedX τ L γ 1) = pinnedX τ L (w • π γ) 1 := by
    have h0 : S.D.step (pinnedX τ L γ 1) = S.D.n * S.D.Φ (pinnedX τ L γ 1) * S.D.n⁻¹ := by
      simp [LangDatum.step, MulAut.conj_apply]
    rw [h0, hΦ, units_map_entrywiseHom_pinnedX, map_one, h₁, e₁, one_mul, hn, h₂, e₂, one_mul]
  have hmem : S.D.step (pinnedX τ L γ 1) ∈ rootSubgroup τ L (S.ρ γ) := by
    rw [← S.frob.map_rootSubgroup γ hγ]
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨1, rfl⟩)
  rw [hs] at hmem ⊢
  have hroot : IsRoot τ (w • π γ) := (isRoot_smul_iff w).2 hπγ
  rw [eq_of_pinnedX_one_mem_rootSubgroup hroot ((S.frob.isRoot_iff γ).2 hγ) hmem]

theorem rootSL2_WSL_mem_model_of_rho
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hρ : S.ρ γ = γ ∨ S.ρ γ = -γ) :
    rootSL2 τ L γ WSL ∈ S.D.model := by
  have h₁ := step_pinnedX_one_of_charTwo S hγ
  have h₂ := step_pinnedX_one_of_charTwo S (IsRoot.neg hγ)
  rw [S.frob.neg_eq] at h₂
  rcases hρ with h | h
  · rw [h] at h₁ h₂
    have hu := rootSL2_uSL_of_charTwo (K := L) hγ 1
    have hv := rootSL2_vSL_of_charTwo (K := L) hγ 1
    have e₁ : (WSL : SL2 L) = uSL 1 * vSL 1 * uSL 1 := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
    refine ⟨(exceptional_Lang_root_rank_one_data τ L γ).2.2.2.2.1 WSL, ?_⟩
    change S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L γ WSL
    rw [e₁]
    simp only [map_mul, hu, hv, h₁, h₂]
  · rw [h] at h₁ h₂
    rw [neg_neg] at h₂
    exact rootSL2_WSL_mem_model S.D hγ h₁ h₂

theorem isRoot_of_mem_rationalRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) : IsRoot τ γ := by
  obtain ⟨k, δ, hδ, rfl⟩ := hγ
  induction k with
  | zero => exact hδ.1.1
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (S.frob.isRoot_iff _).2 ih

theorem neg_mem_rationalRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) :
    -γ ∈ rationalRoots S.ρ (rootCharHom a) i := by
  obtain ⟨k, δ, hδ, rfl⟩ := hγ
  exact ⟨k, -δ, (isRootComponent_componentRoots i).neg_mem δ hδ, (rho_iterate_neg S k δ).symm⟩

theorem rootSL2_HSL_sq_mem_rationalComponent_of_mem_rationalRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) {t : Lˣ}
    (ht : rootSL2 τ L γ (HSL t) ∈ S.Γ) (hW : rootSL2 τ L γ WSL ∈ S.Γ) :
    rootSL2 τ L γ (HSL (t ^ 2)) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hr : IsRoot τ γ := isRoot_of_mem_rationalRoots S i hγ
  have hle : rootRankOneGroup τ L γ ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hr).1]
    exact sup_le (le_iSup₂_of_le γ hγ le_rfl)
      (le_iSup₂_of_le (-γ) (neg_mem_rationalRoots S i hγ) le_rfl)
  have hmem : ∀ A, rootSL2 τ L γ A ∈ S.Γ →
      rootSL2 τ L γ A ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    fun A h => ⟨hle (MonoidHom.mem_range.2 ⟨A, rfl⟩), h⟩
  rw [← commutatorElement_HSL_WSL, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (hmem _ ht) (hmem _ hW)

theorem langModel_mem_Γ_of_sq_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hq : S.D.q = 2 ^ f)
    (hAlg : S.IsAlgebraic) {m : ModGL τ L} (hm : m ∈ S.D.model) (hm2 : m ^ 2 ∈ S.Γ) :
    m ∈ S.Γ := by
  obtain ⟨k, hk⟩ := langModel_pow_mem_Γ S hτ hq hAlg
  exact mem_of_sq_mem_of_pow_mem S.Γ k (hk m hm) hm2

theorem langCorootFactor
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ f p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic)
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {α : Fin τ.rank → ℤ} (hα : α ∈ rationalRoots S.ρ (rootCharHom a) i)
    (hρα : S.ρ α = α ∨ S.ρ α = -α) {ζ : Lˣ} (hζ : ζ ^ p = 1)
    (hT : rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) ∈ S.D.torus) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq
  have hr : IsRoot τ α := isRoot_of_mem_rationalRoots S i hα
  have hwM : rootSL2 τ L α WSL ∈ S.D.model := rootSL2_WSL_mem_model_of_rho S hr hρα
  have hwΓ : rootSL2 τ L α WSL ∈ S.Γ :=
    langModel_mem_Γ_of_sq_eq_one S hτ hq hAlg hwM (by rw [pow_two]; exact rootSL2_WSL_mul_self α)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 2 * m := by
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    exact ⟨j + 1, by omega⟩
  obtain ⟨η, hη⟩ : ∃ η : Lˣ, η = ζ ^ m := ⟨_, rfl⟩
  have hηζ : η ^ 2 = ζ := by
    rw [hη, ← pow_mul, mul_comm, ← hm, pow_succ, hζ, one_mul]
  have hd : ∀ c : Lˣ, rootSL2 τ L α (HSL c) =
      rootDiagUnit τ (fun j => c ^ corootPair α (Pi.single j 1)) :=
    fun c =>
      CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hr c
  have hhT : rootSL2 τ L α (HSL η) ∈ S.D.torus := by
    have h1 : rootSL2 τ L α (HSL η) =
        (rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1))) ^ m := by
      rw [hd, rootDiagUnit_pow]
      congr 1
      funext j
      simp only [Pi.pow_apply, hη]
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h1]
    exact pow_mem hT m
  have hhM : rootSL2 τ L α (HSL η) ∈ S.D.model := S.D.torus_le_model hhT
  have hsq : rootSL2 τ L α (HSL η) ^ 2 = ⁅rootSL2 τ L α (HSL η), rootSL2 τ L α WSL⁆ := by
    have e : (HSL η : SL2 L) ^ 2 = HSL (η ^ 2) := by
      ext i j
      simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_HSL]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sq]
    rw [← map_commutatorElement, commutatorElement_HSL_WSL, ← e, map_pow]
  have hhΓ : rootSL2 τ L α (HSL η) ∈ S.Γ := by
    refine langModel_mem_Γ_of_sq_mem S hτ hq hAlg hhM ?_
    rw [hsq]
    exact Subgroup.commutator_mem_commutator hhM hwM
  have key := rootSL2_HSL_sq_mem_rationalComponent_of_mem_rationalRoots S i hα hhΓ hwΓ
  rw [hηζ, hd] at key
  exact key

end CFSG.StandardType.LangRat
