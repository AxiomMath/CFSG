module

public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotRoots
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGLangCoroot
public import CFSG.LocalAnalysis.StandardType.GGLatDefs

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped commutatorElement

private theorem rootSL2_WSL_eq_pinnedX_of_charTwo
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootSL2 τ L γ WSL = pinnedX τ L γ 1 * pinnedX τ L (-γ) 1 * pinnedX τ L γ 1 := by
  have e : (WSL : SL2 L) = uSL 1 * vSL 1 * uSL 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  rw [e, map_mul, map_mul, rootSL2_uSL_of_charTwo hγ 1, rootSL2_vSL_of_charTwo hγ 1]

theorem step_rootSL2_WSL_of_charTwo
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L (S.ρ γ) WSL := by
  have hργ : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have h₁ := step_pinnedX_one_of_charTwo S hγ
  have h₂ := step_pinnedX_one_of_charTwo S (IsRoot.neg hγ)
  rw [S.frob.neg_eq] at h₂
  rw [rootSL2_WSL_eq_pinnedX_of_charTwo hγ, rootSL2_WSL_eq_pinnedX_of_charTwo hργ, map_mul,
    map_mul, h₁, h₂]

theorem rootSL2_mem_rootSpan_of_mem_rationalRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) (A : SL2 L) :
    rootSL2 τ L γ A ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
  have hr : IsRoot τ γ := isRoot_of_mem_rationalRoots S i hγ
  have hle : rootRankOneGroup τ L γ ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hr).1]
    exact sup_le (le_iSup₂_of_le γ hγ le_rfl)
      (le_iSup₂_of_le (-γ) (neg_mem_rationalRoots S i hγ) le_rfl)
  exact hle (MonoidHom.mem_range.2 ⟨A, rfl⟩)

private theorem perm_eq_one_of_cartan_F4 (π : Equiv.Perm (Fin Tag.F4.rank))
    (h : ∀ i j, Tag.F4.cartan (π i) (π j) = Tag.F4.cartan i j) : π = 1 := by
  have key : ∀ π : Equiv.Perm (Fin Tag.F4.rank),
      (∀ i j, tagCartanEntry .F4 (π i) (π j) = tagCartanEntry .F4 i j) → π = 1 := by
    decide +kernel
  exact key π h

private theorem iform_self_eq_two_E6
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have : Tag.E6.symmetrizer j j = 1 := by simp [Tag.symmetrizer]
  omega

private theorem not_isRoot_add_of_orthogonal_E6
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (h0 : iform α β = 0) : ¬ IsRoot Tag.E6 (α + β) := by
  intro h
  have h1 := iform_self_eq_two_E6 h
  have h2 : iform β α = 0 := by rw [iform_comm, h0]
  rw [iform_add_left, iform_add_right, iform_add_right, h0, h2, iform_self_eq_two_E6 hα,
    iform_self_eq_two_E6 hβ] at h1
  omega

private theorem rho_orthogonal_E6_sigma
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = ε • latPerm excDiagramSigmaE6 γ)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hπα : latPerm excDiagramSigmaE6 α ≠ α) :
    S.ρ (S.ρ α) = α ∧ iform α (S.ρ α) = 0 ∧ ¬ IsRoot Tag.E6 (α + S.ρ α) ∧
      ¬ IsRoot Tag.E6 (α - S.ρ α) := by
  have h0 : iform α (latPerm excDiagramSigmaE6 α) = 0 :=
    SeitzReduction.TwistedE6Pilot.iform_permLattice_eq_zero hα hπα
  have hρα : S.ρ α = ε • latPerm excDiagramSigmaE6 α := hρ α hα
  have hrρα : IsRoot Tag.E6 (S.ρ α) := (S.frob.isRoot_iff α).2 hα
  have hls : ∀ (c : ℤ) (v : Fin Tag.E6.rank → ℤ),
      latPerm excDiagramSigmaE6 (c • v) = c • latPerm excDiagramSigmaE6 v := fun c v => rfl
  have hσ : ∀ k : Fin Tag.E6.rank,
      excDiagramSigmaE6.symm (excDiagramSigmaE6.symm k) = k := by decide +kernel
  have hσσ : ∀ v : Fin Tag.E6.rank → ℤ,
      latPerm excDiagramSigmaE6 (latPerm excDiagramSigmaE6 v) = v := fun v =>
    funext fun k => by simp only [latPerm, hσ]
  have hρρ : S.ρ (S.ρ α) = α := by
    rw [hρ _ hrρα, hρα, hls, hσσ, smul_smul]
    rcases hε with rfl | rfl <;> simp
  have h0' : iform α (S.ρ α) = 0 := by rw [hρα, iform_smul_right, h0, mul_zero]
  refine ⟨hρρ, h0', not_isRoot_add_of_orthogonal_E6 hα hrρα h0', ?_⟩
  rw [sub_eq_add_neg]
  exact not_isRoot_add_of_orthogonal_E6 hα (IsRoot.neg hrρα)
    (by rw [iform_neg_right, h0', neg_zero])

theorem rho_orthogonal_of_latPerm_ne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hπα : latPerm π α ≠ α) :
    S.ρ (S.ρ α) = α ∧ iform α (S.ρ α) = 0 ∧ ¬ IsRoot τ (α + S.ρ α) ∧
      ¬ IsRoot τ (α - S.ρ α) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · rw [perm_eq_one_of_cartan_F4 π hπ] at hπα
    exact absurd rfl hπα
  · rcases perm_eq_one_or_eq_sigma_of_cartan_E6 π hπ with rfl | rfl
    · exact absurd rfl hπα
    · exact rho_orthogonal_E6_sigma S hε hρ hα hπα
  · rw [perm_eq_one_of_cartan_E7 π hπ] at hπα
    exact absurd rfl hπα
  · rw [perm_eq_one_of_cartan_E8 π hπ] at hπα
    exact absurd rfl hπα

private theorem corootPair_neg_of_isRoot
    {τ : Tag} {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (v : Fin τ.rank → ℤ) :
    corootPair (-δ) v = -corootPair δ v := by
  have h1 := corootPair_mul hδ v
  have h2 := corootPair_mul (IsRoot.neg hδ) v
  have hnn : iform (-δ) (-δ) = iform δ δ := by rw [iform_neg_left, iform_neg_right, neg_neg]
  apply mul_right_cancel₀ (iform_self_pos_of_isRoot hδ).ne'
  rw [neg_mul, h1, ← hnn, h2, iform_neg_left]
  ring

theorem langCorootPairFactor_of_orthogonal
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ f p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic)
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {α : Fin τ.rank → ℤ} (hα : α ∈ rationalRoots S.ρ (rootCharHom a) i)
    (hρρ : S.ρ (S.ρ α) = α) (h0 : iform α (S.ρ α) = 0) (hsum : ¬ IsRoot τ (α + S.ρ α))
    (hdiff : ¬ IsRoot τ (α - S.ρ α)) {ζ ξ : Lˣ} (hζ : ζ ^ p = 1) (hξ : ξ ^ p = 1)
    (hT : rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1) *
      ξ ^ corootPair (S.ρ α) (Pi.single j 1)) ∈ S.D.torus) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1) *
      ξ ^ corootPair (S.ρ α) (Pi.single j 1)) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq
  have hr : IsRoot τ α := isRoot_of_mem_rationalRoots S i hα
  have hrβ : IsRoot τ (S.ρ α) := (S.frob.isRoot_iff α).2 hr
  have hβ : S.ρ α ∈ rationalRoots S.ρ (rootCharHom a) i := by
    obtain ⟨k, δ, hδ, hk⟩ := hα
    exact ⟨k + 1, δ, hδ, by rw [hk, Function.iterate_succ_apply']⟩
  have hstepα := step_rootSL2_WSL_of_charTwo S hr
  have hstepβ := step_rootSL2_WSL_of_charTwo S hrβ
  rw [hρρ] at hstepβ
  generalize S.ρ α = β at h0 hsum hdiff hT hrβ hβ hstepα hstepβ ⊢
  have hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L α A) (rootSL2 τ L β B) := fun A B =>
    exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ L hr hrβ h0 hsum hdiff _
      (MonoidHom.mem_range.2 ⟨A, rfl⟩) _ (MonoidHom.mem_range.2 ⟨B, rfl⟩)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : SL2 L × SL2 L →* ModGL τ L,
      ∀ A B, Φ (A, B) = rootSL2 τ L α A * rootSL2 τ L β B :=
    ⟨MonoidHom.noncommCoprod (rootSL2 τ L α) (rootSL2 τ L β) hcomm, fun A B => rfl⟩
  have hwM : Φ (WSL, WSL) ∈ S.D.model := by
    refine ⟨?_, ?_⟩
    · rw [hΦ]
      exact mul_mem ((exceptional_Lang_root_rank_one_data τ L α).2.2.2.2.1 WSL)
        ((exceptional_Lang_root_rank_one_data τ L β).2.2.2.2.1 WSL)
    · change S.D.step (Φ (WSL, WSL)) = Φ (WSL, WSL)
      rw [hΦ, map_mul, hstepα, hstepβ]
      exact (hcomm WSL WSL).symm.eq
  have hw2 : Φ (WSL, WSL) ^ 2 = 1 := by
    rw [hΦ, (hcomm WSL WSL).mul_pow, pow_two, pow_two, rootSL2_WSL_mul_self α,
      rootSL2_WSL_mul_self β, one_mul]
  have hwΓ : Φ (WSL, WSL) ∈ S.Γ := langModel_mem_Γ_of_sq_eq_one S hτ hq hAlg hwM hw2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 2 * m := by
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    exact ⟨j + 1, by omega⟩
  have hhalf : ∀ c : Lˣ, c ^ p = 1 → (c ^ m) ^ 2 = c := fun c hc => by
    rw [← pow_mul, mul_comm, ← hm, pow_succ, hc, one_mul]
  have hpowcomm : ∀ (c : Lˣ) (x : ℤ), (c ^ m) ^ x = (c ^ x) ^ m := fun c x => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hd : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c : Lˣ, rootSL2 τ L γ (HSL c) =
      rootDiagUnit τ (fun j => c ^ corootPair γ (Pi.single j 1)) := fun γ hγ c =>
    CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hγ c
  have hhd : Φ (HSL (ζ ^ m), HSL (ξ ^ m)) = (rootDiagUnit τ (fun j =>
      ζ ^ corootPair α (Pi.single j 1) * ξ ^ corootPair β (Pi.single j 1))) ^ m := by
    rw [hΦ, hd α hr, hd β hrβ, ← rootDiagUnit_mul, rootDiagUnit_pow]
    congr 1
    funext j
    simp only [Pi.mul_apply, Pi.pow_apply, mul_pow, hpowcomm]
  have hhT : Φ (HSL (ζ ^ m), HSL (ξ ^ m)) ∈ S.D.torus := by
    rw [hhd]
    exact pow_mem hT m
  have hhM : Φ (HSL (ζ ^ m), HSL (ξ ^ m)) ∈ S.D.model := S.D.torus_le_model hhT
  have hHW : ∀ t : Lˣ, (HSL t : SL2 L) ^ 2 = ⁅HSL t, (WSL : SL2 L)⁆ := by
    intro t
    rw [commutatorElement_HSL_WSL]
    ext i j
    simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_HSL]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sq]
  have hsq : Φ (HSL (ζ ^ m), HSL (ξ ^ m)) ^ 2 =
      ⁅Φ (HSL (ζ ^ m), HSL (ξ ^ m)), Φ (WSL, WSL)⁆ := by
    rw [← map_pow, ← map_commutatorElement]
    exact congrArg Φ (Prod.ext (hHW _) (hHW _))
  have hhΓ : Φ (HSL (ζ ^ m), HSL (ξ ^ m)) ∈ S.Γ := by
    refine langModel_mem_Γ_of_sq_mem S hτ hq hAlg hhM ?_
    rw [hsq]
    exact Subgroup.commutator_mem_commutator hhM hwM
  have hspanα := rootSL2_mem_rootSpan_of_mem_rationalRoots S i hα
  have hspanβ := rootSL2_mem_rootSpan_of_mem_rationalRoots S i hβ
  have hhspan : Φ (HSL (ζ ^ m), HSL (ξ ^ m)) ∈
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [hΦ]
    exact mul_mem (hspanα _) (hspanβ _)
  have hwspan : Φ (WSL, WSL) ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [hΦ]
    exact mul_mem (hspanα _) (hspanβ _)
  have key : ⁅Φ (HSL (ζ ^ m), HSL (ξ ^ m)), Φ (WSL, WSL)⁆ ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_mem_commutator ⟨hhspan, hhΓ⟩ ⟨hwspan, hwΓ⟩
  rw [← hsq] at key
  have hHSL2 : ∀ t : Lˣ, (HSL t : SL2 L) ^ 2 = HSL (t ^ 2) := fun t =>
    (hHW t).trans (commutatorElement_HSL_WSL t)
  have hh2 : Φ (HSL (ζ ^ m), HSL (ξ ^ m)) ^ 2 = rootDiagUnit τ (fun j =>
      ζ ^ corootPair α (Pi.single j 1) * ξ ^ corootPair β (Pi.single j 1)) := by
    rw [← map_pow]
    change Φ ((HSL (ζ ^ m)) ^ 2, (HSL (ξ ^ m)) ^ 2) = _
    rw [hHSL2, hHSL2, hhalf ζ hζ, hhalf ξ hξ, hΦ, hd α hr, hd β hrβ, ← rootDiagUnit_mul]
    rfl
  rw [hh2] at key
  exact key

theorem langCorootPairFactor
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ f p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic)
    (hp : p.Prime) (hp2 : p ≠ 2) (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {α : Fin τ.rank → ℤ}
    (hα : α ∈ rationalRoots S.ρ (rootCharHom a) i) (hπα : latPerm π α ≠ α) {ζ ξ : Lˣ}
    (hζ : ζ ^ p = 1) (hξ : ξ ^ p = 1)
    (hT : rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1) *
      ξ ^ corootPair (latPerm π α) (Pi.single j 1)) ∈ S.D.torus) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1) *
      ξ ^ corootPair (latPerm π α) (Pi.single j 1)) ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hr : IsRoot τ α := isRoot_of_mem_rationalRoots S i hα
  obtain ⟨hρρ, h0, hsum, hdiff⟩ := rho_orthogonal_of_latPerm_ne S hτ π hπ hε hρ hr hπα
  have hρα : S.ρ α = ε • latPerm π α := hρ α hr
  have hrρ : IsRoot τ (S.ρ α) := (S.frob.isRoot_iff α).2 hr
  rcases hε with rfl | rfl
  · rw [one_smul] at hρα
    rw [← hρα] at hT ⊢
    exact langCorootPairFactor_of_orthogonal S hτ hq hAlg hp hp2 i hα hρρ h0 hsum hdiff hζ hξ hT
  · rw [neg_one_smul] at hρα
    have hπroot : IsRoot τ (latPerm π α) := by
      have h1 := IsRoot.neg hrρ
      rwa [hρα, neg_neg] at h1
    have hconv : (fun j => ζ ^ corootPair α (Pi.single j 1) *
        ξ⁻¹ ^ corootPair (S.ρ α) (Pi.single j 1)) = fun j => ζ ^ corootPair α (Pi.single j 1) *
          ξ ^ corootPair (latPerm π α) (Pi.single j 1) := by
      funext j
      rw [hρα, corootPair_neg_of_isRoot hπroot, zpow_neg, inv_zpow, inv_inv]
    have hξ' : ξ⁻¹ ^ p = 1 := by rw [inv_pow, hξ, inv_one]
    rw [← hconv] at hT ⊢
    exact langCorootPairFactor_of_orthogonal S hτ hq hAlg hp hp2 i hα hρρ h0 hsum hdiff hζ hξ' hT

end CFSG.StandardType.LangRat
