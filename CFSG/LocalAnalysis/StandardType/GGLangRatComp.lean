module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.Chevalley

open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem commutatorElement_HSL_WSL {L : Type*} [Field L] (t : Lˣ) :
    ⁅HSL t, (WSL : SL2 L)⁆ = HSL (t ^ 2) := by
  rw [commutatorElement_def]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_HSL,
    coe_WSL, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sq]

theorem WSL_conj_HSL {L : Type} [Field L] (a : Lˣ) :
    (WSL : SL2 L) * HSL a * WSL⁻¹ = HSL a⁻¹ := by
  have h1 : (WSL : SL2 L) * HSL a = HSL a⁻¹ * WSL := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

section Roots

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}

theorem rationalRoots_eq_of_rho_neg (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    (i : KernelComponent (rootCharHom a)) :
    rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  have hΨ := isRootComponent_componentRoots i
  refine Set.Subset.antisymm ?_ fun γ hγ => ⟨0, γ, hγ, rfl⟩
  rintro _ ⟨k, δ, hδ, rfl⟩
  induction k with
  | zero => exact hδ
  | succ k ih =>
    rw [Function.iterate_succ_apply', hρ _ (hΨ.isRoot _ ih)]
    exact hΨ.neg_mem _ ih

end Roots

section Comp

variable
  {τ : Tag} {L : Type} [Field L]

theorem rationalComponent_le_centralizer [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {b : Fin τ.rank → Lˣ}
    (hb : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Subgroup.centralizer {rootDiagUnit τ b} := by
  have hr : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, IsRoot τ γ := by
    rintro _ ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ.1.1
    | succ k ih => rw [Function.iterate_succ_apply']; exact (S.frob.isRoot_iff _).2 ih
  have hRS : ⁅rationalSpan S.ρ S.Γ (rootCharHom a) i, rationalSpan S.ρ S.Γ (rootCharHom a) i⁆ ≤
      rationalSpan S.ρ S.Γ (rootCharHom a) i := Subgroup.commutator_le.2 fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  exact hRS.trans (inf_le_left.trans (rootSpan_le_centralizer b fun γ hγ => ⟨hr γ hγ, hb γ hγ⟩))

theorem rootSL2_HSL_sq_mem_rationalComponent [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) {t : Lˣ} (ht : rootSL2 τ L γ (HSL t) ∈ S.Γ)
    (hW : rootSL2 τ L γ WSL ∈ S.Γ) :
    rootSL2 τ L γ (HSL (t ^ 2)) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hΨ := isRootComponent_componentRoots i
  have hle : rootRankOneGroup τ L γ ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L (hΨ.isRoot γ hγ)).1]
    exact sup_le (le_iSup₂_of_le γ ⟨0, γ, hγ, rfl⟩ le_rfl)
      (le_iSup₂_of_le (-γ) ⟨0, -γ, hΨ.neg_mem γ hγ, rfl⟩ le_rfl)
  have hmem : ∀ A, rootSL2 τ L γ A ∈ S.Γ →
      rootSL2 τ L γ A ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    fun A h => ⟨hle (MonoidHom.mem_range.2 ⟨A, rfl⟩), h⟩
  rw [← commutatorElement_HSL_WSL, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (hmem _ ht) (hmem _ hW)

theorem rootSL2_HSL_mem_rationalComponent_of_model_pow [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i)
    (hW : rootSL2 τ L γ WSL ∈ S.Γ)
    {t : Lˣ} (hmodel : rootSL2 τ L γ (HSL t) ∈ S.D.model)
    {k : ℕ} (hk : 1 ≤ k) (hpow : t ^ (2 ^ k) = t) :
    rootSL2 τ L γ (HSL t) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have h2 : rootSL2 τ L γ (HSL (t ^ 2)) ∈ S.Γ := by
    rw [← commutatorElement_HSL_WSL, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hmodel
      (Subgroup.commutator_le_self S.D.model hW)
  have hRΓ : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.Γ :=
    (Subgroup.commutator_le_self
      (rationalSpan S.ρ S.Γ (rootCharHom a) i)).trans inf_le_right
  have hmem : ∀ j : ℕ, 1 ≤ j →
      rootSL2 τ L γ (HSL (t ^ (2 ^ (j + 1)))) ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      have h := rootSL2_HSL_sq_mem_rationalComponent S i hγ (t := t ^ 2) h2 hW
      have h4 : (t ^ 2) ^ 2 = t ^ (2 ^ (1 + 1)) := by
        rw [← pow_mul]
        norm_num
      rwa [h4] at h
    | succ j _ ih =>
      have hΓ : rootSL2 τ L γ (HSL (t ^ (2 ^ (j + 1)))) ∈ S.Γ := hRΓ ih
      have h := rootSL2_HSL_sq_mem_rationalComponent S i hγ
        (t := t ^ (2 ^ (j + 1))) hΓ hW
      rwa [← pow_mul, ← pow_succ] at h
  rcases lt_or_eq_of_le hk with hk2 | rfl
  · have hk' : 1 ≤ k - 1 := by omega
    have h := hmem (k - 1) hk'
    rwa [Nat.sub_add_cancel (le_of_lt hk2), hpow] at h
  · have h2t : t ^ 2 = t := by simpa using hpow
    have h4 : t ^ 4 = t := by
      calc
        t ^ 4 = (t ^ 2) ^ 2 := pow_mul t 2 2
        _ = t ^ 2 := by rw [h2t, h2t]
        _ = t := h2t
    rw [← h4]
    exact hmem 1 le_rfl

theorem rootSL2_HSL_mem_rationalComponent_of_model_odd [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i)
    (hW : rootSL2 τ L γ WSL ∈ S.Γ)
    {t : Lˣ} (hmodel : rootSL2 τ L γ (HSL t) ∈ S.D.model)
    {m : ℕ} (hm : Odd m) (ht : t ^ m = 1) :
    rootSL2 τ L γ (HSL t) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  obtain ⟨k, rfl⟩ := hm
  rcases k with _ | k
  ·
    have ht1 : t = 1 := by simpa using ht
    subst ht1
    have hHSL : HSL (1 : Lˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [HSL]
    rw [hHSL, map_one]
    exact Subgroup.one_mem _
  ·
    have hm1 : 1 < 2 * (k + 1) + 1 := by omega
    have hcop : Nat.Coprime 2 (2 * (k + 1) + 1) :=
      Nat.coprime_two_left.mpr ⟨k + 1, by ring⟩
    have hmod : 2 ^ Nat.totient (2 * (k + 1) + 1) ≡ 1 [MOD 2 * (k + 1) + 1] :=
      Nat.ModEq.pow_totient hcop
    have hpow : t ^ (2 ^ Nat.totient (2 * (k + 1) + 1)) = t := by
      have h := pow_eq_pow_of_modEq hmod ht
      simpa using h
    exact rootSL2_HSL_mem_rationalComponent_of_model_pow S i hγ hW hmodel
      (Nat.totient_pos.mpr (by omega)) hpow

theorem rootSL2_WSL_mem_model [CharP L 2] (D : LangDatum τ L) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (h₁ : D.step (pinnedX τ L γ 1) = pinnedX τ L (-γ) 1)
    (h₂ : D.step (pinnedX τ L (-γ) 1) = pinnedX τ L γ 1) : rootSL2 τ L γ WSL ∈ D.model := by
  have hu := rootSL2_uSL_of_charTwo (K := L) hγ 1
  have hv := rootSL2_vSL_of_charTwo (K := L) hγ 1
  have e₁ : (WSL : SL2 L) = uSL 1 * vSL 1 * uSL 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have e₂ : (WSL : SL2 L) = vSL 1 * uSL 1 * vSL 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  refine ⟨(exceptional_Lang_root_rank_one_data τ L γ).2.2.2.2.1 WSL, ?_⟩
  change D.step (rootSL2 τ L γ WSL) = rootSL2 τ L γ WSL
  calc D.step (rootSL2 τ L γ WSL) = rootSL2 τ L γ (vSL 1 * uSL 1 * vSL 1) := by
        rw [e₁]; simp only [map_mul, hu, hv, h₁, h₂]
    _ = rootSL2 τ L γ WSL := by rw [← e₂]

theorem rootSL2_WSL_mul_self [CharP L 2] (γ : Fin τ.rank → ℤ) :
    rootSL2 τ L γ WSL * rootSL2 τ L γ WSL = 1 := by
  have e : (WSL : SL2 L) * WSL = 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_WSL, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  rw [← map_mul, e, map_one]

end Comp

end CFSG.StandardType.LangRat

end
