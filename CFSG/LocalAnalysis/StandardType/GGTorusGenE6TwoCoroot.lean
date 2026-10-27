module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6TwoRoots
public import CFSG.LocalAnalysis.StandardType.GGLangRatStep
public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTwoTorus
import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
import CFSG.LocalAnalysis.StandardType.GGLangRootSym3
import CFSG.LocalAnalysis.StandardType.GGLangTwoPairAux
import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open TableBExc.E6Three LangRat

namespace E6TwoGen


theorem exists_rootDiagUnit_mem_rationalComponent_e6Two
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    {Fr : L →+* L} (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) (hq : S.D.q = 2)
    (hn : S.D.n = canonicalRep (coxeterSystem .E6) L wE6Two) (hFrq : ∀ c, Fr c = c ^ S.D.q)
    (hAlg : S.IsAlgebraic) {ω : Lˣ} (hωo : orderOf ω = 3)
    (hωF : Units.map Fr.toMonoidHom ω = ω⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ componentRoots (rootCharHom a) i) :
    ∃ b : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit .E6 b ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧ (∀ k, b k ^ 3 = 1) ∧
        rootDiagUnit .E6 b ≠ 1 := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow (f := 1) S (by rw [hq]; norm_num)
  have hαr : IsRoot .E6 α := (isRootComponent_componentRoots i).isRoot α hα
  have hρ : ∀ γ, IsRoot .E6 γ → S.ρ γ = wE6Two • γ :=
    fun γ hγ => S.rho_eq_smul_of_frob hFrq hΦ hn hγ
  have hτ : (Tag.E6 = Tag.F4 ∨ Tag.E6 = Tag.E6 ∨ Tag.E6 = Tag.E7 ∨ Tag.E6 = Tag.E8) :=
    Or.inr (Or.inl rfl)
  have hω3 : ω ^ 3 = 1 := by
    rw [← hωo]
    exact pow_orderOf_eq_one ω
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hωo] at hdvd
    norm_num at hdvd
  have hω3z : ∀ x : ℤ, (ω ^ x) ^ 3 = 1 := by
    intro x
    simpa [hωo] using zpow_pow_orderOf (x := ω) (i := x)
  have hω23z : ∀ y : ℤ, ((ω ^ 2) ^ y) ^ 3 = 1 := by
    intro y
    rw [← zpow_natCast ω 2, ← zpow_mul]
    exact hω3z (2 * y)
  have hω23 : (ω ^ 2) ^ 3 = 1 := by simpa using hω23z 1
  have hω4 : (ω ^ 2) ^ 2 = ω := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
  rcases wE6Two_smul_root hαr with hneg | ⟨horth, hsq⟩
  ·
    have hρα : S.ρ α = -α := by rw [hρ α hαr, hneg]
    have h₁ : ∀ c, S.D.step (pinnedX .E6 L α c) = pinnedX .E6 L (-α) (Fr c) := by
      intro c
      rw [step_pinnedX_of_charTwo S hαr c, hρα]
      congr 1
      rw [hFrq, hq]
    have h₂ : ∀ c, S.D.step (pinnedX .E6 L (-α) c) = pinnedX .E6 L α (Fr c) := by
      intro c
      rw [step_pinnedX_of_charTwo S (IsRoot.neg hαr) c, S.frob.neg_eq α, hρα, neg_neg]
      congr 1
      rw [hFrq, hq]
    have hW : rootSL2 .E6 L α WSL ∈ S.Γ :=
      rootSL2_WSL_mem_Γ_of_rho S hτ (f := 1) (by rw [hq]; norm_num) hAlg hαr (Or.inr hρα)
    have hmem : rootSL2 .E6 L α (HSL ω) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      rootSL2_HSL_mem_rationalComponent_of_step S i hα h₁ h₂ hW hωF (m := 3) (by decide) hω3
    have hpairα : corootPair α α = 2 := by
      rw [corootPair, Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hαr).ne']
    have hχ : rootChar (fun j => ω ^ corootPair α (Pi.single j 1)) α = ω ^ 2 := by
      rw [j4e_rootChar_corootTuple hαr ω α, hpairα]
      rfl
    refine ⟨fun j => ω ^ corootPair α (Pi.single j 1), ?_, ?_, ?_⟩
    · rwa [← j4e_rootSL2_HSL_eq_rootDiagUnit hαr ω]
    · intro k
      exact hω3z _
    · intro h1
      have hb1 : (fun j => ω ^ corootPair α (Pi.single j 1)) = 1 :=
        rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
      have h1' : rootChar (fun j => ω ^ corootPair α (Pi.single j 1)) α = 1 := by
        rw [hb1]
        simp [rootChar]
      exact hω2 (hχ.symm.trans h1')
  ·
    set β : Fin Tag.E6.rank → ℤ := wE6Two • α with hβdef
    have hβr : IsRoot .E6 β := by
      rw [hβdef, ← hρ α hαr]
      exact (S.frob.isRoot_iff α).2 hαr
    have hρβ : S.ρ β = α := by
      rw [hρ β hβr, hβdef]
      exact hsq
    have horthβ : iform α β = 0 := by rw [hβdef]; exact horth
    have hβ : β ∈ rationalRoots S.ρ (rootCharHom a) i := by
      refine ⟨1, α, hα, ?_⟩
      rw [Function.iterate_one, hβdef, ← hρ α hαr]
    have hstepα : S.D.step (rootSL2 .E6 L α (HSL ω)) = rootSL2 .E6 L β (HSL (ω ^ 2)) := by
      rw [j4e_step_rootSL2_HSL_swap S hq hαr ω, hρ α hαr, hβdef]
    have hstepβ : S.D.step (rootSL2 .E6 L β (HSL (ω ^ 2))) = rootSL2 .E6 L α (HSL ω) := by
      rw [j4e_step_rootSL2_HSL_swap S hq hβr (ω ^ 2), hρβ, hω4]
    have hstepWα : S.D.step (rootSL2 .E6 L α WSL) = rootSL2 .E6 L β WSL := by
      rw [step_rootSL2_WSL_of_charTwo S hαr, hρ α hαr, hβdef]
    have hstepWβ : S.D.step (rootSL2 .E6 L β WSL) = rootSL2 .E6 L α WSL := by
      rw [step_rootSL2_WSL_of_charTwo S hβr, hρβ]
    have hmem := rootDiagUnit_mul_corootPair_mem_rationalComponent_of_step S hτ (f := 1)
      (by rw [hq]; norm_num) hAlg i hα hβ horthβ (m := 3) (by decide) hω3 hω23
      hstepα hstepβ hstepWα hstepWβ
    have hpairα : corootPair α α = 2 := by
      rw [corootPair, Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hαr).ne']
    have hpairβ : corootPair β α = 0 := by
      have h0 : iform β α = 0 := by rw [iform_comm, hβdef]; exact horth
      rw [corootPair, h0, mul_zero, Int.zero_ediv]
    have hχ : rootChar (fun j => ω ^ corootPair α (Pi.single j 1) *
        (ω ^ 2) ^ corootPair β (Pi.single j 1)) α = ω ^ 2 := by
      rw [show (fun j => ω ^ corootPair α (Pi.single j 1) *
            (ω ^ 2) ^ corootPair β (Pi.single j 1)) =
          (fun j => ω ^ corootPair α (Pi.single j 1)) *
            (fun j => (ω ^ 2) ^ corootPair β (Pi.single j 1)) from rfl,
        rootChar_mul_tuple, j4e_rootChar_corootTuple hαr ω α,
        j4e_rootChar_corootTuple hβr (ω ^ 2) α, hpairα, hpairβ]
      simp
    refine ⟨fun j => ω ^ corootPair α (Pi.single j 1) *
      (ω ^ 2) ^ corootPair β (Pi.single j 1), hmem, ?_, ?_⟩
    · intro k
      rw [mul_pow, hω3z, hω23z, mul_one]
    · intro h1
      have hb1 : (fun j => ω ^ corootPair α (Pi.single j 1) *
          (ω ^ 2) ^ corootPair β (Pi.single j 1)) = 1 :=
        rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
      have h1' : rootChar (fun j => ω ^ corootPair α (Pi.single j 1) *
          (ω ^ 2) ^ corootPair β (Pi.single j 1)) α = 1 := by
        rw [hb1]
        simp [rootChar]
      exact hω2 (hχ.symm.trans h1')

end E6TwoGen

end CFSG.StandardType
