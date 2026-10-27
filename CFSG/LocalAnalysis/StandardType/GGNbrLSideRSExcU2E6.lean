module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU2Excl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.LocalAnalysis.GLTheoremA CFSG.Open
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggNbrLSideRSExc_u2_e6
    (hExcl : GGNbrLSideRSExcExcl) {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (h2 : (2 : L) = 0) {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {Q : ℕ}
    (hP : GGNbrLSideRSExcPSL3 S a i Q) (hE : L154E6Class a i) : False := by
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by simpa using h2)
  have hch : ringChar L = 2 := ringChar.eq L 2
  obtain ⟨hT, hp3, hne, hqs, hQ4, h3Q, F, hFf, hFin, hFc, ⟨e⟩⟩ := hP
  have hF4 : 4 ≤ Nat.card F := hFc ▸ hQ4
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h3 : (3 : L) = 2 + 1 := by norm_num
    have h0 : (3 : L) = 0 := by simpa using h
    rw [h3, h2, zero_add] at h0
    exact one_ne_zero h0
  have hTp := l154_rootDiagUnit_pow hp3
  have hle := l154_compRank_le (componentRoots (rootCharHom a) i)
  have h6r := hE.1
  have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
    rintro ⟨-, h⟩
    rw [hE.1, hE.2] at h
    norm_num at h
  cases τ with
  | G2 =>
    have hr : Tag.G2.rank = 2 := rfl
    omega
  | F4 =>
    have hr : Tag.F4.rank = 4 := rfl
    omega
  | D4 =>
    have hr : Tag.D4.rank = 4 := rfl
    omega
  | E6 => exact l154_not_E6 hne i hE
  | E7 =>
    by_cases hin : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨t, r, e', hPt, hLie⟩ :=
        S265C.DynE.tagLie_inner_nonA_E7 S Nat.prime_three hpL hT hTp i hnonA hin
      rw [hch] at hLie
      obtain ⟨ht, -, -⟩ := hExcl hF4 e hLie
      rcases hPt with rfl | rfl | rfl | rfl <;> cases ht
    · obtain ⟨v, hv⟩ := l154_form_E7 S Nat.prime_three hpL hTp i hE
      obtain ⟨f, -, -, hmodel⟩ :=
        KD264Lie.ExcUntw.lieModel_rationalComponent_of_e6_outer S hT i v hv hin
      rw [hch] at hmodel
      obtain ⟨ht, -, -⟩ := hExcl hF4 e hmodel
      cases ht
  | E8 =>
    by_cases hin : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨t, r, e', hPt, hLie⟩ :=
        S265C.DynE.tagLie_inner_nonA_E8 S Nat.prime_three hpL hT hTp i hnonA hin
      rw [hch] at hLie
      obtain ⟨ht, -, -⟩ := hExcl hF4 e hLie
      rcases hPt with rfl | rfl | rfl | rfl <;> cases ht
    · obtain ⟨v, hv⟩ := l154_form_E8 S Nat.prime_three hpL hTp i hE
      obtain ⟨f, -, -, hmodel⟩ :=
        KD264Lie.ExcUntw.lieModel_rationalComponent_of_e6_outer S hT i v hv hin
      rw [hch] at hmodel
      obtain ⟨ht, -, -⟩ := hExcl hF4 e hmodel
      cases ht

end CFSG.StandardType
