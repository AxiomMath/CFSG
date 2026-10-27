module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.SuN
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.Models.Transport
public import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private lemma lk0xlqreca_mul_succ_injective :
    Function.Injective (fun n : ℕ => n * (n + 1)) := by
  have hmono : StrictMono (fun n : ℕ => n * (n + 1)) := by
    intro a b hab
    calc a * (a + 1) < (a + 1) * (a + 1) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self a) (Nat.succ_pos a)
      _ ≤ b * (b + 1) := Nat.mul_le_mul (by omega) (by omega)
  exact hmono.injective

private lemma lk0xlqreca_frame_dim {ν r : ℕ} (hν : 3 ≤ ν) (h : ν * (ν - 1) = r * (r + 1)) :
    ν = r + 1 := by
  have h1 : (ν - 1) * ((ν - 1) + 1) = r * (r + 1) := by
    have h2 : (ν - 1) * ((ν - 1) + 1) = ν * (ν - 1) := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ ν), Nat.mul_comm]
    rw [h2, h]
  have h3 : ν - 1 = r := lk0xlqreca_mul_succ_injective h1
  omega

theorem lq_rec_A1
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (h1 : compRank (componentRoots (rootCharHom a) i) = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N)
    (hN2 : 2 ≤ N) :
    GGHasLabel ⟨.A, 1, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hq4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [hN]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN2
  have hk : twistKind S.ρ (rootCharHom a) i = .inner :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.twistKind_eq_inner_of_compRank_eq_one S i h1
  have hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    rationalComponent_quasisimple_inner_of_four_leT S
      CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk hq4
  obtain ⟨f, -, hfeq, hmodel⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_rankOne_model S hT i h1 hn hQS
  have hchar : ringChar L = 2 := ringChar.eq L 2
  have hfN : f = N := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    change 2 ^ f = 2 ^ N
    rw [hchar] at hfeq
    rw [hfeq, hN]
  subst hfN
  rw [hchar] at hmodel
  exact ggHasLabel_typeA hmodel

theorem lq_rec_A
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner)
    (hr : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.A, compRank (componentRoots (rootCharHom a) i), N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_frame_of_typeA_tag_T_of_prime
      CFSG.HardMathSupport.Timmesfeld.CrossChar.g2LongA2Frame_proved S hp hpL hTp i hr hn
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    rw [hsdef]
    exact twistInner_of_twistKind_eq_innerT S
      CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk
  have hmaps : ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        CFSG.HardMathSupport.Timmesfeld.CrossChar.frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
      ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) =
        -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · obtain ⟨f, -, hfeq, hmodel⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_splitFrame_model
        S hT i hν hψ hΨ π hπ
    have hcard : ν * (ν - 1) = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [← CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm, ← hΨ]
      exact hn
    have hνeq : ν = compRank (componentRoots (rootCharHom a) i) + 1 :=
      lk0xlqreca_frame_dim hν hcard
    have hchar : ringChar L = 2 := ringChar.eq L 2
    have hfN : f = N := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      change 2 ^ f = 2 ^ N
      rw [hchar] at hfeq
      rw [hfeq, hN]
    subst hfN
    rw [hchar, hνeq] at hmodel
    exact ggHasLabel_typeA hmodel
  · exfalso
    exact (CFSG.StandardType.TablePThreeKG.not_twistInner_of_unitaryFrame hν hψ hκ hnorm
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) π hπ) (hΨ ▸ hinner)

theorem lq_rec_SU
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .suN)
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N)
    (hnot : ¬ (compRank (componentRoots (rootCharHom a) i) = 2 ∧ N = 1)) :
    GGHasLabel ⟨.twA, compRank (componentRoots (rootCharHom a) i), N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨h2, hn⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hk
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_frame_of_typeA_tag_T_of_prime
      CFSG.HardMathSupport.Timmesfeld.CrossChar.g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.ssexc_suN_perm S hT i hk hν hψ hκ hnorm hΨ
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := by
    have h1 : r = ringChar L := CharP.eq L hchar (ringChar.charP L)
    have h2 : ringChar L = 2 := by
      clear hchar
      exact ringChar.eq L 2
    exact h1.trans h2
  have hq2 : S.D.q = 2 ^ e := by rw [hq, hr2]
  have heq : (2 : ℕ) ^ (e * s) = 2 ^ N := by
    calc (2 : ℕ) ^ (e * s) = (2 ^ e) ^ s := pow_mul 2 e s
      _ = S.D.q ^ s := by rw [← hq2]
      _ = 2 ^ N := hN
  have hes : e * s = N := Nat.pow_right_injective (by norm_num : 2 ≤ 2) heq
  have hνeq : ν = compRank (componentRoots (rootCharHom a) i) + 1 := by
    apply lk0xlqreca_frame_dim hν
    rw [← CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm, ← hΨ]
    exact hn
  have hνQ : (ν, r ^ (e * s)) ≠ (3, 2) := by
    rintro h
    apply hnot
    have h1 : ν = 3 := by simpa using congrArg Prod.fst h
    have h2 : r ^ (e * s) = 2 := by simpa using congrArg Prod.snd h
    have h2e : (2 : ℕ) ^ (e * s) = 2 := by simpa [hr2] using h2
    have hN1 : (2 : ℕ) ^ N = 2 ^ 1 := by
      rw [← heq, h2e]
      norm_num
    have hNval : N = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hN1
    refine ⟨by omega, hNval⟩
  have hmodel :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.rationalComponent_suN_model
      S hT i hν hψ hΨ π hπ hr hchar he hq hνQ
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eC⟩⟩ := hmodel
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hcard' : Nat.card K = (2 ^ N) ^ 2 := by
    rw [hKcard, hes, hr2]
  refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (E := K)
    (b := compRank (componentRoots (rootCharHom a) i)) (m := N) hcard' ?_
  rw [hνeq, hes, hr2] at eC
  exact eC

end CFSG.StandardType.GGK0LQ

end
