module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open (IsElemAbelian)

theorem excTwE6Cover_holds :
    ExcTwE6Cover := by
  classical
  intro G _ _ H E hmark
  unfold GGInnerDiagOnLabel at hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, hQraw⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨_, hPraw⟩ := hQraw.2.2
  obtain ⟨hlabEq, -, -⟩ := hPraw
  subst hlabEq
  let Qmark : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : H ⧸ Subgroup.center H ≃* R,
        (⟨.twE6, 0, 1⟩ : LargeEvenLabel) = ⟨.twE6, 0, 1⟩ ∧
          E ≤ Subgroup.normalizer (H : Set G) ∧
          ∀ b ∈ E, ∃ φ ∈ I, LargeEvenInduces θ
            (fun l l' => (l' : G) = (b : G)⁻¹ * l * (b : G)) φ
  have hn : 1 ≤ (⟨.twE6, 0, 1⟩ : LargeEvenLabel).n := hlab.1
  have hrawCanon : CFSG.Assembly.LargeEvenRawDatum (⟨.twE6, 0, 1⟩ : LargeEvenLabel) Qmark :=
    hraw
  obtain ⟨K, instF, instFin, σ, hKcard, hσpow, hQ0⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_raw_of_label
      (lab := (⟨.twE6, 0, 1⟩ : LargeEvenLabel)) (Q := Qmark) rfl hn hrawCanon
  obtain ⟨-, -, θ, -, hEN, hact⟩ := hQ0
  have hK4 : Nat.card K = 4 := by
    rw [hKcard]
    norm_num
  have hσ : ∀ c, σ c = c ^ 2 := by
    simpa using hσpow
  let eR : LargeEvenCenterQuot (twistedE6RootGroup K σ) ≃* ↥(twistedE6RootGroup K σ) :=
    centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let θ' : H ⧸ Subgroup.center H ≃* ↥(twistedE6RootGroup K σ) := θ.trans eR
  let ψ : ↥H →* ↥(twistedE6RootGroup K σ) := ggQuotHom θ'
  have hψl : ∀ l : ↥H, ψ l = eR (ggQuotHom θ l) := fun _ => rfl
  have hcomp : ∀ (e : ↥E) (l : ↥H),
      MulAut.congr eR (ggBeta H θ hEN e) (ψ l) = ψ (ggGamma H hEN e l) := by
    intro e l
    have h1 : ggBeta H θ hEN e (ggQuotHom θ l) = ggQuotHom θ (ggGamma H hEN e l) :=
      ggBeta_ggQuotHom H hEN θ e l
    calc MulAut.congr eR (ggBeta H θ hEN e) (ψ l)
        = MulAut.congr eR (ggBeta H θ hEN e) (eR (ggQuotHom θ l)) := by rw [hψl]
      _ = eR (ggBeta H θ hEN e (ggQuotHom θ l)) := by
          simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      _ = eR (ggQuotHom θ (ggGamma H hEN e l)) := by rw [h1]
      _ = ψ (ggGamma H hEN e l) := by rw [← hψl]
  refine ⟨hEN, hperf, K, instF, instFin, σ, hK4, hσ, ψ,
    ggQuotHom_surjective θ', ker_ggQuotHom θ', ?_⟩
  intro e
  have hmem : ggBeta H θ hEN e ∈
      RecipeExcLang.markIDImage (Blueprint.Chevalley.IsRoot TwistTag.E6.tag) K
        (twistedE6RootGroup K σ) :=
    ggBeta_mem H θ hEN hact e
  obtain ⟨w, hw⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_exists_twConj_of_mem_markID σ hmem
  refine ⟨RecipeExcLang.twConj K σ w, ⟨w, rfl⟩, ?_⟩
  intro l
  have hw' : MulAut.congr eR (ggBeta H θ hEN e) = RecipeExcLang.twConj K σ w := hw
  rw [← hw']
  exact hcomp e l

end CFSG.StandardType.GGQ2Frame.ExcPlacement
