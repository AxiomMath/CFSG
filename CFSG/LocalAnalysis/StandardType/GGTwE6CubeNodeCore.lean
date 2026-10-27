module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeMain
public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeRow
public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeExcl
public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeExclFalse
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreFrame
import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsLangCube
import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeMat

public section

namespace CFSG.StandardType.TwE6Cube

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType
  CFSG.StandardType.TwE6EndNode3


theorem cube_killer_exists {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {v : Fin Tag.E6.rank → ZMod 3}
    (hv : v ≠ 0)
    (hd : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    (hcomp : IsComponentOf (LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)))
      (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)))
    (hexcl : CubeExcl v) :
    ∃ u : Fin Tag.E6.rank → ZMod 3, u ≠ 0 ∧ u ≠ v ∧ u ≠ -v ∧
      ∀ c ∈ LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)),
        (g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
            (c : ModGL TwistTag.E6.tag K) * g) * rootDiagUnit Tag.E6 (zetaVec ζ hζ u) =
          rootDiagUnit Tag.E6 (zetaVec ζ hζ u) * (g⁻¹ * baseChangeGL (τ := Tag.E6)
            (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g) := by
  classical
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h30 : (3 : AlgebraicClosure K) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨w, hw, hbc, hconj⟩ := exists_matrix_of_cube hn hK σ hσ Fr hFr hd
  have hta : g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (w : ModGL TwistTag.E6.tag K) * g = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
    have h : baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        (w : ModGL TwistTag.E6.tag K) = g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ := hbc
    rw [h]
    group
  obtain ⟨S, ι, -, -, hT, hinj, hrange, hconjι, hιform, hρ, -⟩ :=
    TwE6D5Core.exists_langSetup_of_twE6Frame σ hK hσ (ringChar.eq K 2) hFr hg
      (TwE6RootAs.langCubeData hn hK σ hσ Fr hFr h3 hg hgn (le_refl _)).hg0 hw hta
  have hρ' : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ := fun γ hγ =>
    (hρ γ hγ).trans (TwE6RootAs.langCubeData_v hn hK σ hσ Fr hFr h3 hg hgn (le_refl _) γ)
  have hβ : ∀ c, ι (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ c) =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * ι c * (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹ :=
    fun c => by
      rw [hconj, ← twistedE6InndiagConj_eq_twConj σ w hw]
      exact hconjι c
  obtain ⟨u, hu0, huv, hun, hcomm⟩ := exists_killer_of_component S hρ' h30 hζ hζ1 hv hT ι hinj
    hrange hβ hcomp hexcl
  refine ⟨u, hu0, huv, hun, fun c hc => ?_⟩
  have h := hcomm c hc
  rw [hιform c] at h
  exact h

theorem cube_excl_false {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {v : Fin Tag.E6.rank → ZMod 3}
    (hv : v ≠ 0)
    (hd : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    (hcomp : IsComponentOf (LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)))
      (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)))
    (hfix : ∀ y ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g,
      (∀ j ∈ LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)), y j = j) ↔
        y ∈ Subgroup.zpowers (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩))
    (hexcl : CubeExcl v) : False := by
  obtain ⟨u, hu0, huv, hun, hcomm⟩ :=
    cube_killer_exists hn hK σ hσ h3 hFr hg hgn hζ hζ1 hv hd hcomp hexcl
  exact cube_killer_false hn hK σ hσ h3 hFr hg hgn hζ hζ1 hd hfix hu0 huv hun hcomm

theorem cube_node_c0 (hCore : TwE6RootAs.TwE6CorootCore) (hD5 : TwE6RootAs.TwE6D5Core)
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g : ModGL Tag.E6 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {x : MulAut ↥(twistedE6RootGroup K σ)} (hx : x ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g)
    (hx1 : x ≠ 1) (hcomp : IsComponentOf (LargeEvenLayer (ggFix x)) (ggFix x))
    (hfix : ∀ y ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g,
      (∀ j ∈ LargeEvenLayer (ggFix x), y j = j) ↔ y ∈ Subgroup.zpowers x)
    {E : Subgroup ↥(twistedE6RootGroup K σ)} (hE : IsElemAbelian 3 E) (hEx : E ≤ ggFix x) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ LargeEvenLayer (ggFix x) : Subgroup _) := by
  obtain ⟨ζ, hζ, hζ1, v, hv, hd, rfl⟩ := exists_cube_coord hn hK σ hσ Fr hFr h3 hg hgn hx hx1
  rcases cube_dichotomy hv with hrow | hrow | hexcl
  · exact cube_row_bound hCore hD5 hn hK σ hσ h3 hFr hg hgn hζ hζ1 hv hd hx (Or.inl hrow) hE hEx
  · exact cube_row_bound hCore hD5 hn hK σ hσ h3 hFr hg hgn hζ hζ1 hv hd hx (Or.inr hrow) hE hEx
  · exact (cube_excl_false hn hK σ hσ h3 hFr hg hgn hζ hζ1 hv hd hcomp hfix hexcl).elim

theorem ggTwE6CubeNodeInput_of_cores (hCore : TwE6RootAs.TwE6CorootCore)
    (hD5 : TwE6RootAs.TwE6D5Core) : SmallExc.GGTwE6CubeNodeInput :=
  ggTwE6CubeNodeInput_of_c0 (cube_node_c0 hCore hD5)

end CFSG.StandardType.TwE6Cube

end
