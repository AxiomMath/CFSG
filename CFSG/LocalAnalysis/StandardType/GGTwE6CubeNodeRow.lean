module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeFinite
public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeBound
import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeCoords
import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeFrame
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.StandardType.TwE6Cube

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
  CFSG.StandardType CFSG.StandardType.TwE6EndNode3


theorem cube_row_bound (hCore : TwE6RootAs.TwE6CorootCore) (hD5 : TwE6RootAs.TwE6D5Core)
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g : ModGL Tag.E6 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {v : Fin Tag.E6.rank → ZMod 3}
    (hv : v ≠ 0)
    (hd : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    (hx : rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g)
    (hrow : (∃ γ, IsRoot Tag.E6 γ ∧ corootVec γ = v) ∨
      Set.ncard {α : Fin 6 → ℤ | IsRoot Tag.E6 α ∧ KerP v α} = 40)
    {E : Subgroup ↥(twistedE6RootGroup K σ)} (hE : IsElemAbelian 3 E)
    (hEx : E ≤ ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)) :
    Nat.card E ≤ 3 * Nat.card (E ⊓
      LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)) : Subgroup _) := by
  suffices h : ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
      ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩) = X ⊔ D ∧ IsCyclic X ∧
        X ≤ Subgroup.centralizer (D : Set ↥(twistedE6RootGroup K σ)) ∧ CFSG.IsQuasisimple D by
    obtain ⟨X, D, hfix, hXc, hXD, hDq⟩ := h
    haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
    rw [hfix] at hEx ⊢
    exact TwE6D3.card_le_three_mul_inf_layer hXc hXD
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hDq) hE hEx
  rcases hrow with ⟨γ, hγ, rfl⟩ | h40
  ·
    have e := corootTuple_eq_zetaVec ζ hζ γ
    have hd' : g * rootDiagUnit Tag.E6 (TwE6RootAs.corootTuple γ ζ) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr := by
      rw [e]
      exact hd
    have hxx : ∀ (b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
        (hb : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp (AlgebraicClosure K) Fr),
        b = zetaVec ζ hζ (corootVec γ) →
          rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hb⟩ = rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ := by
      rintro b hb rfl
      rfl
    have hx3 := (TwE6DD2.isElemAbelian_langCube hn hK σ hσ Fr hFr g).2 _ hx
    obtain ⟨τ, hτY, hτ1, X, D, hfix, hXc, hXD, hDq, -⟩ := exists_coroot_data_of_mem hCore hn hK
      σ hσ h3 hFr hg hgn (CFSG.Open.isElemAbelian_zpowers hx3) (Subgroup.zpowers_le.2 hx) hγ hζ
      hζ1 hd' (by rw [hxx _ hd' e]; exact Subgroup.mem_zpowers _)
    refine ⟨X, D, ?_, hXc, hXD, hDq⟩
    have hzp := TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three hx3 hτ1 hτY
    have key : ∀ a b : MulAut ↥(twistedE6RootGroup K σ), a ∈ Subgroup.zpowers b →
        ggFix b ≤ ggFix a := fun a b hab c hc => by
      have hb : b ∈ MulAction.stabilizer (MulAut ↥(twistedE6RootGroup K σ)) c := hc
      exact Subgroup.zpowers_le.2 hb hab
    rw [← hfix]
    exact le_antisymm (key _ _ hτY) (key _ _ (by rw [hzp]; exact Subgroup.mem_zpowers _))
  ·
    have hprim : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hζ hζ1)
    have hker : ∀ α : Fin Tag.E6.rank → ℤ, rootChar (zetaVec ζ hζ v) α = 1 ↔ KerP v α := by
      intro α
      have e : zetaVec ζ hζ v = fun k => ζ ^ ((v k).val : ℤ) :=
        funext fun k => by rw [zetaVec_apply, zpow_natCast]
      rw [e, TwE6RootKill.rootChar_val_eq_one_iff_wk hprim]
      rfl
    have hcount : Set.ncard {α : Fin TwistTag.E6.tag.rank → ℤ |
        IsRoot TwistTag.E6.tag α ∧ rootChar (zetaVec ζ hζ v) α = 1} = 40 := by
      rw [← h40]
      exact congrArg Set.ncard (Set.ext fun α => and_congr_right fun _ => hker α)
    haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
    obtain ⟨w, hw, hbc, hxw⟩ := exists_matrix_of_cube hn hK σ hσ Fr hFr hd
    have hS := le_refl (TwE6DD2.langCube hn hK σ hσ Fr hFr g)
    obtain ⟨X, D, hc, hXc, hXD, hDq⟩ := hD5 K σ (2 ^ n) hK hσ (ringChar.eq K 2) h3 Fr hFr _
      (TwE6RootAs.langCubeData_v hn hK σ hσ Fr hFr h3 hg hgn hS) g hg
      (TwE6RootAs.langCubeData hn hK σ hσ Fr hFr h3 hg hgn hS).hg0 (w : ModGL TwistTag.E6.tag K)
      hw (zetaVec (τ := Tag.E6) ζ hζ v)
      (fun (k : Fin Tag.E6.rank) => by rw [zetaVec_apply, pow_right_comm, hζ, one_pow]) hcount
      (by
        rw [hbc]
        change g⁻¹ * (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹) * g =
          rootDiagUnit Tag.E6 (zetaVec ζ hζ v)
        group)
    exact ⟨X, D, by rw [hxw, ggFix_twConj_eq σ w, hc], hXc, hXD, hDq⟩

end CFSG.StandardType.TwE6Cube

end
