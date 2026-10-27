module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeCount
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAutT
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftT

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.E6ThreeModel CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem p10_twE6_model_realization
    {F : Type} [Field F] [Finite F] (hK : Nat.card F = (2 ^ 1) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (Fr : AlgebraicClosure F →+* AlgebraicClosure F) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 (AlgebraicClosure F)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure F))
    (hgn : g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure F) Fr g =
      TwistedDiag.n0 (AlgebraicClosure F)) :
    ∃ e : (TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g) ≃*
        Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3),
      ∀ α : MulAut ↥(twistedE6RootGroup F σ),
        ∀ hα : α ∈ Subgroup.normalizer
          ((TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g : Subgroup _) :
            Set (MulAut ↥(twistedE6RootGroup F σ))),
        ∃ (w : WeylGroup TwistTag.E6.tag) (ε : ZMod 3), (ε = 1 ∨ ε = -1) ∧
          ∀ s, Multiplicative.toAdd (e (ggConjAut _ hα s)) =
            ε • TwE6NormThree.weylDual w (Multiplicative.toAdd (e s)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_two_of_card (m := 1 * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure F) := AlgebraicClosure.isAlgClosed F
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h30 : (3 : AlgebraicClosure F) ≠ 0 :=
    three_ne_zero_of_dvd_card_add_one (ℓ := 2) le_rfl h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root h30
  have hL : IsLang Fr g := ⟨hg, hgn⟩
  obtain ⟨D, hD⟩ := exists_tFrame le_rfl hK σ hσ Fr hFr h3 hL hζ hζo
  have hfaith : Function.Injective D.diag :=
    tFrame_faithful le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
  have haut := tFrame_aut le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
  have hle : TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g ≤ D.diag.range := by
    intro y hy
    obtain ⟨b, hb, hx, hyeq⟩ := (TwE6DD2.mem_langCube le_rfl hK σ hσ Fr hFr).1 hy
    have hb3 : b ^ 3 = 1 := by funext i; simpa using hb i
    obtain ⟨x, hxeq⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3
    obtain ⟨hx', hx'eq⟩ := hD.diag_eq x
    have hval : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ =
        g * rootDiagUnit Tag.E6 b * g⁻¹ := by rw [hxeq]
    have hsub : (⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hx'⟩ :
        ↥(TwistedDiag.Rgrp (AlgebraicClosure F) Fr)) =
        ⟨g * rootDiagUnit Tag.E6 b * g⁻¹, hx⟩ := Subtype.ext hval
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    rw [show D.diag (Multiplicative.ofAdd x) = D.ad x from rfl, hx'eq, hsub, hyeq]
  have hge : D.diag.range ≤ TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨hx', hx'eq⟩ := hD.diag_eq (Multiplicative.toAdd x)
    refine (TwE6DD2.mem_langCube le_rfl hK σ hσ Fr hFr).2
      ⟨zetaVec ζ hζ (Multiplicative.toAdd x), ?_, hx', ?_⟩
    · intro i
      rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    · rw [← hx'eq]
      rfl
  have hrange : TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g = D.diag.range :=
    le_antisymm hle hge
  let e : (TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g) ≃*
      Multiplicative (Fin Tag.E6.rank → ZMod 3) :=
    (MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hfaith).symm
  have he : ∀ s, D.diag (e s) = s.1 := fun s =>
    MonoidHom.apply_ofInjective_symm hfaith _
  refine ⟨e, ?_⟩
  intro α hα
  have hS : ∀ x : Fin Tag.E6.rank → ZMod 3,
      ∃ y : Fin Tag.E6.rank → ZMod 3, α * D.ad x * α⁻¹ = D.ad y := by
    intro x
    have hx : D.ad x ∈ TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g := by
      rw [hrange]
      exact ⟨Multiplicative.ofAdd x, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hα (D.ad x)).mp hx
    rw [hrange] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Multiplicative.toAdd y, hy.symm⟩
  obtain ⟨c, u, hc, hform⟩ := haut α Set.univ (Or.inl rfl)
    (fun x _ => by
      obtain ⟨y, hy⟩ := hS x
      exact ⟨y, trivial, hy⟩)
  refine ⟨u⁻¹, c, ?_, ?_⟩
  · have hc3 : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
    exact hc3 c hc
  · intro s
    have hsx : s.1 = D.ad (Multiplicative.toAdd (e s)) := by
      rw [← he s]
      rfl
    have h2 : (ggConjAut _ hα s).1 =
        D.ad (c • adAct Tag.E6 3 u (Multiplicative.toAdd (e s))) := by
      rw [ggConjAut_apply, hsx]
      exact hform _ trivial
    have h3 : e (ggConjAut _ hα s) =
        Multiplicative.ofAdd (c • adAct Tag.E6 3 u (Multiplicative.toAdd (e s))) := by
      apply hfaith
      rw [he]
      exact h2
    have h4 : Multiplicative.toAdd (e (ggConjAut _ hα s)) =
        c • adAct Tag.E6 3 u (Multiplicative.toAdd (e s)) := by
      rw [h3]
      rfl
    have h5 : adAct Tag.E6 3 u (Multiplicative.toAdd (e s)) =
        TwE6NormThree.weylDual u⁻¹ (Multiplicative.toAdd (e s)) := by
      funext j
      simp only [adAct, TwE6NormThree.weylDual, TwE6NormThree.dot3]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    exact h4.trans (congrArg (c • ·) h5)

end CFSG.StandardType.FrameRoute
