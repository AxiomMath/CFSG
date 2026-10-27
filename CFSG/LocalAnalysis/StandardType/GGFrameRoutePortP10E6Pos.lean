module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP8dAct
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem p10h_card_range_le
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
    (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs K) :
    Nat.card (ggGamma K hN).range ≤ 3 ^ 6 := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hK
  obtain ⟨R, _, I, F, -, -, -, ⟨hlabeq, -, -⟩⟩ := largeEvenRawDatum_exists hraw
  subst hlabeq
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K', instF, instFin, hK', hQ⟩ := hraw
  obtain ⟨-, -, θ, hθ⟩ := hQ
  have hK'' : Nat.card K' = (2 ^ 1) ^ 2 := by simpa using hK'
  have hEβI : ((ggBeta K θ hN).range : Set (MulAut _)) ⊆ TwE6Delta.RecipeI K' 1 := by
    rintro φ ⟨b, rfl⟩
    exact ggBeta_mem (L := K) (θ := θ) hN hθ.2.2 b
  have hX := ggTwE6ThreeInndiagRankInput_holds (K := K') (n := 1) le_rfl hK'' (by norm_num)
  have hup : Nat.card (ggBeta K θ hN).range ≤ 3 ^ 6 :=
    hX _ (p8dAct_isElemAbelian_range_ggBeta θ hBs hN) hEβI
  rwa [p8dAct_card_range_ggBeta_eq θ hperf hBs hz hz1 hN hker] at hup

theorem p10h_exists_mulEquiv {A : Type} [Group A] (hexp : ∀ x : A, x ^ 3 = 1)
    (hab : ∀ x y : A, x * y = y * x) {m : ℕ} (hcard : Nat.card A = 3 ^ m) :
    Nonempty (A ≃* Multiplicative (Fin m → ZMod 3)) := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨k, ⟨e⟩⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence.abelian_equiv Nat.prime_three hexp hab
  have hk : 3 ^ k = 3 ^ m := by
    rw [← hcard, Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
  obtain rfl : k = m := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hk
  exact ⟨e⟩

set_option linter.unusedVariables false in
theorem p10h_twE6_full_adjoint
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
    {n : ℕ} (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs K) :
    n = 7 ∧ Nat.card (ggGamma K hN).range = 3 ^ 6 ∧
      Nonempty ((ggGamma K hN).range ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3)) := by
  have hmul := p8dAct_card_range_ggGamma hBs hz hz1 hN hker
  have hup := p10h_card_range_le hBs hz hz1 hN hker hK
  have hn7 : n = 7 := by
    have h1 : 3 ^ n ≤ 3 ^ 7 := by
      rw [← hcard, ← hmul]
      calc Nat.card (ggGamma K hN).range * 3 ≤ 3 ^ 6 * 3 := Nat.mul_le_mul_right 3 hup
        _ = 3 ^ 7 := by norm_num
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  have hA : Nat.card (ggGamma K hN).range = 3 ^ 6 := by
    rw [hn7] at hcard
    rw [hcard] at hmul
    omega
  have hEA := p8dAct_isElemAbelian_range_ggGamma hBs hN
  refine ⟨hn7, hA, ?_⟩
  exact p10h_exists_mulEquiv (fun x => Subtype.ext (hEA.2 x x.2))
    (fun x y => Subtype.ext (IsElemAbelian.comm hEA x.2 y.2)) (m := 6) hA

end CFSG.StandardType.FrameRoute

end
