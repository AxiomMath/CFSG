module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZClass

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

private theorem ggHasLabel_of_centerQuotEquiv {G H : Type} [Group G] [Group H]
    {X : Subgroup G} {Y : Subgroup H} {lab : LargeEvenLabel}
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* ↥Y ⧸ Subgroup.center ↥Y)
    (h : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) :
    GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
  unfold GGHasLabel at h ⊢
  refine largeEvenRawDatum_mono ?_ h
  rintro R' _ I F ⟨ψ⟩
  exact ⟨θ.symm.trans ψ⟩

theorem exists_rationalComponent_label_of_langSetup
    {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hinj : Function.Injective ι) (hrange : ι.range = S.Γ) (h : ↥(twistedE6InndiagGL K σ))
    (hconj : ∀ c, ι (twistedE6InndiagConj K σ h c) =
      rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (J : Subgroup ↥(twistedE6RootGroup K σ))
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h)))
    {lab : LargeEvenLabel} (hlab : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne
      Nat.prime_three (by rw [ringChar.eq (AlgebraicClosure K) 2]; norm_num)
  have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
      S Nat.prime_three h3L (fun hG2 => absurd hG2 (by decide)) hT hap h1
  obtain ⟨i, hQS, hJR⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S Nat.prime_three
      ι hinj hrange (twistedE6InndiagConj K σ h) hconj hT hap h1 hTame hJ
  set Ri : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)) :=
    rationalComponent S.ρ S.Γ (rootCharHom a) i with hRidef
  have hlab' : GGHasLabel lab (↥Ri ⧸ Subgroup.center ↥Ri) := by
    let eJ : ↥J ≃* ↥Ri :=
      (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
    exact ggHasLabel_of_centerQuotEquiv
      (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥Ri) eJ
        (Subgroup.map_center_eq eJ)) hlab
  exact ⟨i, hQS, hlab'⟩

theorem exists_component_a2_of_langSetup
    {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5) (hSq : S.D.q = 2 ^ n)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hinj : Function.Injective ι) (hrange : ι.range = S.Γ) (h : ↥(twistedE6InndiagGL K σ))
    (hconj : ∀ c, ι (twistedE6InndiagConj K σ h c) =
      rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (J : Subgroup ↥(twistedE6RootGroup K σ))
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h)))
    (hlab : GGHasLabel (⟨.twA, 2, 3 * n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    ∃ i : KernelComponent (rootCharHom a),
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 ∧ (componentRoots (rootCharHom a) i).ncard = 6 ∧
        ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]) := by
  obtain ⟨i, hQS, hlab'⟩ := exists_rationalComponent_label_of_langSetup hK S ι hinj hrange h
    hconj hT hap h1 J hJ hlab
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hΛ : LargeEvenInLambda2 (⟨.twA, 2, 3 * n⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]
    omega
  exact ⟨i, CFSG.StandardType.TablePThreeKG.tableZ_classA2 S hn hSq hT hap h1 i hQS hΛ hlab'⟩

end CFSG.StandardType.TwE6TwA2K

end
