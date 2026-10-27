module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeLang
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

section Frame

variable {L : Type} [Field L]

@[expose] noncomputable def e6ThreeDiag (ζ : Lˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.F4.rank → ZMod 3) →* ModGL .E6 L where
  toFun s :=
    rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame (Multiplicative.toAdd s)))
  map_one' := by
    change rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
      (twE6ThreeFrame (0 : Fin Tag.F4.rank → ZMod 3))) = 1
    have h1 : TableBExc.E6Three.zetaVec ζ hζ (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
      funext i
      simp [TableBExc.E6Three.zetaVec_apply]
    rw [twE6ThreeFrame_zero, h1, rootDiagUnit_one]
  map_mul' := by
    intro s t
    change rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
        (twE6ThreeFrame (Multiplicative.toAdd (s * t)))) =
      rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
        (twE6ThreeFrame (Multiplicative.toAdd s))) *
      rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
        (twE6ThreeFrame (Multiplicative.toAdd t)))
    rw [show Multiplicative.toAdd (s * t) =
          Multiplicative.toAdd s + Multiplicative.toAdd t from rfl,
      twE6ThreeFrame_add, CFSG.StandardType.ExcFrames.zetaVec_add, rootDiagUnit_mul]

theorem e6ThreeDiag_apply (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (s : Fin Tag.F4.rank → ZMod 3) :
    e6ThreeDiag ζ hζ (Multiplicative.ofAdd s) =
      rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)) := rfl

private theorem rootDiag_rootVec' {τ : Tag} {K : Type} [Field K]
    (b : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootDiag b (rootVec τ K α) = ((rootChar b α : Kˣ) : K) • rootVec τ K α := by
  rw [CFSG.LieType.Chevalley.rootVec_eq_single hα, rootDiag_single_inr]
  rfl

private theorem rootDiagUnit_injective' {τ : Tag} {K : Type} [Field K] :
    Function.Injective (rootDiagUnit τ : (Fin τ.rank → Kˣ) → ModGL τ K) := by
  intro b b' h
  funext i
  have hv := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))
    (rootVec τ K (Pi.single i 1))) h
  change rootDiag b (rootVec τ K (Pi.single i 1)) =
    rootDiag b' (rootVec τ K (Pi.single i 1)) at hv
  rw [rootDiag_rootVec' b (isRoot_single τ i),
    rootDiag_rootVec' b' (isRoot_single τ i)] at hv
  have hne : rootVec τ K (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := by
    rw [CFSG.LieType.Chevalley.rootVec_eq_single (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h1 := smul_left_injective K hne hv
  have e : ∀ c : Fin τ.rank → Kˣ, rootChar c (Pi.single i 1) = c i := fun c => by
    have := rootChar_nsmul_single c i 1
    rwa [one_nsmul, pow_one] at this
  rw [e, e] at h1
  exact Units.ext h1

theorem e6ThreeDiag_injective {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (e6ThreeDiag ζ hζ) := by
  intro s t h
  have h1 := rootDiagUnit_injective' (τ := .E6) (K := L) h
  have h2 := TableBExc.E6Three.zetaVec_injective (τ := .E6) hζo hζ h1
  have h3 := twE6ThreeFrame_injective h2
  exact h3

end Frame

section Certs

variable {L : Type} [Field L]

private theorem unitsMap_zetaVec (Fr : L →+* L) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hFr : Units.map Fr.toMonoidHom ζ = ζ ^ 2) (x : Fin Tag.E6.rank → ZMod 3) :
    (fun i => Units.map Fr.toMonoidHom (TableBExc.E6Three.zetaVec ζ hζ x i)) =
      TableBExc.E6Three.zetaVec ζ hζ (fun i => 2 * x i) := by
  funext i
  rw [TableBExc.E6Three.zetaVec_apply, TableBExc.E6Three.zetaVec_apply, map_pow, hFr, ← pow_mul]
  have hv : (2 * x i : ZMod 3).val = (2 * (x i).val) % 3 := by
    rw [ZMod.val_mul, show (2 : ZMod 3).val = 2 from by decide]
  rw [hv]
  exact pow_eq_pow_mod (2 * (x i).val) hζ

private theorem adAct_e6W0
    (y : Fin Tag.E6.rank → ZMod 3) :
    TableBExc.E6Three.adAct .E6 3 e6W0 y = fun i => - y (e6Perm i) := by
  funext i
  change (∑ j : Fin Tag.E6.rank,
      (((e6W0⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j : ℤ) : ZMod 3) * y j) =
    - y (e6Perm i)
  rw [inv_eq_of_mul_eq_one_right e6W0_mul_self, e6W0_smul, permLattice_single]
  have he : CFSG.RankThree.E6.e6Rho i = e6Perm i := rfl
  rw [he, Fintype.sum_eq_single (e6Perm i) (fun b hb => by
    simp only [Pi.neg_apply, Pi.single_apply, if_neg hb, neg_zero, Int.cast_zero,
      zero_mul])]
  rw [Pi.neg_apply, Pi.single_apply, if_pos rfl, Int.cast_neg, Int.cast_one]
  exact neg_one_mul _

theorem negPhi_eqpN_rootDiagUnit_zetaVec
    (Fr : L →+* L) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hFr : Units.map Fr.toMonoidHom ζ = ζ ^ 2) (x : Fin Tag.E6.rank → ZMod 3) :
    negPhi Fr (eqpN L) (rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x)) =
      rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ (fun i => x (e6Perm i))) := by
  rw [negPhi_rootDiagUnit_gen]
  congr 1
  rw [unitsMap_zetaVec Fr hζ hFr x,
    TableBExc.E6Three.weylTuple_zetaVec ζ hζ e6W0 (fun i => 2 * x i), adAct_e6W0]
  congr 1
  funext i
  show -(2 * x (e6Perm i)) = x (e6Perm i)
  rw [show (2 : ZMod 3) = -1 from by decide,
    show (-1 : ZMod 3) * x (e6Perm i) = - x (e6Perm i) from neg_one_mul _]
  exact neg_neg (x (e6Perm i))

theorem negPhi_eqpN_e6ThreeDiag
    (Fr : L →+* L) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hFr : Units.map Fr.toMonoidHom ζ = ζ ^ 2) (s : Multiplicative (Fin Tag.F4.rank → ZMod 3)) :
    negPhi Fr (eqpN L) (e6ThreeDiag ζ hζ s) = e6ThreeDiag ζ hζ s := by
  rw [show s = Multiplicative.ofAdd (Multiplicative.toAdd s) from rfl, e6ThreeDiag_apply,
    negPhi_eqpN_rootDiagUnit_zetaVec Fr hζ hFr]
  congr 1
  congr 1
  funext i
  rw [twE6ThreeFrame_perm]

theorem e6ThreeDiag_mem_NFix
    [IsAlgClosed L] (Fr : L →+* L) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hFr : Units.map Fr.toMonoidHom ζ = ζ ^ 2) (s : Multiplicative (Fin Tag.F4.rank → ZMod 3)) :
    e6ThreeDiag ζ hζ s ∈ NFix (eqpN L) Fr := by
  rw [mem_NFix]
  refine ⟨?_, negPhi_eqpN_e6ThreeDiag Fr hζ hFr s⟩
  rw [show s = Multiplicative.ofAdd (Multiplicative.toAdd s) from rfl, e6ThreeDiag_apply]
  exact torusGroup_le_monomialSubgroup' (rootDiagUnit_mem_torusGroup _)

theorem exists_e6ThreeDiag_eq
    (Fr : L →+* L) {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (hFr : Units.map Fr.toMonoidHom ζ = ζ ^ 2) {z : ModGL .E6 L}
    (hz : z ∈ CFSG.RankThree.PartOne.KE.twistedTorus (eqpN L) Fr) (hz3 : z ^ 3 = 1) :
    ∃ s, e6ThreeDiag ζ hζ s = z := by
  rw [CFSG.RankThree.PartOne.KE.twistedTorus, mem_twistedTorusOf_iff_negPhi] at hz
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hz.1
  have ha3 : a ^ 3 = 1 := by
    apply rootDiagUnit_injective (K := L)
    rw [← rootDiagUnit_pow, ← ha, hz3, rootDiagUnit_one]
  obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq (τ := .E6) hζo hζ ha3
  have hneg : negPhi Fr (eqpN L) (rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x)) =
      rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) := by
    rw [hx, ← ha]
    exact hz.2
  have hfix : (fun i => x (e6Perm i)) = x := by
    apply TableBExc.E6Three.zetaVec_injective (τ := .E6) hζo hζ
    apply rootDiagUnit_injective (K := L)
    rw [← negPhi_eqpN_rootDiagUnit_zetaVec Fr hζ hFr x]
    exact hneg
  have h0 : x (e6Idx 0) = x e6Five := by
    have h := congrFun hfix (e6Idx 0)
    rw [show e6Perm (e6Idx 0) = e6Five from by decide] at h
    exact h.symm
  have h2 : x (e6Idx 2) = x e6Four := by
    have h := congrFun hfix (e6Idx 2)
    rw [show e6Perm (e6Idx 2) = e6Four from by decide] at h
    exact h.symm
  obtain ⟨s, hs⟩ := (exists_twE6ThreeFrame_eq_iff x).2 ⟨h0, h2⟩
  exact ⟨Multiplicative.ofAdd s, by rw [e6ThreeDiag_apply, hs, hx, ha]⟩

theorem monomial_conj_e6ThreeDiag
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) {y : ModGL .E6 L}
    (hy : y ∈ monomialSubgroup .E6 L) {u : WeylGroup Tag.E6} (hyu : MapsRootLines y u)
    (hu : u ∈ relWeylTwist TwistTag.E6) (s : Fin Tag.F4.rank → ZMod 3) :
    y * e6ThreeDiag ζ hζ (Multiplicative.ofAdd s) * y⁻¹ =
      e6ThreeDiag ζ hζ (Multiplicative.ofAdd
        (TableBExc.torusAct .F4 3 (foldedWeylEquiv TwistTag.E6 ⟨u, hu⟩) s)) := by
  rw [e6ThreeDiag_apply, e6ThreeDiag_apply,
    TableBExc.E6Three.monomial_conj_rootDiagUnit_weylTuple hy hyu,
    TableBExc.E6Three.weylTuple_zetaVec ζ hζ u (twE6ThreeFrame s)]
  rw [adAct_twE6ThreeFrame ⟨u, hu⟩ s]

end Certs

end CFSG.StandardType.ExcFrames.E6QPlusThree
