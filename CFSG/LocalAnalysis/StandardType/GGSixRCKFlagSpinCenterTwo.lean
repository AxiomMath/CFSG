module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagOmGen
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightFixed
public import CFSG.LieType.Universal.SpinOmega.Products
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal CFSG.ComponentClassification.RankTwoOddLie
  CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal QuadraticMap

private theorem rckSC2_centerPPrime_of_finrank_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : Type} [Fintype σ] [DecidableEq σ] (Q : QuadraticForm K (σ → K))
    (hQ : (polarBilin Q).Nondegenerate) (hV : Module.finrank K (σ → K) = 2)
    (hinj : Function.Injective (Spin.spinMatrix Q)) :
    CenterPPrime (spinGroup Q) 2 := by
  intro z _hz hz2
  have hzsq : z * z = 1 := by
    rw [← pow_two]
    exact hz2
  obtain ⟨l, hl, hev, hnorm, hx⟩ := Spin.exists_list_of_spinGroup z
  have hmemO : ∀ l : List (σ → K),
      (l.map (reflect Q)).prod ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_mem (reflect_mem_orthogonalGroup Q a) ih
  have key : ∀ l : List (σ → K), (∀ a ∈ l, Q a ≠ 0) →
      (Module.finrank K (commSpace ((l.map (reflect Q)).prod)) : ZMod 2) =
        (l.length : ZMod 2) := by
    intro l
    induction l with
    | nil =>
      intro _
      rw [List.map_nil, List.prod_nil]
      exact natCast_finrank_commSpace_one
    | cons a l ih =>
      intro hl
      have ha : Q a ≠ 0 := hl a (by simp)
      have hl' : ∀ x ∈ l, Q x ≠ 0 := fun x hx => hl x (by simp [hx])
      rw [List.map_cons, List.prod_cons]
      have hmul := natCast_finrank_commSpace_mul hQ
        (reflect_mem_orthogonalGroup Q a) (hmemO l)
      rw [hmul, ih hl']
      have h1 : Module.finrank K (commSpace (reflect Q a)) = 1 := by
        letI : Invertible (Q a) := invertibleOfNonzero ha
        rw [reflect_eq_reflection]
        exact finrank_commSpace_reflection hQ a
      rw [h1, List.length_cons]
      push_cast
      ring
  have heven : Even (Module.finrank K (commSpace ((l.map (reflect Q)).prod))) := by
    rw [← ZMod.natCast_eq_zero_iff_even, key l hl]
    exact ZMod.natCast_eq_zero_iff_even.mpr hev
  have hom : (l.map (reflect Q)).prod ∈ omegaGroup Q hQ :=
    mem_omegaGroup.mpr ⟨hmemO l, heven⟩
  have hmem : Spin.spinAction Q z ∈ omegaGroup Q hQ := by
    rw [hx]
    exact hom
  let t : TauCeti.QuadraticMap.orthogonalGroup Q :=
    ⟨Spin.spinAction Q z, (mem_omegaGroup.mp hmem).1⟩
  have heven : Even (Module.finrank K (commSpace (Spin.spinAction Q z))) :=
    (mem_omegaGroup.mp hmem).2
  have hδ : dicksonHom Q hQ t = 1 := by
    rw [dicksonHom_apply, ZMod.natCast_eq_zero_iff_even.mpr heven, ofAdd_zero]
  have ht : t ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    change (Spin.spinAction Q z : (σ → K) ≃ₗ[K] (σ → K)) * Spin.spinAction Q z = 1
    rw [← map_mul, hzsq, map_one]
  have hone : t = 1 :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthEight.eq_one_of_sq_eq_one_of_dicksonHom
      hQ hV ht hδ
  have hsp : (Spin.spinAction Q z : (σ → K) ≃ₗ[K] (σ → K)) = 1 := by
    have h := congrArg (fun u : TauCeti.QuadraticMap.orthogonalGroup Q =>
      (u : (σ → K) ≃ₗ[K] (σ → K))) hone
    exact h
  have hmat : Spin.spinMatrix Q z = 1 := by
    apply Units.ext
    rw [Spin.coe_spinMatrix, hsp]
    simp
  exact hinj (hmat.trans (map_one (Spin.spinMatrix Q)).symm)

theorem rckFlagSC2_oddCenter_quadPlus_one (g : ℕ) (_hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadPlus 1 (GaloisField 2 g))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus 1 (GaloisField 2 g))) :=
    (MonoidHom.ker_eq_bot_iff _).1 (Spin.ker_spinMatrix_quadPlus_eq_bot h2)
  have hV : Module.finrank (GaloisField 2 g) (Fin 1 ⊕ Fin 1 → GaloisField 2 g) = 2 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hfin : Finite (spinGroup (Spin.quadPlus 1 (GaloisField 2 g))) :=
    Finite.of_injective (Spin.spinMatrix (Spin.quadPlus 1 (GaloisField 2 g))) hinj
  have hcp : CenterPPrime (spinGroup (Spin.quadPlus 1 (GaloisField 2 g))) 2 :=
    rckSC2_centerPPrime_of_finrank_two _ (Spin.nondegenerate_polarBilin_quadPlus 1
      (GaloisField 2 g)) hV hinj
  unfold OddCenterOf
  exact CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_of_centerPPrime_two hcp

private theorem rckSC2_oddCenter_quadMinus_aux (g n : ℕ) (hn : n = 0 ∨ n = 1) :
    Odd (Nat.card (Subgroup.center (spinGroup (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) :=
    (MonoidHom.ker_eq_bot_iff _).1
      (Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 g) h2)
  have hV : Module.finrank (GaloisField 2 g)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 g) = 2 := by
    rcases hn with rfl | rfl <;> simp [Module.finrank_fintype_fun_eq_card]
  have hfin : Finite (spinGroup (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) :=
    Finite.of_injective (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) hinj
  have hcp : CenterPPrime (spinGroup (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) 2 :=
    rckSC2_centerPPrime_of_finrank_two _
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 g)
        (minusCoeffs_irr 2 g)) hV hinj
  exact CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_of_centerPPrime_two hcp

theorem rckFlagSC2_oddCenter_quadMinus_zero (g : ℕ) (_hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadMinus 0 (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) := by
  unfold OddCenterOf
  exact rckSC2_oddCenter_quadMinus_aux g 0 (Or.inl rfl)

theorem rckFlagSC2_oddCenter_quadMinus_one (g : ℕ) (_hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadMinus 1 (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) := by
  unfold OddCenterOf
  exact rckSC2_oddCenter_quadMinus_aux g 1 (Or.inr rfl)

end CFSG.StandardType.RCKFlag
