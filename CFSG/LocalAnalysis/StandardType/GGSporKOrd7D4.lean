module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LieType.ChevTwo.OppCl.D4Lift
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.GroupTheory.CardSupInf
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LieType.ChevTwo.OppositeFixedExcTri
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalTwisted
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
open CFSG.Blueprint.Chevalley CFSG.LieType.ChevTwo.Semi CFSG.HardMathSupport.Lang.D4Three

private theorem lr2od4_subsingleton_ringAut {K : Type} [Field K] (hK : Nat.card K = 2) :
    Subsingleton (RingAut K) := by
  obtain ⟨b, -, hcov⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
  have hb1 : b = 1 := (hcov 1 one_ne_zero).symm
  refine ⟨fun σ τ => RingEquiv.ext fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · have hx1 : x = 1 := (hcov x hx).trans hb1
    rw [hx1, map_one, map_one]

private theorem lr2od4_ringChar_eq_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ringChar K = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card]; simpa using hK)
  exact ringChar.eq K 2

private theorem lr2od4_card_d4Chat_dvd
    {K : Type} [Field K] [Finite K] :
    Nat.card (d4Chat K) ∣ 3 * Nat.card (adjointGroup Tag.D4 K) := by
  have hnorm : Subgroup.zpowers (d4P K) ≤
      Subgroup.normalizer (adjointGroup Tag.D4 K : Set (ModGL Tag.D4 K)) :=
    Subgroup.zpowers_le.2 d4P_mem_normalizer_adjointGroup
  have hprod := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := Subgroup.zpowers (d4P K)) (K := adjointGroup Tag.D4 K) hnorm
  have ht : Nat.card (Subgroup.zpowers (d4P K)) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.2 d4P_pow_three
  have hdiv : Nat.card (d4Chat K) ∣ Nat.card (Subgroup.zpowers (d4P K)) *
      Nat.card (adjointGroup Tag.D4 K) := by
    refine ⟨Nat.card ↥(Subgroup.zpowers (d4P K) ⊓ adjointGroup Tag.D4 K), ?_⟩
    rw [d4Chat, sup_comm]
    exact hprod.symm
  exact hdiv.trans (Nat.mul_dvd_mul_right ht (Nat.card (adjointGroup Tag.D4 K)))

private theorem lr2od4_card_d4LiftSub_eq
    {K : Type} [Field K] [Finite K]
    (hsub : Subsingleton (RingAut K)) :
    Nat.card (d4LiftSub K) = Nat.card (d4Chat K) := by
  refine Nat.card_congr
    { toFun := fun s => ⟨s.1.left, s.2⟩
      invFun := fun m => ⟨⟨m.1, 1⟩, by show m.1 ∈ d4Chat K; exact m.2⟩
      left_inv := fun s => by
        apply Subtype.ext
        apply SemidirectProduct.ext
        · rfl
        · exact Subsingleton.elim _ _
      right_inv := fun m => by
        apply Subtype.ext
        rfl }

private theorem lr2od4_ord7_bound
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2) :
    (Nat.card (MulAut (adjointGroup Tag.D4 K))).factorization 7 ≤
      (Nat.card (adjointGroup Tag.D4 K)).factorization 7 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hKchar : ringChar K = 2 := lr2od4_ringChar_eq_two hKcard
  have hsub : Subsingleton (RingAut K) := lr2od4_subsingleton_ringAut hKcard
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow 7 (MulAut (adjointGroup Tag.D4 K))))
  obtain ⟨T, hTle, -, hcorr1, hcorr2⟩ :=
    exists_lift_group (K := K) hKchar Nat.prime_seven (by norm_num : (7 : ℕ) ≠ 2) S.isPGroup'
  haveI : Finite (RingAut K) := inferInstance
  haveI : Finite (ModGL Tag.D4 K) := CFSG.LieType.Chevalley.finite_modGL (τ := Tag.D4) (K := K)
  haveI : Finite (GamL Tag.D4 K) :=
    Finite.of_injective (fun s : GamL Tag.D4 K => (s.left, s.right)) (by
      intro a b h
      exact SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  haveI : Finite T := inferInstance
  have hcardST : Nat.card S = Nat.card T := by
    have key1 : ∀ α : S, ∃ s : T,
        d4LiftHom (K := K) (⟨s.1, hTle s.2⟩ : d4LiftSub K) =
          (α : MulAut (adjointGroup Tag.D4 K)) := by
      intro α
      obtain ⟨s, hs, hseq⟩ := hcorr1 α.1 α.2
      refine ⟨⟨s, hs⟩, ?_⟩
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [coe_d4LiftHom]; exact (hseq h).symm
    have key2 : ∀ t : T, ∃ α : S,
        d4LiftHom (K := K) (⟨t.1, hTle t.2⟩ : d4LiftSub K) =
          (α : MulAut (adjointGroup Tag.D4 K)) := by
      intro t
      obtain ⟨α, hαS, hαeq⟩ := hcorr2 t.1 t.2
      refine ⟨⟨α, hαS⟩, ?_⟩
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [coe_d4LiftHom]; exact (hαeq h).symm
    have hf : ∀ α : S, d4LiftHom (K := K)
        (⟨(Classical.choose (key1 α)).1, hTle (Classical.choose (key1 α)).2⟩ : d4LiftSub K) =
        (α : MulAut (adjointGroup Tag.D4 K)) := fun α => Classical.choose_spec (key1 α)
    have hg : ∀ t : T, d4LiftHom (K := K)
        (⟨t.1, hTle t.2⟩ : d4LiftSub K) =
        ((Classical.choose (key2 t) : S) : MulAut (adjointGroup Tag.D4 K)) :=
      fun t => Classical.choose_spec (key2 t)
    have hle1 : Nat.card S ≤ Nat.card T :=
      Nat.card_le_card_of_injective (fun α : S => Classical.choose (key1 α)) (by
        intro α β hab
        apply Subtype.ext
        have hval : (⟨(Classical.choose (key1 α)).1, hTle (Classical.choose (key1 α)).2⟩ :
            d4LiftSub K) =
            ⟨(Classical.choose (key1 β)).1, hTle (Classical.choose (key1 β)).2⟩ :=
          Subtype.ext (congrArg (fun x : T => (x : GamL Tag.D4 K)) hab)
        rw [← hf α, ← hf β, hval])
    have hle2 : Nat.card T ≤ Nat.card S :=
      Nat.card_le_card_of_injective (fun t : T => Classical.choose (key2 t)) (by
        intro t u hab
        have h1 : d4LiftHom (K := K) (⟨t.1, hTle t.2⟩ : d4LiftSub K) =
            d4LiftHom (K := K) (⟨u.1, hTle u.2⟩ : d4LiftSub K) := by
          rw [hg t, hg u]
          exact congrArg (fun α : S => (α : MulAut (adjointGroup Tag.D4 K))) hab
        have h2 : (⟨t.1, hTle t.2⟩ : d4LiftSub K) = ⟨u.1, hTle u.2⟩ :=
          d4LiftHom_injective h1
        have h2b : (⟨t.1, hTle t.2⟩ : d4LiftSub K).val =
            (⟨u.1, hTle u.2⟩ : d4LiftSub K).val := congrArg Subtype.val h2
        exact Subtype.ext h2b)
    exact le_antisymm hle1 hle2
  have hTdvd : Nat.card T ∣ 3 * Nat.card (adjointGroup Tag.D4 K) :=
    (Subgroup.card_dvd_of_le hTle).trans
      (by rw [lr2od4_card_d4LiftSub_eq (K := K) hsub]; exact lr2od4_card_d4Chat_dvd (K := K))
  have hcardS : Nat.card S =
      7 ^ (Nat.card (MulAut (adjointGroup Tag.D4 K))).factorization 7 :=
    Sylow.card_eq_multiplicity S
  have hdvd : 7 ^ (Nat.card (MulAut (adjointGroup Tag.D4 K))).factorization 7 ∣
      3 * Nat.card (adjointGroup Tag.D4 K) := by
    rw [← hcardS, hcardST]
    exact hTdvd
  have hcop : Nat.Coprime (7 ^ (Nat.card (MulAut (adjointGroup Tag.D4 K))).factorization 7) 3 :=
    Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 7 3)
  have hdvdC : 7 ^ (Nat.card (MulAut (adjointGroup Tag.D4 K))).factorization 7 ∣
      Nat.card (adjointGroup Tag.D4 K) := by
    exact hcop.dvd_of_dvd_mul_left hdvd
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_seven
    (Nat.card_pos (α := adjointGroup Tag.D4 K)).ne').1 hdvdC

theorem ord7Param_D4_two :
    Ord7Param .POmegaPlus 4 2 1 := by
  intro R _ _ hRsimple hmodel
  have hclass : StatedClassicalModel R .POmegaPlus 4 2 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0) hmodel
  obtain ⟨-, K, hKfield, hKfin, hKcard, hRK⟩ := hclass
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hKcard2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨e0⟩ := hRK
  obtain ⟨e1⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup (F := K)
  let e : R ≃* adjointGroup Tag.D4 K := e0.trans e1
  rw [show Nat.card (MulAut R) = Nat.card (MulAut (adjointGroup Tag.D4 K)) from
        Nat.card_congr (MulAut.congr e).toEquiv,
      show Nat.card R = Nat.card (adjointGroup Tag.D4 K) from Nat.card_congr e.toEquiv]
  exact lr2od4_ord7_bound hKcard2

end CFSG.StandardType.SporadicShape
