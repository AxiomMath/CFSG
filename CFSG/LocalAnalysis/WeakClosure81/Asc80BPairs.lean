module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsCases

import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4
import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed
import CFSG.Adapters.TauCetiExceptional.EvenD4
import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Vol2Native.L239

theorem asc80ThmBCase_of_pairsFor {P : ∀ (X : Type) [Group X], Prop}
    {Ty : ∀ {G : Type} [Group G], Subgroup G → Subgroup G → Prop} (hPairs : PairsFor Ty)
    (hTy : ∀ {G : Type} [Group G] (L R : Subgroup G), P ↥L → Ty L R) : Asc80ThmBCase P := by
  intro G _ _ H A M hs hnab hP hAH hA hM
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := asc80BSetup hs hnab hAH hA hM
  let L : Subgroup G := Fstar H
  have : IsSimpleGroup ↥L := hs
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hAH hA.isPGroup
  have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fstar_le_group H)).1
      (normal_subgroupOf_fstar H)
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hT.le.trans hHN
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    hT.inf_normal (fstar_le_group H) (normal_subgroupOf_fstar H)
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  obtain ⟨K₁, K₂, h₁L, h₂L, h₁ne, h₂ne, hsup, hN₁, hN₂, -⟩ :=
    hPairs G L T hq (hTy L T hP) hT.isPGroup hTN hSyl
  have key : ∀ K : Subgroup G, K ≤ L → K ≠ L → K ≠ ⊥ →
      T ≤ Subgroup.normalizer (K : Set G) → K ≤ M := by
    intro K hKL hKne hKbot hTNK
    let X : Subgroup G := H ⊓ Subgroup.normalizer (K : Set G)
    have hAX : A ≤ X := le_inf hAH (hAT.trans hTNK)
    have hKX : K ≤ X := le_inf (hKL.trans (fstar_le_group H)) (Subgroup.le_normalizer)
    have hXne : X ≠ H := by
      intro hXH
      have hHK : H ≤ Subgroup.normalizer (K : Set G) := hXH ▸ inf_le_right
      have hKnormal : (K.subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 ((fstar_le_group H).trans hHK)
      have := hKnormal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf L) with hbot | htop
      · apply hKbot
        have hmap := Subgroup.map_subgroupOf_eq_of_le hKL
        rw [hbot, Subgroup.map_bot] at hmap
        exact hmap.symm
      · apply hKne
        have hmap := Subgroup.map_subgroupOf_eq_of_le hKL
        rw [htop, Subgroup.map_top, Subgroup.range_subtype] at hmap
        exact hmap.symm
    have hXlt : X < H := lt_of_le_of_ne inf_le_left hXne
    exact hKX.trans (h.le_of_lt X hAX hXlt)
  have h₁bot : K₁ ≠ ⊥ := by
    intro hb
    exact h₂ne (by rw [← hsup, hb, bot_sup_eq])
  have h₂bot : K₂ ≠ ⊥ := by
    intro hb
    exact h₁ne (by rw [← hsup, hb, sup_bot_eq])
  have hLle : L ≤ M := hsup ▸
    sup_le (key K₁ h₁L h₁ne h₁bot hN₁) (key K₂ h₂L h₂ne h₂bot hN₂)
  exact h.not_fstar_le hLle

theorem chevalleyExceptionalModel_of_lieModel_trialityD4
    {X : Type} [Group X] {n f : ℕ} (hm : CFSG.Models.LieModel X .trialityD4 n 2 f) :
    CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f := by
  obtain ⟨hadm, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | trialityD4 q =>
      simp only [CFSG.Models.NamesTag] at hN
      obtain ⟨hq2, hqf⟩ := hN
      rw [← hqf]
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      let K := GaloisField q.p (q.exponent * 3)
      let σ : K →+* K := iterateFrobenius K q.p q.exponent
      have hK : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
        dsimp [K]
        rw [GaloisField.card q.p (q.exponent * 3)
          (Nat.mul_ne_zero q.exponent_pos.ne' (by norm_num)),
          TauCeti.PrimePower.card_def, pow_mul]
        rfl
      have hσ : ∀ x : K, σ x = x ^ q.card := by
        intro x
        dsimp [σ, K]
        rw [iterateFrobenius_def, TauCeti.PrimePower.card_def]
      obtain ⟨ψ⟩ :=
        CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq2 K hK σ hσ
      have hcard : q.card = 2 ^ q.exponent := by
        rw [TauCeti.PrimePower.card_def, hq2]
      rw [hcard] at hK hσ
      exact ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩, K, inferInstance, inferInstance,
        hK, σ, hσ, ⟨φ.trans ψ.symm⟩⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem reeTitsModel_of_lieModel_twistedF4
    {X : Type} [Group X] {n f : ℕ} (hm : CFSG.Models.LieModel X .twistedF4 n 2 f) :
    CFSG.Blueprint.ReeTitsModel X .twistedF4 2 f := by
  obtain ⟨-, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | reeF4 m =>
      simp only [CFSG.Models.NamesTag] at hN
      obtain ⟨-, hf⟩ := hN
      subst f
      have hfin : ∀ d : TauCeti.ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
      have hchar : ∀ d : TauCeti.ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
      have := hfin (TauCeti.ReeF4LieIndex.of m hv)
      have := hchar (TauCeti.ReeF4LieIndex.of m hv)
      have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have hhalf : (TauCeti.ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
        TauCeti.SuzukiReeIndex.halfExponent_reeF4 m hv
      obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4
        (TauCeti.ReeF4LieIndex.of m hv)
      rw [hhalf] at e₁
      have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4
        (TauCeti.ReeF4LieIndex.of m hv)
      rw [hhalf] at hK
      exact ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl,
        (TauCeti.ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
        ⟨(φ.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem asc80ThmBCase_trialityD4 :
    Asc80ThmBCase fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .trialityD4 n 2 f := by
  refine asc80ThmBCase_of_pairsFor (Ty := Type3D4)
    (P := fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .trialityD4 n 2 f)
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.pairsFor_3D4) ?_
  intro G _ L R h
  obtain ⟨n, f, hm⟩ := h
  exact ⟨f, hm.1.2.1, chevalleyExceptionalModel_of_lieModel_trialityD4 hm⟩

theorem asc80ThmBCase_twistedF4 :
    Asc80ThmBCase fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .twistedF4 n 2 f := by
  refine asc80ThmBCase_of_pairsFor (Ty := Type2F4)
    (P := fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .twistedF4 n 2 f)
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.pairsFor_2F4) ?_
  intro G _ L R h
  obtain ⟨n, f, hm⟩ := h
  exact ⟨f, hm.1.2.2.2.2.1, hm.1.2.2.2.2.2, reeTitsModel_of_lieModel_twistedF4 hm⟩

end CFSG.LocalAnalysis.WeakClosure81

end
