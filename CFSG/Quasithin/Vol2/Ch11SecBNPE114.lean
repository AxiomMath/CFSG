module

public import CFSG.Quasithin.Vol2.Ch11SecBNPAut
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def TypeOne (Y : Type) [Group Y] : Prop :=
  IsPSL 3 2 1 Y ∨ IsAlt 6 Y ∨ (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 s p 1 Y

theorem TypeOne.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeOne Y') : TypeOne Y := by
  rcases h with h | h | ⟨p, f, hp, hp2, h5, h⟩ | ⟨s, p, hp, hp2, h⟩
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
  · obtain ⟨e'⟩ : Nonempty (Y' ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, hp2, h5, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨s, p, hp, hp2, ?_⟩))
    cases s with
    | true => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h
    | false => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h

@[expose] def E114TypeOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      TypeOne (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114TypeOne_of_e114 (h : ASInputs.AS_E_1_14) : E114TypeOne := by
  intro G _ _ T hSQ hFs hT hFT hty
  obtain ⟨h1, -, -, -, -, -, h6, h7⟩ := h G T hSQ hFs hT hFT
  rcases hty with hh | hh | ⟨p, f, hp, hp2, h5, hh⟩ | ⟨s, p, hp, hp2, hh⟩
  · exact (h1 1 le_rfl (Or.inr (Or.inr (Or.inr (Or.inl hh))))).le
  · exact (h1 1 le_rfl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, hh⟩))))))).le
  · exact (h6 p f hp hp2 h5 hh).le
  · exact (h7 s p hp hp2 hh).le

theorem sqtkGroup_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : SQTKGroup B) : SQTKGroup A := by
  refine ⟨fun p hp hp2 => ?_, h.2.of_mulEquiv e⟩
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 2 := h.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2
  omega

theorem sqtkGroup_subgroup {A : Type} [Group A] [Finite A] (h : SQTKGroup A) (K : Subgroup A) :
    SQTKGroup ↥K := by
  refine ⟨fun p hp hp2 => ?_, h.2.subgroup K⟩
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt K.subtype K.subtype_injective
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2 := h.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2
  omega

theorem nParam_sup_le_one (h1114 : E114TypeOne) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (hSQ : SQTKGroup X) (hT : TypeOne X)
    {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
      (MulAut.conj : X →* MulAut X).range) :
    E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ 1 := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set Z := I ⊔ B with hZdef
  have hIn : I.Normal := normal_range_conj X
  have hSQI : SQTKGroup ↥I :=
    sqtkGroup_of_mulEquiv (rangeConjEquiv (center_eq_bot_of_nonabelian' hnab)).symm hSQ
  have hSQZ : SQTKGroup ↥Z := InternalSec.sqtkGroup_of_two_pow le_sup_left
    (fun y _ k hk => hIn.conj_mem k hk y) (pow_mem_of_mem_sup hB) hSQI
  set e := generalizedFittingEquiv hnab B with he
  have hFs : IsSimpleGroup (ASInputs.FStar ↥Z) := e.isSimpleGroup
  have hFT : TypeOne (ASInputs.FStar ↥Z) := TypeOne.of_mulEquiv e hT
  rw [E1.nParam_subgroupOf]
  exact h1114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
    (generalizedFitting_sup_sup hnab B) hFT

end CFSG.Quasithin.Vol2.Ch11.SecB
