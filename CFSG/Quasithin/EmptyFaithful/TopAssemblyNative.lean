module

public import CFSG.Quasithin.Recognition.CertG2Two
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Recognition.ModelBridgesJ3
public import CFSG.Open.QuasithinSixModelBridges
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.EmptyFaithful.Skeleton
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open.QuasithinSixModelsTauCeti

theorem exists_lieModel_trialityD4_two :
    ∃ (X : Type) (_ : Group X), LieModel X .trialityD4 0 2 1 := by
  refine ⟨DerivedCentralQuotient
    (twistedFixedGroup .D4 (GaloisField 2 3) (frobenius (GaloisField 2 3) 2)), inferInstance, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨⟨Nat.prime_two, le_rfl, rfl⟩, ?_⟩⟩)
  refine ⟨GaloisField 2 3, inferInstance, inferInstance, ?_, frobenius (GaloisField 2 3) 2, ?_,
    ⟨MulEquiv.refl _⟩⟩
  · rw [GaloisField.card 2 3 (by norm_num)]
    rfl
  · intro c
    exact frobenius_def 2 c

theorem exists_lieModel_tits : ∃ (X : Type) (_ : Group X), LieModel X .Tits 0 2 1 := by
  refine ⟨DerivedCentralQuotient (reeFixedGroup .F4 (ZMod 2) reeF4Perm
      fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)), inferInstance, ?_⟩
  refine Or.inr (Or.inr (Or.inl ⟨rfl, by decide,
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, ?_⟩⟩))
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩

theorem lieModel_trialityD4_of_bridge (hD4 : TrialityD4ModelBridge) {G : Type} [Group G]
    (h : Nonempty (G ≃* CFSG.Open.quasithinTrialityD4Two)) : LieModel G .trialityD4 0 2 1 := by
  obtain ⟨X, _, hX⟩ := exists_lieModel_trialityD4_two
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := hD4 X hX
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (f.trans e.symm) hX

theorem lieModel_tits_of_bridge (hTits : TitsModelBridge) {G : Type} [Group G]
    (h : Nonempty (G ≃* CFSG.Open.quasithinTits)) : LieModel G .Tits 0 2 1 := by
  obtain ⟨X, _, hX⟩ := exists_lieModel_tits
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := hTits X hX
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (f.trans e.symm) hX

@[expose] def NativeSixModels (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* NativeSporadic.J2) ∨
  Nonempty (G ≃* NativeSporadic.J3) ∨
  LieModel G .trialityD4 0 2 1 ∨
  LieModel G .Tits 0 2 1 ∨
  (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ∧
    Nonempty (G ≃* ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆)) ∨
  Nonempty (G ≃* NativeSporadic.M12)

theorem SixModels.toNative
    (hD4 : TrialityD4ModelBridge) (hTits : TitsModelBridge)
    {G : Type} [Group G] (h : SixModels G) : NativeSixModels G := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h | h | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨e.trans quasithinJ2MulEquivNative⟩
  · exact Or.inr (Or.inl ⟨e.trans quasithinJ3MulEquivNative⟩)
  · exact Or.inr (Or.inr (Or.inl (lieModel_trialityD4_of_bridge hD4 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (lieModel_tits_of_bridge hTits h))))
  · obtain ⟨f⟩ := g2_derived_mulEquiv_PSU3 (ZMod 2) (Nat.card_zmod 2)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨e.trans f.symm⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e.trans (MulEquiv.subgroupCongr quasithinM12_eq_native)⟩))))

theorem nativeSixModels_of_parts
    (hD4 : TrialityD4ModelBridge) (hTits : TitsModelBridge)
    (P1 : StageMfExists) (P2 : StageTheorem1513) (P3 : StageTheorem1531)
    (G : Type) [Group G] [Finite G] (T Mc : Subgroup G) (h : quasithinQTFE14Cat G T Mc) :
    NativeSixModels G :=
  SixModels.toNative hD4 hTits (six_models_of_parts P1 P2 P3 G T Mc h)

end CFSG.Quasithin
