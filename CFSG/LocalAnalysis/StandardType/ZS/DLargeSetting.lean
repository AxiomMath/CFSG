module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSeven
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNine
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtMain
import CFSG.LocalAnalysis.StandardType.ZS.PropOneEight

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime]

theorem propOneEightAt_of_tableFacts (hp : p ≠ 2) {m : ℕ} (hlt : ∀ k < m, TableFactsAt p k) :
    PropOneEightAt p m := by
  intro h4 U _ _ _ G hdim hG hirr hprim d hd hd3
  subst hdim
  exact exists_splitSupport_dMax hp h4 (fun k hk => (hlt k hk).1) (fun k hk => (hlt k hk).2.1)
    (hlt _ (by omega)).2.2 hG hirr hprim hd hd3

theorem lemmaOneNineInput_holds : LemmaOneNineInput := by
  intro p _ U _ _ _ G _ _ htv habs hprim
  exact centreOrderBound_of_primitive htv habs hprim

variable {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem exists_maxCard_subgroup {G : Type} [Group G] [Finite G] (P : Subgroup G → Prop)
    (h : ∃ H, P H) : ∃ H, P H ∧ ∀ K, P K → Nat.card K ≤ Nat.card H := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (Set G) := Set.fintype
  let : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G))
      (fun H K hHK => SetLike.ext (Set.ext_iff.mp hHK))
  obtain ⟨H, hH, hmax⟩ := Set.exists_max_image {K : Subgroup G | P K} (fun K => Nat.card K)
    (Set.toFinite _) h
  exact ⟨H, hH, fun K hK => hmax K hK⟩

theorem exists_dMax_of_isRefl_pair [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ d, DMax p A d ∧ 3 < d := by
  classical
  have : Finite U := Module.finite_of_finite (ZMod p)
  let : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) LinearEquiv.coe_injective
  let S : Set ℕ :=
    {k | ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = k}
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hlt⟩ := h
    exact ⟨orderOf (x * y), x, hx, y, hy, hxr, hyr, rfl⟩
  have hSbdd : BddAbove S := ⟨Nat.card (U ≃ₗ[ZMod p] U), fun k hk => by
    obtain ⟨x, hx, y, hy, hxr, hyr, rfl⟩ := hk
    exact orderOf_le_card⟩
  refine ⟨sSup S, ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy hxr hyr
    exact le_csSup hSbdd ⟨x, hx, y, hy, hxr, hyr, rfl⟩
  · obtain ⟨x, hx, y, hy, hxr, hyr, hk⟩ := Nat.sSup_mem hSne hSbdd
    exact ⟨x, hx, y, hy, hxr, hyr, hk⟩
  · obtain ⟨x, hx, y, hy, hxr, hyr, hlt⟩ := h
    have hle := le_csSup hSbdd (show orderOf (x * y) ∈ S from
      ⟨x, hx, y, hy, hxr, hyr, rfl⟩)
    omega

theorem family_of_isOrthType {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : IsOrthType p A) :
    Family p A := by
  obtain ⟨Q, hQ, h | ⟨c, hc, h⟩⟩ := h
  · exact Family.orth Q hQ h
  · exact Family.orthClass Q c hQ hc h

theorem isOrthType_of_exists_isPrimOrthSub (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (h4 : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A)
    (hA : AbsIrred p A) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A)
    (htv : QTwoLin.TransvectionFree A) (hX : ∃ X ≤ A, IsPrimOrthSub p X)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hT1 : TFOrthOvergroup p (Module.finrank (ZMod p) U - 1))
    (hT4 : TFOrthCorankOne p (Module.finrank (ZMod p) U - 1)) (hT5 : TFDegThree p) :
    IsOrthType p A := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  let : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) LinearEquiv.coe_injective
  obtain ⟨H, hHmem, hHmax⟩ :=
    exists_maxCard_subgroup (fun X => X ≤ A ∧ IsPrimOrthSub p X) hX
  obtain ⟨hHA, hHprim⟩ := hHmem
  exact isOrthType_of_orthType_subgroup hp rfl h4 ⟨hgen, htv⟩ hA hprim hHA hHprim
    (fun X hXA hXp => hHmax X ⟨hXA, hXp⟩) htab hT1 hT4 hT5

theorem family_of_exists_isPrimOrthSub (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (h4 : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A)
    (hA : AbsIrred p A) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A)
    (htv : QTwoLin.TransvectionFree A) (hX : ∃ X ≤ A, IsPrimOrthSub p X)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hT1 : TFOrthOvergroup p (Module.finrank (ZMod p) U - 1))
    (hT4 : TFOrthCorankOne p (Module.finrank (ZMod p) U - 1)) (hT5 : TFDegThree p) :
    Family p A :=
  family_of_isOrthType
    (isOrthType_of_exists_isPrimOrthSub hp h4 hgen hA hprim htv hX htab hT1 hT4 hT5)

theorem exists_primExtSetting_or_impExtSetting [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (h4 : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A)
    (hA : AbsIrred p A) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A)
    (htv : QTwoLin.TransvectionFree A) {d : ℕ} (hd : DMax p A d) (hd3 : 3 < d)
    (hno : ¬ ∃ X ≤ A, IsPrimOrthSub p X)
    (hN : ∃ N ≤ A, ReflGen p N ∧ SplitSupport N (Module.finrank (ZMod p) U - 1) ∧ DMax p N d) :
    ∃ H : Subgroup (U ≃ₗ[ZMod p] U), PrimExtSetting A H d ∨ ImpExtSetting A H d := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  let : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) LinearEquiv.coe_injective
  obtain ⟨H, hHmem, hHmax⟩ := exists_maxCard_subgroup
    (fun X => X ≤ A ∧ ReflGen p X ∧ SplitSupport X (Module.finrank (ZMod p) U - 1) ∧
      DMax p X d) hN
  obtain ⟨hHA, hHrefl, hHsplit, hHdmax⟩ := hHmem
  have hmax : ∀ X : Subgroup (U ≃ₗ[ZMod p] U), X ≤ A → ReflGen p X →
      SplitSupport X (Module.finrank (ZMod p) U - 1) → DMax p X d →
      Nat.card X ≤ Nat.card H :=
    fun X hXA hXr hXs hXd => hHmax X ⟨hXA, hXr, hXs, hXd⟩
  have hnoOrth : ∀ X : Subgroup (U ≃ₗ[ZMod p] U), X ≤ A → ReflGen p X →
      SplitSupport X (Module.finrank (ZMod p) U - 1) →
      ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) →
      (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
      ¬ IsOrthType p (movedGroup X) := by
    intro X hXA hXr hXs hXni hXpair hXorth
    exact hno ⟨X, hXA, hXr, hXs, hXni, hXorth, hXpair⟩
  by_cases hHimp : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup H)
  · exact ⟨H, Or.inr ⟨h4, hgen, hA, hprim, htv, hd, hd3, hnoOrth, hHA, hHrefl, hHsplit,
      hHdmax, hmax, hHimp⟩⟩
  · exact ⟨H, Or.inl ⟨h4, hgen, hA, hprim, htv, hd, hd3, hnoOrth, hHA, hHrefl, hHsplit,
      hHdmax, hmax, hHimp⟩⟩

end CFSG.StandardType.ZS

end
