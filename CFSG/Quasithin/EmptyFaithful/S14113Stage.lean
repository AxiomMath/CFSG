module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.QTFE14Cat
public import CFSG.Quasithin.EmptyFaithful.S1412

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

@[expose] def StageLemma14113 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∀ M H : Subgroup G, InM T M → T ≤ H → H ≤ M → pCoreOf 2 H ≠ ⊥ →
      cgsIn M (pCoreOf 2 H) ≤ H →
      (oTwoFstarIn M ≤ H ∧ pCoreOf 2 H = pCoreOf 2 M) ∨
        (2 < Nat.card (quasithinOmegaOneCenter T) ∧ M = Mc ∧ IsUniqueM H M)

section MaxTwoLocal

variable {G : Type} [Group G] [Finite G]

theorem eq_normalizer_pCoreOf_of_isMaxTwoLocal {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
  hM.2 _ ⟨pCoreOf 2 M, pCoreOf_ne_bot_of_isTwoLocal hM.1, pCoreOf_isPGroup 2 M, rfl⟩
    (le_normalizer_pCoreOf 2 M)

theorem eq_of_pCoreOf_eq_of_isMaxTwoLocal {M₁ M₂ : Subgroup G} (h₁ : quasithinIsMaxTwoLocal M₁)
    (h₂ : quasithinIsMaxTwoLocal M₂) (h : pCoreOf 2 M₁ = pCoreOf 2 M₂) : M₁ = M₂ := by
  rw [← eq_normalizer_pCoreOf_of_isMaxTwoLocal h₁, ← eq_normalizer_pCoreOf_of_isMaxTwoLocal h₂, h]

theorem normalizer_eq_of_char_pCoreOf {M₂ C : Subgroup G} (hM₂ : quasithinIsMaxTwoLocal M₂)
    (hC : C ≠ ⊥) (hCle : C ≤ pCoreOf 2 M₂) (hchar : (C.subgroupOf (pCoreOf 2 M₂)).Characteristic) :
    Subgroup.normalizer (C : Set G) = M₂ := by
  have hM₂C : M₂ ≤ Subgroup.normalizer (C : Set G) :=
    (le_normalizer_pCoreOf 2 M₂).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hCle hchar)
  exact hM₂.2 _ ⟨C, hC, (pCoreOf_isPGroup 2 M₂).to_le hCle, rfl⟩ hM₂C

theorem cgsIn_pCoreOf_le {M₂ : Subgroup G} (hM₂ : quasithinIsMaxTwoLocal M₂) (X : Subgroup G) :
    cgsIn X (pCoreOf 2 M₂) ≤ X ⊓ M₂ := by
  refine iSup_le fun C => iSup_le fun hCle => iSup_le fun hC => iSup_le fun hchar => ?_
  rw [← normalizer_eq_of_char_pCoreOf hM₂ hC hCle hchar]

theorem pCoreOf_le_pCoreOf_inf_of_sylow {T : Sylow 2 G} {M M₁ : Subgroup G}
    (hM : (T : Subgroup G) ≤ M) (hM₁ : (T : Subgroup G) ≤ M₁) :
    pCoreOf 2 M ≤ pCoreOf 2 (M ⊓ M₁) :=
  le_pCoreOf_of_le_normalizer 2 (le_inf ((pCoreOf_two_le_sylow M T hM).trans hM)
    ((pCoreOf_two_le_sylow M T hM).trans hM₁))
    (inf_le_left.trans (le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M)

end MaxTwoLocal

section FStar

variable {G : Type} [Group G]

omit [Group G] in
private theorem comap_congr_of_eq {X : Type} [Group X] (N N' : Subgroup X) [N.Normal] [N'.Normal]
    (h : N = N') (F : ∀ (Y : Type) [Group Y], Subgroup Y) :
    (F (X ⧸ N)).comap (QuotientGroup.mk' N) = (F (X ⧸ N')).comap (QuotientGroup.mk' N') := by
  subst h
  rfl

theorem map_O2Fstar_eq_oTwoFstarIn (H : Subgroup G) :
    (O2Fstar ↥H).map H.subtype = oTwoFstarIn H := by
  unfold oTwoFstarIn preimageModTwoCore O2Fstar
  rw [comap_congr_of_eq (X := ↥H) (CFSG.pCore 2 ↥H) (CFSG.Open.pCore 2 ↥H)
    (CFSG.pCore_eq_open ↥H 2) (fun Y _ => CFSG.generalizedFitting Y)]

theorem oTwoFstarIn_le (H : Subgroup G) : oTwoFstarIn H ≤ H :=
  Subgroup.map_subtype_le _

theorem pCoreOf_le_oTwoFstarIn (H : Subgroup G) : pCoreOf 2 H ≤ oTwoFstarIn H := by
  rw [← map_O2Fstar_eq_oTwoFstarIn]
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) n ∈ CFSG.generalizedFitting _
  have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [h1]
  exact Subgroup.one_mem _

theorem a44Hyp_oTwoFstarIn (H : Subgroup G) : A44Hyp H (oTwoFstarIn H) := by
  right
  rw [← map_O2Fstar_eq_oTwoFstarIn, imageOTwoQuot_O2Fstar]
  exact ⟨IsSubnormal.refl _, fun x hx _ => hx.2⟩

end FStar

end CFSG.Quasithin
