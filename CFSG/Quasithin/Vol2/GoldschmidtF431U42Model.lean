module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Geom
public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting
public import CFSG.LieType.Multipliers.U42
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.GH74.Exceptional CFSG.Fischer.Classification U42F431

@[expose] noncomputable def eY : Y ≃* PSp43 :=
  (MulEquiv.subgroupCongr Xs_eq).trans
    CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP.symm

theorem lieModel_of_equiv_PSp43 {X : Type} [Group X] (e : X ≃* PSp43) :
    CFSG.Blueprint.LieModel X .PSU 4 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, Blueprint.Fischer.K,
    inferInstance, inferInstance, Unitary.card_K, ⟨e.trans (psp43EquivU2.trans u2FourEquiv)⟩⟩

theorem lieModel_Y : CFSG.Blueprint.LieModel Y .PSU 4 2 1 :=
  lieModel_of_equiv_PSp43 eY

theorem nonempty_mulEquiv_Y {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSU 4 2 1) : Nonempty (X ≃* Y) := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 h
  exact ⟨e.trans eY.symm⟩

theorem isSimpleGroup_of_lieModel_PSU_four_two {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSU 4 2 1) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem f431ModelFacts_psu : F431ModelFacts .PSU 4 1 := by
  intro D _ h
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 h
  have hc : Nat.card D = 25920 := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Multipliers.U42.card_PSp43]
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by omega)
  refine ⟨hfin, ?_⟩
  have : IsSimpleGroup D := isSimpleGroup_of_lieModel_PSU_four_two h
  rcases (inferInstance : (Subgroup.center D).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    have hcomm : ∀ a b : D, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top b) a
    let _ : CommGroup D := { ‹Group D› with mul_comm := hcomm }
    have hprime : (Nat.card D).Prime := IsSimpleGroup.prime_card
    rw [hc] at hprime
    norm_num at hprime

end CFSG.Quasithin.H13.F431.U42
