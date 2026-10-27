module

public import CFSG.Quasithin.Background.FFC13C

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

section Transfer

variable {V : Type} [CommGroup V]

theorem autSec_sup_eq {A L : Subgroup (MulAut V)} {W U : Subgroup V} (hZW : L ⊔ A ≤ stabSub W)
    (hZU : L ⊔ A ≤ stabSub U) :
    autSec (L ⊔ A) W U = autSec L W U ⊔ autSec A W U := by
  rw [← B5.range_secHom (L ⊔ A) hZW hZU,
    ← B5.map_secHom_eq_autSec (L ⊔ A) hZW hZU (le_sup_left : L ≤ L ⊔ A),
    ← B5.map_secHom_eq_autSec (L ⊔ A) hZW hZU (le_sup_right : A ≤ L ⊔ A),
    ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem eq_map_of_autSec_eq_map {Z Y : Subgroup (MulAut V)} (hYZ : Y ≤ Z) {W U : Subgroup V}
    (hZW : Z ≤ stabSub W) (hZU : Z ≤ stabSub U) (hfaith : Z ⊓ centSec W U = ⊥) {Γ : Type*} [Group Γ]
    (π' : Γ →* ↥Z) (ψ : Γ →* MulAut (Sec W U)) (hψ : ∀ γ, B5.secHom Z hZW hZU (π' γ) = ψ γ)
    (K : Subgroup Γ) (hK : autSec Y W U = K.map ψ) :
    Y = K.map (Z.subtype.comp π') := by
  have hinj : Function.Injective (B5.secHom Z hZW hZU) :=
    (MonoidHom.ker_eq_bot_iff _).1 (B5.ker_secHom_eq_bot Z hZW hZU hfaith)
  have hmap := B5.map_secHom_eq_autSec Z hZW hZU hYZ
  ext g
  constructor
  · intro hg
    have h1 : B5.secHom Z hZW hZU ⟨g, hYZ hg⟩ ∈ autSec Y W U := by
      rw [← hmap]
      exact Subgroup.mem_map.2 ⟨⟨g, hYZ hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    rw [hK] at h1
    obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1 h1
    have h2 : π' γ = ⟨g, hYZ hg⟩ := hinj ((hψ γ).trans hγg)
    exact Subgroup.mem_map.2 ⟨γ, hγ, congrArg Subtype.val h2⟩
  · intro hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hg
    have h1 : B5.secHom Z hZW hZU (π' γ) ∈ autSec Y W U := by
      rw [hψ γ, hK]
      exact Subgroup.mem_map_of_mem _ hγ
    rw [← hmap] at h1
    obtain ⟨y, hy, hyγ⟩ := Subgroup.mem_map.1 h1
    have h2 : y = π' γ := hinj hyγ
    rw [Subgroup.mem_subgroupOf, h2] at hy
    exact hy

end Transfer

section Equiv

theorem exists_core_equiv_top {S : Type} [CommGroup S] {J : Subgroup (MulAut S)}
    {π : Equiv.Perm (Fin 5) →* ↥J} (h : (FFModel.symDn 5).RealizesVia J ⊤ ⊥ π) :
    ∃ e : S ≃* ↥(G6.coreMod 5), ∀ (σ : Equiv.Perm (Fin 5)) (s : S),
      e (((π σ : ↥J) : MulAut S) s) = G6.coreAct 5 σ (e s) := by
  obtain ⟨e0, he0⟩ := exists_core_equiv (by decide : Odd 5) h
  exact ⟨Subgroup.topEquiv.symm.trans e0, fun σ s => he0 σ ⟨s, trivial⟩ trivial⟩

end Equiv

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem alt_data (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X)
    (hLA : ⁅L, A⁆ = L) {W U : Subgroup V} (hU : U = ⊥) (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hLU : L ≤ stabSub U) (hAU : A ≤ stabSub U) (hsup : W ⊔ fixV A = ⊤)
    {J : Subgroup (MulAut (Sec W U))} (hJ : J = autSec (L ⊔ A) W U)
    (π : Equiv.Perm (Fin 5) →* ↥J) (hπi : Function.Injective π)
    (hπ : (FFModel.symDn 5).RealizesVia J ⊤ ⊥ π)
    (hLeq : autSec L W U = (alternatingGroup (Fin 5)).map (J.subtype.comp π))
    {t : Equiv.Perm (Fin 5)} (ht : t.IsSwap)
    (hAeq : autSec A W U = (Subgroup.zpowers t).map (J.subtype.comp π)) :
    ∃ π' : Equiv.Perm (Fin 5) →* ↥(L ⊔ A), Function.Injective π' ∧ Function.Surjective π' ∧
      (FFModel.symDn 5).RealizesVia (L ⊔ A) W ⊥ π' ∧
      L = (alternatingGroup (Fin 5)).map ((L ⊔ A).subtype.comp π') ∧
      ∃ i j : Fin 5, i ≠ j ∧
        A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π') := by
  subst hU
  subst hJ
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW).1
  have hAW : A ≤ stabSub W :=
    B1.le_stabSub_of_invariant (a_stab_irr hV hA hL.2.2 hLA hW)
  have hZW : L ⊔ A ≤ stabSub W := sup_le hLW hAW
  have hZU : L ⊔ A ≤ stabSub ⊥ := sup_le hLU hAU
  have hfaith : (L ⊔ A) ⊓ centSec W ⊥ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, hgc⟩
    rw [Subgroup.mem_bot]
    refine eq_one_of_trivial_on_W hV hO2 hA hL hLA hW hsup hg fun w hw => ?_
    have := hgc.2 w hw
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  set E := B5.secEquiv (L ⊔ A) hZW hZU hfaith with hE
  let π' : Equiv.Perm (Fin 5) →* ↥(L ⊔ A) := E.symm.toMonoidHom.comp π
  have hψ : ∀ σ, B5.secHom (L ⊔ A) hZW hZU (π' σ) =
      (((autSec (L ⊔ A) W ⊥).subtype.comp π) σ : MulAut (Sec W ⊥)) := fun σ =>
    (B5.secHom_symm hZW hZU hfaith (π σ)).symm
  obtain ⟨i, j, hij, rfl⟩ := ht
  refine ⟨π', fun a b h => hπi (E.symm.injective h), E.symm.surjective.comp hπ.1,
    B5.realizesVia_of_autSec bot_le hZW hZU hfaith hπ,
    eq_map_of_autSec_eq_map le_sup_left hZW hZU hfaith π' _ hψ _ hLeq, i, j, hij, ?_⟩
  exact eq_map_of_autSec_eq_map le_sup_right hZW hZU hfaith π' _ hψ _ hAeq

end Main

end B69

end CFSG.Quasithin
