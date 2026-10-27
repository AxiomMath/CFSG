module

public import CFSG.Milestones.ASVolI.F48.Small.Trans
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoF48Eqv
public import CFSG.Milestones.ASVolI.F4K.Main
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.Base

public section

namespace CFSG.ASVolI

section Chart

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431.TwoF4 CFSG.ASVolI.ChF
  CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Blueprint CFSG.Blueprint.Chevalley


theorem burnsideF48s_tits_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits 2 1 Gp M₁ M₂) :
    ∃ θ : ↥(M₁ ⊔ M₂) ≃* ↥(titsH ⊔ titsN),
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) ∈ titsH) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔
          ((θ x : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) ∈ titsN) ∨
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) ∈ titsN) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔
          ((θ x : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) ∈ titsH) := by
  have hyp4 := hyp.toHypF_4_4g
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr rfl)
  obtain ⟨K, fK, finK, charK, hscope, marking, h1, h2⟩ := burnsideF4gF4Two_chart_tits hyp4
  letI := fK
  haveI := finK
  haveI : CharP K F4.prime := charK
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := hscope
  have hK : Nat.card K = 2 := by simpa using hK'
  obtain ⟨Φ, hΦ⟩ := burnsideF4gF4Two_key hK
  let e1 : ↥(reeGroup K 0) ≃* Gm K 0 := MulEquiv.subgroupCongr burnsideF4gF4Two_reeGroup_eq
  let Φ' : ↥(reeGroup K 0) ≃* ↥twoF4M := e1.trans Φ
  obtain ⟨Θ, hΘ⟩ := burnsideF4gF4Two_commutator_equiv (reeGroup K 0) Φ'
  have hZ : Subgroup.center ↥⁅reeGroup K 0, reeGroup K 0⁆ = ⊥ := by
    have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv Θ
    rw [titsD_center] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Θ.injective).1 h
  obtain ⟨eC, heC⟩ := burnsideF4gF4Two_exists_derivedEquiv (reeGroup K 0)
    ⁅reeGroup K 0, reeGroup K 0⁆ rfl hZ
  let Ψ : ↥Gp ≃* ↥titsD := marking.symm.trans (eC.trans Θ)
  have hsup : M₁ ⊔ M₂ = Gp := hyp4.gen.trans hGp.symm
  let θ : ↥(M₁ ⊔ M₂) ≃* ↥(titsH ⊔ titsN) :=
    (MulEquiv.subgroupCongr hsup).trans (Ψ.trans (MulEquiv.subgroupCongr titsH_sup_N.symm))
  have hle : ⁅reeGroup K 0, reeGroup K 0⁆ ≤ reeGroup K 0 := Subgroup.commutator_le_self _
  have hM : ∀ (M : Subgroup E) (P : Subgroup (ModGL Tag.F4 K)),
      M.subgroupOf Gp = (derivedImage (reeGroup K 0) P).map marking.toMonoidHom →
      ∀ y : ↥Gp, (y : E) ∈ M ↔
        (((eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆) : ModGL Tag.F4 K) ∈ P) := by
    intro M P hMP y
    have hy : (y : E) ∈ M ↔ y ∈ M.subgroupOf Gp := Iff.rfl
    have h3 := burnsideF4gF4Two_map_derivedImage (reeGroup K 0) ⁅reeGroup K 0, reeGroup K 0⁆ P rfl
      eC heC
    have h4 : ∀ z : DerivedCentralQuotient (reeGroup K 0),
        z ∈ derivedImage (reeGroup K 0) P ↔
          ((eC z : ↥⁅reeGroup K 0, reeGroup K 0⁆) : ModGL Tag.F4 K) ∈ P := by
      intro z
      have h5 : eC z ∈ (derivedImage (reeGroup K 0) P).map eC.toMonoidHom ↔
          z ∈ derivedImage (reeGroup K 0) P := by
        rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
      rw [← h5, h3]
      exact Iff.rfl
    rw [hy, hMP, Subgroup.mem_map_equiv]
    exact h4 _
  have hM₁ : ∀ y : ↥Gp, (y : E) ∈ M₁ ↔
      (e1 ⟨(eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆),
        hle (eC (marking.symm y)).2⟩ : Gm K 0) ∈ (burnsideF4gF4Two_system hK).P₁ := fun y =>
    (hM M₁ _ h1 y).trans (burnsideF4gF4Two_mem_P₁_iff hK (e1 ⟨(eC (marking.symm y) :
      ↥⁅reeGroup K 0, reeGroup K 0⁆), hle (eC (marking.symm y)).2⟩)).symm
  have hM₂ : ∀ y : ↥Gp, (y : E) ∈ M₂ ↔
      (e1 ⟨(eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆),
        hle (eC (marking.symm y)).2⟩ : Gm K 0) ∈ (burnsideF4gF4Two_system hK).P₂ := fun y =>
    (hM M₂ _ h2 y).trans (burnsideF4gF4Two_mem_P₂_iff hK (e1 ⟨(eC (marking.symm y) :
      ↥⁅reeGroup K 0, reeGroup K 0⁆), hle (eC (marking.symm y)).2⟩)).symm
  have hz : ∀ (P : Subgroup (Gm K 0)) (z : Gm K 0), Φ z ∈ P.map Φ.toMonoidHom ↔ z ∈ P := by
    intro P z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hΨ : ∀ y : ↥Gp, ((Ψ y : ↥titsD) : Equiv.Perm (Fin 1755)) =
      ((Φ (e1 ⟨(eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆),
        hle (eC (marking.symm y)).2⟩) : ↥twoF4M) : Equiv.Perm (Fin 1755)) := fun y =>
    hΘ (eC (marking.symm y))
  have hH : ∀ g : ↥titsD, (g : Equiv.Perm (Fin 1755)) ∈ twoF4H ↔
      (g : Equiv.Perm (Fin 1755)) ∈ titsH := fun g =>
    ⟨fun hg => mem_of_mem_extSub_of_mem_D titsH_le_titsD hg g.2, fun hg => Or.inl hg⟩
  have hN : ∀ g : ↥titsD, (g : Equiv.Perm (Fin 1755)) ∈ twoF4N ↔
      (g : Equiv.Perm (Fin 1755)) ∈ titsN := fun g =>
    ⟨fun hg => mem_of_mem_extSub_of_mem_D titsN_le_titsD hg g.2, fun hg => Or.inl hg⟩
  rcases hΦ with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · have k1 : ∀ z : Gm K 0, z ∈ (burnsideF4gF4Two_system hK).P₁ ↔
        ((Φ z : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4H := by
      intro z
      rw [← hz _ z, hp1]
      exact Iff.rfl
    have k2 : ∀ z : Gm K 0, z ∈ (burnsideF4gF4Two_system hK).P₂ ↔
        ((Φ z : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4N := by
      intro z
      rw [← hz _ z, hp2]
      exact Iff.rfl
    refine ⟨θ, Or.inl ⟨fun x => (hM₁ (MulEquiv.subgroupCongr hsup x)).trans ((k1 _).trans ?_),
      fun x => (hM₂ (MulEquiv.subgroupCongr hsup x)).trans ((k2 _).trans ?_)⟩⟩
    · rw [← hΨ]
      exact hH _
    · rw [← hΨ]
      exact hN _
  · have k1 : ∀ z : Gm K 0, z ∈ (burnsideF4gF4Two_system hK).P₁ ↔
        ((Φ z : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4N := by
      intro z
      rw [← hz _ z, hp1]
      exact Iff.rfl
    have k2 : ∀ z : Gm K 0, z ∈ (burnsideF4gF4Two_system hK).P₂ ↔
        ((Φ z : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4H := by
      intro z
      rw [← hz _ z, hp2]
      exact Iff.rfl
    refine ⟨θ, Or.inr ⟨fun x => (hM₁ (MulEquiv.subgroupCongr hsup x)).trans ((k1 _).trans ?_),
      fun x => (hM₂ (MulEquiv.subgroupCongr hsup x)).trans ((k2 _).trans ?_)⟩⟩
    · rw [← hΨ]
      exact hN _
    · rw [← hΨ]
      exact hH _

end Chart

section Match

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits


theorem burnsideF48s_tits_match : burnsideF48s_Match titsH titsN 8 :=
  burnsideF48s_match_of_equiv fun _ _ _ β hβ hs =>
    CFSG.Quasithin.TitsGeo.titsF48_equiv_small Certificates.certificate4190
      Certificates.certificate4191 β hβ hs

end Match

section Main

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Sporadic.Schreier.Tits


theorem burnsideF48s_small_Tits (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .Tits p f Gp M₁ M₂) : F48Concl .Tits p f Gp M₁ M₂ := by
  obtain rfl : p = 2 := hyp.model.1
  obtain rfl : f = 1 := hyp.model.2.1
  haveI : Finite E := hyp.finite
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr rfl)
  subst hGp
  obtain ⟨θ, hθ⟩ := burnsideF48s_tits_chart hyp
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .Tits 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  have h13 := (burnside_as_F_4_13_of h45 h46 .Tits 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
  rw [card_G0] at h13
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [h13]; exact Nat.card_pos.ne')
  exact burnsideF48s_qe_of_match_or burnsideF48s_tits_match θ hθ β hβ hs

end Main

end CFSG.ASVolI
