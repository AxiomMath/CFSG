module

public import CFSG.Milestones.ASVolI.F48.Small.Trans
public import CFSG.Quasithin.Vol2.TwoF4F48Eqv
public import Certificates.Certificate15080
public import CFSG.Milestones.ASVolI.F4K.Main
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm

public section

namespace CFSG.ASVolI

section Chart

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431.TwoF4 CFSG.ASVolI.ChF
  CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Blueprint CFSG.Blueprint.Chevalley


theorem burnsideF48s_twoF4_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .F4tw 2 1 Gp M₁ M₂) :
    Gp = ⊤ ∧ ∃ θ : ↥(M₁ ⊔ M₂) ≃* ↥(twoF4H ⊔ twoF4N),
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(twoF4H ⊔ twoF4N)) : Equiv.Perm (Fin 1755)) ∈ twoF4H) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔
          ((θ x : ↥(twoF4H ⊔ twoF4N)) : Equiv.Perm (Fin 1755)) ∈ twoF4N) ∨
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(twoF4H ⊔ twoF4N)) : Equiv.Perm (Fin 1755)) ∈ twoF4N) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔
          ((θ x : ↥(twoF4H ⊔ twoF4N)) : Equiv.Perm (Fin 1755)) ∈ twoF4H) := by
  haveI := hyp.normal
  obtain ⟨a, K, fK, finK, charK, hscope, hfa, marking, h1, h2⟩ := burnsideF4gF4Two_chart_F4tw hyp
  have ha : a = 0 := by omega
  subst ha
  letI := fK
  haveI := finK
  haveI : CharP K F4.prime := charK
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := hscope
  have hK : Nat.card K = 2 := by simpa using hK'
  have hcen : Subgroup.center ↥(reeGroup K 0) = ⊥ := by
    have := large_Ree_fixed_group_center_trivial 0 K hK'
    rwa [burnsideF4gF4Two_reeGroup_eq]
  obtain ⟨q, hq⟩ := burnsideF4gF4Two_exists_quotEquiv hcen
  obtain ⟨Φ, hΦ⟩ := burnsideF4gF4Two_key hK
  let e1 : ↥(reeGroup K 0) ≃* Gm K 0 := MulEquiv.subgroupCongr burnsideF4gF4Two_reeGroup_eq
  let Ψ0 : ↥(reeGroup K 0) ≃* ↥Gp := q.trans marking
  let Ψ : ↥Gp ≃* ↥twoF4M := Ψ0.symm.trans (e1.trans Φ)
  have hGp : Gp = ⊤ := burnsideF4gF4Two_eq_top hyp.centralizer_trivial Ψ
  have hsup : M₁ ⊔ M₂ = Gp := hyp.gen.trans hGp.symm
  let θ : ↥(M₁ ⊔ M₂) ≃* ↥(twoF4H ⊔ twoF4N) :=
    (MulEquiv.subgroupCongr hsup).trans
      (Ψ.trans (MulEquiv.subgroupCongr J47.sup_twoF4H_N.symm))
  have hM₁ : ∀ y : ↥Gp, (y : E) ∈ M₁ ↔
      (e1 (Ψ0.symm y) : Gm K 0) ∈ (burnsideF4gF4Two_system hK).P₁ := fun y =>
    (burnsideF4gF4Two_mem_centralImage marking q hq h1 y).trans
      (burnsideF4gF4Two_mem_P₁_iff hK (e1 (Ψ0.symm y))).symm
  have hM₂ : ∀ y : ↥Gp, (y : E) ∈ M₂ ↔
      (e1 (Ψ0.symm y) : Gm K 0) ∈ (burnsideF4gF4Two_system hK).P₂ := fun y =>
    (burnsideF4gF4Two_mem_centralImage marking q hq h2 y).trans
      (burnsideF4gF4Two_mem_P₂_iff hK (e1 (Ψ0.symm y))).symm
  have hz : ∀ (P : Subgroup (Gm K 0)) (z : Gm K 0), Φ z ∈ P.map Φ.toMonoidHom ↔ z ∈ P := by
    intro P z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  refine ⟨hGp, θ, ?_⟩
  rcases hΦ with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · refine Or.inl ⟨fun x => (hM₁ (MulEquiv.subgroupCongr hsup x)).trans ?_,
      fun x => (hM₂ (MulEquiv.subgroupCongr hsup x)).trans ?_⟩
    · rw [← hz _, hp1]
      exact Iff.rfl
    · rw [← hz _, hp2]
      exact Iff.rfl
  · refine Or.inr ⟨fun x => (hM₁ (MulEquiv.subgroupCongr hsup x)).trans ?_,
      fun x => (hM₂ (MulEquiv.subgroupCongr hsup x)).trans ?_⟩
    · rw [← hz _, hp1]
      exact Iff.rfl
    · rw [← hz _, hp2]
      exact Iff.rfl

end Chart

section Match

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits


theorem burnsideF48s_twoF4_match : burnsideF48s_Match twoF4H twoF4N 8 :=
  burnsideF48s_match_of_equiv fun _ _ _ β hβ hs =>
    CFSG.Quasithin.H13.TwoF4F48.twoF4_equiv_small β hβ hs

end Match

section Main

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits


theorem burnsideF48s_small_F4tw_two (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .F4tw p f Gp M₁ M₂) (hq : p ^ f ≤ 3) :
    F48Concl .F4tw p f Gp M₁ M₂ := by
  obtain ⟨hp, -, hf⟩ := hyp.model
  subst hp
  have hf1 : f = 1 := by
    rcases hf with ⟨h, -⟩ | ⟨h3, -⟩
    · exact h
    · exfalso
      have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
      omega
  subst hf1
  haveI : Finite E := hyp.finite
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  obtain ⟨hGp, θ, hθ⟩ := burnsideF48s_twoF4_chart hyp.toHypF_4_4g
  subst hGp
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .F4tw 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  have h13 := (burnside_as_F_4_13_of h45 h46 .F4tw 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
  rw [card_G0] at h13
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [h13]; exact Nat.card_pos.ne')
  exact burnsideF48s_qe_of_match_or burnsideF48s_twoF4_match θ hθ β hβ hs

end Main

end CFSG.ASVolI
