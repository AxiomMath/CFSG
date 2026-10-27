module

public import CFSG.Milestones.ASVolI.F48.Small.Trans
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Eqv
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.Milestones.ASVolI.F48.Id
public import CFSG.Milestones.ASVolI.F4K.Main
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.U42

section Model

theorem burnsideF48s_u42_isLieParabolics : IsLieParabolics 2 (⊤ : Subgroup Y) B0 P1 P2 := by
  have hcard : Nat.card Y = 25920 := card_Xs
  have hidx : T.index = 405 := by
    have h := Subgroup.card_mul_index T
    rw [card_T, hcard] at h
    omega
  have h1 : Nat.card P1 = 576 := card_P1
  have h2 : Nat.card P2 = 960 := card_P2
  have hb : Nat.card B0 = 192 := card_B0
  have hne1 : P1 ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top, hcard] at h1
    norm_num at h1
  have hne2 : P2 ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top, hcard] at h2
    norm_num at h2
  have hB1 : B0 ≠ P1 := fun h => by
    rw [h, h1] at hb
    norm_num at hb
  have hco1 : IsCoatom P1 := by
    refine ⟨hne1, fun R hR => ?_⟩
    rcases lattice (B0_le_P1.trans hR.le) with h | h | h | h
    · subst h
      exact absurd B0_le_P1 (not_le_of_gt hR)
    · exact absurd h hR.ne'
    · subst h
      have hd := Subgroup.card_dvd_of_le hR.le
      rw [h1, h2] at hd
      norm_num at hd
    · exact h
  have hco2 : IsCoatom P2 := by
    refine ⟨hne2, fun R hR => ?_⟩
    rcases lattice (B0_le_P2.trans hR.le) with h | h | h | h
    · subst h
      exact absurd B0_le_P2 (not_le_of_gt hR)
    · subst h
      have hd := Subgroup.card_dvd_of_le hR.le
      rw [h1, h2] at hd
      norm_num at hd
    · exact absurd h hR.ne'
    · exact h
  refine burnsideF4h_cl_isLieParabolics_top_of (S := T)
    (IsPGroup.of_card (n := 6) (by rw [card_T]; norm_num)) (by rw [hidx]; decide) normalizer_T
    P1_ne_P2 rfl hco1 hco2 fun Q hBQ hQc => ?_
  rcases lattice hBQ with h | h | h | h
  · subst h
    exact absurd (hQc.2 P1 (lt_of_le_of_ne B0_le_P1 hB1)) hne1
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hQc.1

theorem burnsideF48s_u42_conj_injective : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  intro a b h
  have hc : b⁻¹ * a ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : (MulAut.conj (b⁻¹ * a) : MulAut Y) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h3 := congrArg (fun φ : MulAut Y => φ y) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * (b⁻¹ * a) = (b⁻¹ * a * y * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [h3]
      _ = (b⁻¹ * a) * y := by group
  rw [center_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem burnsideF48s_u42_range :
    (MulAut.conj : Y →* MulAut Y).range = A0.N1 ⊔ A0.N2 :=
  A0_K.symm

@[expose] noncomputable def burnsideF48s_u42_conjEquiv : Y ≃* ↥(A0.N1 ⊔ A0.N2) :=
  (MonoidHom.ofInjective burnsideF48s_u42_conj_injective).trans
    (MulEquiv.subgroupCongr burnsideF48s_u42_range)

theorem burnsideF48s_u42_conjEquiv_coe (y : Y) :
    ((burnsideF48s_u42_conjEquiv y : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) = MulAut.conj y :=
  rfl

theorem burnsideF48s_u42_mem_N1 (y : Y) :
    ((burnsideF48s_u42_conjEquiv y : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N1 ↔ y ∈ P1 := by
  rw [burnsideF48s_u42_conjEquiv_coe, A0_N1]
  exact Subgroup.mem_map_iff_mem burnsideF48s_u42_conj_injective

theorem burnsideF48s_u42_mem_N2 (y : Y) :
    ((burnsideF48s_u42_conjEquiv y : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N2 ↔ y ∈ P2 := by
  rw [burnsideF48s_u42_conjEquiv_coe, A0_N2]
  exact Subgroup.mem_map_iff_mem burnsideF48s_u42_conj_injective

end Model

section Match

theorem burnsideF48s_u42_match : burnsideF48s_Match A0.N1 A0.N2 4 :=
  burnsideF48s_match_of_equiv fun _ _ _ β hβ hs => u42_equiv_small β hβ hs

end Match

section Main

theorem burnsideF48s_u42_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∃ θ : ↥(M₁ ⊔ M₂) ≃* ↥(A0.N1 ⊔ A0.N2),
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N1) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N2) ∨
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N2) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N1) := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hGp
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := nonempty_mulEquiv_Y (burnsideF48_lieModel_U4 hyp.model)
  obtain ⟨ε, -, hε⟩ := burnsideF48_identify ε₀.symm burnsideF48s_u42_isLieParabolics hP
  set θ : ↥(M₁ ⊔ M₂) ≃* ↥(A0.N1 ⊔ A0.N2) :=
    ((MulEquiv.subgroupCongr hyp.gen).trans ε.symm).trans burnsideF48s_u42_conjEquiv with hθ
  have hval : ∀ x : ↥(M₁ ⊔ M₂),
      (x : E) = ((ε (ε.symm (MulEquiv.subgroupCongr hyp.gen x)) : ↥(⊤ : Subgroup E)) : E) := by
    intro x
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hmem : ∀ (Q : Subgroup Y) (M : Subgroup E), burnsideF48_img ε Q = ⊤ ⊓ M →
      ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M ↔ ε.symm (MulEquiv.subgroupCongr hyp.gen x) ∈ Q := by
    intro Q M hQ x
    rw [hval x, ← burnsideF48_mem_img ε Q, hQ, top_inf_eq]
  have hθ1 : ∀ x : ↥(M₁ ⊔ M₂), ((θ x : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N1 ↔
      ε.symm (MulEquiv.subgroupCongr hyp.gen x) ∈ P1 := fun x =>
    burnsideF48s_u42_mem_N1 _
  have hθ2 : ∀ x : ↥(M₁ ⊔ M₂), ((θ x : ↥(A0.N1 ⊔ A0.N2)) : MulAut Y) ∈ A0.N2 ↔
      ε.symm (MulEquiv.subgroupCongr hyp.gen x) ∈ P2 := fun x =>
    burnsideF48s_u42_mem_N2 _
  refine ⟨θ, ?_⟩
  rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨fun x => (hmem P1 M₁ h1 x).trans (hθ1 x).symm,
      fun x => (hmem P2 M₂ h2 x).trans (hθ2 x).symm⟩
  · exact Or.inr ⟨fun x => (hmem P2 M₁ h2 x).trans (hθ2 x).symm,
      fun x => (hmem P1 M₂ h1 x).trans (hθ1 x).symm⟩

theorem burnsideF48s_small_U4_two_top (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .U4 2 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    F48Concl .U4 2 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  obtain ⟨θ, hθ⟩ := burnsideF48s_u42_chart hyp hGp
  subst hGp
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .U4 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  have h13 := (burnside_as_F_4_13_of h45 h46 .U4 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
  rw [card_G0] at h13
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [h13]; exact Nat.card_pos.ne')
  exact burnsideF48s_qe_of_match_or burnsideF48s_u42_match θ hθ β hβ hs

end Main

end CFSG.ASVolI
