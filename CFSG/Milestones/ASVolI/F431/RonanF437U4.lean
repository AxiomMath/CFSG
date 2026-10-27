module

public import CFSG.Milestones.ASVolI.F431.RonanOddU4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.RonanF57
  CFSG.Quasithin.H13.F431.U42Aut

section Model

theorem index_eq_two_of_fullIso {E : Type} [Group E]
    {Gp : Subgroup E} (Θ : E ≃* Ah) (hY : ∀ x : E, Θ x ∈ Yh ↔ x ∈ Gp) : Gp.index = 2 := by
  have hmap : Gp.map Θ.toMonoidHom = Yh := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hY x).2 hx
    · intro ha
      refine ⟨Θ.symm a, (hY _).1 ?_, by simp⟩
      simpa using ha
  have h1 : Gp.index = Yh.index := by
    rw [← hmap, Subgroup.index_map_of_bijective Θ.bijective]
  have hP : Nat.card ↥Yh = 25920 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe CFSG.Quasithin.SimsF5.mk_P_le_A).toEquiv).trans
      CFSG.Quasithin.SimsF5.mk_card_P
  have hA : Nat.card Ah = 51840 := CFSG.Quasithin.SimsF5.mk_card_A
  have h2 := Subgroup.card_mul_index Yh
  rw [hP, hA] at h2
  omega

theorem nonempty_mulEquiv_mulAut_of_fullIso {E : Type} [Group E]
    {Gp : Subgroup E} (Θ : E ≃* Ah) (hY : ∀ x : E, Θ x ∈ Yh ↔ x ∈ Gp) :
    Nonempty (E ≃* MulAut ↥Gp) := by
  obtain ⟨Ψ, -⟩ := CFSG.Quasithin.SimsF5.mk_aut_real
  have hmap : Gp.map Θ.toMonoidHom = Yh := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hY x).2 hx
    · intro ha
      refine ⟨Θ.symm a, (hY _).1 ?_, by simp⟩
      simpa using ha
  let e₁ : ↥Gp ≃* ↥Yh :=
    (Gp.equivMapOfInjective Θ.toMonoidHom Θ.injective).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨Θ.trans (Ψ.symm.trans
    (MulAut.congr (e₁.trans (Subgroup.subgroupOfEquivOfLe CFSG.Quasithin.SimsF5.mk_P_le_A))).symm)⟩


theorem nonempty_mulEquiv_sup_of_autCtx {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}
    {z : G} (c : AutCtx G M₁ M₂ z) : Nonempty (Ah ≃* ↥(M₁ ⊔ M₂)) := by
  obtain ⟨d, -, -, hrange, -, -⟩ := CFSG.Quasithin.SimsF5.exists_rhoData c
  exact ⟨(MonoidHom.ofInjective d.inj).trans (MulEquiv.subgroupCongr hrange)⟩

end Model

section Main


theorem f437FourIIU4_of_lie (hlie : LieOfAutCtx) : F437FourIIU4 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp Tb _hTb fb _hfbT hfbS hfb2 _hIII hsyl _hnoti
  classical
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hfbG : (fb : E) ∉ Gp := by
    intro hG
    apply hfbS
    have hC : (fb : E) ∈ cenIn Gp (fb : E) :=
      ⟨hG, Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]⟩
    have := central_mem_sylowOf hsyl.1 hsyl.2.1 hsyl.2.2 hC hfb2
      (fun c hc => (Subgroup.mem_centralizer_iff.mp hc.2 (fb : E) (Set.mem_singleton _)).symm)
    exact (Subgroup.mem_inf.mp this).1
  have hne : Gp ≠ ⊤ := fun h => hfbG (h ▸ Subgroup.mem_top _)
  have hout : ∃ n ∈ M₁ ⊓ M₂, n ∉ Gp := ⟨fb, fb.2, hfbG⟩
  obtain ⟨K, iK, fK, hKc, σ, hσ, m, point, plane, hp1, hp2, hpp, hiso, hpar1, hpar2⟩ :=
    ronOdd_exists_flag hyp.amalgam.toHypF_4_4g
  obtain ⟨Θ, hY, -, -⟩ := CFSG.Quasithin.RonanF438.exists_fullIso
    hyp.amalgam.centralizer_trivial hne hout hKc hσ m point plane hp1 hp2 hpp hiso hpar1 hpar2
  have hev : ¬ Odd Gp.index := by
    rw [index_eq_two_of_fullIso Θ hY]
    decide
  obtain ⟨c⟩ := ctx_of_even_index_U4 hyp hev
  refine ⟨nonempty_mulEquiv_mulAut_of_fullIso Θ hY, ?_, isL43_of_lieModel (hlie M _ _ z c)⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_sup_of_autCtx c
  exact ⟨Θ.trans (e.trans ((MonoidHom.ofInjective hyp.inj).trans
    (MulEquiv.subgroupCongr (burnsideF4d_Z3_range_epsG β ε))).symm)⟩

end Main

end CFSG.ASVolI
