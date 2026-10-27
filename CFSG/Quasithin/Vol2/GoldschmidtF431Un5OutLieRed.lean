module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieRedGen
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieLab
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNorm
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieMapB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.D4q.Struct

theorem exists_model5 {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSU 5 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K), Nonempty (D ≃* hypPSU h 2 1) := by
  rcases hD with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hc
    have hm : 1 ≤ f := hadm.2.1
    have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
    exact ⟨K, inferInstance, h,
      ⟨e.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm⟩⟩
  all_goals exact absurd hn (by norm_num)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem un5_exists_normalized2 (hf : f = 2) {A' : LieAmalgamExt (hypPSU h 2 1)}
    (hTD : A'.TD = hypProjUnitriangular h 2 1)
    (hP : (A'.P1 = u5PtP h ∧ A'.P2 = u5LnP h) ∨ (A'.P1 = u5LnP h ∧ A'.P2 = u5PtP h))
    (hinn : (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)).range ≤ A'.K) :
    ∃ A'' : LieAmalgamExt (hypPSU h 2 1), A''.TD = hypProjUnitriangular h 2 1 ∧
      ((A''.P1 = u5PtP h ∧ A''.P2 = u5LnP h) ∨ (A''.P1 = u5LnP h ∧ A''.P2 = u5PtP h)) ∧
      Nonempty (KIso A' A'') ∧ ∃ F₂ : Subgroup (K ≃+* K),
        IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) A''.K := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  obtain ⟨g, hg, F₂, hsyl⟩ := exists_normalized5 h hf (K' := A'.K) hinn
  have hf2 : 2 ≤ f := by omega
  have hgU : (hypProjUnitriangular h 2 1).map g.toMonoidHom = hypProjUnitriangular h 2 1 :=
    (AG.mem_autStab_iff_map_eq g _).1 hg
  have hgP : (u5PtP h).map g.toMonoidHom = u5PtP h :=
    (AG.mem_autStab_iff_map_eq g _).1 (autStab_U_le_Pt h hf2 hg)
  have hgL : (u5LnP h).map g.toMonoidHom = u5LnP h :=
    (AG.mem_autStab_iff_map_eq g _).1 (autStab_U_le_Ln h hf2 hg)
  let E : LieExt (hypPSU h 2 1) A'.N1 A'.N2 := A'.toLieExt
  refine ⟨(E.congr g).toLieAmalgamExt, ?_, ?_, ⟨(E.congrOfLocIso g _ rfl).toKIso⟩, F₂, ?_⟩
  · show A'.TD.map g.toMonoidHom = _
    rw [hTD, hgU]
  · show (A'.P1.map g.toMonoidHom = _ ∧ A'.P2.map g.toMonoidHom = _) ∨
      (A'.P1.map g.toMonoidHom = _ ∧ A'.P2.map g.toMonoidHom = _)
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hgP, hgL]
      exact Or.inl ⟨rfl, rfl⟩
    · rw [h1, h2, hgP, hgL]
      exact Or.inr ⟨rfl, rfl⟩
  · have hK0 := LieExt.congrOf_K E g (E.Mbar.map (MulAut.congr g).toMonoidHom) rfl
    have hK : (E.congr g).toLieAmalgamExt.K = A'.K.map (MulAut.conj g).toMonoidHom := by
      refine hK0.trans ?_
      congr 1
    rw [hK]
    exact hsyl

theorem f431UnOutLieProp_of_model5
    (H : ∀ (K : Type) [Field K] (h : UnitaryFieldData 2 2 K)
        (K₀ : Subgroup (MulAut (hypPSU h 2 1))) (F₂ : Subgroup (K ≃+* K)),
      Pi h ≤ K₀ → ¬ Odd (Nat.card K₀ / Nat.card (hypPSU h 2 1)) →
      IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) K₀ →
      ∃ (g z t : MulAut (hypPSU h 2 1)) (V : Subgroup (MulAut (hypPSU h 2 1))),
        UnOutRel K₀ (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂)
          (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥) g
          (K₀ ⊓ autStab (u5PtP h)) (K₀ ⊓ autStab (u5LnP h)) z t V) :
    F431UnOutLieProp 5 2 := by
  intro D _ hD A hnodd
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_model5 hD
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hY := u5_yamStd (h := h)
  have hsupc : ∀ A₀ : LieAmalgamExt (hypPSU h 2 1),
      ((A₀.P1 = u5PtP h ∧ A₀.P2 = u5LnP h) ∨ (A₀.P1 = u5LnP h ∧ A₀.P2 = u5PtP h)) →
      A₀.P1 ⊔ A₀.P2 = ⊤ := by
    rintro A₀ (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [h1, h2]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
    · rw [h1, h2, sup_comm]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
  obtain ⟨A', hTD, hP, ⟨L1⟩⟩ := un5_exists_normalized hY e A
  have hinn := A'.range_conj_le_K (hsupc A' hP)
  obtain ⟨A'', hTD'', hP'', ⟨L2⟩, F₂, hsyl⟩ := un5_exists_normalized2 h rfl hTD hP hinn
  have hinn'' := A''.range_conj_le_K (hsupc A'' hP'')
  have hcard : Nat.card ↥A''.K / Nat.card (hypPSU h 2 1) = Nat.card ↥A.K / Nat.card D := by
    rw [L2.card_K, L1.card_K, Nat.card_congr e.toEquiv]
  obtain ⟨g, z, t, V, R⟩ := H K h A''.K F₂ hinn'' (hcard ▸ hnodd) hsyl
  obtain ⟨g', z', t', hO⟩ := R.toOut
  refine unOutConcl5_of_kiso L1 (unOutConcl5_of_kiso L2
    ⟨(Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂).subgroupOf A''.K,
      (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥).subgroupOf A''.K, g', z', t',
      V.subgroupOf A''.K, ?_⟩)
  rcases hP'' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [A''.Mb1_eq_std, A''.Mb2_eq_std, h1, h2]
    exact hO
  · right
    rw [A''.Mb1_eq_std, A''.Mb2_eq_std, h1, h2]
    exact hO

end CFSG.Quasithin.H13.F431.Un.OL5
