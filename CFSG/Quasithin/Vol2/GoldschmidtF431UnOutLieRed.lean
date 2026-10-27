module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieYam
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieMapB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieIsoB
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructLoc

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.Un.OL
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def UnOutConcl {D : Type} [Group D] (A : LieAmalgamExt D) : Prop :=
  ∃ (T S : Subgroup ↥A.K) (g z t : ↥A.K) (V : Subgroup ↥A.K),
    F431UnOut T S g A.Mb1 A.Mb2 z t V ∨ F431UnOut T S g A.Mb2 A.Mb1 z t V

theorem unOutConcl_of_kiso {D D' : Type} [Group D] [Group D'] {A : LieAmalgamExt D}
    {A' : LieAmalgamExt D'} (L : KIso A A') : UnOutConcl A' → UnOutConcl A := by
  rintro ⟨T', S', g', z', t', V', hD | hD⟩
  · refine ⟨T'.map L.ψ.symm.toMonoidHom, S'.map L.ψ.symm.toMonoidHom, L.ψ.symm g', L.ψ.symm z',
      L.ψ.symm t', V'.map L.ψ.symm.toMonoidHom, Or.inl ?_⟩
    have := F431UnOut.map L.ψ.symm hD
    rwa [L.map_Mb1, L.map_Mb2] at this
  · refine ⟨T'.map L.ψ.symm.toMonoidHom, S'.map L.ψ.symm.toMonoidHom, L.ψ.symm g', L.ψ.symm z',
      L.ψ.symm t', V'.map L.ψ.symm.toMonoidHom, Or.inr ?_⟩
    have := F431UnOut.map L.ψ.symm hD
    rwa [L.map_Mb1, L.map_Mb2] at this

section Normalize

theorem unred_map_conj_conj_inv {H : Type} [Group H] (U : Subgroup H) (c : H) :
    (U.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id H := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem unred_map_refl {H : Type} [Group H] (X : Subgroup H) :
    X.map (MulEquiv.refl H).toMonoidHom = X := by
  ext x
  simp

theorem exists_unNormalized {D : Type} [Group D] {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) [CharP K 2]
    (hY : CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Xg h) (Psy h) (Pt h) (Ln h)) (e : D ≃* Xg h)
    (A : LieAmalgamExt D) :
    ∃ A' : LieAmalgamExt (Xg h), A'.TD = Psy h ∧
      ((A'.P1 = Pt h ∧ A'.P2 = Ln h) ∨ (A'.P1 = Ln h ∧ A'.P2 = Pt h)) ∧ Nonempty (KIso A A') := by
  let E1 : LieExt (Xg h) A.N1 A.N2 := A.toLieExt.congr e
  let L1 : LocIso A.toLieExt E1 := A.toLieExt.congrOfLocIso e _ rfl
  obtain ⟨c, hTD, hP⟩ := hY.pair (MulEquiv.refl (Xg h)) E1.yam
  rw [unred_map_refl] at hTD
  let E2 : LieExt (Xg h) A.N1 A.N2 := E1.conjSylow c⁻¹
  let L2 : LocIso E1 E2 :=
    E1.congrOfLocIso (MulAut.conj c⁻¹) E1.Mbar (E1.Mbar_eq_map_conj c⁻¹)
  refine ⟨E2.toLieAmalgamExt, ?_, ?_, ⟨(L1.trans L2).toKIso⟩⟩
  · show E1.TD.map (MulAut.conj c⁻¹).toMonoidHom = _
    rw [hTD, unred_map_conj_conj_inv]
  · show (E1.P1.map (MulAut.conj c⁻¹).toMonoidHom = _ ∧
        E1.P2.map (MulAut.conj c⁻¹).toMonoidHom = _) ∨
      (E1.P1.map (MulAut.conj c⁻¹).toMonoidHom = _ ∧
        E1.P2.map (MulAut.conj c⁻¹).toMonoidHom = _)
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [unred_map_refl] at h1 h2
      left
      rw [h1, h2, unred_map_conj_conj_inv, unred_map_conj_conj_inv]
      exact ⟨rfl, rfl⟩
    · rw [unred_map_refl] at h1 h2
      right
      rw [h1, h2, unred_map_conj_conj_inv, unred_map_conj_conj_inv]
      exact ⟨rfl, rfl⟩

end Normalize

section Main

theorem f431UnOutLieProp_of_model (f : ℕ) (hf : 2 ≤ f)
    (H : ∀ (K : Type) [Field K] [CharP K 2] (h : UnitaryFieldData 2 f K)
        [IsSimpleGroup (Xg h)],
      CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Xg h) (Psy h) (Pt h) (Ln h) →
      ∀ K₀ : Subgroup (MulAut (Xg h)), (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀ →
        ¬ Odd (Nat.card K₀ / Nat.card (Xg h)) →
        ∃ (T S : Subgroup (MulAut (Xg h))) (g z t : MulAut (Xg h))
          (V : Subgroup (MulAut (Xg h))),
          UnOutRel K₀ T S g (K₀ ⊓ autStab (Pt h)) (K₀ ⊓ autStab (Ln h)) z t V) :
    F431UnOutLieProp 4 f := by
  intro D _ hD A hnodd
  obtain ⟨K, _, h, hc, hs, ⟨e⟩, hY⟩ := exists_model_yamStd hf hD
  obtain ⟨A', hTD, hP, ⟨L⟩⟩ := exists_unNormalized h hY e A
  have hsup : A'.P1 ⊔ A'.P2 = ⊤ := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
    · rw [h1, h2, sup_comm]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
  have hinn := A'.range_conj_le_K hsup
  have hcard : Nat.card ↥A'.K / Nat.card (Xg h) = Nat.card ↥A.K / Nat.card D := by
    rw [L.card_K, Nat.card_congr e.toEquiv.symm]
  obtain ⟨T, S, g, z, t, V, R⟩ := H K h hY A'.K hinn (hcard ▸ hnodd)
  obtain ⟨g', z', t', hO⟩ := R.toOut
  refine unOutConcl_of_kiso L ⟨T.subgroupOf A'.K, S.subgroupOf A'.K, g', z', t',
    V.subgroupOf A'.K, ?_⟩
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [A'.Mb1_eq_std, A'.Mb2_eq_std, h1, h2]
    exact hO
  · right
    rw [A'.Mb1_eq_std, A'.Mb2_eq_std, h1, h2]
    exact hO

end Main

end CFSG.Quasithin.H13.F431.Un
