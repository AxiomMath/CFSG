module

public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTorus
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4CoreAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem ggTorusCoordFrameElt_adjointF4
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusCoordFrameElt p 4 (adjointGroup .F4 K) CoxeterMatrix.F₄ := by
  intro E hE hr _ k τ hτ hτE
  have hcardE : Nat.card E = p ^ 4 := F4AutWeyl.card_eq_pow_four_of_le hp hp2 hE hr
  have hcardτ : Nat.card (Multiplicative (Fin k → ZMod p)) = Nat.card E :=
    Nat.card_congr ((MonoidHom.ofInjective hτ).trans (MulEquiv.subgroupCongr hτE))
  have hk : k = 4 := Nat.pow_right_injective hp.two_le (by
    show p ^ k = p ^ 4
    rw [← CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod k, hcardτ, hcardE])
  subst hk
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hT : GGF4ToralRankInput K p :=
    ggF4ToralRankInput_of_three hp hp2 hpq (fun _ => ggF4ThreeRankInput_holds)
  obtain ⟨g, hg⟩ := hT E hE hr
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod p) := by
    rw [det_cartan_F4, Int.cast_one]; exact isUnit_one
  set χ : Multiplicative (Fin 4 → ZMod p) →* adjointGroup .F4 K :=
    CFSG.RankThree.CentralCover.chevTorus .F4 ζ hζ with hχ
  have hχinj : Function.Injective χ := by
    rw [hχ]
    exact CFSG.RankThree.CentralCover.chevTorus_injective hζo hζ hdet
  have hχr : χ.range = TableBF4.torusPow K p := by
    rw [hχ]
    exact range_chevTorus_eq_torusPow_of_prime hp hpq hζo hζ
  have hbase : GGTorusCoordFrame p χ CoxeterMatrix.F₄ := by
    let θ : Multiplicative (Fin 4 → ZMod p) ≃* ↥(TableBF4.torusPow K p) :=
      (MonoidHom.ofInjective hχinj).trans (MulEquiv.subgroupCongr hχr)
    have hθ_apply : ∀ f, (θ f : adjointGroup .F4 K) = χ f := fun f => by
      rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
      exact MonoidHom.ofInjective_apply hχinj
    let Φ : WeylGroup .F4 →* MulAut (Multiplicative (Fin 4 → ZMod p)) :=
      (MulAut.congr θ.symm).toMonoidHom.comp (F4AutWeyl.weylTorusAut K p)
    have hχΦ : ∀ (w : WeylGroup .F4) (f : Multiplicative (Fin 4 → ZMod p)),
        χ (Φ w f) = F4AutWeyl.weylTorusAut K p w (θ f) := by
      intro w f
      rw [← hθ_apply (Φ w f)]
      change (θ ((MulAut.congr θ.symm (F4AutWeyl.weylTorusAut K p w)) f) :
          adjointGroup .F4 K) = ↑(F4AutWeyl.weylTorusAut K p w (θ f))
      rw [ggMulAut_congr_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
    have hΦinj : Function.Injective Φ :=
      (MulAut.congr θ.symm).injective.comp (F4AutWeyl.weylTorusAut_injective hp hp2 hpq)
    have hΦrange : Φ.range = ggTorusInduced χ := by
      apply le_antisymm
      · rintro _ ⟨w, rfl⟩
        refine mem_ggTorusInduced.mpr
          ⟨⟨canonicalRep (coxeterSystem .F4) K w,
              canonicalRep_mem_adjointGroup (coxeterSystem .F4) K w⟩, fun f => ?_⟩
        rw [hχΦ w f]
        refine Subtype.ext ?_
        rw [F4AutWeyl.coe_weylTorusAut_apply]
        rfl
      · intro u hu
        obtain ⟨g', hg'⟩ := mem_ggTorusInduced.mp hu
        have hg'N : g' ∈ Subgroup.normalizer
            (TableBF4.torusPow K p : Set (adjointGroup .F4 K)) := by
          refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
          · rw [← hχr] at hx ⊢
            obtain ⟨f, rfl⟩ := hx
            exact ⟨u f, (hg' f).symm⟩
          · rw [← hχr] at hx ⊢
            obtain ⟨f, hf⟩ := hx
            refine ⟨u.symm f, ?_⟩
            have h1 := hg' (u.symm f)
            rw [MulEquiv.apply_symm_apply u f] at h1
            exact mul_left_cancel (mul_right_cancel (h1.trans hf))
        obtain ⟨t, ht, w, hgt⟩ :=
          F4AutWeyl.exists_eq_mul_canonicalRep_of_mem_normalizer_torusPow hp hp2 hpq hg'N
        refine ⟨w, ?_⟩
        have hconj := F4AutWeyl.ggConjAut_eq_weylTorusAut hg'N ht hgt
        refine MulEquiv.ext fun f => hχinj ?_
        have hconjf : (F4AutWeyl.weylTorusAut K p w (θ f) : adjointGroup .F4 K) =
            g' * χ f * g'⁻¹ := by
          rw [← hconj, ggConjAut_apply, hθ_apply f]
        rw [hχΦ w f, hconjf, (hg' f).symm]
    let eW : WeylGroup .F4 ≃* ↥(ggTorusInduced χ) :=
      (MonoidHom.ofInjective hΦinj).trans (MulEquiv.subgroupCongr hΦrange)
    refine ⟨fun i : Fin Tag.F4.rank =>
      eW (ggF4Row_coxeterGroupEquiv (CoxeterMatrix.F₄.simple i)), ?_, ?_⟩
    · intro i
      let i' : Fin Tag.F4.rank := i
      change (eW (ggF4Row_coxeterGroupEquiv (CoxeterMatrix.F₄.simple i')) :
        MulAut (Multiplicative (Fin 4 → ZMod p))) ∈ NbrTableBExc.ggTorusInvolSet p χ
      rw [ggF4Row_coxeterGroupEquiv_simple i']
      change MulAut.congr θ.symm (F4AutWeyl.weylTorusAut K p (simple .F4 i')) ∈
        NbrTableBExc.ggTorusInvolSet p χ
      have hs : MulAut.congr θ.symm (F4AutWeyl.weylTorusAut K p (simple .F4 i')) ∈
          ggTorusInduced χ := by
        rw [← hΦrange]
        exact ⟨simple .F4 i', rfl⟩
      have hfix : Nat.card {f : Multiplicative (Fin 4 → ZMod p) //
          MulAut.congr θ.symm (F4AutWeyl.weylTorusAut K p (simple .F4 i')) f = f} =
          Nat.card {v : ↥(TableBF4.torusPow K p) //
            F4AutWeyl.weylTorusAut K p (simple .F4 i') v = v} := by
        refine Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun f => ?_)
        change MulAut.congr θ.symm (F4AutWeyl.weylTorusAut K p (simple .F4 i')) f = f ↔
          F4AutWeyl.weylTorusAut K p (simple .F4 i') (θ f) = θ f
        rw [ggMulAut_congr_apply]
        constructor
        · intro h
          have h1 := congrArg θ h
          rwa [MulEquiv.apply_symm_apply] at h1
        · intro h
          rw [MulEquiv.symm_symm, h, MulEquiv.symm_apply_apply]
      refine ⟨?_, ?_, mem_ggTorusInduced.mp hs⟩
      · rw [← map_pow, ← map_pow, (CFSG.LieType.Chevalley.coxeterSystem .F4).simple_sq i',
          map_one, map_one]
      · rw [hfix, (F4AutWeyl.isReflection_weylTorusAut_simple hp hp2 hpq i').2,
          TableBF4.card_torusPow hp hpq, CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod]
    · exact ⟨ggF4Row_coxeterGroupEquiv.trans eW, fun i => rfl⟩
  set τ₀ : Multiplicative (Fin 4 → ZMod p) →* adjointGroup .F4 K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp χ with hτ₀
  have hτ₀inj : Function.Injective τ₀ := (MulAut.conj g⁻¹).injective.comp hχinj
  have hτ₀range : τ₀.range = E := by
    rw [hτ₀, MonoidHom.range_comp, hχr,
      show TableBF4.torusPow K p = E.map (MulAut.conj g).toMonoidHom from hg.symm,
      Subgroup.map_map]
    have h2 : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (adjointGroup .F4 K) := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [h2, Subgroup.map_id]
  have hτ₀frame : GGTorusCoordFrame p τ₀ CoxeterMatrix.F₄ :=
    ggTorusCoordFrame_post (MulAut.conj g⁻¹) χ hbase
  obtain ⟨P, hP⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hτ hτ₀inj (hτE.trans hτ₀range.symm)
  have hτframe : GGTorusCoordFrame p τ CoxeterMatrix.F₄ := by
    have h1 := ggTorusCoordFrame_comp τ₀ P hτ₀frame
    rwa [hP] at h1
  exact hτframe

end CFSG.StandardType

end

