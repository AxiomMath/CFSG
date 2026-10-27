module

public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
public import CFSG.LocalAnalysis.StandardType.GGFinModelIndex
import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.LocalAnalysis.StandardType.GGLangRatStep

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LangRat

namespace GGDatumModel

theorem rootSL2_mem_model_of_corner
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t} (M : GGDatumModel t f p ht)
    (hc : GGCorner t p f) {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ)
    {ζ : GGLˣ} (hζ : ζ ^ 3 = 1) :
    rootSL2 (langTag t) GGL γ WSL ∈ M.D.model ∧
      rootSL2 (langTag t) GGL γ (HSL ζ⁻¹) ∈ M.D.model := by
  haveI : CharP GGL 2 := inferInstance
  have hconj : ∀ {τ : Tag} (w : WeylGroup τ) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
      (c : GGL), canonicalRep (coxeterSystem τ) GGL w * pinnedX τ GGL δ c *
        (canonicalRep (coxeterSystem τ) GGL w)⁻¹ = pinnedX τ GGL (w • δ) c := by
    intro τ w δ hδ c
    obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv GGL w hδ
    have hε1 : ε = 1 := by
      have h2 : (2 : GGL) = 0 := CharTwo.two_eq_zero
      have h : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
    rw [hεc, hε1, one_mul]
  have hpermlat : ∀ {τ : Tag} (x : Fin τ.rank → ℤ),
      permLattice (1 : Equiv.Perm (Fin τ.rank)) x = x := fun x => rfl
  have hpermlatCast : ∀ {τ : Tag} {R : ℕ} (h : R = τ.rank) (x : Fin τ.rank → ℤ),
      permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) x = x := by
    intro τ R h x
    have hone : (finCongr h).permCongr (1 : Equiv.Perm (Fin R)) =
        (1 : Equiv.Perm (Fin τ.rank)) := by
      ext j
      simp [Equiv.permCongr_apply]
    rw [hone]
    exact hpermlat x
  obtain ⟨hp3, hcase⟩ := hc
  subst hp3
  rcases hcase with ⟨htE6, hE6⟩ | ⟨htTw, hTw⟩
  ·
    subst htE6
    have hwE6 : ∀ u : Fin (langTag StatedLieTag.E6).rank → ℤ, M.w • u = u := by
      intro u
      have h := M.hw u
      rw [show ggGraphLat StatedLieTag.E6 = id from rfl,
        show eps 3 f = 1 from (eps_eq_one_iff 3 f).2 hE6,
        show piB StatedLieTag.E6 3 f = 1 from piB_E6_of_dvd f hE6] at h
      rw [hpermlatCast (rank_eq_langTag f ht) u] at h
      simpa using h
    have hstepE6 : ∀ (δ : Fin (langTag StatedLieTag.E6).rank → ℤ),
        IsRoot (langTag StatedLieTag.E6) δ → ∀ c : GGL,
        M.D.step (pinnedX (langTag StatedLieTag.E6) GGL δ c) =
          pinnedX (langTag StatedLieTag.E6) GGL δ (ggFrobT f c) := by
      intro δ hδ c
      have hΦ : M.D.Φ (pinnedX (langTag StatedLieTag.E6) GGL δ c) =
          pinnedX (langTag StatedLieTag.E6) GGL δ (c ^ 2 ^ f) := by
        rw [M.hΦ]
        exact ggPhi_pinnedX_untw (Or.inr (Or.inl rfl)) f hδ c
      have hs : M.D.step (pinnedX (langTag StatedLieTag.E6) GGL δ c) =
          M.D.n * M.D.Φ (pinnedX (langTag StatedLieTag.E6) GGL δ c) * M.D.n⁻¹ := by
        simp [LangDatum.step, MulAut.conj_apply]
      rw [hs, hΦ, M.hn, hconj M.w hδ, hwE6 δ, ggFrobT_apply]
    have e₁ : (WSL : SL2 GGL) = uSL 1 * vSL 1 * uSL 1 := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
    have hWSL : rootSL2 (langTag StatedLieTag.E6) GGL γ WSL ∈ M.D.model := by
      refine ⟨(exceptional_Lang_root_rank_one_data (langTag StatedLieTag.E6) GGL γ).2.2.2.2.1
        WSL, ?_⟩
      change M.D.step (rootSL2 (langTag StatedLieTag.E6) GGL γ WSL) =
        rootSL2 (langTag StatedLieTag.E6) GGL γ WSL
      rw [e₁]
      simp only [map_mul, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo (K := GGL) hγ,
        CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo (K := GGL) hγ,
        hstepE6 γ hγ 1, hstepE6 (-γ) (IsRoot.neg hγ) 1, map_one]
    have hstepHSL : ∀ t : GGLˣ,
        M.D.step (rootSL2 (langTag StatedLieTag.E6) GGL γ (HSL t)) =
          rootSL2 (langTag StatedLieTag.E6) GGL γ
            (HSL (Units.map (ggFrobT f).toMonoidHom t)) := by
      intro t
      rw [HSL_eq_uvu_two (L := GGL) t,
        HSL_eq_uvu_two (L := GGL) (Units.map (ggFrobT f).toMonoidHom t)]
      simp only [map_mul, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo (K := GGL) hγ,
        CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo (K := GGL) hγ,
        hstepE6 γ hγ, hstepE6 (-γ) (IsRoot.neg hγ), map_one, Units.coe_map,
        Units.coe_map_inv]
      rfl
    have hpowE6 : ζ ^ (2 ^ f) = ζ := by
      have hmod : 1 ≡ 2 ^ f [MOD 3] := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 hE6
      have h := pow_eq_pow_of_modEq hmod hζ
      simpa using h.symm
    have hFrζ : Units.map (ggFrobT f).toMonoidHom ζ = ζ := by
      ext
      rw [Units.coe_map]
      show ggFrobT f (↑ζ) = ↑ζ
      rw [ggFrobT_apply]
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hpowE6
    have hFrζinv : Units.map (ggFrobT f).toMonoidHom ζ⁻¹ = ζ⁻¹ := by
      rw [map_inv, hFrζ]
    have hHSL : rootSL2 (langTag StatedLieTag.E6) GGL γ (HSL ζ⁻¹) ∈ M.D.model := by
      refine ⟨(exceptional_Lang_root_rank_one_data (langTag StatedLieTag.E6) GGL γ).2.2.2.2.1
        (HSL ζ⁻¹), ?_⟩
      change M.D.step (rootSL2 (langTag StatedLieTag.E6) GGL γ (HSL ζ⁻¹)) =
        rootSL2 (langTag StatedLieTag.E6) GGL γ (HSL ζ⁻¹)
      rw [hstepHSL ζ⁻¹, hFrζinv]
    exact ⟨hWSL, hHSL⟩
  ·
    subst htTw
    have hwTw : ∀ u : Fin (langTag StatedLieTag.twistedE6).rank → ℤ,
        M.w • ggGraphLat StatedLieTag.twistedE6 u = -u := by
      intro u
      have h := M.hw u
      rw [show eps 3 f = -1 from
          (eps_eq_neg_one_iff Nat.prime_three (by norm_num) f (Or.inr hTw)).2 hTw,
        show piB StatedLieTag.twistedE6 3 f = 1 from piB_twistedE6_of_dvd f hTw] at h
      rw [hpermlatCast (rank_eq_langTag f ht) u] at h
      simpa using h
    have hstepTw : ∀ (δ : Fin (langTag StatedLieTag.twistedE6).rank → ℤ),
        IsRoot (langTag StatedLieTag.twistedE6) δ → ∀ c : GGL,
        M.D.step (pinnedX (langTag StatedLieTag.twistedE6) GGL δ c) =
          pinnedX (langTag StatedLieTag.twistedE6) GGL
            (M.w • ggGraphLat StatedLieTag.twistedE6 δ) (ggFrobT f c) := by
      intro δ hδ c
      have hδ' : IsRoot (langTag StatedLieTag.twistedE6)
          (permLattice (TwistTag.perm .E6) δ) :=
        hδ.permLattice (TwistTag.cartan_perm .E6)
      have hΦ : M.D.Φ (pinnedX (langTag StatedLieTag.twistedE6) GGL δ c) =
          pinnedX (langTag StatedLieTag.twistedE6) GGL
            (permLattice (TwistTag.perm .E6) δ) (c ^ 2 ^ f) := by
        rw [M.hΦ]
        exact ggPhi_pinnedX_twistedE6 f hδ c
      have hs : M.D.step (pinnedX (langTag StatedLieTag.twistedE6) GGL δ c) =
          M.D.n * M.D.Φ (pinnedX (langTag StatedLieTag.twistedE6) GGL δ c) * M.D.n⁻¹ := by
        simp [LangDatum.step, MulAut.conj_apply]
      rw [hs, hΦ, M.hn, hconj M.w hδ', ggFrobT_apply]
      rfl
    have h₁ : ∀ c : GGL,
        M.D.step (pinnedX (langTag StatedLieTag.twistedE6) GGL γ c) =
          pinnedX (langTag StatedLieTag.twistedE6) GGL (-γ) (ggFrobT f c) := by
      intro c
      rw [hstepTw γ hγ c, hwTw γ]
    have h₂ : ∀ c : GGL,
        M.D.step (pinnedX (langTag StatedLieTag.twistedE6) GGL (-γ) c) =
          pinnedX (langTag StatedLieTag.twistedE6) GGL γ (ggFrobT f c) := by
      intro c
      rw [hstepTw (-γ) (IsRoot.neg hγ) c, hwTw (-γ), neg_neg]
    have hpowTw : ζ ^ (2 ^ f) = ζ⁻¹ := by
      have h2le : 2 ≤ 2 ^ f := by
        have h3 : 3 ≤ 2 ^ f + 1 := Nat.le_of_dvd (Nat.succ_pos _) hTw
        omega
      have hdiv : 3 ∣ 2 ^ f - 2 := by
        obtain ⟨k, hk⟩ := hTw
        refine ⟨k - 1, ?_⟩
        omega
      have hmod : 2 ≡ 2 ^ f [MOD 3] := (Nat.modEq_iff_dvd' h2le).2 hdiv
      have hzeta2 : ζ ^ 2 = ζ⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        rw [← pow_succ]
        exact hζ
      have h := pow_eq_pow_of_modEq hmod hζ
      rw [hzeta2] at h
      exact h.symm
    have hFrζTw : Units.map (ggFrobT f).toMonoidHom ζ = ζ⁻¹ := by
      ext
      rw [Units.coe_map]
      show ggFrobT f (↑ζ) = ↑(ζ⁻¹)
      rw [ggFrobT_apply]
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hpowTw
    refine ⟨?_, ?_⟩
    · exact rootSL2_WSL_mem_model M.D hγ (by simpa using h₁ 1) (by simpa using h₂ 1)
    · refine rootSL2_HSL_mem_model_of_step M.D hγ h₁ h₂ ?_
      rw [map_inv, hFrζTw]

end GGDatumModel

end CFSG.StandardType.GGFinModel
