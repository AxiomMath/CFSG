module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameTau

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G]

private lemma qtwoDOrthBase_tau_perm_sign_zero {n : ℕ}
    {w : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3)
    (hact : ∀ i, w (dBasis (n + 1) i) = c i • dBasis (n + 1) (σ i))
    (hfix : w (dBasis (n + 1) 0) = dBasis (n + 1) 0) : σ 0 = 0 ∧ c 0 = 1 := by
  have hσ0 : σ 0 = 0 := by
    by_contra hσ
    have h := congrFun (hact 0) 0
    rw [hfix] at h
    simp only [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_apply] at h
    rw [if_neg (fun hh : (0 : Fin (n + 1)) = σ 0 => hσ hh.symm), smul_zero] at h
    exact absurd h (by decide)
  have hc0 : c 0 = 1 := by
    have h := congrFun (hact 0) 0
    rw [hfix, hσ0] at h
    simp only [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_eq_same, mul_one] at h
    simpa using h.symm
  exact ⟨hσ0, hc0⟩

theorem ggAutomizer_map_ggLin_tauIota {Bs X : Subgroup G} {n : ℕ}
    {τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs}
    (hmod : HdRo7D.DCoordModel 3 Bs X n τ) :
    (ggAutomizer X Bs).map (ggLin (p := 3) (tauIota τ)) =
      dEvenStab (n + 1) (dBasis (n + 1) 0) := by
  ext w
  constructor
  · intro hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨σ, c, hσ, hc0, hc, hprod, hform⟩ := (hmod a).mp ha
    have hact : ∀ i, ggLin (p := 3) (tauIota τ) a (dBasis (n + 1) i) =
        c i • dBasis (n + 1) (σ i) :=
      (ggLin_tauIota_basis_iff τ a σ c).mp hform
    exact ⟨⟨σ, c, hc, hprod, hact⟩, by rw [hact 0, hσ, hc0, one_smul]⟩
  · intro hw
    obtain ⟨⟨σ, c, hc, hprod, hact⟩, hfix⟩ := hw
    obtain ⟨hσ, hc0⟩ := qtwoDOrthBase_tau_perm_sign_zero σ c hact hfix
    refine Subgroup.mem_map.mpr ⟨ggLinInv (p := 3) (tauIota τ) w, ?_, ?_⟩
    · exact ggLinInv_mem_automizer_d (τ := τ) (X := X) hmod σ c hσ hc0 hc hprod hact
    · exact ggLin_ggLinInv (p := 3) (tauIota τ) w

theorem qtwoDOrthBase_weylD_of_model {Bs X : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    {τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs}
    (hmod : HdRo7D.DCoordModel 3 Bs X n τ) :
    GGWeylOfType 3 (ggCoxeterMatrixD n) (ggAutomizer X Bs) := by
  classical
  obtain ⟨e₁, he₁⟩ := dEven_equiv hn
  have hmap := ggAutomizer_map_ggLin_tauIota hmod
  let e₃ : ↥(ggAutomizer X Bs) ≃* ↥(dEvenStab (n + 1) (dBasis (n + 1) 0)) :=
    (Subgroup.equivMapOfInjective (ggAutomizer X Bs) (ggLin (p := 3) (tauIota τ))
      (ggLin_injective (p := 3) (tauIota τ))).trans (MulEquiv.subgroupCongr hmap)
  have he₃ : ∀ a : ↥(ggAutomizer X Bs),
      ((e₃ a : ↥(dEvenStab (n + 1) (dBasis (n + 1) 0))) :
        DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) =
        ggLin (p := 3) (tauIota τ) (a : MulAut ↥Bs) := by
    intro a
    rw [show ((e₃ a : ↥(dEvenStab (n + 1) (dBasis (n + 1) 0))) :
        DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) =
        (Subgroup.equivMapOfInjective (ggAutomizer X Bs) (ggLin (p := 3) (tauIota τ))
          (ggLin_injective (p := 3) (tauIota τ)) a :
            DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) from rfl]
    rw [Subgroup.coe_equivMapOfInjective_apply]
  let Φ : (ggCoxeterMatrixD n).Group ≃* ↥(ggAutomizer X Bs) :=
    (e₁.trans (dLiftEquiv n)).trans e₃.symm
  refine ⟨Φ, fun t => ?_⟩
  have hΦt : Φ ((ggCoxeterMatrixD n).simple t) =
      e₃.symm (dLiftEquiv n (e₁ ((ggCoxeterMatrixD n).simple t))) := rfl
  rw [hΦt]
  let ε := decide (t.val + 1 = n)
  let lo := OrthTorus.simpleLo t
  let hi := OrthTorus.simpleHi t
  let w₀ : ↥(dEvenStab (n + 1) (dBasis (n + 1) 0)) :=
    dLiftEquiv n (e₁ ((ggCoxeterMatrixD n).simple t))
  change GGIsReflection 3 (((e₃.symm w₀ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
  have hw : (w₀ : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) =
      dTau (n + 1) ε lo.succ hi.succ := by
    change (dLiftEquiv n (e₁ ((ggCoxeterMatrixD n).simple t)) :
      DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) = dTau (n + 1) ε lo.succ hi.succ
    rw [dLiftEquiv_apply, he₁ t]
    exact dLift_dTau n ε (OrthTorus.simpleLo_ne_simpleHi (by omega) t)
  have hlin : ggLin (p := 3) (tauIota τ)
      (((e₃.symm w₀ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) =
      dTau (n + 1) ε lo.succ hi.succ := by
    have h := he₃ (e₃.symm w₀)
    rw [MulEquiv.apply_symm_apply, hw] at h
    exact h.symm
  have hfin : ((e₃.symm w₀ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) ε lo.succ hi.succ) :=
    ((ggLinInv_eq_iff (p := 3) (tauIota τ) (dTau (n + 1) ε lo.succ hi.succ) _).mpr hlin).symm
  rw [hfin]
  exact ggIsReflection_ggLinInv_dTau τ ε (a := lo.succ) (b := hi.succ)
    ((Fin.succ_injective n).ne (OrthTorus.simpleLo_ne_simpleHi (by omega : 2 ≤ n) t))

end CFSG.StandardType.QTwo

end
