module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthNormIso
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsDefs

public section

open CFSG.ClassicalInvolution.PhanDn CFSG.LieType.Steinberg
open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

private lemma pmor_pow_val_neg {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) {ζ : M}
    (hζ : ζ ^ p = 1) (a : ZMod p) :
    ζ ^ ((-a).val) = (ζ ^ a.val)⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [ZMod.neg_val, if_neg ha]
    have hlt : a.val < p := ZMod.val_lt a
    have hsum : p - a.val + a.val = p := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    have h1 : ζ ^ (p - a.val) * ζ ^ a.val = 1 := by
      rw [← pow_add, hsum, hζ]
    exact eq_inv_of_mul_eq_one_left h1

private lemma pmor_sigma_eq_inv {K : Type*} [Field K] {σ : K ≃+* K} (u : normOne σ) :
    σ (((u : Kˣ) : K)) = (((u⁻¹ : normOne σ) : Kˣ) : K) := by
  have hu : σ (((u : Kˣ) : K)) * (((u : Kˣ) : K)) = 1 := (mem_normOne σ).1 u.2
  rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_left hu

theorem OrthFrameCore.exists_realize {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2)
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))} (hw : w ∈ omSigned p Φ.r) :
    ∃ μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
      ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f) := by
  classical
  obtain ⟨inst, E, χ, ζ, hζne, hζp, hχQ, hχτ⟩ := Φ.exists_normIso hF
  letI := inst
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let σ : GaloisField 2 2 ≃+* GaloisField 2 2 := unitaryInvolution (GaloisField 2 2) 2 1
  let D : (Fin Φ.r → Multiplicative (ZMod p)) →
      ((Fin Φ.r → GaloisField 2 2) ≃ₗ[Φ.F] (Fin Φ.r → GaloisField 2 2)) :=
    fun f => diagHom Φ.F σ Φ.r (fun i => ζ ^ (toAdd (f i)).val)
  have hχQ' : ∀ v : Φ.V, Φ.Q v = Qn E Φ.r (χ v) := fun v => (hχQ v).symm
  let H : Subgroup (MulAut (Fin Φ.r → Multiplicative (ZMod p))) :=
    { carrier := {w | ∃ M ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E Φ.r),
        ∀ f, M * D f * M⁻¹ = D (w f)}
      one_mem' := ⟨1, Subgroup.one_mem _, fun f => rfl⟩
      mul_mem' := by
        rintro w₁ w₂ ⟨M₁, hM₁, hc₁⟩ ⟨M₂, hM₂, hc₂⟩
        refine ⟨M₁ * M₂, Subgroup.mul_mem _ hM₁ hM₂, fun f => ?_⟩
        have h1 : M₁ * M₂ * D f * (M₁ * M₂)⁻¹ =
            M₁ * (M₂ * D f * M₂⁻¹) * M₁⁻¹ := by
          rw [mul_inv_rev]; group
        rw [h1, hc₂ f, hc₁ (w₂ f)]
        rfl
      inv_mem' := by
        rintro w ⟨M, hM, hc⟩
        refine ⟨M⁻¹, Subgroup.inv_mem _ hM, fun f => ?_⟩
        rw [inv_inv]
        have h2 : M * D (w⁻¹ f) * M⁻¹ = D f := by
          rw [hc (w⁻¹ f), MulAut.apply_inv_self]
        calc M⁻¹ * D f * M = M⁻¹ * (M * D (w⁻¹ f) * M⁻¹) * M := by rw [h2]
          _ = D (w⁻¹ f) := by group }
  have hgen : (Set.range (SpCoord.permAut (p := p) (k := Φ.r)) ∪
      Set.range (SpCoord.sgnAut (p := p) (k := Φ.r))) ⊆ H := by
    intro w hw
    rcases hw with ⟨s, rfl⟩ | ⟨i, rfl⟩
    ·
      have hPinv : (LinearEquiv.funCongrLeft Φ.F (GaloisField 2 2) s.symm)⁻¹ =
          LinearEquiv.funCongrLeft Φ.F (GaloisField 2 2) s := rfl
      have hP_conj : ∀ t : Fin Φ.r → normOne σ,
          LinearEquiv.funCongrLeft Φ.F (GaloisField 2 2) s.symm *
              diagHom Φ.F σ Φ.r t *
              (LinearEquiv.funCongrLeft Φ.F (GaloisField 2 2) s.symm)⁻¹ =
            diagHom Φ.F σ Φ.r (t ∘ s.symm) := by
        intro t
        apply LinearEquiv.ext
        intro x
        funext j
        rw [hPinv]
        simp only [LinearEquiv.mul_apply, LinearEquiv.funCongrLeft_apply,
          LinearMap.funLeft_apply, diagHom_apply, Function.comp_apply,
          Equiv.apply_symm_apply]
      refine ⟨LinearEquiv.funCongrLeft Φ.F (GaloisField 2 2) s.symm, ?_, ?_⟩
      · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro x
        rw [Qn_apply, Qn_apply]
        simpa only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply] using
          Equiv.sum_comp s.symm (fun i => normQuad E (x i))
      · intro f
        dsimp only [D]
        rw [SpCoord.permAut_apply]
        exact hP_conj (fun i => ζ ^ (toAdd (f i)).val)
    ·
      have hT_conj : ∀ t : Fin Φ.r → normOne σ,
          tauAt E i * diagHom Φ.F σ Φ.r t * (tauAt E i)⁻¹ =
            diagHom Φ.F σ Φ.r (Function.update t i (t i)⁻¹) := by
        intro t
        have hinv : (tauAt E i)⁻¹ = tauAt E i :=
          inv_eq_of_mul_eq_one_right (tauAt_mul_self E i)
        rw [hinv]
        apply LinearEquiv.ext
        intro x
        funext j
        by_cases hj : j = i
        · simp only [LinearEquiv.mul_apply, diagHom_apply, tauAt_apply, hj,
            Function.update_self, if_true, if_pos rfl, map_mul, E.isUnitary.invol,
            pmor_sigma_eq_inv]
        · simp only [LinearEquiv.mul_apply, diagHom_apply, tauAt_apply,
            Function.update_of_ne hj, if_false, if_neg hj]
      refine ⟨tauAt E i, tauAt_mem_orthogonalGroup E i, fun f => ?_⟩
      dsimp only [D]
      rw [SpCoord.sgnAut_apply]
      have hupd : (fun j => ζ ^ (toAdd ((Function.update f i (f i)⁻¹) j)).val) =
          Function.update (fun j => ζ ^ (toAdd (f j)).val) i
            ((fun j => ζ ^ (toAdd (f j)).val) i)⁻¹ := by
        funext j
        by_cases hj : j = i
        · rw [hj]
          rw [Function.update_self, Function.update_self, toAdd_inv,
            pmor_pow_val_neg (Fact.out : p.Prime) hζp (toAdd (f i))]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      rw [hupd]
      exact hT_conj (fun j => ζ ^ (toAdd (f j)).val)
  obtain ⟨M, hM, hMD⟩ := (Subgroup.closure_le H).mpr hgen hw
  let μ : Φ.V ≃ₗ[Φ.F] Φ.V := (LinearEquiv.autCongr χ).symm M
  have hμ : ∀ v : Φ.V, μ v = χ.symm (M (χ v)) := fun v =>
    LinearEquiv.autCongr_symm_apply_apply χ M v
  have hμinv : μ⁻¹ = (LinearEquiv.autCongr χ).symm M⁻¹ := by
    rw [show μ = (LinearEquiv.autCongr χ).symm M from rfl]
    exact (map_inv ((LinearEquiv.autCongr χ).symm) M).symm
  have hμinv_apply : ∀ v : Φ.V, μ⁻¹ v = χ.symm (M⁻¹ (χ v)) := fun v => by
    rw [hμinv]
    exact LinearEquiv.autCongr_symm_apply_apply χ M⁻¹ v
  have hχμ : ∀ u : Φ.V, χ (μ u) = M (χ u) := fun u => by
    rw [hμ, LinearEquiv.apply_symm_apply]
  have hχμinv : ∀ u : Φ.V, χ (μ⁻¹ u) = M⁻¹ (χ u) := fun u => by
    rw [hμinv_apply, LinearEquiv.apply_symm_apply]
  refine ⟨μ, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hμ, hχQ' (χ.symm (M (χ v))), LinearEquiv.apply_symm_apply, hχQ' v]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hM) (χ v)
  · intro f
    apply LinearEquiv.ext
    intro v
    apply χ.injective
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hχμ, hχτ f (μ⁻¹ v), hχμinv]
    change (M * D f * M⁻¹) (χ v) = χ (Φ.Δ.τ (w f) v)
    rw [hMD f]
    dsimp only [D]
    rw [hχτ (w f) v]

end OrthTorus

end CFSG.StandardType

end
