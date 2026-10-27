module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove

open CFSG.Quasithin Matrix

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def CentMove (Γ : Subgroup (GL ι K)) (e₀ : ι → K) : Prop :=
  ∀ u : ι → K, (∀ c : K, u ≠ c • e₀) →
    ∃ γ ∈ Γ, (γ : Matrix ι ι K) *ᵥ u = u ∧ ∀ c : K, (γ : Matrix ι ι K) *ᵥ e₀ ≠ c • e₀

theorem CentMove.mulVec {Γ : Subgroup (GL ι K)} {e₀ : ι → K} (h : CentMove Γ e₀) (x : ↥Γ) :
    CentMove Γ (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by
  intro u hu
  have hxx : ((x : GL ι K) : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    simp only [← Units.val_mul, ← Subgroup.coe_mul Γ x x⁻¹, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  have hx'x : ((x⁻¹ : GL ι K) : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K) = 1 := by
    simp only [← Units.val_mul, ← Subgroup.coe_mul Γ x⁻¹ x, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one]
  have hinj : ∀ {w₁ w₂ : ι → K}, ((x : GL ι K) : Matrix ι ι K) *ᵥ w₁ =
      ((x : GL ι K) : Matrix ι ι K) *ᵥ w₂ → w₁ = w₂ := by
    intro w₁ w₂ hw
    have h1 := congrArg (fun t => ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ t) hw
    simpa only [Matrix.mulVec_mulVec, hx'x, Matrix.one_mulVec] using h1
  have hne : ∀ c : K, ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u ≠ c • e₀ := by
    intro c hc
    apply hu c
    calc u = ((x : GL ι K) : Matrix ι ι K) *ᵥ
          (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) := by
          rw [Matrix.mulVec_mulVec, hxx, Matrix.one_mulVec]
      _ = ((x : GL ι K) : Matrix ι ι K) *ᵥ (c • e₀) := by rw [hc]
      _ = c • (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by rw [Matrix.mulVec_smul]
  obtain ⟨γ, hγ, hfix, hline⟩ := h _ hne
  let y : ↥Γ := x * ⟨γ, hγ⟩ * x⁻¹
  have hyeq : ((y : GL ι K) : Matrix ι ι K)
      = ((x : GL ι K) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K) *
        ((x⁻¹ : GL ι K) : Matrix ι ι K) := by
    simp only [y, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hinner : ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ
      (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) = e₀ := by
    rw [Matrix.mulVec_mulVec, hx'x, Matrix.one_mulVec]
  have hyx : ((y : GL ι K) : Matrix ι ι K) *ᵥ
      (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀)
      = ((x : GL ι K) : Matrix ι ι K) *ᵥ (((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by
    calc ((y : GL ι K) : Matrix ι ι K) *ᵥ
          (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀)
        = (((x : GL ι K) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K) *
            ((x⁻¹ : GL ι K) : Matrix ι ι K)) *ᵥ
              (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by rw [hyeq]
      _ = (((x : GL ι K) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K)) *ᵥ
            (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ
              (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀)) := by rw [← Matrix.mulVec_mulVec]
      _ = ((x : GL ι K) : Matrix ι ι K) *ᵥ
            (((γ : GL ι K) : Matrix ι ι K) *ᵥ
              (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ
                (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀))) := by
            rw [← Matrix.mulVec_mulVec]
      _ = ((x : GL ι K) : Matrix ι ι K) *ᵥ
            (((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by rw [hinner]
  refine ⟨(y : GL ι K), y.2, ?_, ?_⟩
  · calc ((y : GL ι K) : Matrix ι ι K) *ᵥ u
        = (((x : GL ι K) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K) *
            ((x⁻¹ : GL ι K) : Matrix ι ι K)) *ᵥ u := by rw [hyeq]
      _ = (((x : GL ι K) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K)) *ᵥ
            (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) := by rw [← Matrix.mulVec_mulVec]
      _ = ((x : GL ι K) : Matrix ι ι K) *ᵥ
            (((γ : GL ι K) : Matrix ι ι K) *ᵥ
              (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u)) := by rw [← Matrix.mulVec_mulVec]
      _ = ((x : GL ι K) : Matrix ι ι K) *ᵥ
            (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) := by rw [hfix]
      _ = (((x : GL ι K) : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K)) *ᵥ u := by
            rw [← Matrix.mulVec_mulVec]
      _ = u := by rw [hxx, Matrix.one_mulVec]
  · intro c hc
    apply hline c
    apply hinj
    calc ((x : GL ι K) : Matrix ι ι K) *ᵥ (((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀)
        = ((y : GL ι K) : Matrix ι ι K) *ᵥ
            (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) := hyx.symm
      _ = c • (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) := hc
      _ = ((x : GL ι K) : Matrix ι ι K) *ᵥ (c • e₀) := by rw [Matrix.mulVec_smul]

private theorem mem_fixV_iff_coord {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    {S : Subgroup (MulAut W)} {S' : Sylow 2 ↥H} (hSH : S ≤ H)
    (hS' : (S' : Subgroup ↥H) = S.subgroupOf H) {w₀ : ι → K}
    (hfix : ∀ v : ι → K,
      (∀ s ∈ (S' : Subgroup ↥H), ((((π.symm s : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀)
    (y : W) : y ∈ fixV S ↔ ∃ c : K, Multiplicative.toAdd (e y) = c • w₀ := by
  rw [mem_fixV]
  constructor
  · intro hy
    refine (hfix _).1 fun s hs => ?_
    have hmem : (s : MulAut W) ∈ S := by
      rw [hS'] at hs
      exact Subgroup.mem_subgroupOf.1 hs
    have h3 := he (π.symm s) y
    rw [MulEquiv.apply_symm_apply, hy (s : MulAut W) hmem] at h3
    exact h3.symm
  · rintro ⟨c, hc⟩ s hs
    apply e.injective
    apply Multiplicative.toAdd.injective
    have hmem : (⟨s, hSH hs⟩ : ↥H) ∈ (S' : Subgroup ↥H) := by
      rw [hS']
      exact Subgroup.mem_subgroupOf.2 hs
    have h3 := he (π.symm ⟨s, hSH hs⟩) y
    rw [MulEquiv.apply_symm_apply] at h3
    rw [h3, hc, Matrix.mulVec_smul,
      (hfix w₀).2 ⟨1, by simp⟩ ⟨s, hSH hs⟩ hmem]

theorem exists_fix_notMem_stabSub [Finite W] [Finite K] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (hmove : CentMove Γ e₀) {S : Subgroup (MulAut W)}
    (hS : IsSylowIn 2 S H) {v : W} (hv1 : v ≠ 1) (hvS : v ∉ fixV S) :
    ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, e, he⟩ := KTabC.exists_natEquiv hreal
  let S' : Sylow 2 ↥H := hS.toSylow
  have hS' : (S' : Subgroup ↥H) = S.subgroupOf H := IsSylowIn.coe_toSylow hS
  obtain ⟨x, hx⟩ := hline (S'.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective)
  let v₀ : ι → K := ((x : GL ι K) : Matrix ι ι K) *ᵥ e₀
  have hfix' : ∀ u : ι → K,
      (∀ s ∈ (S' : Subgroup ↥H), ((((π.symm s : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ u = u) ↔
        ∃ c : K, u = c • v₀ :=
    fun u => (KTabC.fixed_iff_fixed_sylowMap π S' u).trans (hx u)
  have hcoord : ∀ y : W, y ∈ fixV S ↔
      ∃ c : K, Multiplicative.toAdd (e y) = c • v₀ :=
    fun y => mem_fixV_iff_coord (S := S) (S' := S') (w₀ := v₀) π e he hS.le hS' hfix' y
  let u : ι → K := Multiplicative.toAdd (e v)
  have hu : ∀ c : K, u ≠ c • v₀ := by
    intro c hc
    exact hvS ((hcoord v).2 ⟨c, hc⟩)
  obtain ⟨γ, hγ, hγu, hγv⟩ := hmove.mulVec x u hu
  have hhv : ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) v = v := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [he ⟨γ, hγ⟩ v]
    simpa only [u] using hγu
  refine ⟨((π ⟨γ, hγ⟩ : ↥H) : MulAut W), (π ⟨γ, hγ⟩).2, hhv, ?_⟩
  intro hstab
  have hw₀ : e.symm (Multiplicative.ofAdd v₀) ∈ fixV S := by
    refine (hcoord _).2 ⟨1, ?_⟩
    simp
  have h6 : ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) (e.symm (Multiplicative.ofAdd v₀)) ∈ fixV S :=
    (mem_stabSub.1 hstab _).2 hw₀
  obtain ⟨c, hc⟩ := (hcoord _).1 h6
  have h4 := he ⟨γ, hγ⟩ (e.symm (Multiplicative.ofAdd v₀))
  have h5 : Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd v₀))) = v₀ := by simp
  rw [h5] at h4
  exact hγv c (h4.symm.trans hc)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove
