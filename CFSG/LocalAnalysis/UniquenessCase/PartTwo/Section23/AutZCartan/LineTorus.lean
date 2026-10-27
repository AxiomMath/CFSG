module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Quasithin Matrix

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def LineTorus (Γ : Subgroup (GL ι K)) (e₀ : ι → K) : Prop :=
  ∀ c : Kˣ, ∃ γ ∈ Γ, ((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀ = (c : K) • e₀

private lemma pow_mulVec_eq_smul_of_mulVec_eq {Γ : Subgroup (GL ι K)} {δ : ↥Γ} {c : Kˣ}
    {w₀ : ι → K} (h : ((δ : GL ι K) : Matrix ι ι K) *ᵥ w₀ = (c : K) • w₀) (n : ℕ) :
    (((δ ^ n : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ w₀ = (((c ^ n : Kˣ) : K)) • w₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, Subgroup.coe_mul, Units.val_mul]
      rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
        mul_comm (c : K) (((c ^ n : Kˣ) : K))]

private lemma exists_coord_eq_smul_of_forall_fixed {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (S : Sylow 2 ↥H) {w₀ : ι → K}
    (hS : ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀)
    {y : W} (hy : ∀ s ∈ (S : Subgroup ↥H), ((s : ↥H) : MulAut W) y = y) :
    ∃ a : K, Multiplicative.toAdd (e y) = a • w₀ ∧ (y ≠ 1 → a ≠ 0) := by
  have hcoord : ∃ a : K, Multiplicative.toAdd (e y) = a • w₀ := by
    refine (hS (Multiplicative.toAdd (e y))).1 ?_
    intro s hs
    have h := he (π.symm s) y
    rw [MulEquiv.apply_symm_apply, hy s hs] at h
    exact h.symm
  obtain ⟨a, ha⟩ := hcoord
  refine ⟨a, ha, ?_⟩
  intro hy1 h0
  apply hy1
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [ha, h0, zero_smul]
  simp

theorem exists_zpowers_transitive_of_lineTorus [Finite W] [Finite K] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (htor : LineTorus Γ e₀) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  classical
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  obtain ⟨π, e, he⟩ := KTabC.exists_natEquiv hreal
  obtain ⟨x, hx⟩ := hline (S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective)
  set w₀ : ι → K := ((x : GL ι K) : Matrix ι ι K) *ᵥ e₀ with hw₀
  have hS : ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀ :=
    fun v => (KTabC.fixed_iff_fixed_sylowMap π S v).trans (hx v)
  have hpoint : KTabD.pointStab H S = (KTabD.lineStab Γ w₀).map π.toMonoidHom :=
    KTabD.pointStab_eq_map_lineStab π e he S hS
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨γ, hγΓ, hγ⟩ := htor c₀
  let γ' : ↥Γ := ⟨γ, hγΓ⟩
  set δ : ↥Γ := x * γ' * x⁻¹ with hδdef
  set X : Matrix ι ι K := (((x : ↥Γ) : GL ι K) : Matrix ι ι K) with hX
  set G : Matrix ι ι K := (((γ' : GL ι K)) : Matrix ι ι K) with hG
  set X' : Matrix ι ι K := (((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) with hX'
  have hγ' : G *ᵥ e₀ = (c₀ : K) • e₀ := by
    rw [hG]
    exact hγ
  have hxinv : X' * X = 1 := by
    rw [hX', hX, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    rfl
  have hδcoe : ((δ : GL ι K) : Matrix ι ι K) = X * G * X' := by
    rw [hδdef, hX, hG, hX', Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
      Units.val_mul]
  have hδ : ((δ : GL ι K) : Matrix ι ι K) *ᵥ w₀ = (c₀ : K) • w₀ := by
    rw [hδcoe, hw₀]
    calc (X * G * X') *ᵥ (X *ᵥ e₀)
        = ((X * G * X') * X) *ᵥ e₀ := by rw [Matrix.mulVec_mulVec]
      _ = ((X * G) * (X' * X)) *ᵥ e₀ := by rw [mul_assoc]
      _ = ((X * G) * 1) *ᵥ e₀ := by rw [hxinv]
      _ = (X * G) *ᵥ e₀ := by rw [mul_one]
      _ = X *ᵥ (G *ᵥ e₀) := by rw [Matrix.mulVec_mulVec]
      _ = X *ᵥ ((c₀ : K) • e₀) := by rw [hγ']
      _ = (c₀ : K) • (X *ᵥ e₀) := by rw [Matrix.mulVec_smul]
  have hδmem : δ ∈ KTabD.lineStab Γ w₀ := KTabD.mem_lineStab.2 ⟨c₀, hδ⟩
  refine ⟨π δ, ?_, ?_⟩
  · rw [hpoint]
    exact Subgroup.mem_map_of_mem π.toMonoidHom hδmem
  · intro v hv w hw hv1 hw1
    have hvS : ∀ s ∈ (S : Subgroup ↥H), ((s : ↥H) : MulAut W) v = v := by
      intro s hs
      have h := hv
      rw [FixedPoints.mem_subgroup] at h
      exact h ⟨s, hs⟩
    have hwS : ∀ s ∈ (S : Subgroup ↥H), ((s : ↥H) : MulAut W) w = w := by
      intro s hs
      have h := hw
      rw [FixedPoints.mem_subgroup] at h
      exact h ⟨s, hs⟩
    obtain ⟨a, ha, ha0⟩ := exists_coord_eq_smul_of_forall_fixed π e he S hS hvS
    obtain ⟨b, hb, hb0⟩ := exists_coord_eq_smul_of_forall_fixed π e he S hS hwS
    set u : Kˣ := Units.mk0 b (hb0 hw1) / Units.mk0 a (ha0 hv1) with hu
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff u c₀).mp
      (mem_powers_iff_mem_zpowers.mpr (hc₀ u))
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply e.injective
    apply Multiplicative.toAdd.injective
    have hstep : Multiplicative.toAdd (e ((((π δ) ^ n : ↥H) : MulAut W) v))
        = (((δ ^ n : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e v) := by
      rw [← map_pow]
      exact he (δ ^ n) v
    have hval : a * (((c₀ ^ n : Kˣ) : K)) = b := by
      rw [hn, hu, Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0]
      rw [mul_comm a (b / a)]
      exact div_mul_cancel₀ b (ha0 hv1)
    rw [hstep, ha, Matrix.mulVec_smul, pow_mulVec_eq_smul_of_mulVec_eq hδ n, smul_smul,
      hval, ← hb]

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
