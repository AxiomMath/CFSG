module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalPolarDual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixCocycle
public import CFSG.Quasithin.Vol2.Ch10SecI1CovNat
public import CFSG.CGT.PushingUpLit.CGT6X.ExtSplit
public import CFSG.ClassicalGroups.Orthogonal.LineStabilizer
public import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.CGT6X
open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem pow_two_eq_one_of_commV_eq_top
    {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hWZ : ∀ w : W, w ^ 2 ∈ Z) : ∀ w : W, w ^ 2 = 1 := by
  have hle : commV H ≤ MonoidHom.ker (powMonoidHom 2 : W →* W) := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨h, hh, v, rfl⟩
    show (h v * v⁻¹) ^ 2 = 1
    calc (h v * v⁻¹) ^ 2 = (h v) ^ 2 * (v⁻¹) ^ 2 := by rw [mul_pow]
      _ = h (v ^ 2) * (v ^ 2)⁻¹ := by rw [map_pow, inv_pow]
      _ = v ^ 2 * (v ^ 2)⁻¹ := by
        rw [show h (v ^ 2) = v ^ 2 from (mem_fixV.mp (hZ (hWZ v))) h hh]
      _ = 1 := mul_inv_cancel _
  intro w
  have hw : w ∈ MonoidHom.ker (powMonoidHom 2 : W →* W) :=
    hle (by rw [hcomm]; exact Subgroup.mem_top w)
  simpa [powMonoidHom_apply] using MonoidHom.mem_ker.mp hw

theorem s16_nat_cover_of_dual_h1
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {Γ : Subgroup (GL ι K)} {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hR : (FFModel.nat Γ).Realizes H ⊤ Z)
    (hdual : ∀ c : ↥Γ → Dual (Multiplicative (ι → K)),
      IsCocycle (dualAct ((s16gNatHom ι K).comp Γ.subtype)) c →
        IsCoboundary (dualAct ((s16gNatHom ι K).comp Γ.subtype)) c) :
    Z = ⊥ := by
  classical
  obtain ⟨π, β, hπs, hβs, hβk, hβe⟩ :=
    CFSG.Quasithin.H13.VolI.topBot_data (D := FFModel.nat Γ) rfl rfl hR
  let τ : ↥Γ →* MulAut W := H.subtype.comp π
  let σ : ↥Γ →* MulAut (Multiplicative (ι → K)) :=
    (s16gNatHom ι K).comp Γ.subtype
  have hτ : ∀ γ : ↥Γ, τ γ = (π γ : MulAut W) := fun γ => rfl
  have hWZ : ∀ w : W, w ^ 2 ∈ Z := by
    intro w
    apply (hβk (w ^ 2)).1
    rw [map_pow]
    let n : Multiplicative (ι → K) := β w
    change n ^ 2 = 1
    exact CFSG.Quasithin.ASInputs.C10KH.sq_eq_one_of_charTwo (K := K) (A := ι → K) n
  have hE : ∀ w : W, w ^ 2 = 1 := pow_two_eq_one_of_commV_eq_top hZ hcomm hWZ
  have hExt : ExtData τ σ Z β := by
    refine ⟨?_, ?_, hβs, hβk, ?_⟩
    · intro γ z hz
      show τ γ z ∈ Z
      rw [hτ]
      have hfix : (π γ : MulAut W) z = z := (mem_fixV.mp (hZ hz)) (π γ) (π γ).2
      rw [hfix]
      exact hz
    · intro γ z hz
      show τ γ z = z
      rw [hτ]
      exact (mem_fixV.mp (hZ hz)) (π γ) (π γ).2
    · intro γ w
      have h := hβe γ w
      change β ((π γ : MulAut W) w) = (FFModel.nat Γ).act γ (β w)
      exact h
  obtain ⟨C, hCinv, hCcap, hCsup⟩ :=
    exists_inv_complement_bottom (σ := σ) hdual (Nat.card Z) W hE τ Z β hExt rfl
  have hCH : SInv H.subtype C := by
    intro h c hc
    obtain ⟨γ, hγ⟩ := hπs h
    have hh : H.subtype h = τ γ := by rw [← hγ]; rfl
    rw [hh]
    exact hCinv γ c hc
  have hcomm_le : commV H ≤ C := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨h, hh, w, rfl⟩
    have hw : w ∈ C ⊔ Z := by rw [hCsup]; exact Subgroup.mem_top w
    obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    have hcH : h c ∈ C := hCH ⟨h, hh⟩ c hc
    have hzfix : h z = z := (mem_fixV.mp (hZ hz)) h hh
    have heq : h (c * z) * (c * z)⁻¹ = h c * c⁻¹ := by
      calc h (c * z) * (c * z)⁻¹ = h c * (z * z⁻¹) * c⁻¹ := by
            rw [map_mul, hzfix, mul_inv_rev]
            ac_rfl
        _ = h c * c⁻¹ := by rw [mul_inv_cancel, mul_one]
    rw [heq]
    exact C.mul_mem hcH (C.inv_mem hc)
  have hCtop : C = ⊤ := eq_top_iff.mpr (by rwa [← hcomm])
  rw [hCtop, top_inf_eq] at hCcap
  exact hCcap

private theorem isCoboundary_natDual_omegaMinus_six
    {K : Type} [Field K] [Finite K] [CharP K 2] {b d : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (hH1 : ∀ c : ↥(StatedOmega (StatedQuadMinus 3 K b d)) →
        Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
      IsCocycle ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
        (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c →
        IsCoboundary ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
          (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c)
    {c : ↥(StatedOmega (StatedQuadMinus 3 K b d)) →
        Dual (Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K))}
    (hc : IsCocycle (dualAct ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
      (StatedOmega (StatedQuadMinus 3 K b d)).subtype)) c) :
    IsCoboundary (dualAct ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
      (StatedOmega (StatedQuadMinus 3 K b d)).subtype)) c := by
  classical
  let ι := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2
  let Q := StatedQuadMinus 3 K b d
  let Γ : Subgroup (GL ι K) := StatedOmega Q
  let B : LinearMap.BilinForm K (ι → K) := polarBilin (quadMinus 3 K b d)
  let σ : ↥Γ →* MulAut (Multiplicative (ι → K)) := (s16gNatHom ι K).comp Γ.subtype
  have hB : B.Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  have hBinv : ∀ (a : ↥Γ) (v w : ι → K),
      B (Multiplicative.toAdd (σ a (Multiplicative.ofAdd v)))
        (Multiplicative.toAdd (σ a (Multiplicative.ofAdd w))) = B v w := by
    intro a v w
    have hφ : ∀ x : ι → K,
        quadMinus 3 K b d (toLinEquiv ι K (a : GL ι K) x) = quadMinus 3 K b d x := by
      intro x
      have hx := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
        (Q₀ := StatedQuadMinus 3 K b d)
        (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore
          (StatedQuadMinus 3 K b d) a.2) x
      rw [toLinEquiv_apply]
      rw [← coe_quadMinus (n := 3) (K := K) (b := b) (c := d)] at hx
      exact hx
    have hp := polar_map_of_linearIsometry (Q := quadMinus 3 K b d)
      (Q' := quadMinus 3 K b d) (φ := toLinEquiv ι K (a : GL ι K)) hφ v w
    simpa [B, σ, s16gNatHom_apply, QuadraticMap.polarBilin_apply_apply] using hp
  obtain ⟨e, he⟩ := exists_equivariant_dual_of_invariant_polar
    (K := K) (V := ι → K) (A := ↥Γ) B hB σ hBinv
  exact isCoboundary_dual_of_equiv e he hH1 hc

private theorem s16_omega_minus_six_cover_aux
    {K : Type} [Field K] [Finite K] [CharP K 2] {b d : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hR : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes H ⊤ Z)
    (hH1 : ∀ c : ↥(StatedOmega (StatedQuadMinus 3 K b d)) →
        Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
      IsCocycle ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
        (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c →
      IsCoboundary ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
        (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c) :
    Z = ⊥ := by
  let ι := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2
  let Γ : Subgroup (GL ι K) := StatedOmega (StatedQuadMinus 3 K b d)
  have hR' : (FFModel.nat Γ).Realizes H ⊤ Z := hR
  have hdual : ∀ c : ↥Γ → Dual (Multiplicative (ι → K)),
      IsCocycle (dualAct ((s16gNatHom ι K).comp Γ.subtype)) c →
        IsCoboundary (dualAct ((s16gNatHom ι K).comp Γ.subtype)) c := by
    intro c hc
    exact isCoboundary_natDual_omegaMinus_six (K := K) (b := b) (d := d) hirr hH1 hc
  exact s16_nat_cover_of_dual_h1 hZ hcomm hR' hdual

theorem s16_omega_minus_six_cover
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 2 < Nat.card K) {b d : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hR : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes H ⊤ Z) :
    Z = ⊥ := by
  refine s16_omega_minus_six_cover_aux hirr hZ hcomm hR ?_
  intro c hc
  exact isCoboundary_nat_omegaMinus_six (K := K) (b := b) (d := d) hK hirr c hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

