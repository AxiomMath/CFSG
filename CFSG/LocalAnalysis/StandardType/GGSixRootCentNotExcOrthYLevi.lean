module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootOmega
public import CFSG.LocalAnalysis.StandardType.GGTwoPlaneThree
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualEichler
public import CFSG.Quasithin.Background.GoldschmidtS146PPerf
public import CFSG.LargeExtraspecial.S5Gen2
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

theorem ggTwoPlaneThree_eichler_mul_eichler {K V : Type} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {P₁ P₂ : CFSG.ClassicalGroups.Orthogonal.HypPair Q}
    (h₁₂ : P₁.Orth P₂) :
    GGTwoPlaneThree Q
      (CFSG.ClassicalGroups.Orthogonal.eichler Q P₁.e P₂.f *
        CFSG.ClassicalGroups.Orthogonal.eichler Q P₂.e P₁.f)
      (P₁.e + P₁.f) (P₁.e + P₂.e + P₁.f) := by
  set y : V ≃ₗ[K] V := eichler Q P₁.e P₂.f * eichler Q P₂.e P₁.f with hydef
  have hfe : polar Q P₂.f P₁.e = 0 := by rw [polar_comm]; exact h₁₂.ef
  have hee : polar Q P₂.e P₁.e = 0 := by rw [polar_comm]; exact h₁₂.ee
  have hff : polar Q P₂.f P₁.f = 0 := by rw [polar_comm]; exact h₁₂.ff
  have hcb : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
  have had : polar Q P₁.e P₂.f = 0 := h₁₂.ef
  have hk2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hvv : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v]
    change (2 : K) • v = 0
    rw [hk2, zero_smul]
  have hE2 : ∀ x, eichler Q P₂.e P₁.f x =
      x + polar Q x P₂.e • P₁.f + polar Q x P₁.f • P₂.e := fun x =>
    res_eichler_apply P₂.Q_e P₁.Q_f hcb x
  have hE1 : ∀ x, eichler Q P₁.e P₂.f x =
      x + polar Q x P₁.e • P₂.f + polar Q x P₂.f • P₁.e := fun x =>
    res_eichler_apply P₁.Q_e P₂.Q_f had x
  have hya : y P₁.e = P₂.e := by
    rw [hydef, LinearEquiv.mul_apply, hE2, hE1]
    simp only [polar_add_left, polar_smul_left, polar_add_right, polar_smul_right,
      P₁.polar_ee, P₁.polar_ef, P₁.polar_fe, P₁.polar_ff, P₂.polar_ee, P₂.polar_ef,
      P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had,
      smul_eq_mul, mul_one, mul_zero, zero_mul]
    simp only [zero_smul, one_smul, add_zero, zero_add]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  have hyb : y P₁.f = P₁.f + P₂.f := by
    rw [hydef, LinearEquiv.mul_apply, hE2, hE1]
    simp only [polar_add_left, polar_smul_left, polar_add_right, polar_smul_right,
      P₁.polar_ee, P₁.polar_ef, P₁.polar_fe, P₁.polar_ff, P₂.polar_ee, P₂.polar_ef,
      P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had,
      smul_eq_mul, mul_one, mul_zero, zero_mul]
    simp only [zero_smul, one_smul, add_zero, zero_add]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  have hyc : y P₂.e = P₁.e + P₂.e := by
    rw [hydef, LinearEquiv.mul_apply, hE2, hE1]
    simp only [polar_add_left, polar_smul_left, polar_add_right, polar_smul_right,
      P₁.polar_ee, P₁.polar_ef, P₁.polar_fe, P₁.polar_ff, P₂.polar_ee, P₂.polar_ef,
      P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had,
      smul_eq_mul, mul_one, mul_zero, zero_mul]
    simp only [zero_smul, one_smul, add_zero, zero_add]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  have hyd : y P₂.f = P₁.f := by
    rw [hydef, LinearEquiv.mul_apply, hE2, hE1]
    simp only [polar_add_left, polar_smul_left, polar_add_right, polar_smul_right,
      P₁.polar_ee, P₁.polar_ef, P₁.polar_fe, P₁.polar_ff, P₂.polar_ee, P₂.polar_ef,
      P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had,
      smul_eq_mul, mul_one, mul_zero, zero_mul]
    simp only [zero_smul, one_smul, add_zero, zero_add]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  set v₁ : V := P₁.e + P₁.f with hv1def
  set v₂ : V := P₁.e + P₂.e + P₁.f with hv2def
  have hyv₁ : y v₁ = P₁.f + P₂.e + P₂.f := by
    rw [hv1def, map_add y, hya, hyb]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  have hyv₂ : y v₂ = P₁.e + P₁.f + P₂.f := by
    rw [hv2def, map_add y, map_add y, hya, hyc, hyb]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  have hQv₁ : Q v₁ = 1 := by
    rw [hv1def, QuadraticMap.map_add Q, P₁.Q_e, P₁.Q_f, P₁.polar_ef]
    norm_num
  have hQv₂ : Q v₂ = 1 := by
    rw [hv2def, QuadraticMap.map_add Q, QuadraticMap.map_add Q, P₁.Q_e, P₂.Q_e, P₁.Q_f]
    simp only [polar_add_left, P₁.polar_ee, P₁.polar_ef, h₁₂.ee, h₁₂.fe, hcb]
    norm_num
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hydef]
    exact mul_mem (eichler_mem_orthogonalGroup Q _ _) (eichler_mem_orthogonalGroup Q _ _)
  have hQyv₁ : Q (y v₁) = 1 := by rw [map_of_mem hyO, hQv₁]
  have hQyv₂ : Q (y v₂) = 1 := by rw [map_of_mem hyO, hQv₂]
  have hB11 : polar Q v₁ (y v₁) = 1 := by
    rw [hv1def, hyv₁]
    simp only [polar_add_left, polar_add_right, P₁.polar_ee, P₁.polar_ef, P₁.polar_fe,
      P₁.polar_ff, P₂.polar_ee, P₂.polar_ef, P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef,
      h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had, smul_eq_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]
    try norm_num
    try linear_combination hk2
  have hB22 : polar Q v₂ (y v₂) = 1 := by
    rw [hv2def, hyv₂]
    simp only [polar_add_left, polar_add_right, P₁.polar_ee, P₁.polar_ef, P₁.polar_fe,
      P₁.polar_ff, P₂.polar_ee, P₂.polar_ef, P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef,
      h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had, smul_eq_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]
    try norm_num
    try linear_combination hk2
  have hB12 : polar Q v₁ v₂ = 0 := by
    rw [hv1def, hv2def]
    simp only [polar_add_left, polar_add_right, P₁.polar_ee, P₁.polar_ef, P₁.polar_fe,
      P₁.polar_ff, P₂.polar_ee, P₂.polar_ef, P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef,
      h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had, smul_eq_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]
    try norm_num
    try linear_combination hk2
  have hB1y2 : polar Q v₁ (y v₂) = 0 := by
    rw [hv1def, hyv₂]
    simp only [polar_add_left, polar_add_right, P₁.polar_ee, P₁.polar_ef, P₁.polar_fe,
      P₁.polar_ff, P₂.polar_ee, P₂.polar_ef, P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef,
      h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had, smul_eq_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]
    try norm_num
    try linear_combination hk2
  have hBy12 : polar Q (y v₁) v₂ = 0 := by
    rw [hyv₁, hv2def]
    simp only [polar_add_left, polar_add_right, P₁.polar_ee, P₁.polar_ef, P₁.polar_fe,
      P₁.polar_ff, P₂.polar_ee, P₂.polar_ef, P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef,
      h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had, smul_eq_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]
    try norm_num
    try linear_combination hk2
  have hBy1y2 : polar Q (y v₁) (y v₂) = 0 := by
    rw [hyv₁, hyv₂]
    simp only [polar_add_left, polar_add_right, P₁.polar_ee, P₁.polar_ef, P₁.polar_fe,
      P₁.polar_ff, P₂.polar_ee, P₂.polar_ef, P₂.polar_fe, P₂.polar_ff, h₁₂.ee, h₁₂.ef,
      h₁₂.fe, h₁₂.ff, hee, hfe, hff, hcb, had, smul_eq_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]
    try norm_num
    try linear_combination hk2
  have hsq1 : y (y v₁) = y v₁ + v₁ := by
    rw [hyv₁, hv1def, map_add y, map_add y, hyb, hyc, hyd]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  have hsq2 : y (y v₂) = y v₂ + v₂ := by
    rw [hyv₂, hv2def, map_add y, map_add y, hya, hyb, hyd]
    try abel_nf
    try simp only [two_zsmul, hvv, zero_add, add_zero]
  refine ⟨hQv₁, hQyv₁, hQv₂, hQyv₂, hB11, hB22, hB12, hB1y2, hBy12, hBy1y2, hsq1,
    hsq2, ?_⟩
  intro w h1 h2 h3 h4
  have h1' : polar Q w v₁ = 0 := by rw [polar_comm]; exact h1
  have h2' : polar Q w (y v₁) = 0 := by rw [polar_comm]; exact h2
  have h3' : polar Q w v₂ = 0 := by rw [polar_comm]; exact h3
  have h4' : polar Q w (y v₂) = 0 := by rw [polar_comm]; exact h4
  have H1 : polar Q w P₁.e + polar Q w P₁.f = 0 := by
    rw [hv1def, polar_add_right] at h1'
    exact h1'
  have H2 : polar Q w P₁.f + polar Q w P₂.e + polar Q w P₂.f = 0 := by
    rw [hyv₁, polar_add_right, polar_add_right] at h2'
    exact h2'
  have H3 : polar Q w P₁.e + polar Q w P₂.e + polar Q w P₁.f = 0 := by
    rw [hv2def, polar_add_right, polar_add_right] at h3'
    exact h3'
  have H4 : polar Q w P₁.e + polar Q w P₁.f + polar Q w P₂.f = 0 := by
    rw [hyv₂, polar_add_right, polar_add_right] at h4'
    exact h4'
  have hA : polar Q w P₁.e = 0 := by linear_combination -H1 - H2 + H3 + H4
  have hB : polar Q w P₁.f = 0 := by linear_combination H1 - hA
  have hC : polar Q w P₂.e = 0 := by linear_combination H3 - H1
  have hD : polar Q w P₂.f = 0 := by linear_combination H4 - H1
  have hE2w : eichler Q P₂.e P₁.f w = w := eichler_apply_of_polar_eq_zero hC hB
  have hE1w : eichler Q P₁.e P₂.f w = w := eichler_apply_of_polar_eq_zero hA hD
  rw [hydef, LinearEquiv.mul_apply, hE2w, hE1w]


theorem GGTwoPlaneThree.orderOf_eq_three {K V : Type} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {y : V ≃ₗ[K] V} {v₁ v₂ : V}
    (h : GGTwoPlaneThree Q y v₁ v₂) : orderOf y = 3 := by
  have hk2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hadd : ∀ w : V, w + w = 0 := fun w => by
    rw [← two_smul K w]
    change (2 : K) • w = 0
    rw [hk2, zero_smul]
  have hself1 : polar Q v₁ v₁ = 0 := by
    rw [polar_self_eq_two_mul, h.Q_v₁, hk2, zero_mul]
  have hselfy1 : polar Q (y v₁) (y v₁) = 0 := by
    rw [polar_self_eq_two_mul, h.Q_yv₁, hk2, zero_mul]
  have hself2 : polar Q v₂ v₂ = 0 := by
    rw [polar_self_eq_two_mul, h.Q_v₂, hk2, zero_mul]
  have hselfy2 : polar Q (y v₂) (y v₂) = 0 := by
    rw [polar_self_eq_two_mul, h.Q_yv₂, hk2, zero_mul]
  have hP11 : polar Q v₁ v₁ = 0 := hself1
  have hPy11 : polar Q (y v₁) v₁ = 1 := by rw [polar_comm]; exact h.polar_v₁_yv₁
  have hP1y1 : polar Q v₁ (y v₁) = 1 := h.polar_v₁_yv₁
  have hPy1y1 : polar Q (y v₁) (y v₁) = 0 := hselfy1
  have hP12 : polar Q v₁ v₂ = 0 := h.polar_v₁_v₂
  have hP21 : polar Q v₂ v₁ = 0 := by rw [polar_comm]; exact h.polar_v₁_v₂
  have hP1y2 : polar Q v₁ (y v₂) = 0 := h.polar_v₁_yv₂
  have hPy21 : polar Q (y v₂) v₁ = 0 := by rw [polar_comm]; exact h.polar_v₁_yv₂
  have hPy12 : polar Q (y v₁) v₂ = 0 := h.polar_yv₁_v₂
  have hP2y1 : polar Q v₂ (y v₁) = 0 := by rw [polar_comm]; exact h.polar_yv₁_v₂
  have hPy1y2 : polar Q (y v₁) (y v₂) = 0 := h.polar_yv₁_yv₂
  have hPy2y1 : polar Q (y v₂) (y v₁) = 0 := by rw [polar_comm]; exact h.polar_yv₁_yv₂
  have hP22 : polar Q v₂ v₂ = 0 := hself2
  have hPy22 : polar Q (y v₂) v₂ = 1 := by rw [polar_comm]; exact h.polar_v₂_yv₂
  have hP2y2 : polar Q v₂ (y v₂) = 1 := h.polar_v₂_yv₂
  have hPy2y2 : polar Q (y v₂) (y v₂) = 0 := hselfy2
  have hpow : y ^ 3 = y * y * y := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  have hne : y ≠ 1 := by
    intro hy
    have hs := h.sq_v₁
    rw [hy] at hs
    simp only [LinearEquiv.coe_one, id] at hs
    rw [hadd v₁] at hs
    have h0 : v₁ = 0 := hs
    have hp := h.polar_v₁_yv₁
    rw [h0, hy] at hp
    simp only [LinearEquiv.coe_one, id, map_zero, polar_zero_left] at hp
    exact zero_ne_one hp
  have hy3_v₁ : (y ^ 3) v₁ = v₁ := by
    rw [hpow]
    simp only [LinearEquiv.mul_apply]
    rw [h.sq_v₁, map_add, h.sq_v₁]
    abel_nf
    simp only [two_zsmul, hadd, zero_add]
  have hy3_yv₁ : (y ^ 3) (y v₁) = y v₁ := by
    rw [hpow]
    simp only [LinearEquiv.mul_apply]
    rw [h.sq_v₁, map_add, h.sq_v₁]
    abel_nf
    simp only [two_zsmul, hadd, zero_add]
  have hy3_v₂ : (y ^ 3) v₂ = v₂ := by
    rw [hpow]
    simp only [LinearEquiv.mul_apply]
    rw [h.sq_v₂, map_add, h.sq_v₂]
    abel_nf
    simp only [two_zsmul, hadd, zero_add]
  have hy3_yv₂ : (y ^ 3) (y v₂) = y v₂ := by
    rw [hpow]
    simp only [LinearEquiv.mul_apply]
    rw [h.sq_v₂, map_add, h.sq_v₂]
    abel_nf
    simp only [two_zsmul, hadd, zero_add]
  have h3 : y ^ 3 = 1 := by
    apply LinearEquiv.ext
    intro v
    set s : V := polar Q v (y v₁) • v₁ + polar Q v v₁ • y v₁ +
      polar Q v (y v₂) • v₂ + polar Q v v₂ • y v₂ with hsdef
    set w : V := v - s with hwdef
    have hs1 : polar Q v₁ s = polar Q v v₁ := by
      rw [hsdef]
      simp only [polar_add_right, polar_smul_right_eq, hP11, hPy11, hP1y1, hPy1y1, hP12,
        hP21, hP1y2, hPy21, hPy12, hP2y1, hPy1y2, hPy2y1, hP22, hPy22, hP2y2, hPy2y2,
        mul_one, mul_zero, add_zero, zero_add]
    have hsy1 : polar Q (y v₁) s = polar Q v (y v₁) := by
      rw [hsdef]
      simp only [polar_add_right, polar_smul_right_eq, hP11, hPy11, hP1y1, hPy1y1, hP12,
        hP21, hP1y2, hPy21, hPy12, hP2y1, hPy1y2, hPy2y1, hP22, hPy22, hP2y2, hPy2y2,
        mul_one, mul_zero, add_zero, zero_add]
    have hs2 : polar Q v₂ s = polar Q v v₂ := by
      rw [hsdef]
      simp only [polar_add_right, polar_smul_right_eq, hP11, hPy11, hP1y1, hPy1y1, hP12,
        hP21, hP1y2, hPy21, hPy12, hP2y1, hPy1y2, hPy2y1, hP22, hPy22, hP2y2, hPy2y2,
        mul_one, mul_zero, add_zero, zero_add]
    have hsy2 : polar Q (y v₂) s = polar Q v (y v₂) := by
      rw [hsdef]
      simp only [polar_add_right, polar_smul_right_eq, hP11, hPy11, hP1y1, hPy1y1, hP12,
        hP21, hP1y2, hPy21, hPy12, hP2y1, hPy1y2, hPy2y1, hP22, hPy22, hP2y2, hPy2y2,
        mul_one, mul_zero, add_zero, zero_add]
    have hw1 : polar Q v₁ w = 0 := by
      rw [hwdef, sub_eq_add_neg, polar_add_right, polar_neg_right, hs1,
        polar_comm Q v₁ v]
      abel
    have hw2 : polar Q (y v₁) w = 0 := by
      rw [hwdef, sub_eq_add_neg, polar_add_right, polar_neg_right, hsy1,
        polar_comm Q (y v₁) v]
      abel
    have hw3 : polar Q v₂ w = 0 := by
      rw [hwdef, sub_eq_add_neg, polar_add_right, polar_neg_right, hs2,
        polar_comm Q v₂ v]
      abel
    have hw4 : polar Q (y v₂) w = 0 := by
      rw [hwdef, sub_eq_add_neg, polar_add_right, polar_neg_right, hsy2,
        polar_comm Q (y v₂) v]
      abel
    have hyw : y w = w := h.fix w hw1 hw2 hw3 hw4
    have hy3w : (y ^ 3) w = w := by
      rw [hpow]
      simp only [LinearEquiv.mul_apply, hyw]
    have hy3s : (y ^ 3) s = s := by
      rw [hsdef]
      simp only [map_add (y ^ 3), map_smul (y ^ 3), hy3_v₁, hy3_yv₁, hy3_v₂, hy3_yv₂]
    have hv : v = s + w := by rw [hwdef]; abel
    rw [hv, map_add (y ^ 3), hy3s, hy3w]
    rfl
  exact orderOf_eq_prime h3 hne


private theorem components_le_map_of_sup {A : Type*} [Group A] [Finite A]
    {Q L M : Subgroup A} (hsup : Q ⊔ (L ⊔ M) = ⊤)
    (hQ : Q ≤ CFSG.pCore 2 A)
    (hLM : L ≤ Subgroup.centralizer (M : Set A))
    (hLsol : Group.IsSolvable ↥L) :
    ∀ C : Subgroup (A ⧸ CFSG.pCore 2 A), CFSG.Open.IsComponentOf C ⊤ →
      C ≤ M.map (QuotientGroup.mk' (CFSG.pCore 2 A)) := by
  classical
  let O : Subgroup A := CFSG.pCore 2 A
  let π : A →* A ⧸ O := QuotientGroup.mk' O
  let N : Subgroup (A ⧸ O) := M.map π
  have hQmap : Q.map π = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_bot]
    change (QuotientGroup.mk q : A ⧸ O) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hQ hq
  have htop : L.map π ⊔ N = ⊤ := by
    have h := congrArg (Subgroup.map π) hsup
    rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O),
      Subgroup.map_sup, Subgroup.map_sup, hQmap, bot_sup_eq] at h
    simpa [N] using h
  have hLnorm : L.map π ≤ Subgroup.normalizer (N : Set (A ⧸ O)) := by
    have hLc : L.map π ≤ Subgroup.centralizer (N : Set (A ⧸ O)) := by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul]
      exact congrArg π ((Subgroup.mem_centralizer_iff.mp (hLM hl)) m hm)
    exact hLc.trans (Subgroup.centralizer_le_normalizer _)
  have hNnormal : N.Normal := by
    have htopnorm : (⊤ : Subgroup (A ⧸ O)) ≤
        Subgroup.normalizer (N : Set (A ⧸ O)) := by
      rw [← htop]
      exact sup_le hLnorm (Subgroup.le_normalizer)
    refine ⟨fun n hn g => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (htopnorm (Subgroup.mem_top g)) n).mp hn
  haveI : N.Normal := hNnormal
  have hsol : Group.IsSolvable ((A ⧸ O) ⧸ N) := by
    let f : ↥L →* (A ⧸ O) ⧸ N :=
      (QuotientGroup.mk' N).comp ((QuotientGroup.mk' O).comp L.subtype)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
      have hx : x ∈ L.map π ⊔ N := by rw [htop]; exact Subgroup.mem_top x
      obtain ⟨l, hl, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      refine ⟨⟨l₀, hl₀⟩, ?_⟩
      have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      change QuotientGroup.mk' N (QuotientGroup.mk' O l₀) =
        QuotientGroup.mk' N (QuotientGroup.mk' O l₀ * n)
      rw [map_mul, hn1, mul_one]
    haveI : Group.IsSolvable ↥L := hLsol
    exact Group.isSolvable_of_surjective hf
  intro C hC
  have hperf : ⁅C, C⁆ = C :=
    CFSG.LargeExtraspecial.S5.commutator_eq_self_of_isQuasisimple hC.2.2
  have := CFSG.Quasithin.GoldS146P.perfect_le_of_solvable_quotient N hperf
  simpa [N, π, O] using this


private theorem exists_levi_three_frame {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (hK : Nat.card K = 2) (h₁₂ : P₁.Orth P₂)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) (u : U)
    {r : G} (hr : r = ψ (u * x * u⁻¹)) :
    ∃ y₀ : U, GGTwoPlaneThree Q (σ y₀) (P₁.e + P₁.f) (P₁.e + P₂.e + P₁.f) ∧
      ψ (u * y₀ * u⁻¹) ∈ Subgroup.centralizer ({r} : Set G) ∧
      ∃ J₁ : Subgroup G, J₁ ≤ Subgroup.centralizer ({ψ (u * y₀ * u⁻¹)} : Set G) ∧
        ∀ C : Subgroup (GGInvolCentBar ψ.range r),
          CFSG.Open.IsComponentOf C ⊤ →
          C ≤ (J₁.subgroupOf (Subgroup.centralizer ({r} : Set G) ⊓
            ψ.range)).map (QuotientGroup.mk' (CFSG.Open.pCore 2
              ↥(Subgroup.centralizer ({r} : Set G) ⊓ ψ.range))) := by
  classical
  let φ : U →* G := ψ.comp (MulAut.conj u).toMonoidHom
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hφx : ψ (u * x * u⁻¹) = φ x := by
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hrφ : r = φ x := by rw [hr, hφx]
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ RCSTOm.rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : RCSTOm.omFix Q P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (RCSTOm.mem_omFix.mp hg).1
  set QG := RCSTOm.Φ σ φ (rootRadical Q P₁ P₂) with hQGdef
  set AG := RCSTOm.Φ σ φ (leviFix (elementaryGroup Q) P₁ P₂) with hAGdef
  set BG := RCSTOm.Φ σ φ (RCSTOm.omFix Q P₁ P₂) with hBGdef
  have hsup : QG ⊔ (AG ⊔ BG) =
      RCSTOm.Φ σ φ (rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂ ⊔
        RCSTOm.omFix Q P₁ P₂) := by
    rw [RCSTOm.Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, RCSTOm.Φ_sup hσ φ hRE hL₁E, sup_assoc]
  have hcen : QG ⊔ (AG ⊔ BG) = Subgroup.centralizer ({φ x} : Set G) ⊓ φ.range := by
    rw [inf_comm, ggRCQL_range_inf_centralizer hφ x,
      RCSTOm.centralizer_eq_comap hσ hσE x, hx,
      RCSTOm.centralizer_inf_elementaryGroup_eq h₁₂, hsup]
    rfl
  have hQ2 : IsPGroup 2 QG := RCSTOm.Φ_isPGroup φ hσ isPGroup_rootRadical
  have hLQ : AG ⊔ BG ≤ Subgroup.normalizer (QG : Set G) := by
    have h := RCSTOm.Φ_le_normalizer (σ := σ) φ
      (sup_le (RCSTOm.leviFix_le_normalizer_rootRadical h₁₂)
        (RCSTOm.omFix_le_normalizer_rootRadical h₁₂))
    rwa [RCSTOm.Φ_sup hσ φ hL₁E hL₂E] at h
  have h12 : AG ≤ Subgroup.centralizer (BG : Set G) :=
    RCSTOm.Φ_le_centralizer hσ φ (RCSTOm.leviFix_le_centralizer_omFix h₁₂)
  set yV : V ≃ₗ[K] V := eichler Q P₁.e P₂.f * eichler Q P₂.e P₁.f with hyVdef
  have hyVlevi : yV ∈ leviFix (elementaryGroup Q) P₁ P₂ := by
    have h1 : eichler Q P₁.e P₂.f ∈ leviFix (elementaryGroup Q) P₁ P₂ := by
      simpa using (eichler_mem_leviFix (H := elementaryGroup Q) h₁₂ hE 1).1
    have h2 : eichler Q P₂.e P₁.f ∈ leviFix (elementaryGroup Q) P₁ P₂ := by
      simpa using (eichler_mem_leviFix (H := elementaryGroup Q) h₁₂ hE 1).2
    rw [hyVdef]
    exact mul_mem h1 h2
  have hyVrange : yV ∈ σ.range := by
    rw [hσE]
    exact (mem_leviFix.mp hyVlevi).1
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp hyVrange
  have hGG : GGTwoPlaneThree Q (σ y₀) (P₁.e + P₁.f) (P₁.e + P₂.e + P₁.f) := by
    rw [hy₀]
    rw [hyVdef]
    exact ggTwoPlaneThree_eichler_mul_eichler h₁₂
  have hcommV : yV * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * yV :=
    leviFix_commute_e hyVlevi
  have hcomm : y₀ * x = x * y₀ := by
    apply hσ
    rw [map_mul, map_mul, hy₀, hx, hcommV]
  have hycen : ψ (u * y₀ * u⁻¹) ∈
      Subgroup.centralizer ({r} : Set G) := by
    rw [hrφ, Subgroup.mem_centralizer_singleton_iff]
    have hprod : (u * y₀ * u⁻¹) * (u * x * u⁻¹) = (u * x * u⁻¹) * (u * y₀ * u⁻¹) := by
      rw [show (u * y₀ * u⁻¹) * (u * x * u⁻¹) = u * (y₀ * x) * u⁻¹ by group,
        show (u * x * u⁻¹) * (u * y₀ * u⁻¹) = u * (x * y₀) * u⁻¹ by group, hcomm]
    rw [← hφx, ← map_mul, ← map_mul, hprod]
  refine ⟨y₀, hGG, hycen, BG, ?_, ?_⟩
  ·
    have hy₀L : y₀ ∈ (leviFix (elementaryGroup Q) P₁ P₂).comap σ := by
      rw [Subgroup.mem_comap, hy₀]
      exact hyVlevi
    have hφy : φ y₀ ∈ AG := Subgroup.mem_map.mpr ⟨y₀, hy₀L, rfl⟩
    have hyr : ψ (u * y₀ * u⁻¹) = φ y₀ := by
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hyr]
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (h12 hφy)) b hb
  ·
    intro C hC
    set A₀ : Subgroup G := Subgroup.centralizer ({r} : Set G) ⊓ ψ.range with hA₀def
    have hA₀ : A₀ = QG ⊔ (AG ⊔ BG) := by
      rw [hA₀def, hrφ, hcen, hφr]
    have hQG_A : QG ≤ A₀ :=
      (le_sup_left (a := QG) (b := AG ⊔ BG)).trans (le_of_eq hA₀.symm)
    have hAG_A : AG ≤ A₀ := by
      have h1 : AG ≤ AG ⊔ BG := le_sup_left (a := AG) (b := BG)
      have h2 : AG ⊔ BG ≤ QG ⊔ (AG ⊔ BG) :=
        le_sup_right (a := QG) (b := AG ⊔ BG)
      exact h1.trans (h2.trans (le_of_eq hA₀.symm))
    have hBG_A : BG ≤ A₀ := by
      have h1 : BG ≤ AG ⊔ BG := le_sup_right (a := AG) (b := BG)
      have h2 : AG ⊔ BG ≤ QG ⊔ (AG ⊔ BG) :=
        le_sup_right (a := QG) (b := AG ⊔ BG)
      exact h1.trans (h2.trans (le_of_eq hA₀.symm))
    have hA₀norm : A₀ ≤ Subgroup.normalizer (QG : Set G) :=
      hA₀.le.trans (sup_le Subgroup.le_normalizer hLQ)
    have hQ'p : IsPGroup 2 (QG.subgroupOf A₀) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQG_A).symm
    have hQ'n : (QG.subgroupOf A₀).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQG_A).mpr hA₀norm
    have hQcore : QG.subgroupOf A₀ ≤ CFSG.pCore 2 ↥A₀ := by
      rw [CFSG.pCore_eq_iSup]
      exact le_iSup_of_le (QG.subgroupOf A₀)
        (le_iSup_of_le hQ'n (le_iSup_of_le hQ'p le_rfl))
    have hsupA : (QG.subgroupOf A₀) ⊔ ((AG.subgroupOf A₀) ⊔ (BG.subgroupOf A₀)) = ⊤ := by
      have h1 : (AG ⊔ BG).subgroupOf A₀ = AG.subgroupOf A₀ ⊔ BG.subgroupOf A₀ :=
        Subgroup.subgroupOf_sup hAG_A hBG_A
      have h2 : (QG ⊔ (AG ⊔ BG)).subgroupOf A₀ =
          QG.subgroupOf A₀ ⊔ (AG ⊔ BG).subgroupOf A₀ :=
        Subgroup.subgroupOf_sup hQG_A (sup_le hAG_A hBG_A)
      rw [← h1, ← h2]
      change (QG ⊔ (AG ⊔ BG)).subgroupOf A₀ = ⊤
      rw [hA₀, Subgroup.subgroupOf_self]
    have hLM' : AG.subgroupOf A₀ ≤
        Subgroup.centralizer ((BG.subgroupOf A₀ : Subgroup ↥A₀) : Set ↥A₀) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      apply Subtype.ext
      have haG : (a : G) ∈ AG := Subgroup.mem_subgroupOf.mp ha
      have hbG : (b : G) ∈ BG := Subgroup.mem_subgroupOf.mp hb
      exact (Subgroup.mem_centralizer_iff.mp (h12 haG)) (b : G) hbG
    have hAGsol : Group.IsSolvable ↥AG := by
      have eAG : ↥AG ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
        (RCSTOm.Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv P₁ P₂ h₁₂ hE)
      haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
        SevOmSmall.isSolvable_SL_two hK
      exact Group.isSolvable_of_isSolvable_injective (f := eAG.toMonoidHom) eAG.injective
    have hLsol : Group.IsSolvable ↥(AG.subgroupOf A₀) := by
      have e : ↥(AG.subgroupOf A₀) ≃* ↥AG := Subgroup.subgroupOfEquivOfLe hAG_A
      haveI : Group.IsSolvable ↥AG := hAGsol
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have hcomp := components_le_map_of_sup (A := ↥A₀) (Q := QG.subgroupOf A₀)
      (L := AG.subgroupOf A₀) (M := BG.subgroupOf A₀) hsupA hQcore hLM' hLsol
    exact hcomp C hC


theorem ggRootInvol_exists_levi_three_POmegaMinus {G : Type} [Group G] [Finite G] {n : ℕ}
    (hn : 4 ≤ n) {ψ : spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus n (GaloisField 2 1)
        (CFSG.LieType.Universal.minusCoeffs 2 1).1
        (CFSG.LieType.Universal.minusCoeffs 2 1).2) →* G}
    (hψ : Function.Injective ψ) {r : G}
    (hr : GGRootInvolution
      (CFSG.LieType.Universal.Spin.Twisted.minusDatum n
        (CFSG.LieType.Universal.minusCoeffs_irr 2 1))
      .POmegaMinus ψ r) :
    ∃ (y₀ u : spinGroup
        (CFSG.LieType.Universal.Spin.quadMinus n (GaloisField 2 1)
          (CFSG.LieType.Universal.minusCoeffs 2 1).1
          (CFSG.LieType.Universal.minusCoeffs 2 1).2))
      (v₁ v₂ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 1),
      GGTwoPlaneThree (CFSG.LieType.Universal.Spin.quadMinus n (GaloisField 2 1)
          (CFSG.LieType.Universal.minusCoeffs 2 1).1
          (CFSG.LieType.Universal.minusCoeffs 2 1).2)
        (CFSG.LieType.Universal.Spin.spinAction
          (CFSG.LieType.Universal.Spin.quadMinus n (GaloisField 2 1)
            (CFSG.LieType.Universal.minusCoeffs 2 1).1
            (CFSG.LieType.Universal.minusCoeffs 2 1).2) y₀) v₁ v₂ ∧
      ψ (u * y₀ * u⁻¹) ∈ Subgroup.centralizer ({r} : Set G) ∧
      ∃ J₁ : Subgroup G, J₁ ≤ Subgroup.centralizer ({ψ (u * y₀ * u⁻¹)} : Set G) ∧
        ∀ C : Subgroup (GGInvolCentBar ψ.range r), CFSG.Open.IsComponentOf C ⊤ →
          C ≤ (J₁.subgroupOf (Subgroup.centralizer ({r} : Set G) ⊓ ψ.range)).map
            (QuotientGroup.mk' (CFSG.Open.pCore 2
              ↥(Subgroup.centralizer ({r} : Set G) ⊓ ψ.range)))    := by
  have hirr := CFSG.LieType.Universal.minusCoeffs_irr 2 1
  obtain ⟨hr2, γ, ⟨-, hγl⟩, u, hru⟩ := hr
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn (hγl (Or.inr (Or.inl rfl)))
  obtain ⟨z, hz, hzr⟩ := Subgroup.mem_map.mp hru
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
  have hyz' : u * y * u⁻¹ = z := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyz
  let K : Type := GaloisField 2 1
  let b : K := (CFSG.LieType.Universal.minusCoeffs 2 1).1
  let c : K := (CFSG.LieType.Universal.minusCoeffs 2 1).2
  let V : Type := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K
  let Q : QuadraticForm K V := CFSG.LieType.Universal.Spin.quadMinus n K b c
  let F : CFSG.LieType.Universal.Spin.OddFrame Q (n - 1) := minusFrame n b c
  have hyrange : y ∈ (F.longRoot hij s t).range := by
    dsimp only [F, Q, b, c, K]
    rw [← minusRootGroup_eq_long (n := n) (hirr := hirr)
      (b := (CFSG.LieType.Universal.minusCoeffs 2 1).1)
      (c := (CFSG.LieType.Universal.minusCoeffs 2 1).2) hij s t hst]
    exact hy
  have hexy : ∃ a : K, F.longRoot hij s t (Multiplicative.ofAdd a) = y := by
    dsimp only [F, Q, b, c, K]
    exact MonoidHom.mem_range.mp hyrange
  obtain ⟨a, ha⟩ := hexy
  have hy1 : y ≠ 1 := by
    intro hyeq
    have hz1 : z = 1 := by rw [← hyz', hyeq]; group
    have hr1 : r = 1 := by rw [← hzr, hz1, map_one]
    rw [hr1, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hy1 (by rw [← ha]; exact map_one _)
  have hrr : r = ψ (u * (F.longRoot hij s t (Multiplicative.ofAdd a)) * u⁻¹) := by
    rw [← hzr, ← hyz', ← ha]
  have hQ : (polarBilin Q).Nondegenerate := by
    dsimp only [Q]
    exact nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 1) hirr
  have hK : Nat.card K = 2 := by
    dsimp only [K]
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  let P₁ : CFSG.ClassicalGroups.Orthogonal.HypPair Q := framePair F.toHypFrame j t
  let P₂ : CFSG.ClassicalGroups.Orthogonal.HypPair Q :=
    smulPair (framePair F.toHypFrame i s) ha0
  have h₁₂ : P₁.Orth P₂ := RCSTOm.orth₁₂ F.toHypFrame hij s t ha0
  have hσ : Function.Injective (spinAction Q) := by
    dsimp only [Q]
    exact RootCentOmega.spinAction_quadMinus_injective hirr
  have hσE : (spinAction Q).range = elementaryGroup Q := by
    dsimp only [Q]
    exact CFSG.LieType.Universal.Spin.range_spinAction_quadMinus hn hirr
  have hσx : spinAction Q (F.longRoot hij s t (Multiplicative.ofAdd a)) =
      eichler Q P₁.e P₂.e := by
    dsimp only [P₁, P₂, Q, F, b, c, K, V]
    rw [RootCentOmega.spinAction_longRoot_eq_eichler]
    rfl
  obtain ⟨y₀, hGG, hycen, J₁, hJ₁, hcomp⟩ :=
    exists_levi_three_frame (K := K) (V := V) (Q := Q) (P₁ := P₁) (P₂ := P₂)
      (U := spinGroup Q) (σ := spinAction Q)
      (x := F.longRoot hij s t (Multiplicative.ofAdd a)) (G := G) (r := r)
      hK h₁₂ hσ hσE hσx ψ hψ u hrr
  exact ⟨y₀, u, P₁.e + P₁.f, P₁.e + P₂.e + P₁.f, hGG, hycen, J₁, hJ₁, hcomp⟩


theorem ggRootInvol_exists_levi_three_POmegaPlus {G : Type} [Group G] [Finite G] {n : ℕ}
    (hn : 3 ≤ n) {ψ : spinGroup
      (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 1)) →* G}
    (hψ : Function.Injective ψ) {r : G}
    (hr : GGRootInvolution (CFSG.LieType.Universal.Spin.plusDatum n (GaloisField 2 1) hn)
      .POmegaPlus ψ r) :
    ∃ (y₀ u : spinGroup
        (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 1)))
      (v₁ v₂ : Fin n ⊕ Fin n → GaloisField 2 1),
      GGTwoPlaneThree (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 1))
        (CFSG.LieType.Universal.Spin.spinAction
          (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 1)) y₀) v₁ v₂ ∧
      ψ (u * y₀ * u⁻¹) ∈ Subgroup.centralizer ({r} : Set G) ∧
      ∃ J₁ : Subgroup G, J₁ ≤ Subgroup.centralizer ({ψ (u * y₀ * u⁻¹)} : Set G) ∧
        ∀ C : Subgroup (GGInvolCentBar ψ.range r), CFSG.Open.IsComponentOf C ⊤ →
          C ≤ (J₁.subgroupOf (Subgroup.centralizer ({r} : Set G) ⊓ ψ.range)).map
            (QuotientGroup.mk' (CFSG.Open.pCore 2
              ↥(Subgroup.centralizer ({r} : Set G) ⊓ ψ.range))) := by
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨z, hz, hzr⟩ := Subgroup.mem_map.mp hru
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
  have hyz' : u * y * u⁻¹ = z := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyz
  obtain ⟨i, j, hij, s, t, -, hX⟩ :=
    exists_plusRootGroup_eq (K := GaloisField 2 1) hn hγ
  have hy' : y ∈ ((plusFrame n (GaloisField 2 1) hn).longRoot hij s t).range := by
    rw [← hX]
    exact hy
  obtain ⟨c₀, rfl⟩ := hy'
  have hrr : r = ψ (u * ((plusFrame n (GaloisField 2 1) hn).longRoot hij s t c₀) * u⁻¹) := by
    rw [← hzr, ← hyz']
  have hc : Multiplicative.toAdd c₀ ≠ 0 := by
    intro h0
    have hc₀ : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0, ofAdd_zero]
    have hr1 : r = 1 := by
      rw [hrr, hc₀, map_one, mul_one, mul_inv_cancel, map_one]
    rw [hr1, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hσx : spinAction (quadPlus n (GaloisField 2 1))
      ((plusFrame n (GaloisField 2 1) hn).longRoot hij s t c₀) =
      eichler (quadPlus n (GaloisField 2 1)) ((plusFrame n (GaloisField 2 1) hn).vec j t)
        (Multiplicative.toAdd c₀ • (plusFrame n (GaloisField 2 1) hn).vec i s) := by
    rw [← RootCentOmega.spinAction_longRoot_eq_eichler, ofAdd_toAdd]
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  set P₁ : CFSG.ClassicalGroups.Orthogonal.HypPair (quadPlus n (GaloisField 2 1)) :=
    framePair (plusFrame n (GaloisField 2 1) hn) j t with hP₁def
  set P₂ : CFSG.ClassicalGroups.Orthogonal.HypPair (quadPlus n (GaloisField 2 1)) :=
    smulPair (framePair (plusFrame n (GaloisField 2 1) hn) i s) hc with hP₂def
  have h₁₂ : P₁.Orth P₂ := RCSTOm.orth₁₂ (plusFrame n (GaloisField 2 1) hn) hij s t hc
  have hσ : Function.Injective (spinAction (quadPlus n (GaloisField 2 1))) :=
    RootCentOmega.spinAction_quadPlus_injective
  have hσE : (spinAction (quadPlus n (GaloisField 2 1))).range =
      elementaryGroup (quadPlus n (GaloisField 2 1)) :=
    CFSG.LieType.Universal.Spin.range_spinAction_quadPlus hn
  obtain ⟨y₀, hGG, hycen, J₁, hJ₁, hcomp⟩ :=
    exists_levi_three_frame (K := GaloisField 2 1)
      (V := Fin n ⊕ Fin n → GaloisField 2 1)
      (Q := quadPlus n (GaloisField 2 1)) (P₁ := P₁) (P₂ := P₂)
      (U := spinGroup (quadPlus n (GaloisField 2 1)))
      (σ := spinAction (quadPlus n (GaloisField 2 1)))
      (x := (plusFrame n (GaloisField 2 1) hn).longRoot hij s t c₀)
      (G := G) (r := r)
      hK h₁₂ hσ hσE hσx ψ hψ u hrr
  exact ⟨y₀, u, P₁.e + P₁.f, P₁.e + P₂.e + P₁.f, hGG, hycen, J₁, hJ₁, hcomp⟩

end CFSG.StandardType
