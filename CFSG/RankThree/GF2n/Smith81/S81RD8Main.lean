module

public import CFSG.RankThree.GF2n.Smith81.S81RD8Pt
public import CFSG.RankThree.GF2n.Smith81.S81RD8G1
public import CFSG.RankThree.GF2n.Smith81.S81R213K4
public import CFSG.RankThree.GF2n.Smith81.S81R213Q
public import CFSG.RankThree.GF2n.Smith81.S81LaneE3L

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix exteriorPower

section Frame


theorem with_e3lDat (hFE1 : Smith24E3LUniformStatement) (hFE2 : E3LRootEltStatement)
    (hNF : Smith212ENonfusedE3LStatement) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (IH : Smith1981Below (Nat.card G)) (hSE : SmithECfg M Q Z B) (hc3 : InCaseE3L M Q Z B)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {P : Prop}
    (k : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ) (ψ : M₀.E ≃ₗ[K] Cube K)
      (φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)), E3LDat M Q Z B K γ M₀ ψ φ z → P) : P := by
  have hrem : RemCfg M Q Z B := hSE.toRemCfg
  have H : StrothHyp M Q Z := hrem.ctx.hyp
  obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hrem hc3 K γ M₀ hD
  exact k K γ M₀ ψ φ ⟨hrem.ctx, hD, d, hz, hz1,
    fun y hyc hyM hyQ w hw hw1 => hNF G M Q Z B IH hSE hc3 z hz hz1 y hyM hyQ hyc w hw hw1,
    fun y hyc hyM hyQ => hFE2 G M Q Z B IH hrem hc3 K γ M₀ hD ψ φ d z hz hz1 y hyc hyM hyQ⟩

theorem lin213_left_Q_of_inputs (hFE1 : Smith24E3LUniformStatement) (hFE2 : E3LRootEltStatement)
    (hNF : Smith212ENonfusedE3LStatement) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (IH : Smith1981Below (Nat.card G)) (hSE : SmithECfg M Q Z B) (hc3 : InCaseE3L M Q Z B)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {x y : G} (hxc : IsConj z x) (hyc : IsConj z y)
    (hxQ : x ∈ Q) (hyM : y ∈ M) (h4 : orderOf (x * y) = 4) : InZClass Z ((x * y) ^ 2) := by
  have H : StrothHyp M Q Z := hSE.toCfg.ctx.hyp
  by_cases hyQ : y ∈ Q
  · rcases sq_eq_one_or_inZClass_of_mem_Q H (Q.mul_mem hxQ hyQ) with h | h
    · exfalso
      have h2 : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one h
      rw [h4] at h2
      omega
    · exact h
  · exact with_e3lDat hFE1 hFE2 hNF IH hSE hc3 hz hz1 fun K _ _ _ γ M₀ ψ φ Dt =>
      (concl_Q_left Dt hxc hxQ hyc hyM hyQ).2 h4

end Frame

section Ordered


theorem d8_ordered (hFE1 : Smith24E3LUniformStatement) (hFE2 : E3LRootEltStatement)
    (hNF : Smith212ENonfusedE3LStatement) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (IH : Smith1981Below (Nat.card G)) (hSE : SmithECfg M Q Z B) (hc3 : InCaseE3L M Q Z B)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
    {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} (Dt : E3LDat M Q Z B K γ M₀ ψ φ z)
    {x y : G} (hxc : IsConj z x) (hyc : IsConj z y) (hxM : x ∈ M) (hyM : y ∈ M) (hxQ : x ∉ Q)
    (hyQ : y ∉ Q) (h4 : orderOf (x * y) = 4) {gx gy : GL (Fin 6) K} (hgx : IsTransvec K gx)
    (hgy : IsTransvec K gy) (hx : ActsAs φ x gx) (hy : ActsAs φ y gy) {a f b g : Fin 6 → K}
    (hxm : (gx : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (hym : (gy : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec b g)
    (hfa : f ⬝ᵥ a = 0) (hga : g ⬝ᵥ a = 0) (ha : a ≠ 0) (hf : f ≠ 0) :
    IsConj z ((x * y) ^ 2) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  have hA : ∀ X : Subgroup G, Sit M Q Z X x →
      ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ A ≤ QB X := fun X hs => by
    obtain ⟨A, hA1, hA2, hA3, hA4, -, -⟩ :=
      smith29_of_exists hs (smith28E3L_of_uniform hFE1 G M Q Z B IH hSE hc3 X x hs)
    exact ⟨A, hA1, hA2, hA3, hA4⟩
  obtain ⟨D, hDZ, hxD, hyD⟩ := e3l_exists_point_centralized Dt hxc hxM hxQ hyc hyM hyQ hgx hgy hx hy
    hxm hym hfa hga ha hf hA
  obtain ⟨h, hDh, hQD, hND⟩ := hDZ.QB_eq H
  subst hDh
  have hSE' := hSE.conj h
  have hc3' := hc3.conj h
  have H' : StrothHyp (conjSubgroup h M) (conjSubgroup h Q) (conjSubgroup h Z) :=
    hSE'.toCfg.ctx.hyp
  have hz' : h * z * h⁻¹ ∈ conjSubgroup h Z := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hz
  have hz1' : h * z * h⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have : z = h⁻¹ * (h * z * h⁻¹) * h := by group
    rw [this, h1]
    group
  have hzz' : IsConj z (h * z * h⁻¹) := isConj_iff.mpr ⟨h, rfl⟩
  have hxc' : IsConj (h * z * h⁻¹) x := hzz'.symm.trans hxc
  have hyc' : IsConj (h * z * h⁻¹) y := hzz'.symm.trans hyc
  have hxQ' : x ∈ conjSubgroup h Q := by rw [← hQD]; exact hxD
  have hyM' : y ∈ conjSubgroup h M := by
    rw [← hND]
    exact IsZConjugate.mem_normalizer_of_commute H hDZ hz1' hz'
      (show Commute y (h * z * h⁻¹) from
        (show Commute (h * z * h⁻¹) y from Subgroup.mem_centralizer_iff.mp hyD _ hz').symm)
  have hconj := lin213_left_Q_of_inputs hFE1 hFE2 hNF IH hSE' hc3' hz' hz1' hxc' hyc' hxQ' hyM' h4
  exact hzz'.trans (isConj_of_inZClass H' hz' hz1' hconj)

end Ordered

section Final


theorem e3lD8Centre_of_inputs (hFE1 : Smith24E3LUniformStatement) (hFE2 : E3LRootEltStatement)
    (hNF : Smith212ENonfusedE3LStatement) : E3LD8CentreStatement := by
  intro G _ _ M Q Z B IH hSE hc3 z hz hz1 x y hxc hyc hxM hyM hxQ hyQ _ h4
  have H : StrothHyp M Q Z := hSE.toCfg.ctx.hyp
  refine with_e3lDat hFE1 hFE2 hNF IH hSE hc3 hz hz1 fun K _ _ _ γ M₀ ψ φ Dt => ?_
  obtain ⟨gx, hgx, hx⟩ := Dt.actsAs hxc hxM hxQ
  obtain ⟨gy, hgy, hy⟩ := Dt.actsAs hyc hyM hyQ
  obtain ⟨a, f, ha, hf, hfa, hxm⟩ := IsTransvec.exists hgx
  obtain ⟨b, g, hb, hg, hgb, hym⟩ := IsTransvec.exists hgy
  have hxy4 : (x * y) ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one _
  have hrho : rho K ((gx * gy) ^ 4) = 1 := by
    have h1 : ActsAs φ ((x * y) ^ 4) ((gx * gy) ^ 4) := (hx.mul hy).pow 4
    have hL := h1.mem_Lgen
    have hφ := h1.phi hL
    have h2 : φ ⟨(x * y) ^ 4, hL⟩ = 1 := by
      have : (⟨(x * y) ^ 4, hL⟩ : Lgen M (LB M Q B)) = 1 := Subtype.ext hxy4
      rw [this, map_one]
    rw [h2] at hφ
    exact LinearMap.ext fun ξ => congrArg (fun e : Cube K ≃ₗ[K] Cube K => e ξ) hφ.symm
  rcases transvec_cases_of_rho_pow_four hxm hym hfa hgb hrho with hfb | hga
  ·
    have hyx4 : orderOf (y * x) = 4 := by
      have ho : orderOf (x⁻¹ * (x * y) * x⁻¹⁻¹) = orderOf (x * y) :=
        orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective (x * y)
      have e : x⁻¹ * (x * y) * x⁻¹⁻¹ = y * x := by group
      rw [e] at ho
      rw [ho, h4]
    have hyx : IsConj z ((y * x) ^ 2) :=
      d8_ordered hFE1 hFE2 hNF IH hSE hc3 hz hz1 Dt hyc hxc hyM hxM hyQ hxQ hyx4 hgy hgx hy hx hym
        hxm hgb hfb hb hg
    exact hyx.trans (isConj_iff.mpr ⟨x, by simp only [pow_two]; group⟩)
  · exact d8_ordered hFE1 hFE2 hNF IH hSE hc3 hz hz1 Dt hxc hyc hxM hyM hxQ hyQ h4 hgx hgy hx hy
      hxm hym hfa hga ha hf

end Final

end CFSG.RankThree.GF2n.Smith81.E3LRoot
