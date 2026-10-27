module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthL51Aux

public section

namespace CFSG.StandardType.ZS

open QuadraticMap
open CFSG.ClassicalGroups.Orthogonal

theorem owL5_orthRefl_smul {K : Type*} [Field K] {U : Type} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) (l : K) (hl : l ≠ 0)
    (h : Q (l • a) ≠ 0) :
    owCr_orthRefl Q (l • a) h = owCr_orthRefl Q a ha := by
  ext v
  rw [owCr_orthRefl_apply, owCr_orthRefl_apply]
  have hQl : Q (l • a) = l * l * Q a := by
    simp only [QuadraticMap.map_smul, smul_eq_mul]
  have hBl : polarBilin Q v (l • a) = l * polarBilin Q v a := by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_smul_right, smul_eq_mul]
  rw [hQl, hBl]
  have hcoef : (l * polarBilin Q v a / (l * l * Q a)) • (l • a)
      = (polarBilin Q v a / Q a) • a := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [hcoef]

theorem owL5_zmod3_sq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

theorem owL5_exists_u {K : Type*} [Field K] [CharP K 3] {U : Type} [AddCommGroup U] [Module K U]
    (hsq : ∀ x : K, x ≠ 0 → x * x = 1)
    (Q : QuadraticForm K U) {a b : U} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hra2 : owCr_orthRefl Q a ha * owCr_orthRefl Q a ha = 1)
    (hrb2 : owCr_orthRefl Q b hb * owCr_orthRefl Q b hb = 1)
    (hord : orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb) = 3) :
    ∃ (u b' : U) (hb' : Q b' ≠ 0),
      u ≠ 0 ∧ Q u = 0 ∧ polarBilin Q u a = 0 ∧ b' = a - u ∧
        owCr_orthRefl Q b hb = owCr_orthRefl Q b' hb' := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have hba : polarBilin Q b a = polarBilin Q a b := by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]
  have hκκ : polarBilin Q a b * polarBilin Q a b = Q a * Q b :=
    owL5_sq_polar Q ha hb hra2 hrb2 hord
  have hc2 : Q a * Q a = 1 := hsq (Q a) ha
  have hd2 : Q b * Q b = 1 := hsq (Q b) hb
  have hκne : polarBilin Q a b ≠ 0 := by
    intro h
    rw [h, zero_mul] at hκκ
    exact (mul_ne_zero ha hb) hκκ.symm
  have hκ2 : polarBilin Q a b * polarBilin Q a b = 1 := hsq _ hκne
  have hcd : Q a * Q b = 1 := hκκ.symm.trans hκ2
  have hdc : Q a = Q b := by
    apply mul_left_cancel₀ ha
    rw [hc2, hcd]
  set s : K := Q a * polarBilin Q a b with hs
  have hs2 : s * s = 1 := by
    rw [hs]
    calc (Q a * polarBilin Q a b) * (Q a * polarBilin Q a b)
        = (Q a * Q a) * (polarBilin Q a b * polarBilin Q a b) := by ring
      _ = 1 := by rw [hc2, hκ2, mul_one]
  have hsk : s * polarBilin Q a b = Q a := by
    rw [hs]
    calc (Q a * polarBilin Q a b) * polarBilin Q a b
        = Q a * (polarBilin Q a b * polarBilin Q a b) := by ring
      _ = Q a * 1 := by rw [hκ2]
      _ = Q a := by ring
  have hsne : s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hs2
    exact zero_ne_one hs2
  have hneg : Q (-s • b) ≠ 0 := by
    have hval : Q (-s • b) = Q b := by
      rw [QuadraticMap.map_smul Q, show (-s) * (-s) = 1 by
        rw [show -s * -s = s * s by ring, hs2], one_smul]
    rw [hval]; exact hb
  have hscale : owCr_orthRefl Q (-s • b) hneg = owCr_orthRefl Q b hb :=
    owL5_orthRefl_smul Q b hb (-s) (neg_ne_zero.mpr hsne) hneg
  have hQa2 : polarBilin Q a a = 2 * Q a := by
    rw [polarBilin_apply_apply, polar_self, two_smul]
    ring
  have h2a : (Q a * polarBilin Q a b) * (Q a * polarBilin Q a b) * Q b = Q b := by
    calc (Q a * polarBilin Q a b) * (Q a * polarBilin Q a b) * Q b
        = (Q a * Q a) * (polarBilin Q a b * polarBilin Q a b) * Q b := by ring
      _ = Q b := by rw [hc2, hκ2, one_mul, one_mul]
  have h2b : (Q a * polarBilin Q a b) * polarBilin Q a b = Q a := by
    calc (Q a * polarBilin Q a b) * polarBilin Q a b
        = Q a * (polarBilin Q a b * polarBilin Q a b) := by ring
      _ = Q a := by rw [hκ2, mul_one]
  refine ⟨a + s • b, -s • b, hneg, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hvec : a = -s • b := by
      have h := hzero
      rw [add_eq_zero_iff_eq_neg] at h
      rw [h]
      module
    have hb_eq : owCr_orthRefl Q a ha = owCr_orthRefl Q b hb := by
      have hthis : owCr_orthRefl Q a ha = owCr_orthRefl Q (-s • b) hneg := by
        ext v
        rw [owCr_orthRefl_apply, owCr_orthRefl_apply, hvec]
      exact hthis.trans hscale
    have h1 : owCr_orthRefl Q a ha * owCr_orthRefl Q b hb = 1 := by rw [hb_eq, hrb2]
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  · have hexp : Q (a + s • b) = Q a + s * s * Q b + s * polarBilin Q a b := by
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polarBilin_apply_apply,
        polar_smul_right]
      ring
    rw [hexp, hs, h2a, h2b, hdc, show Q b + Q b + Q b = (3 : K) * Q b by ring, h3, zero_mul]
  · have hexp : polarBilin Q (a + s • b) a
        = polarBilin Q a a + s * polarBilin Q b a := by
      rw [polarBilin_apply_apply, polarBilin_apply_apply, polarBilin_apply_apply,
        polar_add_left, polar_smul_left, smul_eq_mul]
    rw [hexp, hQa2, hba, hsk, show 2 * Q a + Q a = (3 : K) * Q a by ring, h3, zero_mul]
  · rw [show a - (a + s • b) = -s • b by module]
  · exact hscale.symm

theorem owL5_exists_second_isotropic {K : Type*} [Field K] [Finite K]
    {U : Type} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (hodd : Odd (Nat.card K)) (h2 : (2 : K) ≠ 0)
    (Q : QuadraticForm K U) (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ Module.finrank K U) {a u : U} (ha : Q a ≠ 0)
    (hu : Q u = 0) (hau : polarBilin Q u a = 0) (hu0 : u ≠ 0) :
    ∃ u' : U, u' ≠ 0 ∧ Q u' = 0 ∧ polarBilin Q u' a = 0 ∧ polarBilin Q u' u = 0 ∧
      u' ∉ Submodule.span K {u} := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  let V : Submodule K U := LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ a)
  have hQV : (polarBilin (Q.comp V.subtype)).Nondegenerate :=
    owCr_restrict_nondegenerate Q hQ h2 a ha
  have huV : u ∈ V := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply, hau, mul_zero]
  let uV : V := ⟨u, huV⟩
  have huVQ : (Q.comp V.subtype) uV = 0 := by simpa [uV] using hu
  have huV0 : uV ≠ 0 := fun h => hu0 (Subtype.ext_iff.mp h)
  obtain ⟨P, hPe⟩ := exists_hypPair hQV huVQ huV0
  have hW : (polarBilin ((Q.comp V.subtype).restrict P.perp)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (HypPair.polarNondegOn_perp hQV P)
  have hperp3 : 3 ≤ Module.finrank K P.perp := by
    have h1 := CFSG.ClassicalInvolution.ModelFacts.finrank_hypPair_perp hQV P
    have h2' : Module.finrank K V = Module.finrank K U - 1 := by
      have h := LinearMap.BilinForm.finrank_orthogonal (B := polarBilin Q) hQ (K ∙ a)
      rw [finrank_span_singleton ha_ne] at h
      omega
    omega
  obtain ⟨uw, huwne, huwQ⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isotropic_of_finrank_ge_three hodd
      ((Q.comp V.subtype).restrict P.perp) hW hperp3
  refine ⟨V.subtype (P.perp.subtype uw), ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 : P.perp.subtype uw = 0 := Submodule.subtype_injective (p := V) (by simpa using h0)
    exact huwne (Subtype.ext h1)
  · exact huwQ
  · have hthis := (LinearMap.BilinForm.mem_orthogonal_iff.mp (P.perp.subtype uw).2) a
      (Submodule.mem_span_singleton_self a)
    simpa [polarBilin_apply_apply, polar_comm] using hthis
  · have hm := HypPair.mem_perp.mp uw.2
    have h1 : polar (Q.comp V.subtype) P.e uw = 0 := hm.1
    rw [hPe] at h1
    rw [polarBilin_apply_apply, polar_comm]
    exact h1
  · intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hf := HypPair.mem_perp.mp uw.2
    have hcu : (P.perp.subtype uw : V) = c • uV := by
      apply Submodule.subtype_injective (p := V)
      rw [map_smul]
      exact hc.symm
    have hcv : (uw : V) = c • P.e := by
      rw [hPe]
      exact hcu
    have h2' : c = 0 := by
      have h := hf.2
      rw [hcv, polar_smul_right_eq, P.polar_fe, mul_one] at h
      exact h
    apply huwne
    have hzero : (uw : V) = 0 := by rw [hcv, h2', zero_smul]
    exact Subtype.coe_injective (by simpa using hzero)

end CFSG.StandardType.ZS

end
