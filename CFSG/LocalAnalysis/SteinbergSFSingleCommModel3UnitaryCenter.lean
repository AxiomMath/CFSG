module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPointSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneRoot

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {m : ℕ} {F' : Type} [Field F']

section Hyp

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem u2_rkOneQElt_congr {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {a a' b b' : K} (hab : h.norm a + h.trace b = 0) (hab' : h.norm a' + h.trace b' = 0)
    (ha : a = a') (hb : b = b') : rkOneQElt h a b hab = rkOneQElt h a' b' hab' := by
  subst ha
  subst hb
  rfl

private theorem u2_rkOneQElt_zero_mem_center {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {t : K} (ht : h.norm 0 + h.trace t = 0) :
    (⟨rkOneQElt h 0 t ht, rkOneQElt_mem h ht⟩ : ↥(hypUnitriangular h 1 1)) ∈
      center ↥(hypUnitriangular h 1 1) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨a, b, hab, hy⟩ := exists_eq_rkOneQElt h y.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hy]
  change rkOneQElt h a b hab * rkOneQElt h 0 t ht = rkOneQElt h 0 t ht * rkOneQElt h a b hab
  rw [rkOneQElt_mul, rkOneQElt_mul]
  exact u2_rkOneQElt_congr h _ _ (by ring) (by simp; ring)

private theorem u2_central_a_eq_zero {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {a b : K} (hab : h.norm a + h.trace b = 0)
    (hz : (⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ : ↥(hypUnitriangular h 1 1)) ∈
      center ↥(hypUnitriangular h 1 1)) : a = 0 := by
  have hcomm : ∀ (c d : K) (hcd : h.norm c + h.trace d = 0), h.bar c * a = h.bar a * c := by
    intro c d hcd
    have h1 := Subgroup.mem_center_iff.mp hz ⟨rkOneQElt h c d hcd, rkOneQElt_mem h hcd⟩
    have h2 := congrArg (fun x : ↥(hypUnitriangular h 1 1) =>
      (((x : hypSU h 1 1) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
        (.inl 0) (.inr (.inr 0))) h1
    simp only [Subgroup.coe_mul] at h2
    change ((rkOneQElt h c d hcd * rkOneQElt h a b hab : hypSU h 1 1) : GL (HypIndex 1 1) K)
        (.inl 0) (.inr (.inr 0)) =
      ((rkOneQElt h a b hab * rkOneQElt h c d hcd : hypSU h 1 1) : GL (HypIndex 1 1) K)
        (.inl 0) (.inr (.inr 0)) at h2
    rw [rkOneQElt_mul, rkOneQElt_mul, coe_rkOneQElt, coe_rkOneQElt, rkOneQ_ef, rkOneQ_ef] at h2
    linear_combination -h2
  obtain ⟨d1, hd1⟩ := exists_norm_add_trace_eq_zero h (1 : K)
  have hbar1 : h.bar a = a := by
    have := hcomm 1 d1 hd1
    rw [map_one] at this
    linear_combination -this
  obtain ⟨w, hw⟩ := h.exists_bar_ne
  obtain ⟨dw, hdw⟩ := exists_norm_add_trace_eq_zero h w
  have := hcomm w dw hdw
  rw [hbar1] at this
  have hne : h.bar w - w ≠ 0 := sub_ne_zero.mpr hw
  have hprod : a * (h.bar w - w) = 0 := by linear_combination this
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact h0
  · exact absurd h0 hne

private theorem u2_center_eq_range {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) :
    (center ↥(hypUnitriangular h 1 1)).map (hypUnitriangular h 1 1).subtype =
      (rkOneCHomSU h).range := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, b, hab, hzab⟩ := exists_eq_rkOneQElt h z.2
    have hz' : (⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ : ↥(hypUnitriangular h 1 1)) ∈
        center ↥(hypUnitriangular h 1 1) := by
      have hzz : z = ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ := Subtype.ext hzab
      rwa [← hzz]
    have ha := u2_central_a_eq_zero h hab hz'
    subst ha
    have ht : b ∈ h.traceZero := by
      rw [UnitaryFieldData.mem_traceZero]
      have h0 := hab
      rw [UnitaryFieldData.norm, zero_mul, zero_add] at h0
      exact h0
    refine ⟨Multiplicative.ofAdd ⟨b, ht⟩, ?_⟩
    exact hzab.symm
  · rintro ⟨c, rfl⟩
    exact ⟨⟨rkOneQElt h 0 c.toAdd (norm_zero_add_trace c.toAdd.2),
      rkOneQElt_mem h (norm_zero_add_trace c.toAdd.2)⟩,
      u2_rkOneQElt_zero_mem_center h _, rfl⟩

end Hyp

section Transport

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups Matrix

private theorem u2_rkOneQ_zero_mulVec {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (t : K) (w : HypIndex 1 1 → K) :
    rkOneQ h 0 t *ᵥ w = w + (t * w (.inr (.inr 0))) • rkVec 1 0 0 := by
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z : K, w = rkVec x y z := ⟨_, _, _, rkVec_eta w⟩
  rw [rkOneQ_mulVec, rkVec_inr_inr, rkVec_smul, rkVec_add]
  simp

private theorem u2_transport_rkOneQ {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {Rm : Matrix (Fin (2 * 1 + 1)) (HypIndex 1 1) K} (hR : IsHypTransport h Rm) {t : K}
    (ht : h.norm 0 + h.trace t = 0) :
    mulVecLin (((hypTransport h hR (rkOneQElt h 0 t ht) : unitarySU p f K (2 * 1 + 1)) :
        GL (Fin (2 * 1 + 1)) K) : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K) =
      hermTransvection (stdHermForm h (2 * 1 + 1)) (Rm *ᵥ rkVec 1 0 0) t := by
  refine LinearMap.ext fun y => ?_
  rw [mulVecLin_apply, coe_hypTransport, coe_rkOneQElt, ← mulVec_mulVec, ← mulVec_mulVec]
  set w := transportInv h Rm *ᵥ y with hw
  have hy : Rm *ᵥ w = y := by rw [hw, mulVec_mulVec, mul_transportInv hR, one_mulVec]
  rw [u2_rkOneQ_zero_mulVec, mulVec_add, mulVec_smul, hy, hermTransvection_apply]
  congr 2
  rw [← hy, stdHermForm_transport hR, ← single_inl_eq_rkVec, hypForm_single_inl]

private theorem u2_point {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {Rm : Matrix (Fin (2 * 1 + 1)) (HypIndex 1 1) K} (hR : IsHypTransport h Rm) :
    transportSubspace h hR (Submodule.span K {rkVec (1 : K) 0 0}) ∈ isotropicLines h (2 * 1 + 1) ∧
      Rm *ᵥ rkVec (1 : K) 0 0 ∈ transportSubspace h hR (Submodule.span K {rkVec (1 : K) 0 0}) ∧
      Rm *ᵥ rkVec (1 : K) 0 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · refine (transportSubspace_mem_isotropicLines hR _).mpr ?_
    have hinf := (infL h).2
    rwa [coe_infL] at hinf
  · rw [transportSubspace_apply]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  · intro h0
    have h1 : rkVec (1 : K) 0 0 = 0 := by
      have := congrArg (fun v => transportInv h Rm *ᵥ v) h0
      simpa [mulVec_mulVec, transportInv_mul hR] using this
    exact one_ne_zero (rkVec_eq_zero_iff.mp h1).1

private theorem u2_fix {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {Rm : Matrix (Fin (2 * 1 + 1)) (HypIndex 1 1) K} (hR : IsHypTransport h Rm)
    {g : hypSU h 1 1} (hg : g ∈ hypUnitriangular h 1 1) :
    hypTransport h hR g • transportSubspace h hR (Submodule.span K {rkVec (1 : K) 0 0}) =
      transportSubspace h hR (Submodule.span K {rkVec (1 : K) 0 0}) := by
  rw [← transportSubspace_smul hR g]
  congr 1
  obtain ⟨a, b, hab, rfl⟩ := exists_eq_rkOneQElt h hg
  refine (gl_smul_span (K := K) (ι := HypIndex 1 1)
    ((rkOneQElt h a b hab : hypSU h 1 1) : GL (HypIndex 1 1) K) (rkVec 1 0 0)).trans ?_
  change Submodule.span K {rkOneQ h a b *ᵥ rkVec (1 : K) 0 0} = _
  rw [rkOneQ_mulVec]
  simp

end Transport

section Std

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups Matrix

private theorem u2_center_map {H G : Type*} [Group H] [Group G] (e : H ≃* G) (U : Subgroup H) :
    (center ↥(U.map (e : H →* G))).map (U.map (e : H →* G)).subtype =
      ((center ↥U).map U.subtype).map (e : H →* G) := by
  rw [← Subgroup.map_center_eq (e.subgroupMap U), Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem u2_std (hF' : UnitaryFieldData 2 m F') :
    ∃ (P : Sylow 2 ↥(unitarySU 2 m F' 3)) (L : Submodule F' (Fin 3 → F')),
      L ∈ isotropicLines hF' 3 ∧
      (center ↥(P : Subgroup ↥(unitarySU 2 m F' 3))).map
          (P : Subgroup ↥(unitarySU 2 m F' 3)).subtype = isotropicTransvectionGroup hF' 3 L ∧
        ∀ g ∈ (P : Subgroup ↥(unitarySU 2 m F' 3)), g • L = L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Rm, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hF'
  let Φ : hypSU hF' 1 1 ≃* unitarySU 2 m F' (2 * 1 + 1) := hypTransport hF' hR
  obtain ⟨-, ⟨P0, hP0⟩, -⟩ := unitary_order_and_Sylow hF' (r := 1) (ε := 1) le_rfl le_rfl
  obtain ⟨hL₁, ha₁L, ha₁0⟩ := u2_point hR
  refine ⟨Sylow.mapSurjective (f := (Φ : hypSU hF' 1 1 →* unitarySU 2 m F' (2 * 1 + 1)))
      Φ.surjective P0, transportSubspace hF' hR (Submodule.span F' {rkVec (1 : F') 0 0}),
    hL₁, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective, hP0, u2_center_map Φ, u2_center_eq_range,
      MonoidHom.map_range]
    rw [← (unitary_point_subgroup hF' hL₁ ha₁L ha₁0).2.2.1]
    congr 1
    refine MonoidHom.ext fun c => unitarySU_ext_mulVecLin ?_
    rw [mulVecLin_ptTransvectionHom]
    exact u2_transport_rkOneQ hR (norm_zero_add_trace c.toAdd.2)
  · intro g hg
    rw [Sylow.coe_mapSurjective, hP0] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact u2_fix hR hx

private theorem u2_conj (hF' : UnitaryFieldData 2 m F') (γ : ↥(unitarySU 2 m F' 3))
    (P : Subgroup ↥(unitarySU 2 m F' 3))
    (hP : ∃ L : Submodule F' (Fin 3 → F'), L ∈ isotropicLines hF' 3 ∧
      (center ↥P).map P.subtype = isotropicTransvectionGroup hF' 3 L ∧ ∀ g ∈ P, g • L = L) :
    ∃ L : Submodule F' (Fin 3 → F'), L ∈ isotropicLines hF' 3 ∧
      (center ↥(MulAut.conj γ • P)).map (MulAut.conj γ • P).subtype =
        isotropicTransvectionGroup hF' 3 L ∧ ∀ g ∈ MulAut.conj γ • P, g • L = L := by
  obtain ⟨L, hL, hZ, hfix⟩ := hP
  have hsmul : MulAut.conj γ • P = P.map (MulAut.conj γ : ↥(unitarySU 2 m F' 3) →* _) := rfl
  refine ⟨γ • L, (isotropicLines hF' 3).smul_mem γ hL, ?_, ?_⟩
  · rw [hsmul, u2_center_map (MulAut.conj γ) P, hZ]
    exact (unitary_point_conjugation hF' γ hL).2.1
  · intro g hg
    rw [hsmul] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    change (γ * x * γ⁻¹) • γ • L = γ • L
    rw [mul_smul, mul_smul, inv_smul_smul, hfix x hx]

end Std

theorem model3_unitary_center_eq_point (hF' : UnitaryFieldData 2 m F')
    (R : Sylow 2 ↥(unitarySU 2 m F' 3)) :
    ∃ L ∈ isotropicLines hF' 3,
      (center ↥(R : Subgroup ↥(unitarySU 2 m F' 3))).map
          (R : Subgroup ↥(unitarySU 2 m F' 3)).subtype = isotropicTransvectionGroup hF' 3 L ∧
        ∀ g ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)), g • L = L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite F' := hF'.finite
  haveI : Finite ↥(unitarySU 2 m F' 3) := inferInstance
  haveI : Finite (Sylow 2 ↥(unitarySU 2 m F' 3)) := inferInstance
  obtain ⟨P, L, hL, hZ, hfix⟩ := u2_std hF'
  obtain ⟨γ, rfl⟩ := MulAction.exists_smul_eq ↥(unitarySU 2 m F' 3) P R
  obtain ⟨L', hL', h1, h2⟩ := u2_conj hF' γ (P : Subgroup _) ⟨L, hL, hZ, hfix⟩
  exact ⟨L', hL', h1, h2⟩

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
