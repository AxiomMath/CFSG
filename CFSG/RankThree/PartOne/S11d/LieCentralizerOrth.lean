module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerGL
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedCoverage
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Polynomial Module CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

theorem two_le_mult_of_involution_ne_one {K : Type} [Field K] (h2 : (2 : K) = 0) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {x : LinearMap.GeneralLinearGroup K V}
    (hsq : Squarefree (minpoly K (x : Module.End K V))) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ gl_centralizer x) (hg2 : g ^ 2 = 1) (b : primaryFactors (x : Module.End K V))
    (hgb : ∃ v ∈ primaryComponent (x : Module.End K V) (b : K[X]),
      (g : Module.End K V) v ≠ v) :
    2 ≤ primaryMultiplicity (x : Module.End K V) (b : K[X]) := by
  by_contra hno
  push Not at hno
  set w := glCentralizerEquivPi hsq ⟨g, hg⟩ with hw
  have hw2 : w ^ 2 = 1 := by
    rw [hw, ← map_pow]
    have : (⟨g, hg⟩ : gl_centralizer x) ^ 2 = 1 := Subtype.ext hg2
    rw [this, map_one]
  have h2b : (2 : AdjoinRoot (b : K[X])) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot (b : K[X]))) 2, h2, map_zero]
  have hwb : w b = 1 := eq_one_of_sq_eq_one_of_finrank_lt_two h2b hno (w b) (congrFun hw2 b)
  obtain ⟨v, hv, hgv⟩ := hgb
  apply hgv
  have := blockApply_glCentralizerEquivPi hsq ⟨g, hg⟩ b v hv
  rw [← hw, hwb, blockApply_one] at this
  exact this.symm

theorem eq_one_of_mem_scalars_of_mem_orthDerived {K : Type*} [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V] {g : V ≃ₗ[K] V}
    (hg : g ∈ orthDerived Q) (hs : g ∈ scalars K V) : g = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  obtain ⟨v, hv⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hg
  have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v
  rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hcc : c * c = 1 := by
    have := mul_right_cancel₀ hv (show c * c * Q v = 1 * Q v by rw [one_mul]; exact h1)
    exact this
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hc1 : c = 1 := by
    have h8 : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c * c - 1 - 2 * (c - 1) := by ring
      rw [this, hcc, h2]
      ring
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
  exact LinearEquiv.ext fun u => by rw [hc, hc1, one_smul]; rfl

open scoped _root_.Classical in
theorem orth_centralizer_component {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hK : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {a b : ProjOrthDerived Q} (ha : a ^ p = 1) (ha1 : a ≠ 1)
    (hb : b ^ 2 = 1) (hb1 : b ≠ 1) (hab : a * b = b * a) :
    ∃ D : Subgroup (ProjOrthDerived Q), CFSG.IsQuasisimple ↥D ∧
      D ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
      (D.subgroupOf (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hp3 : 3 < p := by omega
  have hpl : p ≠ ringChar K := by rw [ringChar.eq K 2]; omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((scalars K V).subgroupOf (orthDerived Q)) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((scalars K V).subgroupOf (orthDerived Q)) b
  have hx1 : x ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hx1 (Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _))
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgs := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g).mp hg)
    exact Subtype.ext (eq_one_of_mem_scalars_of_mem_orthDerived hQ g.2 hgs)
  have hxp : x ^ p = 1 := hinj (by rw [map_pow, map_one]; exact ha)
  have hy2 : y ^ 2 = 1 := hinj (by rw [map_pow, map_one]; exact hb)
  have hy1 : y ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have hxy : x * y = y * x := hinj (by rw [map_mul, map_mul]; exact hab)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  set x' : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hx'
  set y' : V ≃ₗ[K] V := (y : V ≃ₗ[K] V) with hy'
  have hox : OddOrderIsometry Q p x' := oddOrderIsometry_of_orthDerived hp hpl hQ x hxo
  have hyx : y' * x' = x' * y' := congrArg Subtype.val hxy.symm
  have hy'2 : y' ^ 2 = 1 := congrArg Subtype.val hy2
  have hy'1 : y' ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hE1 : centralizerImage Q x' = Subgroup.centralizer
      ({QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x} :
        Set (ProjOrthDerived Q)) := by
    rw [← map_centralizer_eq_centralizerImage x]
    ext t
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
    · intro ht
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ t
      refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (hinj ?_), rfl⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp ht
  by_cases hout : ∃ h ∈ primaryFactors x'.toLinearMap, h ≠ X - 1 ∧
      ∃ v ∈ primaryComponent x'.toLinearMap h, y' v ≠ v
  ·
    obtain ⟨h, hh, hne1, v, hv, hyv⟩ := hout
    have hm : 2 ≤ primaryMultiplicity x'.toLinearMap h := by
      let e := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
      set x'' : LinearMap.GeneralLinearGroup K V := e.symm x' with hx''
      set y'' : LinearMap.GeneralLinearGroup K V := e.symm y' with hy''
      have hsq : Squarefree (minpoly K (x'' : Module.End K V)) := hox.squarefree_minpoly
      have hg : y'' ∈ gl_centralizer x'' := by
        refine Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext (LinearMap.ext fun w => ?_))
        exact congrArg (fun f : V ≃ₗ[K] V => f w) hyx
      have hg2 : y'' ^ 2 = 1 := e.injective (by
        rw [map_pow, MulEquiv.apply_symm_apply, map_one]
        exact hy'2)
      exact two_le_mult_of_involution_ne_one h2 hsq hg hg2 ⟨h, hh⟩ ⟨v, hv, hyv⟩
    have hsb := hox.specialBlock_le_orthDerived hp hp3 hh hne1 hm
    have hq' := hox.quasisimple_specialBlock hp hp3 hh hne1 hm
    refine ⟨componentImage Q x' h, isQuasisimple_map_projective hsb hq', ?_, ?_⟩
    · rw [← hE1]
      exact componentImage_le_centralizerImage
    · have := (normal_componentImage (Q := Q) (x := x') (h := h)).isSubnormal
      rwa [hE1] at this
  ·
    push Not at hout
    obtain ⟨hc, horth⟩ := hox.fixed_others
    have hR : ∀ r ∈ othersSpace x'.toLinearMap (X - 1), y' r = r := by
      intro r hr
      unfold othersSpace at hr
      refine Submodule.iSup_induction _ (motive := fun r => y' r = r) hr (fun k r hr => ?_)
        (by simp) (fun a b ha hb => by rw [map_add, ha, hb])
      refine Submodule.iSup_induction _ (motive := fun r => y' r = r) hr (fun hk r hr => ?_)
        (by simp) (fun a b ha hb => by rw [map_add, ha, hb])
      exact hout k hk.1 hk.2.1 r hr
    have hW : ∀ w ∈ fixedSpace x', y' w ∈ fixedSpace x' := by
      intro w hw
      rw [mem_fixedSpace] at hw ⊢
      have := congrArg (fun f : V ≃ₗ[K] V => f w) hyx
      simp only [LinearEquiv.mul_apply] at this
      rw [hw] at this
      exact this.symm
    set c := CFSG.RankThree.OrthogonalInvolutions.commSpace y' with hcdef
    have hyy : ∀ v, y' (y' v) = v := fun v => by
      have := congrArg (fun f : V ≃ₗ[K] V => f v) hy'2
      simpa [pow_two] using this
    have hfix : ∀ v, y' (y' v - v) = y' v - v := by
      intro v
      rw [map_sub, hyy v]
      have h0 : y' v - v + (y' v - v) = 0 := by
        rw [← two_smul K (y' v - v), h2, zero_smul]
      calc v - y' v = -(y' v - v) := by abel
        _ = y' v - v := by rw [neg_eq_iff_add_eq_zero]; exact h0
    have hcW : c ≤ fixedSpace x' := by
      intro u hu
      obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hu
      obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
      rw [map_add, hR r hr]
      have : y' w + r - (w + r) = y' w - w := by abel
      rw [this]
      exact sub_mem (hW w hw) hw
    have hcker : ∀ u ∈ c, y' u = u := by
      intro u hu
      obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hu
      exact hfix v
    obtain ⟨w₀, hw₀, hmove⟩ : ∃ w₀ ∈ fixedSpace x', y' w₀ ≠ w₀ := by
      obtain ⟨v, hv⟩ : ∃ v, y' v ≠ v := by
        by_contra hcon
        push Not at hcon
        exact hy'1 (LinearEquiv.ext hcon)
      obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
      refine ⟨w, hw, fun hwe => hv ?_⟩
      rw [map_add, hR r hr, hwe]
    have heven : Even (finrank K c) := by
      have hd := dicksonHom_apply_orthDerived_eq_one hQ y.2
      simp only [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply, ofAdd_eq_one] at hd
      exact (ZMod.natCast_eq_zero_iff_even).mp hd
    have hc1 : 1 ≤ finrank K c := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hbot
      have : y' w₀ - w₀ ∈ c := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr ⟨w₀, rfl⟩
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
      exact hmove this
    have hc2 : 2 ≤ finrank K c := by
      obtain ⟨k, hk⟩ := heven
      omega
    have hlt : c < fixedSpace x' := by
      refine lt_of_le_of_ne hcW fun heq => hmove ?_
      exact hcker w₀ (heq ▸ hw₀)
    have h3 : 3 ≤ finrank K (fixedSpace x') := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x').subtype) := by
      rintro (⟨-, h3'⟩ | ⟨-, h23⟩) <;> omega
    have hcov := (orthogonal_regular_space_coverage (Q.comp (fixedSpace x').subtype)
      hox.polarBilin_fixed_nondegenerate h3).2 hnexc
    obtain ⟨n, C, hn1, hn2, hsup, hC, hcomm, hq⟩ := hox.exists_fixedLayer_components hcov
    refine ⟨C ⟨0, hn1⟩, (hC _).1, ?_, ?_⟩
    · rw [← hE1]
      exact (hC _).2.1
    · have := (hC ⟨0, hn1⟩).2.2
      rwa [hE1] at this

end CFSG.RankThree.PartOne
