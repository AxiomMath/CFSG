module

public import CFSG.Permutation.FiveTransitive.Degree54TwoOrbitRestriction
public import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitPreserved
public import CFSG.Permutation.FiveTransitive.ThirtyTwoTwoGroupBound
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation
public import CFSG.Permutation.FiveTransitive.NormalizerExteriorOrbitFamilyFive

public section

namespace CFSG

namespace FiveTransitive.Degree54ThirtyTwoKernel
open MulAction NormalizerOrbitFamily

theorem card_le_thirty_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hQfixed : Nat.card (fixedPoints Q X) = 6)
    (g : Subgroup.normalizer (Q : Set P)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card {z : X // z ∉ fixedPoints Q X ∧ g.val • z = z} = 3)
    (x y : X) (hx : Nat.card (orbit Q x) = 16) (hy : Nat.card (orbit Q y) = 32) :
    Nat.card (toPermHom Q (orbit Q x)).ker ≤ 32 := by
  classical
  have hX : Nat.card X = 54 := by rwa [Nat.card_eq_fintype_card]
  let Y : Family (X := X) Q 32 := ⟨Quotient.mk'' y,by
    simpa only [orbitRel.Quotient.orbit_mk] using hy⟩
  have hsmall : Nat.card (Family (X := X) Q 32) ≤ 4 := by
    have hb := card_mul_le (X := X) Q 32
    omega
  have hpres := NormalizerExteriorOrbitFamilyFive.five_fixes_family Q 32 hsmall g hg Y
  change NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' y) = Quotient.mk'' y at hpres
  let O := orbit Q y
  let rho := toPermHom Q O
  let R := rho.range
  have hR : IsPGroup 2 R := hQ.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have htrans : IsPretransitive R O := by
    constructor
    intro u v
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp u.property
    obtain ⟨r,hr⟩ := mem_orbit_iff.mp v.property
    refine ⟨⟨rho (r * q⁻¹),⟨r * q⁻¹,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change (r * q⁻¹) • u.val = v.val
    rw [mul_smul,← hq,inv_smul_smul,hr]
  let p := NormalizerOrbitHom.toPermHom (Y := X) Q g
  have hpx : p (Quotient.mk'' y) = Quotient.mk'' y := hpres
  have hstable (w : X) : g.val • w ∈ O ↔ w ∈ O := by
    constructor
    · intro hw
      have hh : p (Quotient.mk'' w) = Quotient.mk'' y := Quotient.sound hw
      exact Quotient.exact (p.injective (hh.trans hpx.symm))
    · intro hw
      have hh : (Quotient.mk'' w : orbitRel.Quotient Q X) = Quotient.mk'' y :=
        Quotient.sound hw
      exact Quotient.exact (show (Quotient.mk'' (g.val • w) : orbitRel.Quotient Q X) =
        Quotient.mk'' y from (congrArg p hh).trans hpx)
  let a : Equiv.Perm O :=
    { toFun := fun u => ⟨g.val • u.val,(hstable u.val).mpr u.property⟩
      invFun := fun u => ⟨g.val⁻¹ • u.val,(hstable (g.val⁻¹ • u.val)).mp (by
        simpa only [smul_inv_smul] using (show u.val ∈ O from u.property))⟩
      left_inv := fun u => Subtype.ext (inv_smul_smul g.val u.val)
      right_inv := fun u => Subtype.ext (smul_inv_smul g.val u.val) }
  have hapow (n : ℕ) (u : O) : ((a ^ n) u).val = g.val ^ n • u.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      change g.val • ((a ^ n) u).val = _
      rw [ih,pow_succ',mul_smul]
  have ha5 : a ^ 5 = 1 := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    rw [hapow,← Subgroup.coe_pow,hg,Subgroup.coe_one,one_smul]
    rfl
  let e : MulAut Q := Q.normalizerMonoidHom g
  have hconj (q : Q) : a * rho q * a⁻¹ = rho (e q) := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    change g.val • (q.val • (g.val⁻¹ • u.val)) = (g.val * q.val * g.val⁻¹) • u.val
    simp only [mul_smul]
  have haN : a ∈ Subgroup.normalizer (R : Set (Equiv.Perm O)) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro b
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨e q,(hconj q).symm⟩
    · rintro ⟨q,hq⟩
      refine ⟨e.symm q,?_⟩
      have hh : a * rho (e.symm q) * a⁻¹ = a * b * a⁻¹ := by
        rw [hconj,e.apply_symm_apply]
        exact hq
      exact mul_left_cancel (mul_right_cancel hh)
  let _ : Fintype O := Fintype.ofFinite _
  have hle : Nat.card {z : O // g.val • z.val = z.val} ≤ 3 := by
    rw [← hfixed]
    let f : {z : O // g.val • z.val = z.val} →
        {z : X // z ∉ fixedPoints Q X ∧ g.val • z = z} := fun z =>
      ⟨z.val.val,Degree52TwoOrbitPreserved.not_fixed_of_mem Q (Quotient.mk'' y)
        (by rw [orbitRel.Quotient.orbit_mk,hy]; decide) z.val.val z.val.property,z.property⟩
    exact Nat.card_le_card_of_injective f (fun u v h =>
      Subtype.ext (Subtype.ext (congrArg (fun t => t.val) h)))
  have hc := Degree54TwoOrbitRestriction.fixed_card_cases hX.le Q hQ g hg y
    (by omega) hpres hle
  have htwo : Nat.card {z : O // g.val • z.val = z.val} = 2 := by
    change Nat.card {z : orbit Q y // g.val • z.val = z.val} = 2
    omega
  let E : Function.fixedPoints a ≃ {z : O // g.val • z.val = z.val} :=
    { toFun := fun z => ⟨z.val,congrArg Subtype.val z.property⟩
      invFun := fun z => ⟨z.val,Subtype.ext z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have haFixed : Nat.card (Function.fixedPoints a) = 2 := (Nat.card_congr E).trans htwo
  let K := (toPermHom Q (orbit Q x)).ker
  let j : K →* Equiv.Perm O := rho.comp K.subtype
  have hmin_global (q : Q) (hq : q ≠ 1) : Nat.card (Function.fixedPoints q.val.val) ≤ 27 := by
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
      q.val.property hne
    rw [hcard] at hb
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.val.sum_cycleType,hcard]
    omega
  have hinj : Function.Injective j := by
    apply (injective_iff_map_eq_one _).mpr
    intro k hk
    by_contra hn
    have hb := hmin_global k.val (fun he => hn (Subtype.ext he))
    have hsub : O ⊆ Function.fixedPoints k.val.val.val := by
      intro z hz
      exact congrArg (fun t : O => t.val) (DFunLike.congr_fun hk ⟨z,hz⟩)
    have hl := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at hl
    change Nat.card (orbit Q y) ≤ _ at hl
    omega
  have hdis (z : X) (hz : Nat.card (orbit Q z) ≠ 1) :
      Disjoint (fixedPoints Q X) (orbit Q z) := by
    apply Set.disjoint_left.mpr
    intro w hw hwO
    have he : orbit Q w = orbit Q z := orbit_eq_iff.mpr hwO
    have h1 : Nat.card (orbit Q w) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hw
    exact hz (he ▸ h1)
  have hxy : Disjoint (orbit Q x) O := by
    apply AbelianOrbitEvaluation.orbit_disjoint_of_notMem x y
    intro hmem
    have he : orbit Q y = orbit Q x := orbit_eq_iff.mpr hmem
    rw [he,hx] at hy
    omega
  have hmin : ∀ k : j.range, k ≠ 1 → 27 ≤ k.val.support.card := by
    rintro ⟨k,⟨q,rfl⟩⟩ hk
    have hq : q.val ≠ 1 := by
      intro he
      have hq1 : q = 1 := Subtype.ext he
      subst q
      exact hk (Subtype.ext (map_one j))
    let T : Set X := {z | z ∈ O ∧ q.val.val.val z = z}
    let et : Function.fixedPoints (j q) ≃ T :=
      { toFun := fun z => ⟨z.val.val,z.val.property,congrArg Subtype.val z.property⟩
        invFun := fun z => ⟨⟨z.val,z.property.1⟩,Subtype.ext z.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hsub : (fixedPoints Q X ∪ orbit Q x) ∪ T ⊆ Function.fixedPoints q.val.val.val := by
      intro z hz
      rcases hz with (hz | hz) | hz
      · exact hz q.val
      · exact congrArg (fun t : orbit Q x => t.val) (DFunLike.congr_fun q.property ⟨z,hz⟩)
      · exact hz.2
    have hd : Disjoint (fixedPoints Q X ∪ orbit Q x) T := by
      apply Set.disjoint_left.mpr
      intro z hz ht
      rcases hz with hz | hz
      · exact Set.disjoint_left.mp (hdis y (by omega)) hz ht.1
      · exact Set.disjoint_left.mp hxy hz ht.1
    have hl := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hd,Set.ncard_union_eq (hdis x (by omega)),
      ← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq,hQfixed,hx,← Nat.card_congr et] at hl
    have hb := hmin_global q.val hq
    have hlocal : Nat.card (Function.fixedPoints (j q)) ≤ 5 := by omega
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,
      (j q).sum_cycleType,← Nat.card_eq_fintype_card] at hlocal
    change Nat.card (orbit Q y) - (j q).support.card ≤ 5 at hlocal
    change 27 ≤ (j q).support.card
    omega
  have hb := ThirtyTwoTwoGroupBound.card_le_thirty_two hy R hR htrans ⟨a,haN⟩
    (Subtype.ext ha5) haFixed j.range (by rintro _ ⟨q,rfl⟩; exact ⟨q.val,rfl⟩) hmin
  exact (Nat.card_le_card_of_injective j.rangeRestrict (fun u v he =>
    hinj (congrArg Subtype.val he))).trans hb

end FiveTransitive.Degree54ThirtyTwoKernel

end CFSG
