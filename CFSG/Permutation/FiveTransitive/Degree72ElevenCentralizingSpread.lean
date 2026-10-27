module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenCentralizingSpread
open MulAction

private theorem fixes_preserved_orbit
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hcomm : ∀ q : Q, g.val * q.val = q.val * g.val)
    (x : X) (hOx : Nat.card (orbit Q x) = 11) (hx : g.val • x ∈ orbit Q x)
    (y : X) (hy : y ∈ orbit Q x) : g.val • y = y := by
  classical
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' x) = Quotient.mk'' x :=
    Quotient.sound hx
  obtain ⟨z,hz,hgz⟩ := NormalizerOrbitFamily.exists_fixed_of_preserved Q g hg
    (Quotient.mk'' x) hpres (by rw [orbitRel.Quotient.orbit_mk,hOx]; decide)
  rw [orbitRel.Quotient.orbit_mk] at hz
  obtain ⟨r,hr⟩ := mem_orbit_iff.mp hz
  have hfixx : g.val • x = x := by
    have he : r.val • (g.val • x) = r.val • x := by
      rw [← mul_smul,← hcomm r,mul_smul]
      change g.val • (r • x) = r • x
      rwa [hr]
    simpa only [inv_smul_smul] using congrArg (fun w : X => r.val⁻¹ • w) he
  obtain ⟨q,hq⟩ := mem_orbit_iff.mp hy
  rw [← hq]
  change g.val • (q.val • x) = q.val • x
  rw [← mul_smul,hcomm q,mul_smul,hfixx]

theorem exists_fixed_spread
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (Q : Subgroup G) [IsMulCommutative Q]
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 5)
    (hcomm : ∀ q : Q, g.val * q.val = q.val * g.val)
    (x : X) (hx : g.val • x ≠ x) (hOx : Nat.card (orbit Q x) = 11) :
    ∃ D : Set X, D.ncard = 55 ∧ Disjoint (fixedPoints Q X) D ∧
      ∀ r : stabilizer Q x, ∀ y ∈ D, r • y = y := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := Subgroup.normalizer (Q : Set G)
  let Y := orbitRel.Quotient Q X
  let _ : MulAction N Y := NormalizerOrbitHom.action Q
  let A := Subgroup.zpowers g
  let O : Y := Quotient.mk'' x
  let T : Set Y := orbit A O
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,hg]; norm_num)
  have hAc : Nat.card A = 5 := by rw [Nat.card_zpowers,hg]
  have hTc : Nat.card T = 5 := by
    have hd := (stabilizer A O).index_dvd_card
    rw [index_stabilizer,← Nat.card_coe_set_eq,hAc] at hd
    rcases (show Nat.Prime 5 by decide).eq_one_or_self_of_dvd _ hd with he | he
    · have hf : O ∈ fixedPoints A Y := mem_fixedPoints_iff_card_orbit_eq_one.mpr
        (by rwa [← Nat.card_eq_fintype_card])
      have hpres := hf (⟨g,Subgroup.mem_zpowers g⟩ : A)
      have hgx : g.val • x ∈ orbit Q x := by
        apply Quotient.exact (s := orbitRel Q X)
        exact hpres
      exact (hx (fixes_preserved_orbit Q g (hg ▸ pow_orderOf_eq_one g)
        hcomm x hOx hgx x (mem_orbit_self x))).elim
    · exact he
  have hsize (t : T) : Nat.card t.val.orbit = 11 := by
    obtain ⟨a,ha⟩ := mem_orbit_iff.mp t.property
    rw [← ha]
    change Nat.card ((NormalizerOrbitHom.toPermHom (Y := X) Q a.val O).orbit) = 11
    rw [NormalizerLargeOrbit.card_orbit_eq]
    exact hOx
  let D : Set X := {y | (Quotient.mk'' y : Y) ∈ T}
  have hDc : D.ncard = 55 := by
    have he := Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype
      (fun y : X => (Quotient.mk'' y : Y)) (fun _ => Iff.rfl (a := _ ∈ T)))
    let _ : Fintype T := Fintype.ofFinite T
    have hfiber (t : T) : Nat.card {y : X // (Quotient.mk'' y : Y) = t.val} = 11 := by
      let e : {y : X // (Quotient.mk'' y : Y) = t.val} ≃ t.val.orbit :=
        { toFun := fun y => ⟨y.val,orbitRel.Quotient.mem_orbit.mpr y.property⟩
          invFun := fun y => ⟨y.val,orbitRel.Quotient.mem_orbit.mp y.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr e,hsize t]
    change Nat.card {y : X // (Quotient.mk'' y : Y) ∈ T} = 55
    rw [← he,Nat.card_sigma]
    simp_rw [hfiber]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,← Nat.card_eq_fintype_card,hTc]
  have hcommA (a : A) (q : Q) : a.val.val * q.val = q.val * a.val.val := by
    have hle : A ≤ (Subgroup.centralizer (Q : Set G)).comap N.subtype := by
      apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_centralizer_iff.mpr (fun q hq => (hcomm ⟨q,hq⟩).symm)
    exact (Subgroup.mem_centralizer_iff.mp (hle a.property) q.val q.property).symm
  refine ⟨D,hDc,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro y hy hyD
    have hs := hsize ⟨Quotient.mk'' y,hyD⟩
    rw [orbitRel.Quotient.orbit_mk] at hs
    have h1 := mem_fixedPoints_iff_card_orbit_eq_one.mp hy
    rw [← Nat.card_eq_fintype_card,hs] at h1
    omega
  · intro r y hy
    obtain ⟨a,ha⟩ := mem_orbit_iff.mp hy
    have hyo : y ∈ orbit Q (a.val.val • x) := by
      apply Quotient.exact (s := orbitRel Q X)
      exact ha.symm
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp hyo
    rw [← hq]
    change r.val • (q • (a.val.val • x)) = q • (a.val.val • x)
    rw [← mul_smul,mul_comm' r.val q,mul_smul]
    congr 1
    change r.val.val • (a.val.val • x) = a.val.val • x
    rw [← mul_smul,← hcommA a r.val,mul_smul]
    exact congrArg (fun z => a.val.val • z) r.property

end FiveTransitive.Degree72ElevenCentralizingSpread

end CFSG
