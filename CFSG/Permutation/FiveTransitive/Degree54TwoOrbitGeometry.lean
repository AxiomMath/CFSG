module

public import CFSG.Permutation.FiveTransitive.Degree54TwoOrbitCount
public import CFSG.Permutation.FiveTransitive.Degree54TwoSixteenWitness
public import CFSG.Permutation.FiveTransitive.NormalizerExteriorOrbitFamilyFive

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoOrbitGeometry

open MulAction NormalizerOrbitFamily

private theorem preserved_sizes
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 54) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} = 3)
    (O : orbitRel.Quotient Q X) (hO : Nat.card O.orbit ≠ 1)
    (hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O) :
    Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 16 ∨ Nat.card O.orbit = 32 := by
  revert hO hpres
  refine Quotient.inductionOn O ?_
  intro x hO hpres
  rw [orbitRel.Quotient.orbit_mk] at hO ⊢
  let f : {y : orbit Q x // g.val • y.val = y.val} →
      {y : X // y ∉ fixedPoints Q X ∧ g.val • y = y} := fun y =>
    ⟨y.val.val,Degree52TwoOrbitPreserved.not_fixed_of_mem Q (Quotient.mk'' x)
      (by rwa [orbitRel.Quotient.orbit_mk]) y.val.val
      (by simpa only [orbitRel.Quotient.orbit_mk] using y.val.property),y.property⟩
  have hf : Function.Injective f := by
    intro y z he
    have hv := congrArg (fun t : {y : X // y ∉ fixedPoints Q X ∧ g.val • y = y} => t.val) he
    exact Subtype.ext (Subtype.ext hv)
  have hle : Nat.card {y : orbit Q x // g.val • y.val = y.val} ≤ 3 := by
    rw [← hfixed]
    exact Nat.card_le_card_of_injective f hf
  have hc := Degree54TwoOrbitRestriction.fixed_card_cases hX Q hQ g hg x hO hpres hle
  tauto

theorem orbit_sizes
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 54) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQfixed : Nat.card (fixedPoints Q X) = 6)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} = 3) :
    ∀ O : orbitRel.Quotient Q X, Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨
      Nat.card O.orbit = 4 ∨ Nat.card O.orbit = 16 ∨ Nat.card O.orbit = 32 := by
  obtain ⟨x,_,_,h16,_⟩ := Degree54TwoSixteenWitness.exists_sixteen hX.le Q hQ g hg hfixed
  have h16pos : 0 < Nat.card (Family (X := X) Q 16) := Finite.card_pos_iff.mpr
    ⟨⟨Quotient.mk'' x,by simpa only [orbitRel.Quotient.orbit_mk] using h16⟩⟩
  have h8div : 5 ∣ Nat.card (Family (X := X) Q 8) := by
    apply Degree52TwoOrbitPreserved.five_dvd_family_of_not_preserved Q g hg 8
    intro O hp
    have hc := preserved_sizes hX.le Q hQ g hg hfixed O.val
      (by rw [O.property]; decide) hp
    rw [O.property] at hc
    omega
  have htotal := Degree54TwoOrbitCount.card_eq_orbit_sum hX.le Q hQ
  rw [hX,hQfixed] at htotal
  have h8 : Nat.card (Family (X := X) Q 8) = 0 := by omega
  intro O
  have hnot8 : Nat.card O.orbit ≠ 8 := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q 8) := Finite.card_pos_iff.mpr ⟨⟨O,he⟩⟩
    omega
  have hc := Degree54TwoOrbitPreserved.orbit_card_cases hX.le Q hQ O
  omega

theorem image_card_sixteen
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 54) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} = 3)
    (x : X) (hO : Nat.card (orbit Q x) = 16) :
    Nat.card (toPermHom Q (orbit Q x)).range = 16 := by
  classical
  let O : Family (X := X) Q 16 := ⟨Quotient.mk'' x,by
    simpa only [orbitRel.Quotient.orbit_mk] using hO⟩
  have hsmall : Nat.card (Family (X := X) Q 16) ≤ 4 := by
    have hb := card_mul_le (X := X) Q 16
    omega
  have hp := NormalizerExteriorOrbitFamilyFive.five_fixes_family Q 16 hsmall g hg O
  obtain ⟨y,hy,hgy⟩ := exists_fixed_of_preserved Q g hg O.val hp (by rw [O.property]; decide)
  have hyO : y ∈ orbit Q x := by
    change y ∈ orbitRel.Quotient.orbit (Quotient.mk'' x : orbitRel.Quotient Q X) at hy
    simpa only [orbitRel.Quotient.orbit_mk] using hy
  have he : orbit Q y = orbit Q x := orbit_eq_iff.mpr hyO
  have hy16 : Nat.card (orbit Q y) = 16 := he ▸ hO
  have hp' : NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' y) =
      Quotient.mk'' y := by
    change Quotient.mk'' (g.val • y) = Quotient.mk'' y
    rw [hgy]
  let f : {z : orbit Q y // g.val • z.val = z.val} →
      {z : X // z ∉ fixedPoints Q X ∧ g.val • z = z} := fun z =>
    ⟨z.val.val,Degree52TwoOrbitPreserved.not_fixed_of_mem Q (Quotient.mk'' y)
      (by rw [orbitRel.Quotient.orbit_mk,hy16]; decide) z.val.val
      (by simpa only [orbitRel.Quotient.orbit_mk] using z.val.property),z.property⟩
  have hle : Nat.card {z : orbit Q y // g.val • z.val = z.val} ≤ 3 := by
    rw [← hfixed]
    apply Nat.card_le_card_of_injective f
    intro z w hh
    have hv := congrArg (fun t : {z : X // z ∉ fixedPoints Q X ∧ g.val • z = z} => t.val) hh
    exact Subtype.ext (Subtype.ext hv)
  have hc := Degree54TwoOrbitRestriction.fixed_card_cases hX Q hQ g hg y
    (by omega) hp' hle
  have hc1 : Nat.card {z : orbit Q y // g.val • z.val = z.val} = 1 := by omega
  have hsub : Subsingleton {z : orbit Q y // g.val • z.val = z.val} :=
    Finite.card_le_one_iff_subsingleton.mp hc1.le
  have hunique (z : X) (hz : z ∈ orbit Q y) (hgz : g.val • z = z) : z = y := by
    have hh : (⟨⟨z,hz⟩,hgz⟩ : {z : orbit Q y // g.val • z.val = z.val}) =
        ⟨⟨y,mem_orbit_self y⟩,hgy⟩ := hsub.elim _ _
    exact congrArg (fun z => z.val.val) hh
  have hb := Degree52TwoOrderImage.image_card_sixteen Q hQ g hg y hy16 hgy hunique
  have hk : (MulAction.toPermHom Q (orbit Q y)).ker = (MulAction.toPermHom Q (orbit Q x)).ker := by
    ext q
    change MulAction.toPermHom Q (orbit Q y) q = 1 ↔ MulAction.toPermHom Q (orbit Q x) q = 1
    constructor
    · intro hh
      apply Equiv.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun w : orbit Q y => w.val) (DFunLike.congr_fun hh (⟨z.val,he.symm ▸ z.property⟩ : orbit Q y))
    · intro hh
      apply Equiv.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun w : orbit Q x => w.val) (DFunLike.congr_fun hh (⟨z.val,he ▸ z.property⟩ : orbit Q x))
  rw [← Subgroup.index_ker,hk,Subgroup.index_ker] at hb
  exact hb

end FiveTransitive.Degree54TwoOrbitGeometry

end CFSG
