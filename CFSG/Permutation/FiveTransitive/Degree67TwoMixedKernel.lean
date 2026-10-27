module

public import CFSG.Permutation.FiveTransitive.Degree67TwoMixedFixedSet
public import CFSG.Permutation.FiveTransitive.Degree67TwoKernelBound

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoMixedKernel
open MulAction NormalizerOrbitFamily Degree67TwoMixedAction

private theorem kernel_card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hcard : Fintype.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (horbit : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33)
    (p : Family (X := X) Q 2) (a : Fin 4 ↪ Family (X := X) Q 4) :
    Nat.card (mixedHom Q p a).ker ≤ 16 := by
  classical
  let R := (mixedHom Q p a).ker
  obtain ⟨s,hs,hfixed⟩ := Degree67TwoMixedFixedSet.exists_fixed_set Q hF p a
  have hRorbit (x : X) : Nat.card (orbit R x) ≤ 4 := by
    have hsub : orbit R x ⊆ orbit Q x := by
      intro y hy
      obtain ⟨r,hr⟩ := mem_orbit_iff.mp hy
      exact mem_orbit_iff.mpr ⟨r.val,hr⟩
    have hle := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at hle
    exact hle.trans (horbit x)
  have hRbound (r : R) (hr : r ≠ 1) : Nat.card (fixedBy X r) ≤ 33 :=
    hbound r.val (fun he => hr (Subtype.ext he))
  exact Degree67TwoKernelBound.card_le_sixteen (hQ.to_subgroup R) hcard s hs
    hfixed hRorbit hRbound

private theorem projection_data
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hcard : Fintype.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (horbit : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33)
    (p : Family (X := X) Q 2) (a : Fin 4 ↪ Family (X := X) Q 4) :
    let rho := mixedHom Q p a
    Nat.card (orbitAction Q p.val) = 2 ∧
      (∀ i : Fin 4, Nat.card (orbitAction Q (a i).val) = 4) ∧
      IsPGroup 2 rho.range ∧ Nat.card rho.range ≤ 8192 ∧ Nat.card rho.ker ≤ 16 ∧
      Nat.card Q = Nat.card rho.ker * Nat.card rho.range := by
  dsimp only
  refine ⟨card_orbitAction Q 2 p,fun i => card_orbitAction Q 4 (a i),
    range_isPGroup Q hQ p a,range_card_le Q hQ p a,
    kernel_card_le hcard Q hQ hF horbit hbound p a,?_⟩
  have hm := (mixedHom Q p a).ker.card_mul_index
  rw [Subgroup.index_ker] at hm
  exact hm.symm

theorem exists_projection
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hcard : Fintype.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (horbit : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33)
    (hpair : 1 ≤ Nat.card (Family (X := X) Q 2))
    (hquad : 4 ≤ Nat.card (Family (X := X) Q 4)) :
    ∃ (A : SubMulAction Q X) (B : Fin 4 → SubMulAction Q X)
      (rho : Q →* (Equiv.Perm A × (∀ i : Fin 4, Equiv.Perm (B i)))),
      Nat.card A = 2 ∧ (∀ i : Fin 4, Nat.card (B i) = 4) ∧
      IsPGroup 2 rho.range ∧ Nat.card rho.range ≤ 8192 ∧ Nat.card rho.ker ≤ 16 ∧
      Nat.card Q = Nat.card rho.ker * Nat.card rho.range := by
  classical
  obtain ⟨p⟩ : Nonempty (Family (X := X) Q 2) := Finite.card_pos_iff.mp hpair
  let a : Fin 4 ↪ Family (X := X) Q 4 :=
    (Fin.castLEEmb hquad).trans (Finite.equivFin _).symm.toEmbedding
  exact ⟨orbitAction Q p.val,fun i => orbitAction Q (a i).val,mixedHom Q p a,
    projection_data hcard Q hQ hF horbit hbound p a⟩

end FiveTransitive.Degree67TwoMixedKernel

end CFSG
