module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import CFSG.Permutation.FiveTransitive.SylowKernelImagePrimeFree
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.NormalizerKernelPrimeFree

open MulAction FixedSetNormalizerHom

theorem prime_not_dvd_kernel_image
    (G X : Type*) [Group G] [Finite G] [MulAction G X]
    (s : Set X) {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G s))
    (hcomm : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ a b : Q, a * b = b * a) :
    let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
    ¬ p ∣ Nat.card ((fixedPermHom G X Q).ker.map Q.normalizerMonoidHom) := by
  classical
  let H := fixingSubgroup G s
  let Q : Subgroup G := (S : Subgroup H).map H.subtype
  let N := Subgroup.normalizer (Q : Set G)
  let rho : N →* Equiv.Perm (fixedPoints Q X) := fixedPermHom G X Q
  let K := rho.ker
  change ¬ p ∣ Nat.card (K.map Q.normalizerMonoidHom)
  change ∀ a b : Q, a * b = b * a at hcomm
  have hsF : s ⊆ fixedPoints Q X := by
    intro x hx
    rw [mem_fixedPoints]
    intro q
    obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp q.property
    change (q : G) • x = x
    rw [← heq]
    exact (mem_fixingSubgroup_iff G).mp u.property x hx
  have hKH (a : K) : ((a.val : N) : G) ∈ H := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact (mem_ker_iff G X Q a.val).mp a.property x (hsF hx)
  let i : K →* H :=
    { toFun := fun a => ⟨((a.val : N) : G), hKH a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : H => (x : G)) h
  have hS : (S : Subgroup H) ≤ i.range := by
    intro u hu
    have huQ : (u : G) ∈ Q := Subgroup.mem_map_of_mem H.subtype hu
    let n : N := ⟨(u : G), Q.le_normalizer huQ⟩
    have hn : n ∈ K := by
      apply (mem_ker_iff G X Q n).mpr
      intro x hx
      exact mem_fixedPoints.mp hx ⟨(u : G),huQ⟩
    exact ⟨⟨n,hn⟩, rfl⟩
  apply SylowKernelImagePrimeFree.prime_not_dvd_map_card S K i hi hS Q.normalizerMonoidHom
  intro a ha
  have haQ : ((a.val : N) : G) ∈ Q := Subgroup.mem_map_of_mem H.subtype ha
  let q : Q := ⟨((a.val : N) : G),haQ⟩
  apply MulEquiv.ext
  intro r
  apply Subtype.ext
  rw [Q.normalizerMonoidHom_apply_apply_coe]
  change ((a.val : N) : G) * (r : G) * ((a.val : N) : G)⁻¹ = (r : G)
  have hc : ((a.val : N) : G) * (r : G) = (r : G) * ((a.val : N) : G) :=
    congrArg (fun x : Q => (x : G)) (hcomm q r)
  rw [hc, mul_inv_cancel_right]

end FiveTransitive.NormalizerKernelPrimeFree

end CFSG
