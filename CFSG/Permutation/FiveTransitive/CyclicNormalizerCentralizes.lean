module

public import CFSG.Permutation.FiveTransitive.CyclicTwoAutomorphismKernel
public import CFSG.Permutation.FiveTransitive.FixedNormalizerCompatibleSylow

public section

namespace CFSG

namespace FiveTransitive.CyclicNormalizerCentralizes

open MulAction FixedNormalizerAction

private theorem local_kernel_centralizes
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hcyclic : IsCyclic Q)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q) :
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker ≤
      (Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsCyclic Q := hcyclic
  let _ : CommGroup Q := IsCyclic.commGroup
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let φ := Q.normalizerMonoidHom
  let ψ := φ.comp f.ker.subtype
  have hQp : IsPGroup 2 Q := by
    rw [← hS]
    exact S.isPGroup'.map (fixingSubgroup G (fixedPoints Q X)).subtype
  have hAut : IsPGroup 2 (MulAut Q) := CyclicTwoAutomorphismKernel.automorphism_two_group hQp
  have hIker : Inside Q ≤ φ.ker := by
    change Inside Q ≤ Q.normalizerMonoidHom.ker
    rw [Q.normalizerMonoidHom_ker]
    intro q hq
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro r hr
    exact congrArg (fun t : Q => t.val) (mul_comm (⟨r, hr⟩ : Q) ⟨q.val, hq⟩)
  obtain ⟨T, hT⟩ := FixedNormalizerCompatibleSylow.exists_kernel_sylow Q S hS
  have hTker : (T : Subgroup f.ker) ≤ ψ.ker := by
    intro t ht
    exact hIker (hT.le ⟨t, ht, rfl⟩)
  have hψ := CyclicTwoAutomorphismKernel.hom_eq_one_of_sylow_le_kernel hAut ψ T hTker
  intro n hn
  rw [← Q.normalizerMonoidHom_ker]
  exact hψ ⟨n, hn⟩

theorem normalizer_centralizes
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hcyclic : IsCyclic Q)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤) :
    ∀ n : Normalizer Q, n.val ∈ Subgroup.centralizer (Q : Set G) := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let C := (Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)
  have hker : f.ker ≤ C := local_kernel_centralizes Q hcyclic S hS
  intro n
  have hn : f n ∈ C.map f := by rw [himage]; trivial
  obtain ⟨c, hc, hcn⟩ := hn
  have hk : c⁻¹ * n ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcn, inv_mul_cancel]
  have hnC : n ∈ C := by
    have hh := C.mul_mem hc (hker hk)
    simpa only [mul_inv_cancel_left] using hh
  exact hnC

end FiveTransitive.CyclicNormalizerCentralizes

end CFSG
