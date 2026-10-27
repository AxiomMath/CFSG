module

public import CFSG.Permutation.FiveTransitive.Degree28CentralizerImageExclusion
public import CFSG.Permutation.FiveTransitive.Degree28SmallTwoFiveCentralization
public import CFSG.Permutation.FiveTransitive.Degree28FiveFixerStructure

public section

namespace CFSG

namespace FiveTransitive.Degree28SmallFixerExclusion

open MulAction FixedNormalizerAction

theorem contradiction
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hsmall : Nat.card (fixingSubgroup P s) ≤ 16) : False := by
  classical
  let H := fixingSubgroup P s
  let F := Fixed (X := X) H
  let N := Normalizer H
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  obtain ⟨hH,_,_,hF,himage,_⟩ := Degree28FiveFixerStructure.data P hcard h5 hnotAlt s hs
  change Nat.card F = 6 at hF
  have hsurj : Function.Surjective rho := MonoidHom.range_eq_top.mp himage
  have hk : IsPGroup 2 rho.ker := by
    change IsPGroup 2 (toPermHom (Normalizer H) (Fixed (X := X) H)).ker
    rw [FullFixerKernel.kernel_eq_inside]
    exact hH.comap_subtype
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : 5 ∣ Nat.card (Equiv.Perm F) := by
    rw [Nat.card_perm,hF]
    norm_num [Nat.factorial]
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := Equiv.Perm F) 5 hdvd
  obtain ⟨z,hzy,hz5⟩ := CoprimeKernelPrimeLift.exists_lift rho hsurj hk
    (by norm_num : (5 : ℕ) ≠ 2) y hy
  have hzne : rho z ≠ 1 := by
    rw [hzy]
    intro he
    rw [he,orderOf_one] at hy
    norm_num at hy
  have hcent := Degree28SmallTwoFiveCentralization.centralizes P hcard h5 hnotAlt H hH
    hsmall hF z hz5 hzne
  exact Degree28CentralizerImageExclusion.false_of_nontrivial_image
    P hcard h5 hnotAlt s hs hH hF himage z hcent hzne

end FiveTransitive.Degree28SmallFixerExclusion

end CFSG
