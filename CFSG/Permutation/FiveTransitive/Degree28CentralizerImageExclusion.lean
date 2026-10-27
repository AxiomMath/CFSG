module

public import CFSG.Permutation.FiveTransitive.Degree28CentralThree
public import CFSG.Permutation.FiveTransitive.FullFixerKernel
public import CFSG.Permutation.FiveTransitive.CoprimeKernelPrimeLift

public section

namespace CFSG

namespace FiveTransitive.Degree28CentralizerImageExclusion

open MulAction FixedNormalizerAction

theorem false_of_nontrivial_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (_hs : s.ncard = 5)
    (hH : IsPGroup 2 (fixingSubgroup P s))
    (hF : Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 6)
    (himage : Image (X := X) (fixingSubgroup P s) = ⊤)
    (z : Normalizer (fixingSubgroup P s))
    (hz : (fixingSubgroup P s).normalizerMonoidHom z = 1)
    (hzimage : toPermHom (Normalizer (fixingSubgroup P s))
      (Fixed (X := X) (fixingSubgroup P s)) z ≠ 1) : False := by
  classical
  let H := fixingSubgroup P s
  let F := Fixed (X := X) H
  let N := Normalizer H
  change Nat.card F = 6 at hF
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  let C : Subgroup N := H.normalizerMonoidHom.ker
  let psi : C →* Equiv.Perm F := rho.comp C.subtype
  have hsurj : Function.Surjective rho := MonoidHom.range_eq_top.mp himage
  have hrange : psi.range = C.map rho := by
    rw [show psi = rho.comp C.subtype from rfl,MonoidHom.range_comp]
    simp
  let _ : psi.range.Normal := by
    rw [hrange]
    exact (inferInstance : C.Normal).map rho hsurj
  have hnontriv : Nontrivial psi.range := by
    apply psi.range.nontrivial_iff_ne_bot.mpr
    intro he
    have hm : rho z ∈ psi.range := ⟨⟨z,hz⟩,rfl⟩
    rw [he] at hm
    exact hzimage (Subgroup.mem_bot.mp hm)
  have hAlt : alternatingGroup F ≤ psi.range :=
    Equiv.Perm.alternatingGroup_le_of_normal (by omega) hnontriv
  obtain ⟨t,_,ht⟩ := Equiv.Perm.exists_mem_stabilizer_isThreeCycle (∅ : Set F)
    (by omega)
  have htm : t ∈ psi.range := hAlt (by rw [Equiv.Perm.mem_alternatingGroup]; exact ht.sign)
  have hk : IsPGroup 2 psi.ker := FullFixerKernel.restricted_kernel_isPGroup s hH C
  have hkr : IsPGroup 2 psi.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c,hc,hc3⟩ := CoprimeKernelPrimeLift.exists_lift psi.rangeRestrict
    psi.rangeRestrict_surjective hkr (by norm_num : (3 : ℕ) ≠ 2)
    (⟨t,htm⟩ : psi.range) (by rw [← Subgroup.orderOf_coe]; exact ht.orderOf)
  have hcval : psi c = t := congrArg Subtype.val hc
  have hcN : orderOf c.val = 3 := (Subgroup.orderOf_coe c).trans hc3
  have hcomm : ∀ q : H, c.val.val * q.val = q.val * c.val.val := by
    intro q
    have he := congrArg Subtype.val (DFunLike.congr_fun
      (show H.normalizerMonoidHom c.val = 1 from c.property) q)
    change c.val.val * q.val * c.val.val⁻¹ = q.val at he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun u : P => u * c.val.val) he
  apply Degree28CentralThree.false_of_local_fixed_three P hcard h5 hnotAlt H hH c.val hcN hcomm
  change Nat.card (Function.fixedPoints (psi c)) = 3
  rw [hcval,Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,t.sum_cycleType,ht.card_support]
  have hFfin : Fintype.card F = 6 := by simpa only [Nat.card_eq_fintype_card] using hF
  omega

end FiveTransitive.Degree28CentralizerImageExclusion

end CFSG
