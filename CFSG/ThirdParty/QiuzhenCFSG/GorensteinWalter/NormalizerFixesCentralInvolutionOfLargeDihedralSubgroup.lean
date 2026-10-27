module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra

namespace CFSG
end CFSG
open CFSG

/-!
# A large normalized subgroup fixes the central dihedral involution

If a subgroup of a dihedral two-group has order at least eight and contains
the central involution, every ambient element normalizing that subgroup fixes
the central involution.  This is the normalizer step used in the final
component contradiction of Gorenstein--Walter Theorem 2.6.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Let Q ≤ P, where P is a dihedral two-group of order at least eight.
If Q has order at least eight and contains the central involution z of P,
then every element normalizing Q centralizes z. -/
public theorem normalizer_fixes_central_involution_of_large_subgroup_of_dihedral
    {G : Type u} [Group G] [Finite G]
    (P Q : Subgroup G) (hQP : Q ≤ P)
    {m : ℕ} (hm : 2 ≤ m) (e : P ≃* DihedralGroup (2 ^ m))
    {z y : G}
    (hzP : z ∈ P) (hzQ : z ∈ Q)
    (hzI : IsInvolution z)
    (hzcenter : (⟨z, hzP⟩ : P) ∈ Subgroup.center P)
    (hQcard : 8 ≤ Nat.card Q)
    (hyN : y ∈ Subgroup.normalizer (Q : Set G)) :
    y * z * y⁻¹ = z := by
  let QP : Subgroup P := Q.subgroupOf P
  have hQPcard : Nat.card QP = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
  have hQPge : 8 ≤ Nat.card QP := by
    rwa [hQPcard]
  have hyInvN : y⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hyN
  have hzConjQ : y * z * y⁻¹ ∈ Q :=
    ((Subgroup.mem_normalizer_iff.mp hyN) z).mp hzQ
  have hzConjP : y * z * y⁻¹ ∈ P := hQP hzConjQ
  let zP : P := ⟨z, hzP⟩
  let zConjP : P := ⟨y * z * y⁻¹, hzConjP⟩
  have hzConjI : IsInvolution zConjP := by
    constructor
    · intro hone
      apply hzI.1
      have hval : y * z * y⁻¹ = 1 :=
        congrArg Subtype.val hone
      have hback := congrArg (fun w : G => y⁻¹ * w * y) hval
      simpa [mul_assoc] using hback
    · apply Subtype.ext
      change (y * z * y⁻¹) ^ 2 = 1
      calc
        (y * z * y⁻¹) ^ 2 = y * (z ^ 2) * y⁻¹ := by
          simp [pow_two, mul_assoc]
        _ = 1 := by rw [hzI.2]; simp
  have hzConjQP : zConjP ∈ QP := by
    exact Subgroup.mem_subgroupOf.mpr hzConjQ
  have hzConjCentQP : ∀ q : QP,
      (⟨zConjP, hzConjQP⟩ : QP) * q =
        q * (⟨zConjP, hzConjQP⟩ : QP) := by
    intro q
    have hqQ : (q : G) ∈ Q :=
      Subgroup.mem_subgroupOf.mp q.2
    have hqBackQ0 : y⁻¹ * (q : G) * (y⁻¹)⁻¹ ∈ Q :=
      ((Subgroup.mem_normalizer_iff.mp hyInvN) (q : G)).mp hqQ
    have hqBackQ : y⁻¹ * (q : G) * y ∈ Q := by
      simpa using hqBackQ0
    let qBackP : P := ⟨y⁻¹ * (q : G) * y, hQP hqBackQ⟩
    have hcommP := Subgroup.mem_center_iff.mp hzcenter qBackP
    have hcommG :
        z * (y⁻¹ * (q : G) * y) =
          (y⁻¹ * (q : G) * y) * z :=
      congrArg Subtype.val hcommP.symm
    apply Subtype.ext
    apply Subtype.ext
    change (y * z * y⁻¹) * (q : G) =
      (q : G) * (y * z * y⁻¹)
    calc
      (y * z * y⁻¹) * (q : G) =
          y * (z * (y⁻¹ * (q : G) * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * (q : G) * y) * z) * y⁻¹ := by rw [hcommG]
      _ = (q : G) * (y * z * y⁻¹) := by group
  have hzConjCenter : zConjP ∈ Subgroup.center P :=
    central_of_centralizes_large_subgroup_of_dihedral
      zConjP hzConjI.2 hzConjI.1 hm e QP hQPge hzConjQP hzConjCentQP
  have hzPI : IsInvolution zP := by
    constructor
    · intro hone
      apply hzI.1
      exact congrArg Subtype.val hone
    · apply Subtype.ext
      exact hzI.2
  have hezCenter :
      e zP ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    rcases e.surjective a with ⟨p, rfl⟩
    simpa using congrArg e (Subgroup.mem_center_iff.mp hzcenter p)
  have hezConjCenter :
      e zConjP ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    rcases e.surjective a with ⟨p, rfl⟩
    simpa using congrArg e
      (Subgroup.mem_center_iff.mp hzConjCenter p)
  have hezPow : (e zP) ^ 2 = 1 := by
    calc
      (e zP) ^ 2 = e (zP ^ 2) := (e.toMonoidHom.map_pow zP 2).symm
      _ = 1 := by rw [hzPI.2]; simp
  have hezConjPow : (e zConjP) ^ 2 = 1 := by
    calc
      (e zConjP) ^ 2 =
          e (zConjP ^ 2) := (e.toMonoidHom.map_pow zConjP 2).symm
      _ = 1 := by rw [hzConjI.2]; simp
  have hezNe : e zP ≠ 1 := by
    intro hone
    apply hzPI.1
    exact e.injective (by simpa using hone)
  have hezConjNe : e zConjP ≠ 1 := by
    intro hone
    apply hzConjI.1
    exact e.injective (by simpa using hone)
  have hez :=
    unique_central_involution_of_dihedral_two_pow
      hm (e zP) hezCenter hezPow hezNe
  have hezConj :=
    unique_central_involution_of_dihedral_two_pow
      hm (e zConjP) hezConjCenter hezConjPow hezConjNe
  have hsubtype : zConjP = zP :=
    e.injective (hezConj.trans hez.symm)
  exact congrArg Subtype.val hsubtype

end CFSG.GorensteinWalter
