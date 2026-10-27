module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumDef
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG

theorem false_of_fixedDatum_isQuasisimple {F : Type} [Group F] (hFq : IsQuasisimple F)
    (hZ : ∀ z ∈ Subgroup.center F, z ^ 3 = 1) (h : FixedDatum F) : False := by
  obtain ⟨R, P, hPR, hP2, hPnc, hRs, hRn⟩ := h
  haveI hRnormal : R.Normal := ⟨fun n hn g => hRn g n hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hFq hRnormal with htop | hle
  · let e : R ≃* F := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    haveI : Group.IsSolvable F := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have : Group.IsPerfect F := hFq.1
    have := CFSG.LocalCores.isQuasisimple_nontrivial hFq
    exact Group.IsPerfect.not_isSolvable F inferInstance
  · apply hPnc
    have hP1 : ∀ x : P, x = 1 := by
      intro x
      have hxc : (x : F) ∈ Subgroup.center F := hle (hPR x.2)
      have h3 : (x : F) ^ 3 = 1 := hZ _ hxc
      obtain ⟨k, hk⟩ := hP2 x
      have hk' : (x : F) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      have h4 : (x : F) ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hk', h3⟩
      rw [hcop, pow_one] at h4
      exact Subtype.ext h4
    haveI : Subsingleton P := ⟨fun a b => (hP1 a).trans (hP1 b).symm⟩
    exact isCyclic_of_subsingleton

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
