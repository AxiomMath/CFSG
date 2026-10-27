module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Minimal normal p-subgroups are elementary abelian at the same prime
-/

namespace CFSG.Glauberman

universe u

public theorem minimalNormal_pSubgroup_isElementaryAbelian
    {p : ℕ} [Fact p.Prime] {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) [H.Normal] [IsMinimalNormal H]
    (hHne : H ≠ ⊥) (hHp : IsPGroup p H) :
    IsElementaryAbelian p H := by
  classical
  have hnilpotent : Group.IsNilpotent H := hHp.isNilpotent
  have hsolvable : Group.IsSolvable H :=
    @IsNilpotent.to_isSolvable H _ hnilpotent
  obtain ⟨r, hrprime, hHelem⟩ :=
    @minimalNormal_solvable_exists_isElementaryAbelian Q _ _ H _ _ hsolvable
  have hnontrivial : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  obtain ⟨x, hx_ne⟩ := @exists_ne H hnontrivial (1 : H)
  have hxpow : x ^ r = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (@IsElementaryAbelian.exponent_dvd_p r H _ hHelem) x
  have horder_eq_r : orderOf x = r :=
    @orderOf_eq_prime H _ x r ⟨hrprime⟩ hxpow hx_ne
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := p) (G := H)).1 hHp x
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hx_ne
    exact orderOf_eq_one_iff.mp (by simpa [hn0] using hn)
  have hp_dvd_r : p ∣ r := by
    rw [← horder_eq_r, hn]
    exact dvd_pow_self p hn0
  have hr_eq_p : r = p := by
    simpa [eq_comm] using
      (hrprime.dvd_iff_eq (Fact.out : p.Prime).ne_one).1 hp_dvd_r
  simpa [hr_eq_p] using hHelem

end CFSG.Glauberman
