module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Klein-four subgroups containing a given involution of a dihedral 2-group

Every involution of a non-cyclic dihedral `2`-group lies in some Klein-four
subgroup: if it is the central rotation, any Klein four contains it; if it
is a reflection, it commutes with the central rotation and the two generate
a Klein four.  This supplies the Klein-four `V` needed for the fixed-point
step of Lemma 2.7.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An involution in an ambient subgroup isomorphic to a dihedral `2`-group
is contained in a Klein-four subgroup of that ambient subgroup. -/
public theorem exists_kleinFour_of_dihedral_mulEquiv_containing_involution
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) {m : ℕ} (hm : 1 ≤ m)
    (e : P ≃* DihedralGroup (2 ^ m))
    {t : G} (htP : t ∈ P) (ht : IsInvolution t) :
    ∃ V : Subgroup G, V ≤ P ∧ IsKleinFour V ∧ t ∈ V := by
  classical
  rcases exists_kleinFour_le_of_dihedral_subgroup_mulEquiv P hm e with ⟨V0, hV0P, hV0⟩
  by_cases htV0 : t ∈ V0
  · exact ⟨V0, hV0P, hV0, htV0⟩
  · have hm2 : 2 ≤ m := by
      by_contra h
      have hm1 : m = 1 := by omega
      have hPcard4 : Nat.card (↥P) = 4 := by
        rw [Nat.card_congr e.toEquiv]
        simpa [hm1, DihedralGroup.nat_card]
      have hV0card : Nat.card (↥V0) = 4 := hV0.card_four
      have hV0P_eq : V0 = P :=
        Subgroup.eq_of_le_of_card_ge hV0P (by rw [hPcard4, hV0card])
      exact htV0 (hV0P_eq.symm ▸ htP)
    let zP : P := e.symm (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)))
    let z : G := (zP : P)
    have hzP : z ∈ P := zP.2
    have hzM : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈
        Subgroup.center (DihedralGroup (2 ^ m)) :=
      central_rotation_mem_center_dihedral_two_pow hm2
    have hzcenterP : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center (↥P) := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply e.injective
      change e (x * (⟨z, hzP⟩ : ↥P)) = e ((⟨z, hzP⟩ : ↥P) * x)
      calc
        e (x * (⟨z, hzP⟩ : ↥P)) = e (x : ↥P) * e (⟨z, hzP⟩ : ↥P) :=
          e.map_mul x (⟨z, hzP⟩ : ↥P)
        _ = e (x : ↥P) * DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) := by
          simp [z, zP]
        _ = DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) * e (x : ↥P) :=
          Subgroup.mem_center_iff.mp hzM (e (x : ↥P))
        _ = e (⟨z, hzP⟩ : ↥P) * e (x : ↥P) := by simp [z, zP]
        _ = e ((⟨z, hzP⟩ : ↥P) * x) := (e.map_mul (⟨z, hzP⟩ : ↥P) x).symm
    let V0i : Subgroup (↥P) := V0.subgroupOf P
    have hV0i : IsKleinFour V0i := by
      let e0 : V0i ≃* V0 := Subgroup.subgroupOfEquivOfLe hV0P
      refine ⟨?_, ?_⟩
      · exact (Nat.card_congr e0.toEquiv).trans hV0.card_four
      · exact (Monoid.exponent_eq_of_mulEquiv e0).trans hV0.exponent_two
    have hzV0i : (⟨z, hzP⟩ : ↥P) ∈ V0i :=
      center_mem_kleinFour_of_dihedral_mulEquiv hm e V0i hV0i hzcenterP
    have hzV : z ∈ V0 := by
      exact (Subgroup.mem_subgroupOf).mp hzV0i
    have hz2 : z * z = 1 := by
      have h := congrArg Subtype.val (IsKleinFour.mul_self (⟨z, hzV⟩ : V0))
      exact h
    have hzne : z ≠ 1 := by
      intro hz1
      have hr1 : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) = 1 := by
        have hzP1 : zP = 1 := by
          apply Subtype.ext
          exact hz1
        have h := congrArg e hzP1
        simpa [zP] using h
      have h0 : (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 := by
        have h' := (DihedralGroup.r.injEq (2 ^ (m - 1) : ZMod (2 ^ m)) 0).mp
          (by simpa using hr1)
        exact h'
      have hdvd : 2 ^ m ∣ 2 ^ (m - 1) :=
        (ZMod.natCast_eq_zero_iff (2 ^ (m - 1)) (2 ^ m)).mp (by simpa using h0)
      have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) (m - 1)
      have hle : 2 ^ m ≤ 2 ^ (m - 1) := Nat.le_of_dvd hpos hdvd
      have hlt : 2 ^ (m - 1) < 2 ^ m :=
        Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m - 1 < m)
      omega
    have hzInv : IsInvolution z := ⟨hzne, by simpa [pow_two] using hz2⟩
    have htz : Commute t z := by
      have h := congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzcenterP (⟨t, htP⟩ : ↥P))
      exact h
    have htzne : t ≠ z := by
      intro htz
      exact htV0 (htz ▸ hzV)
    rcases exists_kleinFour_of_commuting_involutions_le
        P t z ht hzInv htzne htz htP hzP with ⟨V, hVP, hV, htV, _hzV'⟩
    exact ⟨V, hVP, hV, htV⟩

end CFSG.GorensteinWalter
