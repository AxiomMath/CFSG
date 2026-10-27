module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral Sylow subgroups survive odd-kernel images
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

/-- The range of a homomorphism with odd-order kernel inherits dihedral
Sylow `2`-subgroups from the source. -/
public theorem image_hasDihedralSylowTwo_of_odd_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (hG : HasDihedralSylowTwo G) (f : G →* H)
    (hkerodd : Odd (Nat.card f.ker)) :
    HasDihedralSylowTwo f.range := by
  classical
  let fr : G →* f.range := f.rangeRestrict
  have hfr : Function.Surjective fr := f.rangeRestrict_surjective
  intro S
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective (p := 2) hfr S
  have hQmap : (Q : Subgroup G).map fr = (S : Subgroup f.range) := by
    rw [← Sylow.coe_mapSurjective hfr Q]
    exact congrArg (fun X : Sylow 2 (f.range) => (X : Subgroup f.range)) hQ
  rcases hG Q with ⟨m, hm, ⟨eQ⟩⟩
  have hQcop : Nat.Coprime (Nat.card (Q : Subgroup G)) (Nat.card f.ker) := by
    rcases (IsPGroup.iff_card.mp Q.isPGroup') with ⟨n, hn⟩
    rw [hn]
    exact (Nat.coprime_two_left.mpr hkerodd).pow_left n
  have hdisj : (Q : Subgroup G) ⊓ f.ker = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hQcop).eq_bot
  have hfQinj : Function.Injective (fr.subgroupMap (Q : Subgroup G)) := by
    intro a b hab
    have hab' : fr (a : G) = fr (b : G) := congrArg Subtype.val hab
    have hker : f ((a : G)⁻¹ * (b : G)) = 1 := by
      have hEq : f (a : G) = f (b : G) := congrArg Subtype.val hab'
      calc
        f ((a : G)⁻¹ * (b : G)) = (f (a : G))⁻¹ * f (b : G) := by
          rw [map_mul, map_inv]
        _ = 1 := by rw [hEq]; simp
    have hmemker : (a : G)⁻¹ * (b : G) ∈ f.ker := MonoidHom.mem_ker.mpr hker
    have hmemQ : (a : G)⁻¹ * (b : G) ∈ (Q : Subgroup G) :=
      (Q : Subgroup G).mul_mem ((Q : Subgroup G).inv_mem a.2) b.2
    have hbot : (a : G)⁻¹ * (b : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact ⟨hmemQ, hmemker⟩
    have hone : (a : G)⁻¹ * (b : G) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (eq_of_inv_mul_eq_one hone)
  let eQmap : (Q : Subgroup G) ≃* (Q : Subgroup G).map fr :=
    MulEquiv.ofBijective (fr.subgroupMap (Q : Subgroup G))
      ⟨hfQinj, fr.subgroupMap_surjective (Q : Subgroup G)⟩
  let eS : (Q : Subgroup G) ≃* S :=
    eQmap.trans (MulEquiv.subgroupCongr hQmap)
  exact ⟨m, hm, ⟨eS.symm.trans eQ⟩⟩

end CFSG.GorensteinWalter
