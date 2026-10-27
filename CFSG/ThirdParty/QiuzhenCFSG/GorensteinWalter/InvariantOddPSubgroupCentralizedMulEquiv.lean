module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transporting invariant odd-subgroup endpoints through isomorphisms

The property that every involution-centralizer-invariant `p`-subgroup is
centralized by the involution is invariant under group isomorphism.
-/

namespace CFSG.GorensteinWalter

universe u v

/-- Transport an invariant `p`-subgroup centralization endpoint through a
group isomorphism. -/
public theorem invariant_oddP_subgroup_centralized_of_mulEquiv
    {X : Type u} {Y : Type v} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (p : ℕ)
    (hY : ∀ (Q : Subgroup Y), IsPGroup p Q →
      ∀ {s : Y}, IsInvolution s →
      Subgroup.centralizer ({s} : Set Y) ≤
        Subgroup.normalizer (Q : Set Y) →
      Q ≤ Subgroup.centralizer ({s} : Set Y))
    (P : Subgroup X) (hPp : IsPGroup p P) {t : X}
    (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (P : Set X)) :
    P ≤ Subgroup.centralizer ({t} : Set X) := by
  let Q : Subgroup Y := P.map e.toMonoidHom
  let s : Y := e t
  have hQp : IsPGroup p Q := IsPGroup.map hPp e.toMonoidHom
  have hs : IsInvolution s := by
    constructor
    · intro hsone
      apply ht.1
      exact e.injective (by simpa [s] using hsone)
    · simpa [s] using congrArg e ht.2
  have hQinv : Subgroup.centralizer ({s} : Set Y) ≤
      Subgroup.normalizer (Q : Set Y) := by
    intro c hc
    let cX : X := e.symm c
    have hcXcent : cX ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      simpa [cX, s] using
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hcXN : cX ∈ Subgroup.normalizer (P : Set X) := hPinv hcXcent
    have hmap : e cX ∈
        (Subgroup.normalizer (P : Set X)).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨cX, hcXN, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq] at hmap
    simpa [cX, Q] using hmap
  have hQcent := hY Q hQp hs hQinv
  intro x hxP
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxQ : e x ∈ Q := Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  have hxcomm : e x * s = s * e x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hQcent hxQ)
  apply e.injective
  simpa [s, map_mul] using hxcomm

end CFSG.GorensteinWalter
