module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerActorOdd
public import CFSG.RankThree.PartOne.KC.SymplecticInnerActorKappa

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open CFSG.Assembly.LowTwoRank

@[expose] def spQodd (r : ℕ) (K : Type) [Field K]
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (t : MulAut (StatedProj (StatedSp r K))) : Set (MulAut (StatedProj (StatedSp r K))) :=
  {z | z ∈ spCenterN r K t ⊓ (B ⊓ Subgroup.centralizer
    ({t} : Set (MulAut (StatedProj (StatedSp r K))))) ∧ Odd (orderOf z)}

end CFSG.RankThree.PartOne.KCSpComm

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

theorem symplectic_inner_actor_local_core_commutators_odd {ℓ f r p : ℕ} {K : Type} [Field K]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hq : 3 < ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B)
    (t : MulAut (StatedProj (StatedSp r K)))
    (ht : t ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range) (htp : orderOf t = p)
    (A : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hAB : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K)))))
    (hA : IsPGroup p ↥A) :
    (∃! x : StatedSp r K, orderOf x = p ∧ MulAut.conj (proj r K x) = t) ∧
    (∀ x : StatedSp r K, orderOf x = p → MulAut.conj (proj r K x) = t →
      spKappa x ≤ 1 + (p - 1) / 2 ∧ spKappa x < p ∧ spKappa x ≤ r) ∧
    Odd (Nat.card ↥⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))), A⁆) ∧
    (∀ z ∈ ⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))), A⁆,
      z ∈ spQodd r K B t) ∧
    (∀ a ∈ spCenterN r K t ⊓ (B ⊓ Subgroup.centralizer ({t} :
          Set (MulAut (StatedProj (StatedSp r K))))),
        ∀ b ∈ spCenterN r K t ⊓ (B ⊓ Subgroup.centralizer ({t} :
          Set (MulAut (StatedProj (StatedSp r K))))), a * b = b * a) ∧
    ((spCenterN r K t ⊓ (B ⊓ Subgroup.centralizer ({t} :
        Set (MulAut (StatedProj (StatedSp r K)))))).subgroupOf
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K)))))).Normal := by
  obtain ⟨huniq, hdata⟩ := exists_unique_lift hℓ hf hr hK hq hp hp3 hpℓ t ht htp
  obtain ⟨x, hxo, hxt⟩ := huniq.exists
  obtain ⟨D, blocks⟩ := hdata x hxo hxt
  have hinfin : Finite K := D.finite
  refine ⟨huniq, fun y hyo hyt => ?_, ?_⟩
  · obtain ⟨D', blocks'⟩ := hdata y hyo hyt
    exact spKappa_le D' blocks'
  · have ht' : conjAut r K (spXg x) = t := (conjAut_statedSp x).trans hxt
    subst ht'
    have hcomm : ∀ z₁ ∈ spCenterN r K (conjAut r K (spXg x)) ⊓ (B ⊓ Subgroup.centralizer
        ({conjAut r K (spXg x)} : Set (MulAut (StatedProj (StatedSp r K))))),
        ∀ z₂ ∈ spCenterN r K (conjAut r K (spXg x)) ⊓ (B ⊓ Subgroup.centralizer
          ({conjAut r K (spXg x)} : Set (MulAut (StatedProj (StatedSp r K))))),
        Commute z₁ z₂ := fun z₁ h₁ z₂ h₂ =>
      spQ0_comm D (Subgroup.mem_inf.mp h₁).1 (Subgroup.mem_inf.mp h₂).1
    have hle : ⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({conjAut r K (spXg x)} :
          Set (MulAut (StatedProj (StatedSp r K))))), A⁆ ≤ oddOrderSubgroup _ hcomm :=
      Subgroup.commutator_le.mpr fun s hs a ha => spCommutator_mem_odd D blocks B hB hAB hA hs ha
    refine ⟨odd_card_of_forall_odd_orderOf _ (fun z hz => (hle hz).2), fun z hz => hle hz,
      fun a ha b hb => spQ0_comm D (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hb).1,
      spQ0_normal D blocks B hB⟩

end CFSG.RankThree.PartOne
