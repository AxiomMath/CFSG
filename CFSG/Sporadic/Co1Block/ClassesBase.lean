module

public import CFSG.Sporadic.Co1Block.Co1Equiv
public import CFSG.Sporadic.Co1.Module.InvClass
public import CFSG.Monster.B.TwoA.Census.LatticeInv

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier

theorem exists_three_classes :
    ∃ c : ℕ → GA, ∀ s : GA, orderOf s = 2 →
    ∃ i ∈ ({1, 2, 6} : Finset ℕ), IsConj (c i) s := by
  obtain ⟨-, -, hmem, hcls, -⟩ :=
    CFSG.Monster.B.TwoA.Census.lattice_quotient_three_involution_classes
  obtain ⟨c, hc⟩ := CFSG.Sporadic.Co1.Module.exists_conj_three_of_chevalley
    CFSG.Monster.B.TwoA.Census.monoN hmem hcls
  refine ⟨fun i => co1MatEquiv (c i), fun s hs => ?_⟩
  obtain ⟨i, hi, hci⟩ := hc (co1MatEquiv.symm s) (by rw [orderOf_co1MatEquiv_symm]; exact hs)
  refine ⟨i, hi, ?_⟩
  show IsConj (co1MatEquiv (c i)) s
  obtain ⟨g, hg⟩ := isConj_iff.1 hci
  refine isConj_iff.2 ⟨co1MatEquiv g, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hg, MulEquiv.apply_symm_apply]

theorem involution_cases_of
    {x y z : GA} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hz : orderOf z = 2) (hxy : ¬ IsConj x y) (hxz : ¬ IsConj x z) (hyz : ¬ IsConj y z) :
    ∀ s : GA, orderOf s = 2 → IsConj s x ∨ IsConj s y ∨ IsConj s z := by
  obtain ⟨c, hc⟩ := exists_three_classes
  intro s hs
  by_contra hne
  push Not at hne
  obtain ⟨iS, hiS, hcS⟩ := hc s hs
  obtain ⟨iX, hiX, hcX⟩ := hc x hx
  obtain ⟨iY, hiY, hcY⟩ := hc y hy
  obtain ⟨iZ, hiZ, hcZ⟩ := hc z hz
  have hpig : ∀ a ∈ ({1, 2, 6} : Finset ℕ), ∀ b ∈ ({1, 2, 6} : Finset ℕ),
      ∀ c ∈ ({1, 2, 6} : Finset ℕ), ∀ d ∈ ({1, 2, 6} : Finset ℕ),
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by decide
  rcases hpig iS hiS iX hiX iY hiY iZ hiZ with h | h | h | h | h | h
  · subst h
    exact hne.1 (hcS.symm.trans hcX)
  · subst h
    exact hne.2.1 (hcS.symm.trans hcY)
  · subst h
    exact hne.2.2 (hcS.symm.trans hcZ)
  · subst h
    exact hxy (hcX.symm.trans hcY)
  · subst h
    exact hxz (hcX.symm.trans hcZ)
  · subst h
    exact hyz (hcY.symm.trans hcZ)

end CFSG.Sporadic.Co1Block
