module

public import CFSG.Monster.GMS.Leech.OddExists
public import CFSG.Monster.GMS.Leech.OddSylow

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem isConj_phi_conj {t g : G} (h : IsLeechCentralLift z t)
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) (h' : IsLeechCentralLift z (g * t * g⁻¹)) :
    IsConj (L.φ ⟨t, h.mem_centralizer⟩) (L.φ ⟨g * t * g⁻¹, h'.mem_centralizer⟩) :=
  isConj_iff.2 ⟨L.φ ⟨g, hg⟩, (L.phi_conj hg h.mem_centralizer).symm⟩

theorem leechOddPairData
    [Finite G] (hI : Co1InvolutionFacts) (hO : Co1OddPairFacts) :
    LeechOddPairData z := by
  intro t ht
  refine ⟨?_, fun k => L.exists_odd_partner hI hO ht k, ?_, ?_⟩
  ·
    rintro y ⟨g, hg, rfl⟩ hne hodd hfour
    have h' := L.isLeechCentralLift_conj ht hg
    have hconj := L.isConj_phi_conj ht hg h'
    have hne' : L.φ ⟨g * t * g⁻¹, h'.mem_centralizer⟩ ≠ L.φ ⟨t, ht.mem_centralizer⟩ :=
      fun e => hne (L.eq_of_phi_eq ht h' hodd e)
    have hodd' : Odd (orderOf (L.φ ⟨t, ht.mem_centralizer⟩ *
        L.φ ⟨g * t * g⁻¹, h'.mem_centralizer⟩)) := by
      rw [L.orderOf_phi_mul ht.mem_centralizer h'.mem_centralizer hodd]
      exact hodd
    obtain ⟨k, hk, huniq⟩ := (hO _ (L.isCo1TwoA_phi hI ht)).1 _ hconj hne' hodd'
      ((L.hasCommonLeechFour_iff hI ht h').1 hfour)
    exact ⟨k, (L.leechOddType_iff hI ht h' hodd k).2 hk, fun k' hk' =>
      huniq k' ((L.leechOddType_iff hI ht h' hodd k').1 hk')⟩
  ·
    rintro k y y' ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩ hfour hfour' hk hk'
    have h₁ := L.isLeechCentralLift_conj ht hg
    have h₂ := L.isLeechCentralLift_conj ht hg'
    have hodd₁ := odd_orderOf_of_leechOddType hk
    have hodd₂ := odd_orderOf_of_leechOddType hk'
    obtain ⟨γ, hγ, hγs⟩ := (hO _ (L.isCo1TwoA_phi hI ht)).2.2.1 k _ _
      (L.isConj_phi_conj ht hg h₁) (L.isConj_phi_conj ht hg' h₂)
      ((L.hasCommonLeechFour_iff hI ht h₁).1 hfour) ((L.hasCommonLeechFour_iff hI ht h₂).1 hfour')
      ((L.leechOddType_iff hI ht h₁ hodd₁ k).1 hk) ((L.leechOddType_iff hI ht h₂ hodd₂ k).1 hk')
    obtain ⟨c, rfl⟩ := L.φ_surj γ
    have hcr := Subgroup.mem_centralizer_singleton_iff.1 hγ
    obtain ⟨p, hp, hpt, hpy⟩ := L.exists_conj_of_odd_pair hI ht h₁.mem_centralizer
      h₂.mem_centralizer h₁.mul_self h₂.mul_self hodd₁ hodd₂ c.2
      (L.inv_mul_conj_mem_of_phi_conj ht.mem_centralizer ht.mem_centralizer c.2 (by
        rw [hcr]
        group))
      (L.inv_mul_conj_mem_of_phi_conj h₁.mem_centralizer h₂.mem_centralizer c.2 hγs)
    exact ⟨p * c, Subgroup.mem_inf.2 ⟨mul_mem (L.mem_centralizer hp) c.2, hpt⟩, hpy⟩
  ·
    rintro k y hk0 ⟨g, hg, rfl⟩ hfour hk S s _ hcent
    have h' := L.isLeechCentralLift_conj ht hg
    exact L.sylow_center_of_odd_type hI hO ht h' (L.isConj_phi_conj ht hg h') hfour hk0 hk S s hcent

end LeechSystem

theorem leechOddPairStatement_of
    (h13 : Co1ModuleUniqueness) (hI : Co1InvolutionFacts)
    (hO : Co1OddPairFacts) : LeechOddPairStatement := by
  intro G _ _ z hz
  obtain ⟨L⟩ := exists_leechSystem h13 hz
  exact L.leechOddPairData hI hO

end CFSG.Monster.GMS
