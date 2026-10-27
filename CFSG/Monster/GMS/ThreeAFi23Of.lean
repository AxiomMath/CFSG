module

public import CFSG.Monster.GMS.ThreeAFi23
public import CFSG.Monster.GMS.CommonNbr
public import CFSG.Fischer.Rec23Full

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

theorem threeAFi23_of
    {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hS : BabyFi22Slice) :
    ThreeAFi23 a z₀ := by
  intro b x hb hx
  have ha : orderOf a = 2 := hG.1.1
  have hxA : IsConj a x := isConj_of_mem_typeSet hx
  have hord : orderOf (b * x) = 3 := by
    obtain ⟨⟨-, -, -, w, hw, hwB⟩, hty⟩ := hx
    exact (s348_card hty hw hwB).1
  obtain ⟨hcls, htr, hinv, hprod, hloc, hZ⟩ :=
    Fi23Local.fi23Local_hypotheses I hG hS hb hxA hord
  obtain ⟨d, hd⟩ := commonNbr_threeA_nonempty I hG hS hb hx
  have hdH : d ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (S36Lines.mul_comm_of_isConj_mul ha hb hd.1.1 hd.1.2).symm,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (S36Lines.mul_comm_of_isConj_mul ha hxA hd.2.1 hd.2.2).symm⟩
  have hne : (Fi23Local.Dset a b x).Nonempty := ⟨⟨d, hdH⟩, hd⟩
  obtain ⟨-, -, φ, hφ⟩ :=
    CFSG.Fischer.fi23_of_localPoints_full _ hcls htr hne hinv hprod hloc hZ
  exact ⟨φ, fun h => hφ h⟩

end CFSG.Monster.GMS
