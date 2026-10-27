module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Quasithin.J4Loc

section Main


theorem rad_of_list (hF : J4Facts) {M : Subgroup J}
    (hM : M = Hj ∨ M = Subgroup.centralizer ({z0} : Set J) ∨
      M = Subgroup.normalizer (V0 : Set J)) {R : Subgroup J} (hRM : R ≤ M)
    (hN : M ≤ Subgroup.normalizer (R : Set J)) (hs : Group.IsSolvable ↥R) :
    ¬ 9 ∣ Nat.card ↥R := by
  rcases hM with rfl | rfl | rfl
  · exact rad_Hj hRM hN hs
  · exact rad_M2 hF hRM hN hs
  · exact rad_M3 hF hRM hN hs

theorem factJ4TwoLocals2 : CFSG.Quasithin.ModH.FactJ4TwoLocals2 := by
  intro Q _ _ e S hS M hM hSM R hMR hRM hs
  obtain ⟨ψ, -, hcases⟩ := j4MaxTwoLocalList_of_iso e.some hS hM hSM
  have hF : J4Facts := j4Facts
  have h1 : Subgroup.map (ψ : Q →* ↥J) R ≤ Subgroup.map (ψ : Q →* ↥J) M :=
    Subgroup.map_mono hRM
  have h2 : Subgroup.map (ψ : Q →* ↥J) M ≤
      Subgroup.normalizer (↑(Subgroup.map (ψ : Q →* ↥J) R) : Set ↥J) := by
    rw [CFSG.Quasithin.J4Loc.map_normalizer_equiv]
    exact Subgroup.map_mono hMR
  have e1 := Subgroup.equivMapOfInjective R (ψ : Q →* ↥J) ψ.injective
  have h3 : Group.IsSolvable ↥(Subgroup.map (ψ : Q →* ↥J) R) := by
    have := hs
    exact Group.isSolvable_of_surjective (f := (e1 : ↥R →* _)) e1.surjective
  have h4 : Nat.card ↥(Subgroup.map (ψ : Q →* ↥J) R) = Nat.card ↥R :=
    Subgroup.card_map_of_injective ψ.injective
  have := rad_of_list hF hcases h1 h2 h3
  rwa [h4] at this

end Main

end CFSG.Quasithin.J4Rad
