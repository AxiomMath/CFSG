
module

public import CFSG.Quasithin.EmptyFaithful.S151S9TM24Base

public import CFSG.Quasithin.EmptyFaithful.S151S9TM24Inputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.EmptyFaithful.S151S9TCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
  CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b)

theorem m24_idx3Model :
    Idx3Model ↥CFSG.Blueprint.NativeSporadic.M24 m24Ctx.S (m24Ctx.Y 8) :=
  Certificates.certificate4068.2.2.1

theorem m24_threeD :
    ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), IsSporadic .M24 ↥L → IsPGroup 2 ↥S →
      S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
      ∀ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) →
        ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
          ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
          IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
          oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  intro G _ _ L S hL hS2 hSN hSyl z hz hnc
  obtain ⟨e₀⟩ := hL
  exact threeD_of_idx3Model hS2 hSN hSyl hz hnc (Γ := ↥CFSG.Blueprint.NativeSporadic.M24) e₀
    m24_idx3Model

end CFSG.Quasithin.S151S9T
