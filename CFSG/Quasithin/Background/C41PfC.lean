module

public import CFSG.Quasithin.Background.C41PfB
public import CFSG.Quasithin.Background.C41PfDefs
public import CFSG.Quasithin.Background.C24PfC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace C41Pf

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem le_normalizer (h82 : Asc82Thm2)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X) (hC129 : ASC129Statement G)
    (hC111 : ASC111Statement G) (hC19 : ASC19Statement G) (hKG : C41KGBorel)
    (h : HypC28 H R M L V) (hK : K ∈ cComp H) (hKc : CharTwo K)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M) :
    R ≤ Subgroup.normalizer (K : Set G) := by
  by_contra hRN
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 hA37 hA38
  have hsyl : IsSylowTwoOf (R ⊓ K) K :=
    (asc24Two_of_hypC28 h82 hA37 hA38 hS h hK hKc hKq).resolve_right hRN
  obtain ⟨hchi, -, -⟩ :=
    (C24Pf.asc24One_of hA37 hA38 hS hC129 H R M K (c2_10_four h) hK hKc hKq hsyl).resolve_left hKM
  have hNK : conjClosure L M ≤ Subgroup.normalizer (K : Set G) :=
    conjClosure_le_normalizer hA3 h hK
  have hNS : conjClosure L M ≤ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) :=
    le_trans (le_inf (c2_9_two h).1 hNK) Subgroup.inf_normalizer_le_normalizer_inf
  exact not_commutator_le_pCoreOf hC129 hC111 hC19 hA3 h hK hKM
    (hKG G K (conjClosure L M) (R ⊓ K) hKq hchi.2 (C2Nine.perfect_conjClosure_of_hyp h) hNK hsyl
      hNS)

end C41Pf

end CFSG.Quasithin
