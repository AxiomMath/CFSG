module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanD
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_barImage_beta_eq_prod {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) :
    (barImage (conjClosure D.M L)
        (conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))).map
        e.toMonoidHom =
      (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
        (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := conjClosure D.M L
  let P : Subgroup G := D.T ⊓ X
  let Bc : Subgroup G := X ⊓ normalizer (P : Set G)
  let UL : Subgroup (Bar2 L) := barImage L (D.T ⊓ L)
  let UK : Subgroup (Bar2 K) := barImage K (D.T ⊓ K)
  have hQleP : pCoreOf 2 X ≤ P :=
    uc22r3e5c_pCoreOf_le_of_sylow (uc22r3e5c_isSylowTwoOf_inf hL)
  have hBarBc : barImage X Bc = Subgroup.normalizer (barImage X P : Set (Bar2 X)) :=
    uc22r3e5c_barImage_inf_normalizer inf_le_right hQleP
  have hMap : (barImage X P).map e.toMonoidHom = UL.prod UK :=
    uc22r3e5c_map_barImage_inf_eq_prod hL hKC hKne hset hSz heL heK
  calc (barImage X Bc).map e.toMonoidHom
      = (Subgroup.normalizer (barImage X P : Set (Bar2 X))).map e.toMonoidHom := by rw [hBarBc]
    _ = Subgroup.normalizer ((barImage X P).map e.toMonoidHom : Set (Bar2 L × Bar2 K)) :=
        Subgroup.map_normalizer_eq_of_bijective _ e.bijective
    _ = Subgroup.normalizer ((UL.prod UK : Subgroup (Bar2 L × Bar2 K)) :
          Set (Bar2 L × Bar2 K)) := by rw [hMap]
    _ = (Subgroup.normalizer (UL : Set (Bar2 L))).prod
          (Subgroup.normalizer (UK : Set (Bar2 K))) := uc22r3e5c_normalizer_prod UL UK

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
