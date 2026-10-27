module

public import CFSG.Quasithin.Vol2.Ch11SecSX1
public import CFSG.Quasithin.Vol2.Ch11SecSXK

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem inf_eq_sup_pCoreOf (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    T ⊓ K = (T ⊓ LOf L V₁) ⊔ pCoreOf 2 K :=
  le_antisymm (h.inf_le_sup_pCoreOf hP)
    (sup_le (inf_le_inf_left T h.L₁_le_K) h.pCoreOf_le_inf)

theorem cartan_le_normalizer_inf (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  intro x hx
  have h1 := mem_normalizer_inf_of_mem (h.cartan.1 hx).1 (h.cartan.1 hx).2
  have h2 := Subgroup.inf_normalizer_le_normalizer_inf
    ⟨h1, cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx⟩
  rw [inf_assoc, inf_eq_right.mpr ((perfectCore_le _).trans inf_le_left)] at h2
  have h3 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
    (h.cartan_le_normalizer_K hN h1102 hx)
  rw [h.inf_eq_sup_pCoreOf hP, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h2, Subgroup.mem_normalizer_iff_map_conj_eq.mp h3]

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
