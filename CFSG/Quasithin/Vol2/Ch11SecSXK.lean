module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3
public import CFSG.Quasithin.Vol2.Ch11SecSK0b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_sup_of_modO2Image_le {K A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K)
    (h : modO2Image K A ≤ modO2Image K B) : A ≤ B ⊔ pCoreOf 2 K := by
  rw [← map_comap_modO2Image hB]
  exact le_sup_left.trans ((map_comap_modO2Image hA).symm.le.trans
    (Subgroup.map_mono (Subgroup.comap_mono h)))

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem inf_le_sup_pCoreOf (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    T ⊓ K ≤ (T ⊓ LOf L V₁) ⊔ pCoreOf 2 K := by
  have hS : modO2Image K (T ⊓ K) ≤ modO2Image K (LOf L V₁) := by
    rw [hP.l₁]
    exact (Subgroup.le_normalizer.trans hP.borel).trans inf_le_left
  have h1 := le_sup_of_modO2Image_le inf_le_right h.L₁_le_K hS
  have hQ : pCoreOf 2 K ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    h.pCoreOf_le_normalizer h.T_le_normalizer_L₁
  have h2 := A3.eq_sup_inf_of_le_sup hQ (le_inf h.pCoreOf_le_T le_sup_right)
    ((inf_le_right.trans (sup_comm _ _).le : T ⊓ (LOf L V₁ ⊔ pCoreOf 2 K) ≤
      pCoreOf 2 K ⊔ LOf L V₁))
  have h3 : T ⊓ K ≤ T ⊓ (LOf L V₁ ⊔ pCoreOf 2 K) := le_inf inf_le_left h1
  rw [h2, inf_assoc, inf_eq_right.mpr (le_sup_left : LOf L V₁ ≤ LOf L V₁ ⊔ pCoreOf 2 K),
    sup_comm] at h3
  exact h3

theorem modO2Image_inf_L₁ (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    modO2Image K (T ⊓ LOf L V₁) = modO2Image K (T ⊓ K) := by
  refine le_antisymm (Subgroup.map_mono fun x hx => ⟨hx.1, h.L₁_le_K hx.2⟩) ?_
  calc modO2Image K (T ⊓ K) ≤ modO2Image K ((T ⊓ LOf L V₁) ⊔ pCoreOf 2 K) :=
        Subgroup.map_mono fun x hx => h.inf_le_sup_pCoreOf hP hx
    _ = modO2Image K (T ⊓ LOf L V₁) :=
        modO2Image_sup_pCoreOf (inf_le_right.trans h.L₁_le_K)

theorem cartan_inf_L₁_le_k0Of (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    X ⊓ LOf L V₁ ≤ k0Of K P₂ := by
  have hXK : X ⊓ LOf L V₁ ≤ K := inf_le_right.trans h.L₁_le_K
  have hN₁ : X ⊓ LOf L V₁ ≤ Subgroup.normalizer ((T ⊓ LOf L V₁ : Subgroup G) : Set G) := by
    intro x hx
    have h1 := mem_normalizer_inf_of_mem (h.cartan.1 hx.1).1 (h.cartan.1 hx.1).2
    have h2 := Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, Subgroup.le_normalizer hx.2⟩
    rwa [inf_assoc, inf_eq_right.mpr ((perfectCore_le _).trans inf_le_left)] at h2
  have hbar : modO2Image K (X ⊓ LOf L V₁) ≤ modO2Image K (k0Of K P₂) := by
    rw [modO2Image_k0Of K hP.c₂.2.1]
    refine ((modO2Image_le_normalizer hN₁).trans ?_).trans (inf_le_right : P₁ ⊓ P₂ ≤ P₂)
    rw [h.modO2Image_inf_L₁ hP]
    exact hP.borel
  intro x hx
  have hx' := le_sup_of_modO2Image_le hXK (k0Of_le K P₂) hbar hx
  exact mem_of_mem_sup_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    (h.pCoreOf_le_inf.trans hP.inf_le_normalizer_k0Of) hx'
    (odd_orderOf_of_mem h.cartan.2.1 hx.1)

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
