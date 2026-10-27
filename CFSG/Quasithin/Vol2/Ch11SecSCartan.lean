module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanL2
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X : Subgroup G}

theorem cartan_of (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X) :
    CartanL L V₁ V₂ X ∧ (KindSp4 L (fsuV T I) 2 → CartanSp4 L V₁ V₂ X) ∧
      (KindG2 L (fsuV T I) 2 → CartanG2 L V₁ V₂ X) := by
  have d := transportData hN h1102 h hV₁ hV₂ hX
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hP := isSylowTwoOf_P h
  have hU₁ := isFlagW_of_isVi h hV₁
  have hU₂ := isFlagW_of_isVi h hV₂
  have hD := isHall_autOn_cartan h1102 h hX
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I 2 h
  rcases hk with ⟨K, _, _, hK, e, π, hπ, -⟩ | ⟨K, _, _, hK, e, π, hπ, -⟩ |
      ⟨K, _, _, hK, e, hnat⟩
  · have hc := hC.sl3 K 2 le_rfl hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD
    have hk : KindSL3 L (fsuV T I) 2 := ⟨K, inferInstance, inferInstance, hK, e⟩
    exact ⟨cartanL_of_concl d hc, fun h2 => (kind_not_SL3_Sp4 (by norm_num) hk h2).elim,
      fun h2 => (kind_not_SL3_G2 hG2 le_rfl hk h2).elim⟩
  · obtain ⟨hc, hc'⟩ := hC.sp4 K 2 le_rfl hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD
    have hk : KindSp4 L (fsuV T I) 2 := ⟨K, inferInstance, inferInstance, hK, e⟩
    exact ⟨cartanL_of_concl d hc, fun _ => cartanSp4_of_fourDiag d (hc' rfl),
      fun h2 => (kind_not_Sp4_G2 hG2 le_rfl hk h2).elim⟩
  · obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
    obtain ⟨hc, hc'⟩ := hC.g2 K' 2 le_rfl hK' _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD
    have hk : KindG2 L (fsuV T I) 2 := ⟨K, inferInstance, inferInstance, hK, e⟩
    exact ⟨cartanL_of_concl d hc, fun h2 => (kind_not_Sp4_G2 hG2 le_rfl h2 hk).elim,
      fun _ => cartanG2_of_le d (hc' rfl)⟩

end CFSG.Quasithin.Vol2.Ch11.SecS
