module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Std
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2CoreHolds

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.PartOne.CTP
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

theorem subfieldPairOmega8mSmall_of_core (hcore : OmegaF2Core) :
    SubfieldPairOmega8mSmall := by
  intro K _ _ k σ p b c h _ d hd hne
  have : CharP K 2 := h.charP
  have hQK := (omega_reg_K h).1
  obtain ⟨g', rfl⟩ := hd
  obtain ⟨G, hG, hconj⟩ := exists_isometry_projLin_conj hQK g'
  have hinj := projLin_injective hQK
  have hRat := map_projLin_fixed h
  have hRd : ((fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
        (h.quad_invariant (by norm_num) h.order))).map
          (linearConjugationHom (omegaQuad K (b : K) (c : K)) g').toMonoidHom).map
        (projLin hQK) = (omegaRat K k b c).map (MulAut.conj G).toMonoidHom := by
    rw [← hRat]
    ext X
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨projLin hQK x, ⟨x, hx, rfl⟩, (hconj x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, hconj x⟩
  have hne' : (omegaRat K k b c).map (MulAut.conj G).toMonoidHom ≠ omegaRat K k b c := by
    intro h1
    apply hne
    apply Subgroup.map_injective hinj
    rw [hRd, h1, hRat]
  have hk : Nat.card k = 2 := by
    rw [h.card_k]
    norm_num
  have hK : Nat.card K = 2 ^ p := by
    rw [h.card_K]
    norm_num
  have hb1 : (b : K) = 1 := by
    rcases (mem_subfield_two_iff hk).1 b.2 with h0 | h1
    · exact absurd h0 h.bK_ne_zero
    · exact h1
  have hc1 : (c : K) = 1 := by
    rcases (mem_subfield_two_iff hk).1 c.2 with h0 | h1
    · have hc0 : c = 0 := Subtype.ext h0
      exact absurd (by simp [hc0]) (h.irr 0)
    · exact h1
  have hcore' := core_pair_f2 hcore (F := omegaFrame K (b : K) (c : K) h.bK_ne_zero) hb1 hc1
    h.prime h.ne_two hK hk hQK (ratGroupData h) hG hne'
  have hTop : (⊤ : Subgroup (matrixProjectiveDerived (omegaQuad K (b : K) (c : K)))).map
      (projLin hQK) = elementaryGroup (omegaQuad K (b : K) (c : K)) := by
    ext X
    rw [← MonoidHom.range_eq_map, mem_range_projLin hQK, omega_orthDerived_K h]
  apply Subgroup.map_injective hinj
  rw [hTop, MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map, hRd,
    hRat]
  exact hcore'

theorem subfieldPairOmega8mSmall : SubfieldPairOmega8mSmall :=
  subfieldPairOmega8mSmall_of_core omegaF2Core_holds

end CFSG.RankThree.PartOne.SEITZ2
