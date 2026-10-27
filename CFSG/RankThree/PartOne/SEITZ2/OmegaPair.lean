module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaRatData
public import CFSG.RankThree.PartOne.SEITZ2.OmegaOuter

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.PartOne.CTP
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

theorem subfieldPairOmega8mBig :
    SubfieldPairOmega8mCase (fun f₀ => 2 ≤ f₀) := by
  intro K _ _ k σ p f₀ b c h hf d hd hne
  left
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
  have hk4 : 4 ∣ Nat.card k := by
    rw [h.card_k]
    exact (pow_dvd_pow 2 hf : 2 ^ 2 ∣ 2 ^ f₀)
  have hK : Nat.card K = Nat.card k ^ p := by
    rw [h.card_K, h.card_k, ← pow_mul]
  have hcore := core_pair (F := omegaFrame K (b : K) (c : K) h.bK_ne_zero) h.prime h.ne_two hK hk4
    b.2 c.2 hQK (ratGroupData h) hG hne'
  have hTop : (⊤ : Subgroup (matrixProjectiveDerived (omegaQuad K (b : K) (c : K)))).map
      (projLin hQK) = elementaryGroup (omegaQuad K (b : K) (c : K)) := by
    ext X
    rw [← MonoidHom.range_eq_map, mem_range_projLin hQK, omega_orthDerived_K h]
  apply Subgroup.map_injective hinj
  rw [hTop, MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map, hRd,
    hRat]
  exact hcore

@[expose] def SubfieldPairOmega8mF2 : Prop := SubfieldPairOmega8mCase fun f₀ => f₀ = 1

theorem subfieldPairOmega8m_of_f2 (h : SubfieldPairOmega8mF2) :
    SubfieldPairOmega8m := by
  intro K _ _ k σ p f₀ b c hs _ d hd hne
  rcases Nat.lt_or_ge f₀ 2 with h1 | h2
  · exact h K k σ p f₀ b c hs (by have := hs.one_le; omega) d hd hne
  · exact subfieldPairOmega8mBig K k σ p f₀ b c hs h2 d hd hne

end CFSG.RankThree.PartOne.SEITZ2
