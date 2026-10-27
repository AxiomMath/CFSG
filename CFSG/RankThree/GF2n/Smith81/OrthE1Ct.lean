module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

private theorem ct_inSubgroup_pCore_two_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    (H : Subgroup G) :
    (inSubgroup (CFSG.pCore 2) H).map φ.toMonoidHom =
      inSubgroup (CFSG.pCore 2) (H.map φ.toMonoidHom) := by
  rw [inSubgroup, inSubgroup,
    ← CFSG.pCore_map_iso 2 (H.equivMapOfInjective φ.toMonoidHom φ.injective), Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem ctNormalizes_of : CtNormalizesStatement := by
  intro G _ _ M Q Z B t h c hc hct
  have hQM : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (h.ctx.hyp.Q_normal.2 hg) y).mp hy
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQc : conjSubgroup c Q = Q := conjSubgroup_eq_self_iff.mpr (h.ctx.hyp.Q_normal.2 hc)
  rw [commutatorElement_def] at hct
  have hq : c⁻¹ * t * c * t⁻¹ ∈ Q := by
    have h1 : c⁻¹ * t * c * t⁻¹ = c⁻¹ * (c * t * c⁻¹ * t⁻¹)⁻¹ * c⁻¹⁻¹ := by group
    rw [h1]
    exact hQM c⁻¹ (M.inv_mem hc) _ (Q.inv_mem hct)
  have key : ∀ m ∈ M, (t ∈ conjSubgroup (c * m) (LB M Q B) ↔
      t ∈ conjSubgroup m (LB M Q B)) := by
    intro m hm
    rw [mem_conjSubgroup, mem_conjSubgroup]
    have e : (c * m)⁻¹ * t * (c * m) = (m⁻¹ * (c⁻¹ * t * c * t⁻¹) * m) * (m⁻¹ * t * m) := by
      group
    have hq' : m⁻¹ * (c⁻¹ * t * c * t⁻¹) * m ∈ Q := by
      have := hQM m⁻¹ (M.inv_mem hm) _ hq
      rwa [inv_inv] at this
    rw [e]
    constructor
    · intro h1
      have := (LB M Q B).mul_mem ((LB M Q B).inv_mem (hQL hq')) h1
      rwa [inv_mul_cancel_left] at this
    · intro h2
      exact (LB M Q B).mul_mem (hQL hq') h2
  have hRc : conjSubgroup c (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := by
    apply le_antisymm
    · have hle : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) →
          conjSubgroup c (conjSubgroup m (LB M Q B)) ≤ Rt M (LB M Q B) t := by
        intro m hm htm
        rw [← CFSG.RankThree.GF2n.conjSubgroup_mul]
        exact conjSubgroup_le_Rt (M.mul_mem hc hm) ((key m hm).2 htm)
      show Subgroup.map (MulAut.conj c).toMonoidHom (Rt M (LB M Q B) t) ≤ Rt M (LB M Q B) t
      rw [Subgroup.map_le_iff_le_comap]
      unfold Rt
      refine iSup₂_le fun m hm => iSup_le fun htm => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact hle m hm htm
    · unfold Rt
      refine iSup₂_le fun m hm => iSup_le fun htm => ?_
      have hm' : c⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hc) hm
      have htm' : t ∈ conjSubgroup (c⁻¹ * m) (LB M Q B) :=
        (key (c⁻¹ * m) hm').1 (by rwa [mul_inv_cancel_left])
      have hmL : conjSubgroup m (LB M Q B) =
          conjSubgroup c (conjSubgroup (c⁻¹ * m) (LB M Q B)) := by
        rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel_left]
      rw [hmL]
      exact Subgroup.map_mono (conjSubgroup_le_Rt hm' htm')
  have hRc' : (Rt M (LB M Q B) t).map (MulAut.conj c).toMonoidHom = Rt M (LB M Q B) t := hRc
  have hNc : conjSubgroup c (Nt M (LB M Q B) t) = Nt M (LB M Q B) t := by
    unfold Nt
    show Subgroup.map (MulAut.conj c).toMonoidHom
      (inSubgroup (CFSG.pCore 2) (Rt M (LB M Q B) t)) =
        inSubgroup (CFSG.pCore 2) (Rt M (LB M Q B) t)
    rw [ct_inSubgroup_pCore_two_map, hRc']
  have hXc : conjSubgroup c (E1Xpre M Q B t) = E1Xpre M Q B t := by
    show Subgroup.map (MulAut.conj c).toMonoidHom
      (⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ⊔ Q) =
        ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ⊔ Q
    have hQc' : Q.map (MulAut.conj c).toMonoidHom = Q := hQc
    rw [Subgroup.map_sup, Subgroup.map_commutator, hRc', hQc']
  exact ⟨hRc, hNc, hXc⟩

end CFSG.RankThree.GF2n.Smith81.Smith23E1

end
