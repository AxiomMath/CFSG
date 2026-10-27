module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImage

public section

namespace CFSG.StandardType

theorem GGSecFiveRouteCfg.nbr_axis_or_dense {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 3 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hK : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hKL : ¬ ggAutomizer K Bs ≤ ggAutomizer L Bs) (hy : y ∈ Bs) :
    (∃ j : Fin n, j ≠ i0 ∧
        ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∧
        ∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) ∨
      ((∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom) ∧
        ∀ k, eta ⟨y, hy⟩ k ≠ 1) := by
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hfix : ∀ w ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom,
      w (eta ⟨y, hy⟩) = eta ⟨y, hy⟩ := by
    refine ((hR.1.fixLineComp_nbr hFC hR.2.1 hB hnb).forall_map_congr_fix_iff eta _).2 ?_
    rw [MulEquiv.symm_apply_apply]
    exact Subgroup.mem_zpowers y
  rcases hR.nbr_coordType hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hEta hnb hK with
    ⟨j, hj⟩ | ⟨δ, hδ, hS⟩
  · refine Or.inl ⟨j, ?_, hj, ?_⟩
    · rintro rfl
      refine hKL ((Subgroup.map_le_map_iff_of_injective
        (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective).1 ?_)
      rw [hL]
      rcases hj with h | h
      · exact h.le
      · exact h.le.trans (dCoordinateBlock_le_bCoordinateBlock _)
    · rcases hj with h | h
      · rw [h] at hfix
        exact (forall_bCoordinateBlock_fix_iff hp hp2 j _).1 hfix
      · rw [h] at hfix
        exact (forall_dCoordinateBlock_fix_iff hp hp2 hn j _).1 hfix
  · refine Or.inr ⟨⟨δ, hδ, hS⟩, fun k hk => ?_⟩
    rw [hS] at hfix
    obtain ⟨c, hc⟩ := exists_const_of_forall_map_conj_aPermutationFull_fix δ hfix
    obtain ⟨ε, hε, hconst⟩ := exists_signs_apply_const hδ
    have h := hconst c k
    rw [← hc, hk, toAdd_one] at h
    have hc0 : c = 0 := by
      calc c = ε k * (ε k * c) := by rw [← mul_assoc, SpCoord.coord_sign_mul_self (hε k), one_mul]
        _ = 0 := by rw [← h, mul_zero]
    have h1 : eta ⟨y, hy⟩ = 1 := by
      rw [hc, hc0]
      exact map_one δ
    exact hnb.1.2.2.1 (congrArg Subtype.val ((MulEquiv.map_eq_one_iff eta).1 h1))

theorem GGSecFiveRouteCfg.not_nbr_of_two_ne_one_of_eq_one {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 3 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAll : ∀ (y' : G) (M : Subgroup G), GGNbr p B x D J y' M →
      ggAutomizer M Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {y : G} (hy : y ∈ Bs) {a b k0 : Fin n} (hab : a ≠ b)
    (ha : eta ⟨y, hy⟩ a ≠ 1) (hb : eta ⟨y, hy⟩ b ≠ 1)
    (hz : eta ⟨y, hy⟩ k0 = 1) :
    ∀ M : Subgroup G, ¬ GGNbr p B x D J y M := by
  intro M hnb
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hfix : ∀ w ∈ (ggAutomizer M Bs).map (MulAut.congr eta).toMonoidHom,
      w (eta ⟨y, hy⟩) = eta ⟨y, hy⟩ := by
    refine ((hR.1.fixLineComp_nbr hFC hR.2.1 hB hnb).forall_map_congr_fix_iff eta _).2 ?_
    rw [MulEquiv.symm_apply_apply]
    exact Subgroup.mem_zpowers y
  have haxis : ∀ j : Fin n, (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) → False := by
    intro j hcoords
    have haj : a = j := by
      by_contra h
      exact ha (hcoords a h)
    have hbj : b = j := by
      by_contra h
      exact hb (hcoords b h)
    exact hab (haj.trans hbj.symm)
  rcases hR.nbr_coordType hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hEta hnb
      (hAll y M hnb) with ⟨j, hA⟩ | ⟨δ, hδ, hS⟩
  · rcases hA with hA | hA
    · rw [hA] at hfix
      exact haxis j ((forall_bCoordinateBlock_fix_iff hp hp2 j _).1 hfix)
    · rw [hA] at hfix
      exact haxis j ((forall_dCoordinateBlock_fix_iff hp hp2 hn j _).1 hfix)
  · rw [hS] at hfix
    obtain ⟨c, hc⟩ := exists_const_of_forall_map_conj_aPermutationFull_fix δ hfix
    obtain ⟨ε, hε, hconst⟩ := exists_signs_apply_const hδ
    have h := hconst c k0
    rw [← hc, hz, toAdd_one] at h
    have hc0 : c = 0 := by
      calc c = ε k0 * (ε k0 * c) := by
              rw [← mul_assoc, SpCoord.coord_sign_mul_self (hε k0), one_mul]
        _ = 0 := by rw [← h, mul_zero]
    have h1 : eta ⟨y, hy⟩ = 1 := by
      rw [hc, hc0]
      exact map_one δ
    exact hnb.1.2.2.1 (congrArg Subtype.val ((MulEquiv.map_eq_one_iff eta).1 h1))


end CFSG.StandardType

end
