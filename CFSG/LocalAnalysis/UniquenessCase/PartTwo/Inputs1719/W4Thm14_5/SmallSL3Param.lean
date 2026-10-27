module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.AGL81I.Section3.SL3BorelOvergroups
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix

private theorem isSL3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (χ : X ≃* Y) {e : ℕ}
    (h : IsSL3 X e) : IsSL3 Y e :=
  ⟨CFSG.Open.IsQuasisimple.of_mulEquiv χ.symm h.1,
    CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) χ (Subgroup.map_center_eq χ))
      h.2⟩

theorem pCore_two_eq_bot_of_isIrrOn {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥) : CFSG.pCore 2 ↥L = ⊥ := by
  have hO2 := o2Trivial_of_isIrrOn hI hirr
  have hnorm : (((CFSG.pCore 2 ↥L).map L.subtype).subgroupOf L).Normal := by
    show (((CFSG.pCore 2 ↥L).map L.subtype).comap L.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    exact CFSG.pCore_normal
  have h := hO2 _ (Subgroup.map_subtype_le _) hnorm (CFSG.pCore_isPGroup.map L.subtype)
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h

theorem eq_one_of_mem_scalars_of_mem_perfectCore_Q3 {K : Type} [Field K] [Finite K] [CharP K 2]
    (j : Fin 2) {x : SL(3, K)} (hx : x ∈ perfectCore (CFSG.QuasithinUnique.Setup.X7a.Q3 K j))
    (hs : x ∈ LinearFlag.scalars 3 K) : x = 1 := by
  obtain ⟨c, -, hc⟩ := hs
  set y := CFSG.QuasithinUnique.Vol2Native.A312L.blk3 (K := K) j ⟨x, hx⟩
  have hy : ((y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (c : K) := by
    rw [CFSG.QuasithinUnique.Vol2Native.A312L.blk3_coe]
    ext i k
    rw [CFSG.QuasithinUnique.Vol2Native.A312L.blkAt_apply]
    simp only [hc, Matrix.scalar_apply, Matrix.diagonal_apply, Fin.mk.injEq,
      Nat.add_left_cancel_iff, Fin.val_inj]
  have hdet : (c : K) * c = 1 := by
    have h := y.2
    rw [hy, Matrix.det_fin_two] at h
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using h
  have hc1 : (c : K) = 1 := by
    have h2 : ((c : K) + 1) * ((c : K) + 1) = 0 := by
      have h' : ((c : K) + 1) * ((c : K) + 1) = (c : K) * c + 1 + ((c : K) + c) := by ring
      rw [h', hdet, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have h3 : (c : K) + 1 = 0 := mul_self_eq_zero.1 h2
    calc (c : K) = (c : K) + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 := by rw [h3, zero_add]
  apply Subtype.ext
  rw [hc, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]

private theorem commutator_eq_self_of_isQuasisimple {G : Type} [Group G] {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hq.1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem nParam_eq_of_cover {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {L P : Subgroup (MulAut I)} (hq : CFSG.Open.IsQuasisimple ↥L) (hirr : IsIrrOn L ⊤ ⊥)
    {e n : ℕ} (hS : IsSL3 ↥L e) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ e) {φ : SL(3, F) →* ↥L}
    (hφ : CFSG.QuasithinUnique.Setup.X7Sec.Cover φ)
    (hPL : P ≤ L) (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥)
    (hN : NParam (Hinf P) n) : n = e := by
  classical
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNat : Nat.card F = 2 ^ e := by rw [Nat.card_eq_fintype_card, hF]
  set Q : Subgroup SL(3, F) := (P.subgroupOf L).comap φ with hQdef
  have hQmap : Q.map φ = P.subgroupOf L :=
    Subgroup.map_comap_eq_self_of_surjective hφ.surjective _
  have hparQ : IsParabolicTwo SL(3, F) Q := IsParabolicTwo.comap φ hφ.surjective hpar
  have hPeq : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hHinfP : Hinf P = ((Hinf Q).map φ).map L.subtype := by
    rw [Hinf_map φ Q, hQmap, Hinf_map L.subtype, hPeq]
  obtain ⟨S₀, hS₀⟩ := hparQ
  obtain ⟨U₀, hU₀⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3, F) U₀ S₀
  set Q' : Subgroup SL(3, F) := Q.comap (MulAut.conj g).toMonoidHom with hQ'def
  have hQQ' : Q = Q'.map (MulAut.conj g).toMonoidHom :=
    (Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective Q).symm
  have hgU : ((g • U₀ : Sylow 2 SL(3, F)) : Subgroup SL(3, F)) =
      (U₀ : Subgroup SL(3, F)).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hBQ' : LinearFlag.upperTriangular 3 F ≤ Q' := by
    rw [← LinearFlag.normalizer_unitriangular, ← hU₀]
    intro x hx
    rw [hQ'def, Subgroup.mem_comap]
    apply hS₀
    rw [← hg]
    change (MulAut.conj g).toMonoidHom x ∈
      normalizer (((g • U₀ : Sylow 2 SL(3, F)) : Subgroup SL(3, F)) : Set SL(3, F))
    rw [hgU, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hx
  have hHinfQ : Hinf Q = (Hinf Q').map (MulAut.conj g).toMonoidHom := by
    rw [hQQ', Hinf_map]
  have hne' : Hinf Q' ≠ ⊥ := by
    intro h0
    apply hinf
    rw [hHinfP, hHinfQ, h0, Subgroup.map_bot, Subgroup.map_bot, Subgroup.map_bot]
  have hmax : ∀ j : Fin 2, Q' = CFSG.QuasithinUnique.Setup.X7a.Q3 F j → n = e := by
    intro j hQ3
    have hQ'core : Hinf Q' = perfectCore (CFSG.QuasithinUnique.Setup.X7a.Q3 F j) := by
      rw [Hinf_eq_perfectCore, hQ3]
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hF
        exact (Fintype.one_lt_card (α := F)).ne' hF
      · exact h0
    have he2 : 2 ≤ e := by
      by_contra hlt
      have he1' : e = 1 := by omega
      apply hne'
      rw [hQ'core]
      exact perfectCore_Q3_eq_bot_of_card_two (by rw [hNat, he1']; norm_num) j
    have hinj : ∀ x ∈ Hinf Q, φ x = 1 → x = 1 := by
      intro x hx hx1
      have hxs := hφ.ker_le x hx1
      rw [hHinfQ] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hc : (MulAut.conj g).toMonoidHom y ∈ Subgroup.center SL(3, F) := by
        rw [← LinearFlag.scalars_eq_center]
        exact hxs
      have hyz : y = (MulAut.conj g).toMonoidHom y := by
        have hcomm := Subgroup.mem_center_iff.1 hc g
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcomm ⊢
        calc y = g⁻¹ * (g * y * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * y * g⁻¹)) := by rw [hcomm]
          _ = g * y * g⁻¹ := by group
      have hys : y ∈ LinearFlag.scalars 3 F := by
        rw [hyz]
        exact hxs
      rw [hQ'core] at hy
      rw [eq_one_of_mem_scalars_of_mem_perfectCore_Q3 j hy hys, map_one]
    have hsub : Function.Injective (φ.subgroupMap (Hinf Q)) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      apply Subtype.ext
      exact hinj a a.2 (congrArg Subtype.val ha)
    let e1 : ↥(Hinf P) ≃* ↥((Hinf Q).map φ) :=
      (MulEquiv.subgroupCongr hHinfP).trans
        (((Hinf Q).map φ).equivMapOfInjective L.subtype L.subtype_injective).symm
    let e2 : ↥((Hinf Q).map φ) ≃* ↥(Hinf Q) :=
      (MulEquiv.ofBijective (φ.subgroupMap (Hinf Q))
        ⟨hsub, φ.subgroupMap_surjective (Hinf Q)⟩).symm
    let e3 : ↥(Hinf Q) ≃* ↥(Hinf Q') :=
      (MulEquiv.subgroupCongr hHinfQ).trans
        ((Hinf Q').equivMapOfInjective _ (MulAut.conj g).injective).symm
    let e4 : ↥(Hinf Q') ≃* ↥(perfectCore (CFSG.QuasithinUnique.Setup.X7a.Q3 F j)) :=
      MulEquiv.subgroupCongr hQ'core
    obtain ⟨χ⟩ := nonempty_bar2_equiv_of_mulEquiv (e1.trans (e2.trans (e3.trans e4)))
    have hL2 := isL2_bar2_perfectCore_Q3 hNat he2 j
    exact kNshape_holds _ _ n e hN (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hL2))
  rcases CFSG.LocalAnalysis.AGL81I.Section3.borel_overgroups_sl3 Q' hBQ' with hQ' | hQ' | hQ' | hQ'
  ·
    have hQtop : Q = ⊤ := by
      rw [hQQ', hQ', Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
    have hPL' : P = L := by
      have h1 : P.subgroupOf L = ⊤ := by
        rw [← hQmap, hQtop, Subgroup.map_top_of_surjective φ hφ.surjective]
      exact le_antisymm hPL (Subgroup.subgroupOf_eq_top.1 h1)
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPL' (commutator_eq_self_of_isQuasisimple hq)
      (pCore_two_eq_bot_of_isIrrOn hI hirr)
    exact nParam_eq_of_isSL3 hN (isSL3_of_mulEquiv χ.symm hS)
  · exact hmax 0 (by rw [hQ', CFSG.QuasithinUnique.Setup.X7a.Q3_eq]; rfl)
  · exact hmax 1 (by rw [hQ', CFSG.QuasithinUnique.Setup.X7a.Q3_eq]; rfl)
  ·
    exfalso
    apply hne'
    have hsolv : Group.IsSolvable ↥Q' := by
      rw [hQ']
      exact CFSG.QuasithinUnique.Setup.X7a.isSolvable_upperTriangular ⟨e, hNat⟩
    rw [Hinf_eq_perfectCore]
    exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot Q').1 hsolv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
