module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeCentralizerModel
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameA5

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
open CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.RankThree.PartOne.KA5L
open scoped MatrixGroups



theorem mem_jn_zero_of_commute {g : ModGL .E7 (ZMod 2)} (hgL : g ∈ L7)
    (h1 : ∀ x ∈ Jn 1, g * x = x * g) (h5 : ∀ x ∈ Jn 5, g * x = x * g)
    (h6 : ∀ x ∈ Jn 6, g * x = x * g) (hmu : ∀ x ∈ J mu, g * x = x * g) : g ∈ Jn 0 := by
  obtain ⟨hw1, -, hwmu, -, hw0, hw5, hw6⟩ := a5Word_smul
  set n : ModGL .E7 (ZMod 2) := (wordRepE7 (ZMod 2) a5Word : ModGL .E7 (ZMod 2)) with hn
  have hnL : n ∈ L7 := (wordRepE7 (ZMod 2) a5Word).2
  have hJ : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, IsRoot .E7 γ →
      (J γ).map (MulAut.conj n).toMonoidHom =
        J ((coxeterSystem .E7).wordProd a5Word • γ) :=
    fun hγ => by rw [hn]; exact map_conj_wordRepE7_J a5Word hγ
  have hn1 : (Jn 1).map (MulAut.conj n).toMonoidHom = Jn 1 := by
    have h := hJ (isRoot_single .E7 (1 : Fin (Tag.rank .E7)))
    rwa [hw1] at h
  have hnmu : (J mu).map (MulAut.conj n).toMonoidHom = Jn 4 := by
    have h := hJ isRoot_mu
    rwa [hwmu, J_neg (isRoot_single .E7 _)] at h
  have hn0 : (Jn 0).map (MulAut.conj n).toMonoidHom = Jn 6 := by
    have h := hJ (isRoot_single .E7 (0 : Fin (Tag.rank .E7)))
    rwa [hw0, J_neg (isRoot_single .E7 _)] at h
  have hn5 : (Jn 5).map (MulAut.conj n).toMonoidHom = a2SL2 (ZMod 2) := by
    have h := hJ (isRoot_single .E7 (5 : Fin (Tag.rank .E7)))
    rw [hw5, J_neg isRoot_a2Root] at h
    exact h.trans (rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_a2Root)
  have hn6 : (Jn 6).map (MulAut.conj n).toMonoidHom = highRootSL2 .E7 (ZMod 2) := by
    have h := hJ (isRoot_single .E7 (6 : Fin (Tag.rank .E7)))
    rw [hw6] at h
    exact h.trans (rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_theta)
  have hcomm : ∀ {X : Subgroup (ModGL .E7 (ZMod 2))}, (∀ x ∈ X, g * x = x * g) →
      ∀ y ∈ X.map (MulAut.conj n).toMonoidHom,
        n * g * n⁻¹ * y = y * (n * g * n⁻¹) := by
    rintro X hX _ ⟨x, hx, rfl⟩
    have hxg : g * x = x * g := hX x hx
    have h := congrArg (MulAut.conj n) hxg
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  have hgC : n * g * n⁻¹ ∈ rootSpan .E7 (ZMod 2) (parabolicRoots .E7 a2PerpNodes) := by
    rw [← adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_a2SL2 (K := ZMod 2)
      (fun u => Subsingleton.elim u 1)]
    refine ⟨⟨L7.mul_mem (L7.mul_mem hnL hgL) (L7.inv_mem hnL),
      Subgroup.mem_centralizer_iff.mpr ?_⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · intro y hy
      rw [← hn6] at hy
      exact (hcomm h6 y hy).symm
    · intro y hy
      rw [← hn5] at hy
      exact (hcomm h5 y hy).symm
  rw [← subsystemGroup_eq_rootSpan, a2PerpNodes_eq_a5Nodes, ← range_a5Frame] at hgC
  obtain ⟨A, hA⟩ := hgC
  have hinj := a5Frame_injective
  have hb0 : (blk 0).map (a5Frame (ZMod 2)) = Jn 1 := map_a5Frame_blk 0
  have hb2 : (blk 2).map (a5Frame (ZMod 2)) = Jn 4 := map_a5Frame_blk 2
  have hb4 : (blk 4).map (a5Frame (ZMod 2)) = Jn 6 := map_a5Frame_blk 4
  have hA0 : ∀ x ∈ blk 0, A * x = x * A := by
    intro x hx
    apply hinj
    rw [map_mul, map_mul, hA]
    apply hcomm h1
    rw [hn1, ← hb0]
    exact Subgroup.mem_map_of_mem _ hx
  have hA2 : ∀ x ∈ blk 2, A * x = x * A := by
    intro x hx
    apply hinj
    rw [map_mul, map_mul, hA]
    apply hcomm hmu
    rw [hnmu, ← hb2]
    exact Subgroup.mem_map_of_mem _ hx
  have hA4 := mem_blk_four_of_commute_blk_zero_two hA0 hA2
  have hg0 := Subgroup.mem_map_of_mem (a5Frame (ZMod 2)) hA4
  rw [hb4, hA, ← hn0] at hg0
  obtain ⟨x, hx, hxg⟩ := hg0
  have hxg' : x = g := (MulAut.conj n).injective hxg
  rwa [hxg'] at hx

theorem inf_centralizer_m0_eq_jn_zero :
    L7 ⊓ Subgroup.centralizer (M0 : Set (ModGL .E7 (ZMod 2))) = Jn 0 := by
  apply le_antisymm
  · rintro g ⟨hgL, hgM⟩
    exact mem_jn_zero_of_commute hgL
      (fun x hx =>
        (Subgroup.mem_centralizer_iff.mp hgM x (jn_le_m0 1 (by decide) (by decide) hx)).symm)
      (fun x hx =>
        (Subgroup.mem_centralizer_iff.mp hgM x (jn_le_m0 5 (by decide) (by decide) hx)).symm)
      (fun x hx =>
        (Subgroup.mem_centralizer_iff.mp hgM x (jn_le_m0 6 (by decide) (by decide) hx)).symm)
      (fun x hx => (Subgroup.mem_centralizer_iff.mp hgM x (j_mu_le_m0 hx)).symm)
  · intro g hg
    refine ⟨e7NatFrame_holds.1 0 hg, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro m hm
    exact (Subgroup.mem_centralizer_iff.mp hm.2 g hg).symm

theorem e7NatCent_holds : E7NatCent :=
  e7NatCent_of_doubleCentralizer inf_centralizer_m0_eq_jn_zero

end CFSG.StandardType.FrameRoute.FS81.E7Frame
