module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42A0Set
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Act

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam.Completion U42F431

theorem stv_lv_eq_range' {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z) :
    stv c c.lv = (f2 (c := c)).range :=
  le_antisymm (stv_lv_le_range_f2 c) (by
    rintro _ ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a))

theorem mem_stv_xv_iff (y : Y) :
    toG0 y ∈ stv u42Setting.ι u42Setting.ι.xv ↔ y ∈ P1 := by
  rw [stv_xv_eq_range]
  show toG0 y ∈ u42Setting.Mb1 ↔ _
  rw [Mb1_eq]
  show eG y ∈ P1.map eG.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem mem_stv_lv_iff (y : Y) :
    toG0 y ∈ stv u42Setting.ι u42Setting.ι.lv ↔ y ∈ P2 := by
  rw [stv_lv_eq_range']
  show toG0 y ∈ u42Setting.Mb2 ↔ _
  rw [Mb2_eq]
  show eG y ∈ P2.map eG.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem smul_inl_zero_iff (y : Y) :
    y • (Sum.inl 0 : Vtx) = Sum.inl 0 ↔ y ∈ P1 := by
  rw [Sum.smul_inl, Sum.inl.injEq]
  exact MulAction.mem_stabilizer_iff.symm

theorem smul_inr_zero_iff (y : Y) :
    y • (Sum.inr 0 : Vtx) = Sum.inr 0 ↔ y ∈ P2 := by
  rw [Sum.smul_inr, Sum.inr.injEq, lnImg_def, lnImg_eq_iff, mem_P2_iff]
  show (y : P45) '' lnS 0 = lnS 0 ↔ _
  rw [lnS_zero]

theorem stabilizer_inl_zero :
    MulAction.stabilizer Y (Sum.inl 0 : Vtx) = P1 := by
  ext y
  rw [MulAction.mem_stabilizer_iff]
  exact smul_inl_zero_iff y

theorem stabilizer_inr_zero :
    MulAction.stabilizer Y (Sum.inr 0 : Vtx) = P2 := by
  ext y
  rw [MulAction.mem_stabilizer_iff]
  exact smul_inr_zero_iff y

open CFSG.Quasithin.H13.F431.F45

theorem u42XDatum :
    XDatum u42Setting toG0 incGraph (Sum.inl 0) (Sum.inr 0) where
  inj := toG0_injective
  N_eq := by
    rw [N_eq_top]
    exact (MonoidHom.range_eq_top.2 toG0_surjective).symm
  dec g := ⟨eG.symm g, 1, one_smul _ _, one_smul _ _, by
    show g = eG (eG.symm g) * 1
    simp⟩
  stab1 y := by
    rw [← MulAction.mem_stabilizer_iff]
    exact (mem_stv_xv_iff y).trans (smul_inl_zero_iff y).symm
  stab2 y := by
    rw [← MulAction.mem_stabilizer_iff]
    exact (mem_stv_lv_iff y).trans (smul_inr_zero_iff y).symm
  disj y z := by
    rw [Sum.smul_inl, Sum.smul_inr]
    exact Sum.inl_ne_inr
  noadj1 y z := by
    rw [Sum.smul_inl, Sum.smul_inl]
    exact not_adj_inl_inl _ _
  noadj2 y z := by
    rw [Sum.smul_inr, Sum.smul_inr]
    exact not_adj_inr_inr _ _
  adj12 := by
    rw [adj_inl_inr]
    show (0 : Fin 45) ∈ lnS 0
    rw [lnS_zero]
    exact zero_mem_L0S

theorem card_nbrs_inl :
    Nat.card (incGraph.neighborSet (Sum.inl 0)) = 3 := by
  have h : incGraph.neighborSet (Sum.inl 0) =
      Sum.inr '' (↑(Finset.univ.filter fun k : Fin 27 => (lnTab.getD k []).contains 0) :
        Set (Fin 27)) := by
    ext w
    rcases w with q | k
    · simp [SimpleGraph.mem_neighborSet, not_adj_inl_inl]
    · simp [SimpleGraph.mem_neighborSet, adj_inl_inr, lnF, lnS, lineSet]
  rw [h, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inr_injective,
    Set.ncard_coe_finset]
  decide

theorem card_nbrs_inr :
    Nat.card (incGraph.neighborSet (Sum.inr 0)) = 5 := by
  have h : incGraph.neighborSet (Sum.inr 0) =
      Sum.inl '' (↑(Finset.univ.filter fun p : Fin 45 => (lnTab.getD 0 []).contains p.val) :
        Set (Fin 45)) := by
    ext w
    rcases w with q | k
    · simp [SimpleGraph.mem_neighborSet, adj_inr_inl, lnF, lnS, lineSet]
    · simp [SimpleGraph.mem_neighborSet, not_adj_inr_inr]
  rw [h, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_coe_finset]
  decide

end CFSG.Quasithin.H13.F431.U42
