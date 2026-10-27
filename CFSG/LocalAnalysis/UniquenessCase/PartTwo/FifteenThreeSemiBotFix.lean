module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15_semiBot_mem_fixV_iSup_iff {W : Type*} [CommGroup W] {ι : Type*}
    (K : ι → Subgroup (MulAut W)) (q : W) :
    q ∈ fixV (⨆ i, K i) ↔ ∀ i, q ∈ fixV (K i) := by
  refine ⟨fun hq i x hx => hq x (Subgroup.mem_iSup_of_mem i hx), fun hq => ?_⟩
  rw [mem_fixV]
  intro x hx
  exact Subgroup.iSup_induction K (C := fun x => x q = q) hx (fun i x hx => hq i x hx) rfl
    (fun x y hx hy => by rw [MulAut.mul_apply, hy, hx])

theorem s15_semiBot_fixV_iSup_le {W : Type*} [CommGroup W] {ι : Type*} [Finite ι]
    (K : ι → Subgroup (MulAut W)) (U : ι → Subgroup W)
    (hKU : ∀ i j, i ≠ j → U i ≤ fixV (K j)) (hU : ⨆ i, U i = ⊤) :
    fixV (⨆ i, K i) ≤ ⨆ i, (U i ⊓ fixV (⨆ j, K j)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let C : Subgroup W := fixV (⨆ i, K i)
  have hC : ∀ q : W, q ∈ C ↔ ∀ i, q ∈ fixV (K i) := s15_semiBot_mem_fixV_iSup_iff K
  have key : ∀ S : Finset ι, ∀ q : W, q ∈ C → q ∈ (⨆ i ∈ S, U i) →
      q ∈ ⨆ i ∈ S, (U i ⊓ C) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro q hq hqS
      have hbot : (⨆ i ∈ (∅ : Finset ι), U i) = ⊥ := by
        rw [← Finset.sup_eq_iSup, Finset.sup_empty]
      rw [hbot, Subgroup.mem_bot] at hqS
      subst q
      exact Subgroup.one_mem _
    | insert a S ha ih =>
      intro q hq hqS
      rw [Finset.iSup_insert] at hqS
      obtain ⟨u, hu, b, hb, hub⟩ := Subgroup.mem_sup.1 hqS
      have hqK : ∀ i, q ∈ fixV (K i) := (hC q).1 hq
      have hSle : (⨆ i ∈ S, U i) ≤ fixV (K a) := by
        refine iSup_le fun i => iSup_le fun hi => ?_
        exact hKU i a (fun hia => ha (hia ▸ hi))
      have hbKa : b ∈ fixV (K a) := hSle hb
      have huKa : u ∈ fixV (K a) := by
        rw [mem_fixV]
        intro g hg
        have h1 : g u * b = u * b := by
          calc g u * b = g u * g b := by rw [hbKa g hg]
            _ = g (u * b) := (map_mul g u b).symm
            _ = g q := by rw [hub]
            _ = q := hqK a g hg
            _ = u * b := hub.symm
        exact mul_right_cancel h1
      have huC : u ∈ C := (hC u).2 fun j => by
        by_cases hj : j = a
        · rwa [hj]
        · exact hKU a j (fun haj => hj haj.symm) hu
      have hbC : b ∈ C := by
        have hb_eq : b = u⁻¹ * q := by
          rw [← hub]
          group
        rw [hb_eq]
        exact C.mul_mem (C.inv_mem huC) hq
      rw [Finset.iSup_insert]
      rw [← hub]
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hu, huC⟩) (ih b hbC hb)
  intro q hq
  have hqC : q ∈ C := hq
  have huniv : (⨆ i ∈ (Finset.univ : Finset ι), U i) = ⊤ := by
    rw [← Finset.iSup_coe, Finset.coe_univ, iSup_univ, hU]
  have hqS : q ∈ (⨆ i ∈ (Finset.univ : Finset ι), U i) := by
    rw [huniv]
    exact Subgroup.mem_top q
  have hgoal : (⨆ i ∈ (Finset.univ : Finset ι), (U i ⊓ C)) = ⨆ i, (U i ⊓ C) := by
    rw [← Finset.iSup_coe, Finset.coe_univ, iSup_univ]
  have hmem := key Finset.univ q hqC hqS
  rwa [hgoal] at hmem

section Concrete

variable {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_imgTil_le_fixV (h : Hyp151 D V₀ V L) :
    imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) ≤
      fixV (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) := by
  intro q hq
  exact (s15_semiBot_mem_fixV_iSup_iff
    (fun m : D.M => barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) q).2
    (fun m => s15_Core_imgTil_v1Sub_le_fixV h m.2 hq)

theorem s15_semiBot_fixV_le_imgTil (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    fixV (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) ≤
      imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) := by
  classical
  have hV := h.isElemAbelian
  let Xb : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))
  let ι := {X : Subgroup (MulAut (Vtil V₀ V hV)) //
    ∃ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G)) = X}
  let K : ι → Subgroup (MulAut (Vtil V₀ V hV)) := Subtype.val
  let U : ι → Subgroup (Vtil V₀ V hV) := fun X => commSub ⊤ X.1
  have hKXb : (⨆ i : ι, K i) = Xb := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => ?_
      obtain ⟨m, hm⟩ := i.2
      change i.1 ≤ Xb
      rw [← hm]
      exact le_iSup (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))) m
    · change Xb ≤ ⨆ i : ι, K i
      refine iSup_le fun m => ?_
      exact le_iSup (fun i : ι => K i) ⟨barSub V₀ V hV (conjSubgroup L (m : G)), m, rfl⟩
  have hU : (⨆ i : ι, U i) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← s15_Two_iSup_commSub_eq_top D h1217 h hL]
    refine iSup_le fun m => ?_
    exact le_iSup (fun i : ι => U i) ⟨barSub V₀ V hV (conjSubgroup L (m : G)), m, rfl⟩
  have hKU : ∀ i j : ι, i ≠ j → U i ≤ fixV (K j) := by
    intro i j hij
    obtain ⟨mi, hmi⟩ := i.2
    obtain ⟨mj, hmj⟩ := j.2
    have hne : (mj : G) * (mi : G)⁻¹ ∉ nBar D.M V₀ V hV L := by
      intro hmem
      apply hij
      apply Subtype.ext
      have hmem' := (s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV mi.2 mj.2).1 hmem
      rw [← hmi, ← hmj]
      exact hmem'.symm
    have hc := (s15_Kbar_commute_conj h mi.2 mj.2 hne).2
    have hle := commSub_eq_bot_iff.mp hc
    have hUi : U i = commSub ⊤ (barSub V₀ V hV (conjSubgroup L (mi : G))) := by
      change commSub ⊤ i.1 = commSub ⊤ (barSub V₀ V hV (conjSubgroup L (mi : G)))
      rw [← hmi]
    have hKj : K j = barSub V₀ V hV (conjSubgroup L (mj : G)) := by
      change j.1 = barSub V₀ V hV (conjSubgroup L (mj : G))
      rw [← hmj]
    rw [hUi, hKj]
    exact hle
  have hmain := s15_semiBot_fixV_iSup_le K U hKU hU
  rw [hKXb] at hmain
  refine hmain.trans ?_
  refine iSup_le fun i => ?_
  obtain ⟨m, hm⟩ := i.2
  have hUi : U i = commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m : G))) := by
    change commSub ⊤ i.1 = commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m : G)))
    rw [← hm]
  rw [hUi]
  exact s15_Core_inf_fixV_le_imgTil_v1Sub h hL m

theorem s15_semiBot_imgTil_v1Sub_eq_fixV (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) =
      fixV (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) :=
  le_antisymm (s15_semiBot_imgTil_le_fixV h) (s15_semiBot_fixV_le_imgTil h1217 h hL)

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
