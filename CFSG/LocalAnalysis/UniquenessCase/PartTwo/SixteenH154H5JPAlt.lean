module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvFive
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
import CFSG.CGT.PushingUpLit.SYMB.Delta5Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16jp_isPerfect_of_alt_five {G : Type*} [Group G]
    (e : G ≃* ↥(alternatingGroup (Fin 5))) : Group.IsPerfect G := by
  have h : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (by simp))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16jp_le_commSub_sup {D : FFModel} {H : Subgroup (MulAut W)}
    {I Z : Subgroup W} {π : D.Gam →* ↥H} (h : D.RealizesVia H I Z π)
    (hG : D.sec ≤
      Subgroup.closure {x | ∃ γ : D.Gam, ∃ y ∈ D.sec, D.act γ y * y⁻¹ = x} ⊔ D.ker) :
    I ≤ commSub I H ⊔ Z := by
  obtain ⟨-, -, hks, hIinv, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have key : ∀ x ∈ Subgroup.closure
        {x | ∃ γ : D.Gam, ∃ y ∈ D.sec, D.act γ y * y⁻¹ = x} ⊔ D.ker,
      ∃ hx : x ∈ D.sec, ∃ c : ↥I, (c : W) ∈ commSub I H ∧
        β c = QuotientGroup.mk ⟨x, hx⟩ := by
    intro x hx
    rw [← Subgroup.closure_eq D.ker, ← Subgroup.closure_union] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨γ, y, hy, rfl⟩ | hx
      · obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, hy⟩)
        have hπu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I := hIinv (π γ) u u.2
        have hy' : D.act γ (y : D.Amb) ∈ D.sec := hsec γ y hy
        refine ⟨D.sec.mul_mem hy' (D.sec.inv_mem hy), ⟨_, hπu⟩ * u⁻¹,
          Subgroup.subset_closure ⟨((π γ : ↥H) : MulAut W), (π γ).2, (u : W), u.2, rfl⟩, ?_⟩
        rw [map_mul, map_inv, hβe γ u ⟨y, hy⟩ hπu hy' hu, hu]
        rfl
      · refine ⟨hks hx, 1, (commSub I H).one_mem, ?_⟩
        rw [map_one, eq_comm, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hx
    | one => exact ⟨D.sec.one_mem, 1, (commSub I H).one_mem, by rw [map_one]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hx, c, hc, hcx⟩ := hx
      obtain ⟨hy, d, hd, hdy⟩ := hy
      exact ⟨D.sec.mul_mem hx hy, c * d, (commSub I H).mul_mem hc hd,
        by rw [map_mul, hcx, hdy]; rfl⟩
    | inv x _ hx =>
      obtain ⟨hx, c, hc, hcx⟩ := hx
      exact ⟨D.sec.inv_mem hx, c⁻¹, (commSub I H).inv_mem hc, by rw [map_inv, hcx]; rfl⟩
  intro w hw
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
  obtain ⟨hmx, c, hc, hcm⟩ := key m (hG m.2)
  have h1 : β (⟨w, hw⟩ * c⁻¹) = 1 := by
    rw [map_mul, map_inv, hcm, ← hm]
    exact mul_inv_cancel _
  have h2 := (hβk _).mp h1
  have e : w = (w * (c : W)⁻¹) * c := by group
  rw [e]
  exact (commSub I H ⊔ Z).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hc)

private theorem s16jp_altDn_five_generator :
    (FFModel.altDn 5).sec ≤
      Subgroup.closure {x : G6.PermMod 5 |
        ∃ γ : (FFModel.altDn 5).Gam, ∃ y ∈ (FFModel.altDn 5).sec,
          (FFModel.altDn 5).act γ y * y⁻¹ = x} ⊔ (FFModel.altDn 5).ker := by
  let Gens : Set (G6.PermMod 5) := {x : G6.PermMod 5 |
    ∃ γ : (FFModel.altDn 5).Gam, ∃ y ∈ (FFModel.altDn 5).sec,
      (FFModel.altDn 5).act γ y * y⁻¹ = x}
  have hle : Subgroup.closure {x : G6.coreMod 5 |
      ∃ σ : Equiv.Perm (Fin 5), ∃ u : G6.coreMod 5,
        Equiv.Perm.sign σ = 1 ∧ x = G6.coreAct 5 σ u * u⁻¹} ≤
      (Subgroup.closure Gens).comap (G6.coreMod 5).subtype := by
    rw [Subgroup.closure_le]
    rintro x ⟨σ, u, hσ, rfl⟩
    change (G6.coreMod 5).subtype (G6.coreAct 5 σ u * u⁻¹) ∈ Subgroup.closure Gens
    refine Subgroup.subset_closure ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩, (u : G6.PermMod 5),
      u.2, ?_⟩
    show G6.permAct 5 σ (u : G6.PermMod 5) * (u : G6.PermMod 5)⁻¹ =
      ((G6.coreMod 5).subtype (G6.coreAct 5 σ u * u⁻¹) : G6.PermMod 5)
    rfl
  intro w hw
  have h1 := hle (CFSG.CGT.PushingUpLit.SYMB.Delta5Fix.comm_closure ⟨w, hw⟩)
  exact Subgroup.mem_sup_left h1

theorem s16jp_alt5_commSub_sup {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : AlternatingNatural L I Z 5) : commSub I L ⊔ Z = I := by
  obtain ⟨π, hπ⟩ := h
  refine le_antisymm (sup_le ?_ hπ.2.1) ?_
  · exact commSub_le_of_invariant fun x hx w hw => hπ.2.2.2.1 ⟨x, hx⟩ w hw
  · exact s16jp_le_commSub_sup hπ s16jp_altDn_five_generator

theorem s16jp_row_A5 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (h : s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    commSub ⊤ L ⊓ fixV L = ⊥ := by
  obtain ⟨k, -, (⟨hOM, hS⟩ | ⟨hAlt, hS⟩)⟩ := h
  · have hperf : Group.IsPerfect ↥L :=
      s16jp_isPerfect_of_alt_five (s16k_isAlt_five_of_isOmegaMinus_four hOM).some
    have hN : ∀ I : Subgroup W, AlternatingNatural L I (commSub ⊤ L ⊓ fixV L) 5 →
        ∃ D : FFModel, S16C11V1ModelCover D ∧
          D.Realizes L I (commSub ⊤ L ⊓ fixV L) ∧
          commSub I L ⊔ (commSub ⊤ L ⊓ fixV L) = I := by
      intro I hI
      exact ⟨FFModel.altDn 5, s16c11_v1_cover_alt_odd (by decide) le_rfl, hI,
        s16jp_alt5_commSub_sup hI⟩
    obtain ⟨I, hZI, hind, hsup, hN'⟩ := hS
    have hS' : SumOfNat (fun H U Z => AlternatingNatural H U Z 5) L
        (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k :=
      ⟨I, hZI, hind, hsup,
        fun i => s16k_alternatingNatural_five_of_natOmegaMinus_four (hN' i)⟩
    exact s16jp_sum_cover (W := W) (N := fun H U Z => AlternatingNatural H U Z 5) (k := k)
      hW2 hperf hN hS'
  · have hperf : Group.IsPerfect ↥L := s16jp_isPerfect_of_alt_five hAlt.some
    exact s16jp_sum_cover (W := W) (N := fun H U Z => AlternatingNatural H U Z 5) (k := k)
      hW2 hperf (fun I hI => ⟨FFModel.altDn 5, s16c11_v1_cover_alt_odd (by decide) le_rfl, hI,
        s16jp_alt5_commSub_sup hI⟩) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
