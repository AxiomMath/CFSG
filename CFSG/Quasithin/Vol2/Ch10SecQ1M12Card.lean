module

public import CFSG.Quasithin.Vol2.Ch10SecQ1M12Res
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM23

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native.L239.Covers
open scoped Pointwise

theorem psi23_j23 (g : Equiv.Perm (Fin 23)) (i : Fin 23) : psi23 g (j23 i) = j23 (g i) := by
  show j23Split.symm (Equiv.optionCongr g (j23Split (j23 i))) = j23 (g i)
  rw [j23Split_j23]
  rfl

theorem psi23_mog23EquivM23
    (x : ↥mog23) :
    psi23 ((mog23EquivM23 x : NativeSporadic.M23) : Equiv.Perm (Fin 23)) = x := by
  rw [← Subgroup.coe_equivMapOfInjective_apply NativeSporadic.M23 psi23 psi23_injective]
  simp [mog23EquivM23]

theorem card_stabilizer_D23 :
    Nat.card (MulAction.stabilizer M23g D23) = 7920 := by
  rw [stabilizer_eq_closure]
  exact card_closure_eq yM yM_rel1 yM_rel2 yM_ne_one

theorem smul_D23_of_mem_presSub
    (x : ↥mog23) (hx : (x : Equiv.Perm (Fin 24)) ∈ presSub) :
    (mog23EquivM23 x : M23g) • D23 = D23 := by
  set g := mog23EquivM23 x
  have hg : psi23 (g : Equiv.Perm (Fin 23)) = x := psi23_mog23EquivM23 x
  have hsub : D23.image (fun i => (g : Equiv.Perm (Fin 23)) i) ⊆ D23 := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    rw [← dodecadW_j23, ← psi23_j23, hg, hx (j23 i)]
    exact (dodecadW_j23 i).2 hi
  have himg : g • D23 = D23.image (fun i => (g : Equiv.Perm (Fin 23)) i) := by
    rw [Finset.smul_finset_def]
    rfl
  rw [himg]
  exact Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ (g : Equiv.Perm (Fin 23)).injective])

theorem card_m24Fix_le :
    Nat.card ↥(m24Fix dodecadE) ≤ 95040 := by
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥(m24Fix dodecadE) (0 : Fin 24))
  rw [MulAction.index_stabilizer] at h1
  have horb : (MulAction.orbit ↥(m24Fix dodecadE) (0 : Fin 24)).ncard ≤ 12 := by
    have hsub : MulAction.orbit ↥(m24Fix dodecadE) (0 : Fin 24) ⊆
        ↑(Finset.univ.filter fun y : Fin 24 => dodecadW y = 0) := by
      rintro _ ⟨g, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      show dodecadW ((g : Equiv.Perm (Fin 24)) 0) = 0
      rw [m24Fix_le_presSub g.2 0, dodecadW_zero]
    calc _ ≤ (↑(Finset.univ.filter fun y : Fin 24 => dodecadW y = 0) : Set (Fin 24)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 12 := by rw [Set.ncard_coe_finset, card_compl_dodecad]
  have hstab : Nat.card (MulAction.stabilizer ↥(m24Fix dodecadE) (0 : Fin 24)) ≤ 7920 := by
    rw [← card_stabilizer_D23]
    refine Nat.card_le_card_of_injective (fun s => ⟨mog23EquivM23
      ⟨s.1.1, s.1.2.1, (mem_stab_iff 0 _).2 (MulAction.mem_stabilizer_iff.mp s.2)⟩,
      smul_D23_of_mem_presSub _ (m24Fix_le_presSub s.1.2)⟩) ?_
    intro s t hst
    have h2 := mog23EquivM23.injective (congrArg Subtype.val hst)
    have h3 : ((s.1 : ↥(m24Fix dodecadE)) : Equiv.Perm (Fin 24)) = t.1 :=
      congrArg (fun z : ↥mog23 => (z : Equiv.Perm (Fin 24))) h2
    exact Subtype.ext (Subtype.ext h3)
  calc Nat.card ↥(m24Fix dodecadE) = _ := h1.symm
    _ ≤ 12 * 7920 := Nat.mul_le_mul horb hstab
    _ = 95040 := by norm_num

theorem m24Fix_dodecadE_props :
    Nonempty (↥(m24Fix dodecadE) ≃* NativeSporadic.M12) ∧
      Nat.card ↥(m24Fix dodecadE) = 95040 := by
  have hM12 : Nat.card NativeSporadic.M12 = 95040 := CFSG.Sporadic.Mathieu.card_M12
  have hle := m12_le_range_res12
  have h1 : Nat.card NativeSporadic.M12 ≤ Nat.card res12.range := Subgroup.card_le_of_le hle
  have h2 : Nat.card res12.range ≤ Nat.card ↥(m24Fix dodecadE) :=
    Nat.card_le_card_of_surjective _ res12.rangeRestrict_surjective
  have h3 := card_m24Fix_le
  have hcard : Nat.card ↥(m24Fix dodecadE) = 95040 := by omega
  have hbij : Function.Bijective res12.rangeRestrict :=
    res12.rangeRestrict_surjective.bijective_of_nat_card_le (by omega)
  have hrange : res12.range = NativeSporadic.M12 :=
    (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  exact ⟨⟨(MulEquiv.ofBijective _ hbij).trans (MulEquiv.subgroupCongr hrange)⟩, hcard⟩

end CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
