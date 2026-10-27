module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.SmithB42HatA6Off
public import CFSG.Quasithin.Background.B3Q

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.CharacterTheory.SteinbergBY HatA6
open scoped Matrix

namespace HatA6

variable {V : Type} [CommGroup V] [Finite V]

theorem one_le_rAV_of_le_index (hV : ∀ v : V, v ^ 2 = 1) {X B : Subgroup (MulAut V)}
    (hB : IsA2 X B) (h : Nat.card B ≤ (fixV B).index) : 1 ≤ rAV B :=
  CFSG.Quasithin.RAV.one_le_rAV_of_le_index hV hB h

variable {hsq : ∀ v : V, v * v = 1} {z : MulAut V} {u : Fin 3 → V}
  (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)

omit [Finite V] in
theorem fsmul_mem {S : Subgroup V} (hzS : ∀ s ∈ S, z s ∈ S) (k : FieldFour) {w : V} (hw : w ∈ S) :
    fsmul z k w ∈ S := by
  unfold fsmul
  refine S.mul_mem ?_ ?_
  · split_ifs
    · exact hw
    · exact S.one_mem
  · split_ifs
    · exact hzS w hw
    · exact S.one_mem

@[expose] noncomputable def axisOf (S : Subgroup V) (hzS : ∀ s ∈ S, z s ∈ S) :
    Submodule FieldFour (Fin 3 → FieldFour) where
  carrier := {c | coordEquiv hb (Multiplicative.ofAdd c) ∈ S}
  add_mem' := fun {c d} hc hd => by
    simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul]
    exact S.mul_mem hc hd
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ofAdd_zero, map_one]
    exact S.one_mem
  smul_mem' := fun k c hc => by
    simp only [Set.mem_ofPred_eq]
    rw [coordEquiv_smul hb hzz]
    exact fsmul_mem hzS k hc

omit [Finite V] in
theorem mem_axisOf {S : Subgroup V} (hzS : ∀ s ∈ S, z s ∈ S) {c : Fin 3 → FieldFour} :
    c ∈ axisOf hb hzz S hzS ↔ coordEquiv hb (Multiplicative.ofAdd c) ∈ S := Iff.rfl

omit [Finite V] in
theorem card_axisOf (S : Subgroup V) (hzS : ∀ s ∈ S, z s ∈ S) :
    Nat.card (axisOf hb hzz S hzS) = Nat.card S := by
  refine Nat.card_congr
    { toFun := fun c => ⟨coordEquiv hb (Multiplicative.ofAdd c.1), c.2⟩
      invFun := fun s => ⟨Multiplicative.toAdd ((coordEquiv hb).symm s.1), by
        rw [mem_axisOf, ofAdd_toAdd, MulEquiv.apply_symm_apply]
        exact s.2⟩
      left_inv := fun c => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }

end HatA6

theorem asB42HatA6_holds : AsB42HatA6 := by
  intro V _ _ hV G L hHyp hP A hA
  have hcard := card_V hV hHyp hP hA
  have hfacts := fun B (hB : IsFFStarOffender G B) => offender_facts hV hHyp hP hB
  have hJ : ffJ G = L := le_antisymm (iSup₂_le fun B hB => (hfacts B hB).1)
    (CFSG.QuasithinUnique.Bridge.TypeList.le_ffJ_of_b4Hyp (KP := CFSG.SectionRank.IsKGroupCat)
      hV hHyp hA)
  have hq : qOf G = ((1 : ℚ) : WithTop ℚ) := by
    refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, B1_4_1 hV hA⟩
    obtain ⟨-, h4, h16, -⟩ := hfacts B hB
    refine one_le_rAV_of_le_index hV hB.isA2 ?_
    have := (fixV B).card_mul_index
    rw [h16, hcard] at this
    omega
  obtain ⟨hq', hZ, ⟨e⟩⟩ := hP
  obtain ⟨zL, hcen, h3, hfp⟩ := exists_center_fpf hV hcard hq'.1 hZ e
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hzz : ∀ w, z (z w) = w * z w := fun w =>
    H13.zz_eq_of_fpf hV h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  obtain ⟨u, hb⟩ := exists_coord hsq hcard h3 hfp
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hLz : ∀ x ∈ L, ∀ w, x (z w) = z (x w) := by
    intro x hx w
    exact congrArg (fun y : ↥L => (y : MulAut V) w) (Subgroup.mem_center_iff.1 hzc ⟨x, hx⟩)
  obtain ⟨hdet, hhat, hcenK⟩ := gam_props hb hzz hLz hq'.1 hZ e rfl hcen
  obtain ⟨hAL, hA4, hA16, hAcomm⟩ := hfacts A hA
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hJ, hcard, hq, FieldFour, inferInstance, inferInstance, gam hb hzz hLz,
      FieldFour.natCard_eq, hdet, hhat, hcenK, (gamEquiv hb hzz hLz).symm.toMonoidHom,
      realizesVia_gam hb hzz hLz, ?_⟩)))))))
  set E := gamEquiv hb hzz hLz with hE
  set B' : Subgroup (GL (Fin 3) FieldFour) :=
    ((A.subgroupOf L).comap E.symm.toMonoidHom).map (gam hb hzz hLz).subtype with hB'
  have hmem : ∀ g, g ∈ B' → ∃ h : ↥L, (h : MulAut V) ∈ A ∧ g = glOf hb hzz L hLz h := by
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨E.symm γ, hγ, ?_⟩
    change (γ : GL (Fin 3) FieldFour) = _
    rw [← coe_gamEquiv hb hzz hLz, ← hE, MulEquiv.apply_symm_apply]
  have hzA : ∀ s ∈ fixV A, z s ∈ fixV A := by
    intro s hs a ha
    rw [hLz a (hAL ha), hs a ha]
  refine ⟨?_, axisOf hb hzz (fixV A) hzA, ?_, ?_⟩
  ·
    rw [hB', Subgroup.card_map_of_injective (gam hb hzz hLz).subtype_injective, ← hA4]
    refine (Nat.card_congr ?_).trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv)
    exact
      { toFun := fun γ => ⟨E.symm γ.1, γ.2⟩
        invFun := fun k => ⟨E k.1, by
          change E.symm (E k.1) ∈ A.subgroupOf L
          rw [MulEquiv.symm_apply_apply]
          exact k.2⟩
        left_inv := fun γ => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  ·
    have h16 : Nat.card (axisOf hb hzz (fixV A) hzA) = 16 := by
      rw [card_axisOf, hA16]
    have hfin := Module.natCard_eq_pow_finrank (K := FieldFour) (V := axisOf hb hzz (fixV A) hzA)
    rw [h16, FieldFour.natCard_eq] at hfin
    have : (4 : ℕ) ^ 2 = 4 ^ Module.finrank FieldFour (axisOf hb hzz (fixV A) hzA) := by
      rw [← hfin]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) this).symm
  · intro g hg _
    obtain ⟨h, hhA, rfl⟩ := hmem g hg
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · rw [glOf_mulVec]
      apply Multiplicative.ofAdd.injective
      apply (coordEquiv hb).injective
      rw [coordEquiv_linOf, (mem_axisOf hb hzz hzA).1 hw _ hhA]
    · rw [glOf_mulVec, mem_axisOf, ofAdd_sub, map_div, coordEquiv_linOf, div_eq_mul_inv]
      exact hAcomm _ hhA _

end CFSG.Quasithin
