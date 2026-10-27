module

public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Quasithin.AppendixH.H14.H142Arr
public import CFSG.Quasithin.AppendixH.H14.H142StdDefs
public import CFSG.Quasithin.AppendixH.Common.OctadOrbit
public import CFSG.Quasithin.Background.H158TNF
public import CFSG.Quasithin.AppendixH.H14.H141T1Data

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin.H158T CFSG.Quasithin.H.Mathieu

theorem o0F_eq_mask : o0F = maskSetOf 2167367 := by decide

theorem o1F_eq_mask : o1F = maskSetOf 4752568 := by decide

theorem o2F_eq_mask : o2F = maskSetOf 9857280 := by decide

@[expose] def trioOf (a : Array ℕ) : Finset (Finset (Fin 24)) :=
  {maskSetOf (permM a 2167367), maskSetOf (permM a 4752568), maskSetOf (permM a 9857280)}

@[expose] def trioList : List (Finset (Finset (Fin 24))) := t1reps.map trioOf

@[expose] def t1Good : Bool :=
  t1reps.all fun a => inAutOK a && (permM a 9857280 == 9857280)

theorem t1Good_eq : t1Good = true := by decide +kernel

theorem t1Good_spec : ∀ a ∈ t1reps, inAutOK a = true ∧ permM a 9857280 = 9857280 := by
  intro a ha
  have h := List.all_eq_true.mp t1Good_eq a ha
  simpa only [t1Good, Bool.and_eq_true, beq_iff_eq] using h

theorem trioList_nodup : trioList.Nodup := by decide +kernel

theorem trioList_length : trioList.length = 15 := by decide

theorem smul_labTrio {g : S24} {a : Array ℕ} (hg : HasArr g a) :
    g • labTrio = trioOf a := by
  simp only [labTrio, trioOf, o0F_eq_mask, o1F_eq_mask, o2F_eq_mask,
    Finset.smul_finset_insert, Finset.smul_finset_singleton, smul_maskSetOf hg]

theorem mem_octStab_of_arr {a : Array ℕ} (hok : inAutOK a = true)
    (hfix : permM a 9857280 = 9857280) :
    permOfArrD a ∈ CFSG.ASVolI.AppH.octStab o2F := by
  refine Subgroup.mem_inf.mpr ⟨permOfArrD_mem_M24g hok, ?_⟩
  exact MulAction.mem_stabilizer_iff.mpr (by
    rw [o2F_eq_mask, smul_maskSetOf (hasArr_permOfArrD hok), hfix])

theorem trioList_mem_orbit :
    ∀ t ∈ trioList, t ∈ MulAction.orbit ↥(CFSG.ASVolI.AppH.octStab o2F) labTrio := by
  intro t ht
  rw [trioList, List.mem_map] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨hok, hfix⟩ := t1Good_spec a ha
  exact MulAction.mem_orbit_iff.mpr
    ⟨⟨permOfArrD a, mem_octStab_of_arr hok hfix⟩, smul_labTrio (hasArr_permOfArrD hok)⟩

theorem card_orbit_labTrio_ge :
    15 ≤ Nat.card (MulAction.orbit ↥(CFSG.ASVolI.AppH.octStab o2F) labTrio) := by
  let f : Fin trioList.length → MulAction.orbit ↥(CFSG.ASVolI.AppH.octStab o2F) labTrio :=
    fun k => ⟨trioList.get k, trioList_mem_orbit _ (List.get_mem _ k)⟩
  have hf : Function.Injective f := fun k k' h =>
    (List.Nodup.get_inj_iff trioList_nodup).1 (congrArg Subtype.val h)
  have hcard : trioList.length ≤
      Nat.card (MulAction.orbit ↥(CFSG.ASVolI.AppH.octStab o2F) labTrio) := by
    simpa using Nat.card_le_card_of_injective f hf
  rw [trioList_length] at hcard
  exact hcard

theorem card_inf_octStab_labTrio_le :
    Nat.card ↥(CFSG.ASVolI.AppH.octStab o2F ⊓ MulAction.stabilizer S24 labTrio) ≤ 21504 := by
  set A : Subgroup S24 := CFSG.ASVolI.AppH.octStab o2F with hA
  have hO2 : IsOctad o2F := by
    rw [o2F_eq_mask]
    exact isOctad_maskSetOf 9857280 (by decide) (by decide +kernel)
  have hAcard : Nat.card ↥A = 322560 := by
    rw [hA]
    exact CFSG.ASVolI.AppH.card_octStab hO2
  have hge : 15 ≤ Nat.card (MulAction.orbit ↥A labTrio) := by
    rw [hA]
    exact card_orbit_labTrio_ge
  have hge' : 15 ≤ (MulAction.orbit ↥A labTrio).ncard := by
    rwa [Nat.card_coe_set_eq] at hge
  have hos : (MulAction.orbit ↥A labTrio).ncard *
      Nat.card (MulAction.stabilizer ↥A labTrio) = Nat.card ↥A := by
    rw [← MulAction.index_stabilizer, mul_comm]
    exact Subgroup.card_mul_index _
  have h1 : 15 * Nat.card (MulAction.stabilizer ↥A labTrio) ≤ Nat.card ↥A := by
    calc 15 * Nat.card (MulAction.stabilizer ↥A labTrio)
        ≤ (MulAction.orbit ↥A labTrio).ncard *
          Nat.card (MulAction.stabilizer ↥A labTrio) := Nat.mul_le_mul_right _ hge'
      _ = Nat.card ↥A := hos
  have h2 : 15 * Nat.card (MulAction.stabilizer ↥A labTrio) ≤ 322560 := by
    rwa [hAcard] at h1
  rw [show (322560 : ℕ) = 15 * 21504 by norm_num] at h2
  have hstabA_le : Nat.card (MulAction.stabilizer ↥A labTrio) ≤ 21504 :=
    Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hmap : Subgroup.map A.subtype (MulAction.stabilizer ↥A labTrio) =
      A ⊓ MulAction.stabilizer S24 labTrio := by
    rw [← MulAction.stabilizer_subgroupOf A labTrio, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hcard := Subgroup.card_subtype A (MulAction.stabilizer ↥A labTrio)
  rw [hmap] at hcard
  rw [hcard]
  exact hstabA_le

theorem card_MT_le :
    Nat.card ↥(MY M24g labTrio) ≤ 64512 := by
  set G : Subgroup S24 := MY M24g labTrio with hG
  have hG' : G = M24g ⊓ MulAction.stabilizer S24 labTrio := by rw [hG, MY]
  have hG_le_stab : G ≤ MulAction.stabilizer S24 labTrio := by rw [hG']; exact inf_le_right
  have hmap : Subgroup.map G.subtype (MulAction.stabilizer ↥G o2F) =
      G ⊓ MulAction.stabilizer S24 o2F := by
    rw [← MulAction.stabilizer_subgroupOf G o2F, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hstab_card : Nat.card (MulAction.stabilizer ↥G o2F) =
      Nat.card ↥(G ⊓ MulAction.stabilizer S24 o2F) := by
    have hcard := Subgroup.card_subtype G (MulAction.stabilizer ↥G o2F)
    rw [hmap] at hcard
    exact hcard.symm
  have hH_eq : G ⊓ MulAction.stabilizer S24 o2F =
      CFSG.ASVolI.AppH.octStab o2F ⊓ MulAction.stabilizer S24 labTrio := by
    rw [hG', CFSG.ASVolI.AppH.octStab]
    ac_rfl
  have horb_le : (MulAction.orbit ↥G o2F).ncard ≤ 3 := by
    have hsub : (MulAction.orbit ↥G o2F : Set (Finset (Fin 24))) ⊆ (labTrio : Set _) := by
      intro x hx
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      have hstab : (g : S24) • labTrio = labTrio :=
        MulAction.mem_stabilizer_iff.mp (hG_le_stab g.2)
      have hmem : o2F ∈ labTrio := by simp [labTrio]
      exact hstab ▸ Finset.smul_mem_smul_finset hmem
    have hle := Set.ncard_le_ncard hsub labTrio.finite_toSet
    have hcard : labTrio.card = 3 := by decide
    rw [← hcard, ← Set.ncard_coe_finset]
    exact hle
  have hos : (MulAction.orbit ↥G o2F).ncard *
      Nat.card (MulAction.stabilizer ↥G o2F) = Nat.card ↥G := by
    rw [← MulAction.index_stabilizer, mul_comm]
    exact Subgroup.card_mul_index _
  calc Nat.card ↥G
      = (MulAction.orbit ↥G o2F).ncard *
        Nat.card (MulAction.stabilizer ↥G o2F) := hos.symm
    _ = (MulAction.orbit ↥G o2F).ncard *
        Nat.card ↥(G ⊓ MulAction.stabilizer S24 o2F) := by rw [hstab_card]
    _ = (MulAction.orbit ↥G o2F).ncard *
        Nat.card ↥(CFSG.ASVolI.AppH.octStab o2F ⊓ MulAction.stabilizer S24 labTrio) := by
          rw [hH_eq]
    _ ≤ 3 * 21504 := Nat.mul_le_mul horb_le card_inf_octStab_labTrio_le
    _ = 64512 := by norm_num

end CFSG.Quasithin.AppendixH.H14
