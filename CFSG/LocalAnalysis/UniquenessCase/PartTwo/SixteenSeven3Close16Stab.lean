module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Kit3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

@[expose] noncomputable def close16Vec (V : Subgroup G) (hV : IsElemAbelian 2 V) (z : G)
    (hz : z ∈ V) : Vtil ⊥ V hV :=
  mkTil ⊥ V hV (IntMod.mk hV ⟨z, hz⟩)

theorem close16Vec_eq_one_iff {z : G} (hz : z ∈ V) : close16Vec V hV z hz = 1 ↔ z = 1 := by
  have h := mkTil_eq_iff ⊥ V hV (IntMod.mk hV ⟨z, hz⟩) 1
  rw [map_one] at h
  unfold close16Vec
  rw [h, IntMod.val_one, inv_one, mul_one, Subgroup.mem_bot]
  exact Iff.rfl

theorem close16_actTil_vec_eq_iff (g : ↥(stabTil ⊥ V)) {z : G} (hz : z ∈ V) :
    actTil ⊥ V hV g (close16Vec V hV z hz) = close16Vec V hV z hz ↔
      (g : G) * z = z * (g : G) := by
  unfold close16Vec
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
  show (g : G) * z * (g : G)⁻¹ * z⁻¹ = 1 ↔ (g : G) * z = z * (g : G)
  constructor
  · intro h
    have h1 : (g : G) * z * (g : G)⁻¹ = z := mul_inv_eq_one.1 h
    calc (g : G) * z = ((g : G) * z * (g : G)⁻¹) * g := by group
      _ = z * g := by rw [h1]
  · intro h
    rw [h]
    group

theorem close16_kbar_normal (hS : Close16Setting D V L hV) :
    ((kBar D.M ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV)).Normal := by
  obtain ⟨hcomm, -, hsup⟩ := close16_mbar_direct hS
  have hKM : kBar D.M ⊥ V hV L ≤ Mbar D.M ⊥ V hV := inf_le_left
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKM, ← hsup]
  exact sup_le Subgroup.le_normalizer
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((Subgroup.commutator_comm _ _).trans hcomm)).trans (Subgroup.centralizer_le_normalizer _))

theorem close16_barSub_T_sylow (hS : Close16Setting D V L hV) :
    IsSylowIn 2 (barSub ⊥ V hV D.T) (Mbar D.M ⊥ V hV) :=
  s16c1_barSub_sylow (close16_le_stabTil hS) (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM)

theorem close16_exists_tau (hS : Close16Setting D V L hV) :
    ∃ τ : MulAut (Vtil ⊥ V hV),
      τ ∈ barSub ⊥ V hV D.T ∧ τ ∈ kBar D.M ⊥ V hV L ∧ τ ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : kBar D.M ⊥ V hV L ≤ Mbar D.M ⊥ V hV := inf_le_left
  have hsyl := IsSylowIn.inf_normal (close16_barSub_T_sylow hS) hKM (close16_kbar_normal hS)
  by_contra hcon
  have hbot : barSub ⊥ V hV D.T ⊓ kBar D.M ⊥ V hV L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hcon ⟨x, hx.1, hx.2, hx1⟩
  have h2 := hsyl.not_dvd_relIndex
  rw [hbot, Subgroup.relIndex_bot_left, close16_card_kbar hS] at h2
  exact h2 (by norm_num)

theorem close16_ptStab_central (hS : Close16Setting D V L hV) {z : G}
    (hz : z ∈ V ⊓ centralizer (D.T : Set G)) (hz1 : z ≠ 1) :
    Close16PtStab (lBar ⊥ V hV L) (close16Vec V hV z (Subgroup.mem_inf.1 hz).1) := by
  obtain ⟨-, ⟨L₀, -, -, -, hsum⟩, -⟩ := hS.shape
  obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
  obtain ⟨τ, hτT, hτK, hτ1⟩ := close16_exists_tau hS
  refine close16_pt_stab_of_two_summands (close16_card_lbar hS) hnat h01 hsup hτ1 ?_ ?_ ?_
  · intro h hh
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hτK).2 h hh).symm
  · rw [Ne, close16Vec_eq_one_iff]
    exact hz1
  · obtain ⟨g, hgT, rfl⟩ := (mem_barSub ⊥ V hV D.T τ).1 hτT
    exact (close16_actTil_vec_eq_iff g (Subgroup.mem_inf.1 hz).1).2
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 (g : G) hgT)

theorem close16_barSub_cent_eq (hS : Close16Setting D V L hV) {Y : Subgroup G}
    (hY : Close16Pack D V L hV Y) {z : G} (hz : z ∈ V) :
    barSub ⊥ V hV (Y ⊓ centralizer ({z} : Set G)) =
      lBar ⊥ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) (close16Vec V hV z hz) := by
  have hbar : barSub ⊥ V hV Y = lBar ⊥ V hV L := hY.bar_eq
  ext φ
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ V hV _ φ).1 hφ
    have hgY := (Subgroup.mem_inf.1 hg).1
    have hgz := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
    refine ⟨?_, (close16_actTil_vec_eq_iff g hz).2 hgz⟩
    rw [← hbar]
    exact (mem_barSub ⊥ V hV Y _).2 ⟨g, hgY, rfl⟩
  · rintro ⟨hφL, hφz⟩
    rw [← hbar] at hφL
    obtain ⟨g, hgY, rfl⟩ := (mem_barSub ⊥ V hV Y φ).1 hφL
    have hgz := (close16_actTil_vec_eq_iff g hz).1 hφz
    exact (mem_barSub ⊥ V hV _ _).2 ⟨g, Subgroup.mem_inf.2 ⟨hgY,
      Subgroup.mem_centralizer_singleton_iff.2 hgz⟩, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
