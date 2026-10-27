module

public import CFSG.Quasithin.Vol2.Ch10SecC8Claim
public import CFSG.Quasithin.Vol2.Ch10SecC8T1
public import CFSG.Quasithin.Vol2.Ch10SecC8Coord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem omegaOne_T1_le_omegaOne_Q (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1027 : Stmt10_2_7) :
    omegaOneCenterOf (T1 T L) ≤
      omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  have hQ := (omegaOne_le_Q hyp h1027 h37 h38 h1011).2
  have hQT1 := Q_le_T1 h37 h38 hyp h1011
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxT1, hxc⟩, hx2⟩
  have hxQ := hQ (Subgroup.subset_closure ⟨⟨hxT1, hxc⟩, hx2⟩)
  exact Subgroup.subset_closure ⟨⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_iff.mp hxc q (hQT1 hq)⟩, hx2⟩

theorem omegaOne_Q_inf_le_omegaOne_T1 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) :
    omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
      Subgroup.centralizer (fsuL0 T L : Set G) ≤ omegaOneCenterOf (T1 T L) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨hc, hnat⟩ := h3.2
  obtain ⟨D0⟩ := hnat.toL3Coord
  obtain ⟨D, hD⟩ := exists_L3Data_U3 hyp D0
  rintro x ⟨hxX, hxL0⟩
  have hxQ : x ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) :=
    A4.omegaOneCenterOf_le _ hxX
  refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨Q_le_T1 h37 h38 hyp h1011 hxQ, ?_⟩,
    A4.sq_eq_one_of_mem_omegaOneCenterOf hxX⟩
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  obtain ⟨d₁, hd₁, d₂, hd₂, hsd⟩ := exists_decomp_T1 h37 h38 hyp h1011 h3 D hD ht htn hs
  have hgL0 : d₁ * d₂ ∈ fsuL0 T L :=
    (fsuL0 T L).mul_mem (SecA.le_fsuL0 T L hd₁.2) (SecA.conjugate_le_fsuL0 ht hd₂.2)
  have hgT : d₁ * d₂ ∈ T := T.mul_mem hd₁.1 hd₂.1
  have hq : (d₁ * d₂)⁻¹ * s ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem hgT) hs.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 := hsd v hv
    calc v * ((d₁ * d₂)⁻¹ * s) = (d₁ * d₂)⁻¹ * ((d₁ * d₂) * v * (d₁ * d₂)⁻¹) * s := by group
      _ = (d₁ * d₂)⁻¹ * (s * v * s⁻¹) * s := by rw [h1]
      _ = ((d₁ * d₂)⁻¹ * s) * v := by group
  have hxg : (d₁ * d₂) * x = x * (d₁ * d₂) :=
    Subgroup.mem_centralizer_iff.mp hxL0 _ hgL0
  have hxq : ((d₁ * d₂)⁻¹ * s) * x = x * ((d₁ * d₂)⁻¹ * s) :=
    (Subgroup.mem_centralizer_iff.mp (Q_le_centralizer_omegaOne T _ hq) x hxX).symm
  calc s * x = (d₁ * d₂) * (((d₁ * d₂)⁻¹ * s) * x) := by group
    _ = (d₁ * d₂) * (x * ((d₁ * d₂)⁻¹ * s)) := by rw [hxq]
    _ = ((d₁ * d₂) * x) * ((d₁ * d₂)⁻¹ * s) := by group
    _ = (x * (d₁ * d₂)) * ((d₁ * d₂)⁻¹ * s) := by rw [hxg]
    _ = x * s := by group

theorem omegaOne_T1_eq (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) :
    omegaOneCenterOf (T1 T L) =
      omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (fsuL0 T L : Set G) := by
  refine le_antisymm (fun x hx => ?_) (omegaOne_Q_inf_le_omegaOne_T1 h37 h38 hyp h1011 h3)
  have hxX := omegaOne_T1_le_omegaOne_Q h37 h38 hyp h1011 h1027 hx
  refine ⟨hxX, ?_⟩
  have hXc : ∀ a ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)),
      ∀ b ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)), a * b = b * a :=
    fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb
  have h1 : x ∈ (↑(fsuVM T L I ⊔
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (fsuL0 T L : Set G))) : Set G) :=
    le_sup_centralizer_fsuL0 h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne hxX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_of_comm hXc (fsuVM_le_omegaOneCenterOf hyp) inf_le_left)] at h1
  obtain ⟨v, hv, c, hc, hvc⟩ := h1
  have hvc' : v * c = x := hvc
  have hcT1 := omegaOne_Q_inf_le_omegaOne_T1 h37 h38 hyp h1011 h3 hc
  have hvT1 : v ∈ omegaOneCenterOf (T1 T L) := by
    have e : v = x * c⁻¹ := by rw [← hvc']; group
    rw [e]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hcT1)
  have hvC := (A4.omegaOneCenterOf_le_centerOf _ hvT1).2
  have hvL0 := (fsuVM_inf_centralizer_T1_le h37 h38 hyp h1011 h484 h3 hne ⟨hv, hvC⟩).2
  rw [← hvc']
  exact Subgroup.mul_mem _ hvL0 hc.2

theorem omegaOne_Q_eq (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) :
    omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) =
      omegaOneCenterOf (T1 T L) ⊔ fsuVM T L I := by
  refine le_antisymm ?_ (sup_le (omegaOne_T1_le_omegaOne_Q h37 h38 hyp h1011 h1027)
    (fsuVM_le_omegaOneCenterOf hyp))
  rw [omegaOne_T1_eq h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne]
  exact (le_sup_centralizer_fsuL0 h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne).trans
    (le_of_eq (sup_comm _ _))

theorem commutator_Z_L_eq_bot (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) :
    ⁅quasithinOmegaOneCenter T, L⁆ = ⊥ := by
  have hZQ := (omegaOne_le_Q hyp h1027 h37 h38 h1011).1
  have hQT1 := Q_le_T1 h37 h38 hyp h1011
  have hZ : quasithinOmegaOneCenter T ≤ omegaOneCenterOf (T1 T L) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨⟨hzT, hzc⟩, hz2⟩
    have hz : z ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hzT, hzc⟩, hz2⟩
    exact Subgroup.subset_closure ⟨⟨hQT1 (hZQ hz), Subgroup.mem_centralizer_iff.mpr fun s hs =>
      Subgroup.mem_centralizer_iff.mp hzc s hs.1⟩, hz2⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  have h1 := hZ hz
  rw [omegaOne_T1_eq h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne] at h1
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (SecA.le_fsuL0 T L)) h1.2

end CFSG.Quasithin.Vol2.Ch10.SecC
