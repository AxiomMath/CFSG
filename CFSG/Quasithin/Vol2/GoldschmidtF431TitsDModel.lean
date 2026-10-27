module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDForest
public import Certificates.Certificate7050Base

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45
  CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.TitsLoc CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem sylow_D : IsSylowTwoOf titsSD ⊤ := titsTwoLocalLattice.isSylowTwoOf_top

theorem orderOf_zD : orderOf zD = 2 := by
  have h := orderOf_zM
  rwa [← ιD_zD, orderOf_injective ιD ιD_injective] at h

theorem orderOf_tD : orderOf tD = 2 := by
  have h := orderOf_tM
  rwa [← ιD_tD, orderOf_injective ιD ιD_injective] at h

theorem not_conj_D : ¬ IsConj zD tD := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine not_conj_model (isConj_iff.2 ⟨ιD c, ?_⟩)
  have := congrArg ιD hc
  simpa [map_mul, map_inv, ιD_zD, ιD_tD] using this

theorem classes_D : ∀ x : ↥titsD, orderOf x = 2 → IsConj zD x ∨ IsConj tD x := by
  intro x hx
  obtain ⟨m, -, hm⟩ := exists_conj_mem_of_isSylowTwoOf_involution sylow_D (Subgroup.mem_top x) hx
  have hconj : IsConj (m⁻¹ * x * m) x := isConj_iff.2 ⟨m, by group⟩
  have ho : orderOf (m⁻¹ * x * m) = 2 := by
    rw [← hx]
    exact CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hconj
  rcases inv_chain_D _ hm ho with h | h
  · exact Or.inl ((reflTransGen_isConj h).trans hconj)
  · exact Or.inr ((reflTransGen_isConj h).trans hconj)

theorem cent_z_D : Subgroup.centralizer ({zD} : Set ↥titsD) = titsHD := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h : ιD x * zM = zM * ιD x := by
      rw [← ιD_zD, ← map_mul, ← map_mul, hx]
    have h1 : ιD x ∈ twoF4M1 := by
      rw [← cent_z_model]
      exact Subgroup.mem_centralizer_singleton_iff.2 h
    have h0 := (mem_twoF4M1_iff _).1 h1
    exact Subgroup.mem_subgroupOf.2 (mem_titsH_of x.2 h0)
  · intro hx
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1
      (titsH_le_centralizer_z (Subgroup.mem_subgroupOf.1 hx)))

theorem cent_t_D : Subgroup.centralizer ({tD} : Set ↥titsD) ≤ titsND := by
  intro x hx
  have h : ιD x * tM = tM * ιD x := by
    rw [← ιD_tD, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hx]
  have h1 := cent_t_model (Subgroup.mem_centralizer_singleton_iff.2 h)
  have h0 := (mem_twoF4M2_iff _).1 h1
  exact Subgroup.mem_subgroupOf.2 (mem_titsN_of x.2 h0)

theorem center_T_D : ∀ w ∈ titsSD, (∀ y ∈ titsSD, y * w = w * y) → w ≠ 1 →
    ∃ m ∈ titsHD ⊓ titsND, m * zD * m⁻¹ = w := by
  intro w hw hc hne
  have hwS : w.1 ∈ titsS := Subgroup.mem_subgroupOf.1 hw
  have hmem : w.1 ∈ ((Subgroup.center titsS).map titsS.subtype :
      Set (Equiv.Perm (Fin 1755))) := by
    refine ⟨⟨w.1, hwS⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    have := hc ⟨y.1, titsS_le_titsD y.2⟩ (Subgroup.mem_subgroupOf.2 y.2)
    have h3 : y.1 * w.1 = w.1 * y.1 := congrArg Subtype.val this
    exact Subtype.ext h3
  rw [titsS_center] at hmem
  rcases hmem with h | h
  · exact absurd (Subtype.ext h) hne
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact Subtype.ext h.symm

theorem titsD_F431LieI : F431LieI titsSD titsHD titsND zD tD where
  sylow := sylow_D
  T_le₁ := titsSD_le_titsHD
  T_le₂ := titsSD_le_titsND
  z_mem := Subgroup.mem_subgroupOf.2 titsZ_mem_titsS
  t_mem := Subgroup.mem_subgroupOf.2 tEl_mem_titsS
  hz := orderOf_zD
  ht := orderOf_tD
  not_conj := not_conj_D
  classes := classes_D
  cent_z := cent_z_D
  cent_t := cent_t_D
  center_T := center_T_D
  inv_chain := inv_chain_D

end CFSG.Quasithin.H13.F431.TitsD
