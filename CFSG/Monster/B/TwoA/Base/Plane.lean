
module

public import CFSG.Monster.B.TwoA.Base.PlaneBase

public import Certificates.Certificate16033

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert

@[expose] def alpha23K :
    Kstab v0 := ⟨Co2.alpha 23, alpha_mem_Kv 23⟩

theorem alpha23K_wFr :
    wAct v0 alpha23K wFr = wFr + sW := by
  rw [wFr_eq_decW, sW, pairW23_eq_decW, alpha23K, wAct_alpha_decW,
    show Native.actD 22 (genQuotMatrix 23) 31 = 31 ^^^ 12288 from
      Certificates.certificate16033.1, decW_xor]

theorem alpha23K_sW :
    wAct v0 alpha23K sW = sW := by
  rw [sW, pairW23_eq_decW, alpha23K, wAct_alpha_decW,
    show Native.actD 22 (genQuotMatrix 23) 12288 = 12288 from
      Certificates.certificate16033.2]

theorem alpha23K_mem_NU :
    alpha23K ∈ NU :=
  mem_NU_of (by rw [alpha23K_wFr]; exact Uplane.add_mem wFr_mem_Uplane sW_mem_Uplane)
    (by rw [alpha23K_sW]; exact sW_mem_Uplane)

@[expose] def alphaN23 :
    NU := ⟨alpha23K, alpha23K_mem_NU⟩

theorem T2_ne_one :
    resU alphaN23⁻¹ ≠ 1 := by
  intro h
  have := congrArg (fun u : (Module.End (ZMod 2) Uplane)ˣ =>
    (((u : Module.End (ZMod 2) Uplane) ⟨wFr, wFr_mem_Uplane⟩ : Uplane) : Wv v0)) h
  simp only [coe_resU_inv_apply, Units.val_one, Module.End.one_apply] at this
  change wAct v0 alpha23K wFr = wFr at this
  rw [alpha23K_wFr] at this
  exact sW_ne_zero (by simpa using this)

theorem T1_ne_T2 :
    resU sgnN⁻¹ ≠ resU alphaN23⁻¹ := by
  intro h
  have := congrArg (fun u : (Module.End (ZMod 2) Uplane)ˣ =>
    (((u : Module.End (ZMod 2) Uplane) ⟨wFr, wFr_mem_Uplane⟩ : Uplane) : Wv v0)) h
  simp only [coe_resU_inv_apply] at this
  change wAct v0 sgnK wFr = wAct v0 alpha23K wFr at this
  rw [sgnK_wFr, alpha23K_wFr] at this
  exact sW_ne_zero (by simpa using this.symm)

theorem T2_mem_range :
    resU alphaN23⁻¹ ∈ resU.range := ⟨_, rfl⟩

theorem three_le_range :
    3 ≤ Nat.card resU.range := by
  have h1 : (1 : resU.range) ≠ ⟨_, T1_mem_range⟩ := fun h =>
    T1_ne_one (congrArg Subtype.val h).symm
  have h2 : (1 : resU.range) ≠ ⟨_, T2_mem_range⟩ := fun h =>
    T2_ne_one (congrArg Subtype.val h).symm
  have h3 : (⟨_, T1_mem_range⟩ : resU.range) ≠ ⟨_, T2_mem_range⟩ := fun h =>
    T1_ne_T2 (congrArg Subtype.val h)
  let f : Fin 3 → resU.range := ![1, ⟨_, T1_mem_range⟩, ⟨_, T2_mem_range⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij h1 | exact absurd hij h2 | exact absurd hij h3
      | exact absurd hij.symm h1 | exact absurd hij.symm h2 | exact absurd hij.symm h3
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fin] at this

theorem resU_surjective :
    Function.Surjective resU := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [natCard_glU]
  have h2 := two_dvd_range
  have h3 := three_le_range
  have h6 := range_dvd_six
  have hle := Nat.le_of_dvd (by norm_num) h6
  interval_cases (Nat.card resU.range) <;> omega

@[expose] noncomputable def nuQuotEquiv :
    NU ⧸ CU.subgroupOf NU ≃* GL (Fin 2) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq ker_resU.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective resU resU_surjective).trans glUEquiv)

theorem natCard_NU :
    Nat.card NU = 11796480 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CU.subgroupOf NU)
  rw [Nat.card_congr nuQuotEquiv.toEquiv, natCard_GL2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe CU_le_NU).toEquiv, natCard_CU] at h
  exact h

theorem native_rank_two_plane_stabilizer :
    Module.finrank (ZMod 2) Uplane = 2 ∧
    (∀ k : Kstab v0, k ∈ NU ⊓ Mfr ↔ (k : OLq) ∈ monoSub ceqFtwoHyp) ∧
    (∀ k : Kstab v0, k ∈ CU ↔ (k : OLq) ∈ monoSub cbothFtwoHyp) ∧
    Nonempty (↥(NU ⊓ Mfr) ≃* SDD ceqFtwoHyp) ∧ Nonempty (CU ≃* SDD cbothFtwoHyp) ∧
    Nonempty (NU ⧸ CU.subgroupOf NU ≃* GL (Fin 2) (ZMod 2)) ∧
    Nat.card NU = 11796480 ∧ Nat.card CU = 1966080 ∧
    Nat.card (CFSG.pCore 2 CU) = 2 ^ 14 ∧
    Nonempty (CU ⧸ CFSG.pCore 2 CU ≃* Equiv.Perm (Fin 5)) :=
  ⟨finrank_Uplane, mem_NUw_iff, mem_CU_iff,
    ⟨nuwEquivMono.trans (monoSubEquiv ceqFtwoHyp).symm⟩,
    ⟨cuEquivMono.trans (monoSubEquiv cbothFtwoHyp).symm⟩, ⟨nuQuotEquiv⟩, natCard_NU,
    natCard_CU, natCard_pCore_CU, ⟨cuQuotEquiv⟩⟩

end CFSG.Monster.B.TwoA
