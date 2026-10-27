
module

public import CFSG.Monster.B.TwoA.Base.ResGenBase

public import CFSG.Monster.B.TwoA.Base.ResGenData
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Base.Par45BBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.VisCert

open CFSG.Monster.B.Co2 (v0)

theorem alpha_mem_Mfr
    {i : Fin 24} (hi : i.val < 23) :
    (⟨Co2.alpha i, Co2.alpha_mem_Kv i⟩ : Kstab v0) ∈ Mfr := by
  change wAct v0 ⟨Co2.alpha i, Co2.alpha_mem_Kv i⟩ wFr = wFr
  rw [wFr_eq_decW, Co2.wAct_alpha_decW, actD_alpha_31 i hi]

theorem Mfr_sup_NU :
    Mfr ⊔ NU = ⊤ := by
  set T : Subgroup OLq := (Mfr ⊔ NU).map (Kstab v0).subtype
  have hT : ∀ i, Co2.alpha i ∈ T := by
    intro i
    by_cases hi : i.val < 23
    · exact ⟨_, Subgroup.mem_sup_left (alpha_mem_Mfr hi), rfl⟩
    · have h23 : i = 23 := Fin.ext (by omega)
      subst h23
      exact ⟨alpha23K, Subgroup.mem_sup_right alpha23K_mem_NU, rfl⟩
  have hA : Co2.Agrp ≤ T := by
    rw [Co2.Agrp, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact alphaWord_mem_of hT _
    · exact alphaWord_mem_of hT _
  rw [eq_top_iff]
  intro k _
  have hk : (k : OLq) ∈ T := hA (by rw [Co2.Agrp_eq_Kv]; exact k.2)
  obtain ⟨k', hk', hkk'⟩ := hk
  rwa [Subtype.ext hkk'] at hk'

theorem Mfr_eq_sup :
    Mfr = (NU ⊓ Mfr) ⊔ (wSetStab U3 ⊓ Mfr) := by
  refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  rw [← Subgroup.map_le_map_iff_of_injective (Kstab v0).subtype_injective, Subgroup.map_sup,
    map_NUw, map_wSetStab_inf_Mfr_eq pairSpace_U3, map_Mfr]
  exact monoSub_le_sup ceqHyp ceqFtwoHyp (ceqFofAHyp A2) Ppair_eq_sup.le

theorem Jhat_eq_sup :
    Jhat = Ptwo ⊔ H3 := by
  have h := sup_subgroupOf_eq_comap Ptwo_le_Jhat H3_le_Jhat jhatToKv0_surjective
    Ptwo_subgroupOf_eq_Mfr H3_subgroupOf_eq
  rw [Mfr_sup_NU, Subgroup.comap_top, Subgroup.subgroupOf_eq_top] at h
  exact le_antisymm h (sup_le Ptwo_le_Jhat H3_le_Jhat)

theorem Ptwo_inf_K4_subgroupOf :
    (Ptwo ⊓ K4).subgroupOf Jhat = (wSetStab U3 ⊓ Mfr).comap jhatToKv0 := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf]
  have h4 : (g : Dfull) ∈ K4 ↔ jhatToKv0 g ∈ wSetStab U3 := by
    rw [← Subgroup.mem_comap, ← H4_subgroupOf_eq, Subgroup.mem_subgroupOf, H4, Subgroup.mem_inf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [h4, ← mem_Ntwo_iff_Mfr]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨g.2, h.2⟩, h.1⟩⟩

theorem Ptwo_eq_sup :
    Ptwo = (Ptwo ⊓ K3) ⊔ (Ptwo ⊓ K4) := by
  have hle : (Ptwo ⊓ K3) ⊔ (Ptwo ⊓ K4) ≤ Ptwo := sup_le inf_le_left inf_le_left
  have h := sup_subgroupOf_eq_comap (inf_le_left.trans Ptwo_le_Jhat)
    (inf_le_left.trans Ptwo_le_Jhat) jhatToKv0_surjective Ptwo_inf_K3_subgroupOf
    Ptwo_inf_K4_subgroupOf
  rw [← Mfr_eq_sup, ← Ptwo_subgroupOf_eq_Mfr] at h
  have h2 := Subgroup.subgroupOf_inj.1 h
  rw [inf_of_le_left (hle.trans Ptwo_le_Jhat), inf_of_le_left Ptwo_le_Jhat] at h2
  exact h2.symm

theorem native_parabolic_residue_generation :
    Kchain 1 = Subgroup.closure ((↑(Kchain 1 ⊓ Kchain 2) : Set Dfull) ∪ ↑(Kchain 1 ⊓ Kchain 3)) ∧
    Kchain 1 ⊓ Kchain 2 = Subgroup.closure ((↑(Kchain 1 ⊓ Kchain 2 ⊓ Kchain 3) : Set Dfull) ∪
      ↑(Kchain 1 ⊓ Kchain 2 ⊓ Kchain 4)) ∧
    Shat = Subgroup.closure ((Kchain 1 : Set Dfull) ∪ Kchain 2) ∧
    Kchain 1 = Jhat ∧ Kchain 1 ⊓ Kchain 2 = Ptwo ∧ Mfr ⊔ NU = ⊤ ∧ Ppair = Ftwo ⊔ FA2 := by
  have h12 : Kchain 1 ⊓ Kchain 2 = Ptwo := by rw [Kchain_one]; rfl
  refine ⟨?_, ?_, ?_, Kchain_one, h12, Mfr_sup_NU, Ppair_eq_sup⟩
  · rw [← Subgroup.sup_eq_closure, Kchain_one]
    exact Jhat_eq_sup
  · rw [← Subgroup.sup_eq_closure, h12]
    exact Ptwo_eq_sup
  · rw [← Subgroup.sup_eq_closure, Kchain_one]
    exact Shat_eq_sup

end CFSG.Monster.B.TwoA
