module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23MStr
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Norm3Facts

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.M23Norm3 CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def k4Sub : Subgroup (Perm (Fin 7)) where
  carrier := {σ | σ ∈ k4List}
  mul_mem' := fun ha hb => perm7_facts.1 _ ha _ hb
  one_mem' := by
    show (1 : Perm (Fin 7)) ∈ k4List
    exact List.mem_cons_self
  inv_mem' := fun ha => perm7_facts.2.1 _ ha

theorem mem_k4Sub {σ : Perm (Fin 7)} :
    σ ∈ k4Sub ↔ σ ∈ k4List := Iff.rfl

theorem card_k4Sub : Nat.card k4Sub = 4 := by
  have h : (k4Sub : Set (Perm (Fin 7))) = ↑k4List.toFinset := by
    ext σ
    simp [mem_k4Sub]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup perm7_facts.2.2.1]
  rfl

variable {G : Type} [Group G] [Finite G]

theorem map_inf_L_eq_k4Sub
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ((T ⊓ L).subgroupOf M2).map π = k4Sub := by
  obtain ⟨hTK, hUle, -, h64⟩ :=
    inf_L_facts_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hTLM2 : T ⊓ L ≤ M2 := inf_le_left.trans hS.T_le
  have hcard : Nat.card ↥(((T ⊓ L).subgroupOf M2).map π) = 4 := by
    have h1 := card_map_mul_card_inf hS.ker_eq hTLM2
    rw [inf_of_le_right hUle, h64, hU16] at h1
    omega
  have hle : ((T ⊓ L).subgroupOf M2).map π ≤ k4Sub := by
    rintro _ ⟨t, ht, rfl⟩
    have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
    have htK : (t : G) ∈ oTwoUpper H := by
      have : (t : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp ht
      rw [hTK] at this
      exact this.2
    have hs : Perm.sign (π t) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (hS.range_eq ▸ ⟨t, rfl⟩)
    have h4 : π t ^ 4 = 1 := by
      have hd : orderOf (π t) ∣ 4 := hcard ▸ Subgroup.orderOf_dvd_natCard _ ⟨t, ht, rfl⟩
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have h4' : π t 4 = 4 := by
      have h := (hS.orbits 4 (π t 4)).mp ⟨t, htT, rfl⟩
      revert h
      generalize π t 4 = j
      revert j
      decide
    obtain ⟨h5, h6⟩ :=
      fix_five_six_of_mem_oTwoUpper h526 h1284 hSz hU4 hsp hQ hyp hM23 hS htK t.2
    exact mem_k4List_of hs h4 h4' h5 h6
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_k4Sub])

theorem inf_L_eq_comap
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {g : G} (hg : g ∈ M2) :
    g ∈ T ⊓ L ↔ π ⟨g, hg⟩ ∈ k4Sub := by
  have hmap := map_inf_L_eq_k4Sub h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hUle, -, -⟩ := inf_L_facts_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  constructor
  · intro h
    rw [← hmap]
    exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr h, rfl⟩
  · intro h
    rw [← hmap] at h
    obtain ⟨t, ht, hte⟩ := h
    have hk : t⁻¹ * ⟨g, hg⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
    rw [hS.ker_eq, Subgroup.mem_subgroupOf] at hk
    have e : g = t * (t⁻¹ * ⟨g, hg⟩ : ↥M2) := by
      simp
    rw [e]
    exact (T ⊓ L).mul_mem (Subgroup.mem_subgroupOf.mp ht) (hUle hk)

theorem mem_normalizer_inf_L_of
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) (m : ↥M2)
    (hm : π m ∈ Subgroup.normalizer (k4Sub : Set (Perm (Fin 7)))) :
    (m : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hiff : ∀ {g : G} (hg : g ∈ M2), g ∈ T ⊓ L ↔ π ⟨g, hg⟩ ∈ k4Sub := fun hg =>
    inf_L_eq_comap h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS hg
  have hTLM2 : T ⊓ L ≤ M2 := inf_le_left.trans hS.T_le
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have hgM2 := hTLM2 hg
    have hmg : (m : G) * g * (m : G)⁻¹ ∈ M2 := M2.mul_mem (M2.mul_mem m.2 hgM2) (M2.inv_mem m.2)
    rw [hiff hmg]
    have e : (⟨(m : G) * g * (m : G)⁻¹, hmg⟩ : ↥M2) = m * ⟨g, hgM2⟩ * m⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hm _).mp ((hiff hgM2).mp hg)
  · intro hg
    have hgM2 : g ∈ M2 := by
      have := hTLM2 hg
      have e : g = (m : G)⁻¹ * ((m : G) * g * (m : G)⁻¹) * m := by group
      rw [e]
      exact M2.mul_mem (M2.mul_mem (M2.inv_mem m.2) this) m.2
    rw [hiff hgM2]
    have hmg : (m : G) * g * (m : G)⁻¹ ∈ M2 := hTLM2 hg
    have e : (⟨(m : G) * g * (m : G)⁻¹, hmg⟩ : ↥M2) = m * ⟨g, hgM2⟩ * m⁻¹ := rfl
    have h2 := (hiff hmg).mp hg
    rw [e, map_mul, map_mul, map_inv] at h2
    exact (Subgroup.mem_normalizer_iff.mp hm _).mpr h2

end CFSG.Quasithin.H13
