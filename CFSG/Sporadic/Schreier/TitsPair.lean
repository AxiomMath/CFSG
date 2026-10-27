module

public import CFSG.Sporadic.Schreier.TitsCentral
public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Sporadic.Schreier.TitsPrim

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem titsPointStab_eq_stabilizer :
    titsPointStab = MulAction.stabilizer titsD (0 : Fin 1755) := by
  ext g
  rfl

theorem titsPointStab_isCoatom :
    IsCoatom titsPointStab := by
  have := CERT_Tits_derived_primitive
  rw [titsPointStab_eq_stabilizer]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive titsD (0 : Fin 1755)

theorem titsLineStab_isCoatom :
    IsCoatom titsLineStab := by
  let _ : MulAction titsD (Fin 2925) := MulAction.compHom _ titsDLineAct
  let φ : titsD → titsDLineAct.range := fun g => ⟨titsDLineAct g, g, rfl⟩
  let f : Fin 2925 →ₑ[φ] Fin 2925 := ⟨id, fun _ _ => rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, g, rfl⟩
    exact ⟨g, rfl⟩
  have hprim : MulAction.IsPreprimitive titsD (Fin 2925) :=
    (MulAction.isPreprimitive_congr hφ (f := f) Function.bijective_id).2
      AT_Tits_other_parabolic_primitivity.2.2.2.2.2.2
  have e : titsLineStab = MulAction.stabilizer titsD (0 : Fin 2925) := by
    ext g
    rfl
  rw [e]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive titsD (0 : Fin 2925)

theorem subgroupOf_map_titsD {X : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsD) :
    (X.subgroupOf titsD).map titsD.subtype = X := by
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hX]

theorem map_subgroupOf_titsD (Y : Subgroup titsD) : (Y.map titsD.subtype).subgroupOf titsD = Y :=
  Subgroup.comap_map_eq_self_of_injective titsD.subtype_injective Y

theorem map_top_titsD : (⊤ : Subgroup titsD).map titsD.subtype = titsD := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_of_coatom_le {M X : Subgroup (Equiv.Perm (Fin 1755))}
    (hM : IsCoatom (M.subgroupOf titsD)) (hMD : M ≤ titsD) (hXD : X ≤ titsD) (hMX : M ≤ X)
    (hX : X ≠ titsD) : M = X := by
  have hle : M.subgroupOf titsD ≤ X.subgroupOf titsD := fun g hg => hMX hg
  rcases hM.le_iff.1 hle with h | h
  · exact absurd (by rw [← subgroupOf_map_titsD hXD, h, map_top_titsD]) hX
  · rw [← subgroupOf_map_titsD hMD, ← subgroupOf_map_titsD hXD, h]

theorem titsH_isCoatom :
    IsCoatom (titsH.subgroupOf titsD) := by
  rw [titsH_eq_stab, map_subgroupOf_titsD]
  exact titsPointStab_isCoatom

theorem titsN_isCoatom :
    IsCoatom (titsN.subgroupOf titsD) := by
  rw [titsN_eq_stab, map_subgroupOf_titsD]
  exact titsLineStab_isCoatom

abbrev titsZS : Subgroup (Equiv.Perm (Fin 1755)) := (Subgroup.center titsS).map titsS.subtype

theorem titsH_le_CZS :
    titsH ≤ titsD ⊓ Subgroup.centralizer (titsZS : Set (Equiv.Perm (Fin 1755))) := by
  refine le_inf titsH_le_titsD fun h hh => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : g ∈ ({1, titsZ} : Set (Equiv.Perm (Fin 1755))) := titsS_center ▸ hg
  rcases hg' with rfl | rfl
  · simp
  · exact (Subgroup.mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hh)).symm

theorem CZS_ne_D :
    titsD ⊓ Subgroup.centralizer (titsZS : Set (Equiv.Perm (Fin 1755))) ≠ titsD := by
  intro h
  have hz : titsZ ∈ (titsZS : Set (Equiv.Perm (Fin 1755))) := by
    rw [titsS_center]
    exact Or.inr rfl
  have hcen : (⟨titsZ, titsZ_mem_titsD⟩ : titsD) ∈ Subgroup.center titsD := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : (g : Equiv.Perm (Fin 1755)) ∈ titsD ⊓ Subgroup.centralizer
        (titsZS : Set (Equiv.Perm (Fin 1755))) := by
      rw [h]
      exact g.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hg.2 _ hz).symm
  rw [titsD_center, Subgroup.mem_bot] at hcen
  exact titsZ_ne_one (congrArg Subtype.val hcen)

theorem titsH_eq_CZS :
    titsH = titsD ⊓ Subgroup.centralizer (titsZS : Set (Equiv.Perm (Fin 1755))) :=
  eq_of_coatom_le titsH_isCoatom titsH_le_titsD inf_le_left titsH_le_CZS CZS_ne_D

theorem titsK_normal_N :
    (titsK.subgroupOf titsN).Normal :=
  AT_Tits_local_stabilizers_and_normal_cores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsN_le_NK :
    titsN ≤ titsD ⊓ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) :=
  le_inf titsN_le_titsD ((Subgroup.normal_subgroupOf_iff_le_normalizer titsK_le_titsN).1
    titsK_normal_N)

theorem NK_ne_D :
    titsD ⊓ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) ≠ titsD := by
  intro h
  have hKD : titsK ≤ titsD := titsK_le_titsD
  have hle : titsD ≤ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) := by
    rw [← h]
    exact inf_le_right
  have hN : (titsK.subgroupOf titsD).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).2 hle
  have hcard := titsQK_facts.2.2.2
  rcases titsD_simple.eq_bot_or_eq_top_of_normal (titsK.subgroupOf titsD) with h1 | h1
  · have : titsK = ⊥ := by
      rw [← subgroupOf_map_titsD hKD, h1, Subgroup.map_bot]
    rw [this, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  · have : titsK = titsD := by
      rw [← subgroupOf_map_titsD hKD, h1, map_top_titsD]
    rw [this, card_titsD] at hcard
    exact absurd hcard (by norm_num)

theorem titsN_eq_NK :
    titsN = titsD ⊓ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) :=
  eq_of_coatom_le titsN_isCoatom titsN_le_titsD inf_le_left titsN_le_NK NK_ne_D

theorem titsN_not_le_H :
    ¬ titsN ≤ titsH := by
  intro h
  have := Subgroup.card_dvd_of_le h
  rw [titsQN_facts.2.2.2, titsQH_facts.2.2.2] at this
  exact absurd this (by norm_num)

theorem titsH_sup_N :
    titsH ⊔ titsN = titsD := by
  by_contra hne
  have := eq_of_coatom_le titsH_isCoatom titsH_le_titsD (sup_le titsH_le_titsD titsN_le_titsD)
    le_sup_left hne
  exact titsN_not_le_H (this ▸ le_sup_right)

theorem AT_Tits_intrinsic_local_pair :
    (∃ P : Sylow 2 titsD, (P : Subgroup titsD) = titsS.subgroupOf titsD) ∧
    titsH = titsD ⊓ Subgroup.centralizer
      (((Subgroup.center titsS).map titsS.subtype : Subgroup (Equiv.Perm (Fin 1755))) :
        Set (Equiv.Perm (Fin 1755))) ∧
    titsN = titsD ⊓ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) ∧
    titsH ⊔ titsN = titsD ∧
    IsPGroup 2 titsJ ∧ IsPGroup 2 titsK ∧
    (titsJ.subgroupOf titsH).Normal ∧ (titsK.subgroupOf titsN).Normal ∧
    titsJ ≤ titsS ∧ titsK ≤ titsS ∧
    titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) ≤ titsJ ∧
    titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) ≤ titsK := by
  obtain ⟨-, -, -, -, -, -, -, hS, -, -, -, -, -, -, -, -, -, hJn, hKn, hJS, hKS, -⟩ :=
    AT_Tits_local_stabilizers_and_normal_cores
  obtain ⟨-, -, -, -, hCJ, -, hCK⟩ := AT_Tits_local_center_and_centralizer_checks
  exact ⟨hS, titsH_eq_CZS, titsN_eq_NK, titsH_sup_N,
    IsPGroup.of_card (n := 9) (by rw [titsQJ_facts.2.2.2]; norm_num),
    IsPGroup.of_card (n := 10) (by rw [titsQK_facts.2.2.2]; norm_num), hJn, hKn, hJS, hKS,
    hCJ, hCK⟩

end CFSG.Sporadic.Schreier.Tits
