module

public import CFSG.Quasithin.AppendixH.H16.OctadZData

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] noncomputable def dPerm (u : Fin 16) : S24 :=
  permOfArr 24 (dArr u) (dArr u) (dArr_ok u u.2)

theorem hasArr_dPerm (u : Fin 16) : HasArr (dPerm u) (dArr u) :=
  hasArr_permOfArr (dArr_ok u u.2)

private theorem dPerm_mul_closed : ∀ u v : Fin 16, dPerm u * dPerm v = dPerm (xorF u v) := by
  decide +kernel

theorem dPerm_mul (u v : Fin 16) : dPerm u * dPerm v = dPerm (xorF u v) :=
  dPerm_mul_closed u v

theorem dPerm_zero : dPerm 0 = 1 := by
  decide +kernel

private theorem dPerm_sq_closed : ∀ u : Fin 16, dPerm u * dPerm u = 1 := by
  decide +kernel

theorem dPerm_mul_self (u : Fin 16) : dPerm u * dPerm u = 1 :=
  dPerm_sq_closed u

private theorem dArr_inj_of_eq : ∀ u < 16, ∀ v < 16,
    (∀ j < 24, (dArr u)[j]! = (dArr v)[j]!) → u = v := by
  decide +kernel

theorem dPerm_injective : Function.Injective dPerm := by
  intro u v huv
  apply Fin.ext
  exact dArr_inj_of_eq u u.2 v v.2 fun j hj => by
    rw [← hasArr_dPerm u ⟨j, hj⟩, huv, hasArr_dPerm v ⟨j, hj⟩]

theorem dPerm_one : dPerm 1 = koPerm 1 := by
  decide +kernel

theorem dPerm_mem_M24g (u : Fin 16) : dPerm u ∈ M24g :=
  mem_AutPerm_of_arr (dArr_ok u u.2) (dArr_aut u u.2)

private theorem dArr_stab_iff : ∀ u < 16, ∀ j < 24, (j < 8 ↔ (dArr u)[j]! < 8) := by
  decide +kernel

theorem dPerm_mem_octStab (u : Fin 16) : dPerm u ∈ octStab octad0 :=
  mem_octStab_iff.2 ⟨dPerm_mem_M24g u,
    smul_octad0_eq_of_arr (hasArr_dPerm u) fun j hj => dArr_stab_iff u u.2 j hj⟩

@[expose] noncomputable def dGrp : Subgroup S24 where
  carrier := Set.range dPerm
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨xorF u v, (dPerm_mul u v).symm⟩
  one_mem' := ⟨0, dPerm_zero⟩
  inv_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u, by rw [eq_inv_iff_mul_eq_one]; exact dPerm_mul_self u⟩

theorem mem_dGrp_iff {g : S24} : g ∈ dGrp ↔ ∃ u : Fin 16, dPerm u = g :=
  Iff.rfl

theorem dPerm_mem_dGrp (u : Fin 16) : dPerm u ∈ dGrp :=
  ⟨u, rfl⟩

theorem dGrp_le_octStab : dGrp ≤ octStab octad0 := by
  rintro g ⟨u, rfl⟩
  exact dPerm_mem_octStab u

theorem dGrp_le_M24g : dGrp ≤ M24g := by
  rintro g ⟨u, rfl⟩
  exact dPerm_mem_M24g u

theorem card_dGrp : Nat.card ↥dGrp = 16 := by
  have h : Nat.card (Set.range dPerm) = 16 := by
    rw [Nat.card_range_of_injective dPerm_injective, Nat.card_fin]
  exact h

theorem dGrp_isE2k : IsE2k 4 dGrp := by
  refine ⟨?_, ?_⟩
  · refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
    · apply Subtype.ext
      obtain ⟨u, hu⟩ := mem_dGrp_iff.mp a.2
      obtain ⟨v, hv⟩ := mem_dGrp_iff.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, dPerm_mul, dPerm_mul]
      congr 1
      apply Fin.ext
      simp [xorF, Nat.xor_comm]
    · intro x hx
      obtain ⟨u, hu⟩ := mem_dGrp_iff.mp hx
      rw [← hu, pow_two, dPerm_mul_self u]
  · rw [card_dGrp]
    norm_num

theorem dPerm_mem_fixO_iff (u : Fin 16) : dPerm u ∈ fixO ↔ (u : ℕ) < 2 := by
  constructor
  · intro hu
    refine (dArr_fix_octad_iff u u.2).1 fun i hi => ?_
    have h := hu.2 ⟨i, by omega⟩ hi
    have h2 := hasArr_dPerm u ⟨i, by omega⟩
    rw [h] at h2
    exact h2.symm
  · intro hu
    have hu' : (u : ℕ) = 0 ∨ (u : ℕ) = 1 := by omega
    rcases hu' with h | h
    · have hu0 : u = 0 := Fin.ext h
      rw [hu0, dPerm_zero]
      exact fixO.one_mem
    · have hu1 : u = 1 := Fin.ext h
      rw [hu1, dPerm_one]
      exact (mem_fixO_iff (koPerm 1)).2 ⟨1, rfl⟩

theorem dGrp_inf_fixO : dGrp ⊓ fixO = Subgroup.zpowers (koPerm 1) := by
  apply le_antisymm
  · rintro g ⟨hg1, hg2⟩
    obtain ⟨u, hu⟩ := mem_dGrp_iff.mp hg1
    have hu2 : dPerm u ∈ fixO := by rw [hu]; exact hg2
    have hu3 : (u : ℕ) < 2 := (dPerm_mem_fixO_iff u).1 hu2
    have hu' : (u : ℕ) = 0 ∨ (u : ℕ) = 1 := by omega
    rcases hu' with h | h
    · have hu0 : u = 0 := Fin.ext h
      rw [← hu, hu0, dPerm_zero]
      exact Subgroup.one_mem _
    · have hu1 : u = 1 := Fin.ext h
      rw [← hu, hu1, dPerm_one]
      exact Subgroup.mem_zpowers (koPerm 1)
  · rw [Subgroup.zpowers_le]
    exact ⟨by rw [← dPerm_one]; exact dPerm_mem_dGrp 1,
      (mem_fixO_iff (koPerm 1)).2 ⟨1, rfl⟩⟩

theorem card_fixO_sup_dGrp : Nat.card ↥(fixO ⊔ dGrp) = 128 := by
  let G : Subgroup S24 := octStab octad0
  have hKG : fixO ≤ G := fixO_le_octStab_octad0
  have hDG : dGrp ≤ G := dGrp_le_octStab
  have hN : (fixO.subgroupOf G).Normal := by
    rw [← octFix_octad0]
    exact normal_octFix octad0
  let K' : Subgroup ↥G := fixO.subgroupOf G
  let D' : Subgroup ↥G := dGrp.subgroupOf G
  haveI : K'.Normal := hN
  have hprod : Nat.card ↥(K' ⊔ D') * Nat.card ↥(K' ⊓ D') =
      Nat.card ↥K' * Nat.card ↥D' := by
    have h1 := Subgroup.relIndex_mul_card (H := K') (K := D')
    have h2 := Subgroup.relIndex_mul_card (H := K') (K := K' ⊔ D')
    rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h2
    calc Nat.card ↥(K' ⊔ D') * Nat.card ↥(K' ⊓ D')
        = (K'.relIndex D' * Nat.card ↥K') * Nat.card ↥(K' ⊓ D') := by rw [← h2]
      _ = Nat.card ↥K' * (K'.relIndex D' * Nat.card ↥(K' ⊓ D')) := by ring
      _ = Nat.card ↥K' * Nat.card ↥D' := by rw [h1]
  have hK : Nat.card ↥fixO = 16 := by
    rw [← octFix_octad0]
    exact card_octFix isOctad_octad0
  have hK' : Nat.card ↥K' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv).trans hK
  have hD' : Nat.card ↥D' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDG).toEquiv).trans card_dGrp
  have hinf_eq : K' ⊓ D' = (fixO ⊓ dGrp).subgroupOf G :=
    Subgroup.ext fun _ => Iff.rfl
  have hKD_le : fixO ⊓ dGrp ≤ G := inf_le_left.trans hKG
  have hI : Nat.card ↥(fixO ⊓ dGrp) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    rw [inf_comm, dGrp_inf_fixO, Nat.card_zpowers,
      orderOf_eq_prime (p := 2) (by rw [pow_two, ← dPerm_one, dPerm_mul_self])
        (by decide +kernel)]
  have hI' : Nat.card ↥(K' ⊓ D') = 2 := by
    rw [hinf_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD_le).toEquiv).trans hI
  have hmap : (K' ⊔ D').map G.subtype = fixO ⊔ dGrp := by
    change (fixO.subgroupOf G ⊔ dGrp.subgroupOf G).map G.subtype = fixO ⊔ dGrp
    simp only [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKG,
      Subgroup.map_subgroupOf_eq_of_le hDG]
  have hsup_eq : Nat.card ↥(fixO ⊔ dGrp) = Nat.card ↥(K' ⊔ D') := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective G)
  have h128 : Nat.card ↥(K' ⊔ D') = 128 := by
    have h := hprod
    rw [hK', hD', hI'] at h
    omega
  rw [hsup_eq]
  exact h128

theorem rhoC11_dPerm (u : Fin 16) (m : ℕ) :
    rhoC11 AutPerm le_rfl ⟨dPerm u, dPerm_mem_M24g u⟩ (toW 11 m) = toW 11 (actC11 (dArr u) m) :=
  rhoC11_toW AutPerm le_rfl ⟨dPerm u, dPerm_mem_M24g u⟩ (hasArr_dPerm u) m

end CFSG.ASVolI.H16
