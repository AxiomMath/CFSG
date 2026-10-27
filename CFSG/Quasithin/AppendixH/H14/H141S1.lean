module

public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Quasithin.AppendixH.Common.Sextet

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.ASVolI.AppH

noncomputable def tetStabEquiv (B : Finset (Fin 24)) :
    ↥(MulAction.stabilizer (↥M24g) B) ≃ ↥(MY M24g B) where
  toFun k := ⟨(k.1 : S24), Subgroup.mem_inf.mpr ⟨k.1.2, MulAction.mem_stabilizer_iff.mpr (by
    have h : k.1 • B = B := MulAction.mem_stabilizer_iff.mp k.2
    rw [Subgroup.smul_def] at h
    exact h)⟩⟩
  invFun s := ⟨⟨s.1, (Subgroup.mem_inf.mp s.2).1⟩,
    MulAction.mem_stabilizer_iff.mpr (by
      rw [Subgroup.smul_def]
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp s.2).2)⟩
  left_inv k := rfl
  right_inv s := rfl

theorem exists_smul_tetrad_eq {B₁ B₂ : Finset (Fin 24)}
    (h₁ : B₁.card = 4) (h₂ : B₂.card = 4) : ∃ σ ∈ M24g, σ • B₁ = B₂ := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp h₁
  obtain ⟨a', b', c', d', hab', hac', had', hbc', hbd', hcd', rfl⟩ := Finset.card_eq_four.mp h₂
  obtain ⟨p, hp, hp0, hp1, hp2, hp3⟩ :=
    CFSG.Monster.B.TwoA.autPerm_maps_four a b c d hab hac had hbc hbd hcd
  obtain ⟨q, hq, hq0, hq1, hq2, hq3⟩ :=
    CFSG.Monster.B.TwoA.autPerm_maps_four a' b' c' d' hab' hac' had' hbc' hbd' hcd'
  have hpB : p • ({0, 1, 2, 3} : Finset (Fin 24)) = {a, b, c, d} := by
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, Equiv.Perm.smul_def,
      hp0, hp1, hp2, hp3]
  have hqB : q • ({0, 1, 2, 3} : Finset (Fin 24)) = {a', b', c', d'} := by
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, Equiv.Perm.smul_def,
      hq0, hq1, hq2, hq3]
  refine ⟨q * p⁻¹, M24g.mul_mem hq (M24g.inv_mem hp), ?_⟩
  have hp_inv : p⁻¹ • ({a, b, c, d} : Finset (Fin 24)) = {0, 1, 2, 3} := by
    rw [← hpB, ← mul_smul, inv_mul_cancel, one_smul]
  rw [mul_smul, hp_inv, hqB]

theorem orbit_tetrad_eq {B : Finset (Fin 24)}
    (hB : B.card = 4) :
    MulAction.orbit (↥M24g) B =
      ((Finset.univ : Finset (Fin 24)).powersetCard 4 : Set (Finset (Fin 24))) := by
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hT
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    rw [Subgroup.smul_def, smul_finset_eq_map, Finset.card_map]
    exact hB
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hT
    obtain ⟨σ, hσ, hσB⟩ := exists_smul_tetrad_eq hB hT
    exact MulAction.mem_orbit_iff.mpr ⟨⟨σ, hσ⟩, by rw [Subgroup.smul_def]; exact hσB⟩

theorem card_MY_tetrad {B : Finset (Fin 24)}
    (hB : B.card = 4) : Nat.card ↥(MY M24g B) = 23040 := by
  have horbit : (MulAction.orbit (↥M24g) B).ncard = 10626 := by
    rw [orbit_tetrad_eq hB, Set.ncard_coe_finset, Finset.card_powersetCard]
    decide
  have hOS : Nat.card (MulAction.stabilizer (↥M24g) B) * 10626 = Nat.card ↥M24g := by
    have h := (MulAction.stabilizer (↥M24g) B).card_mul_index
    rw [MulAction.index_stabilizer, horbit] at h
    exact h
  have hG : Nat.card ↥M24g = 244823040 := by
    change Nat.card ↥AutPerm = 244823040
    exact card_AutPerm
  have hstab : Nat.card (MulAction.stabilizer (↥M24g) B) = 23040 := by
    have h : Nat.card (MulAction.stabilizer (↥M24g) B) * 10626 = 23040 * 10626 :=
      hOS.trans (hG.trans (by norm_num))
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  exact (Nat.card_congr (tetStabEquiv B)).symm.trans hstab

theorem stab_tetrad_le_MY_sextet {S : Finset (Finset (Fin 24))} (hS : IsSextet S)
    {B : Finset (Fin 24)} (hB : B ∈ S) :
    M24g ⊓ MulAction.stabilizer S24 B ≤ MY M24g S := by
  intro g hg
  obtain ⟨hgM, hgB⟩ := Subgroup.mem_inf.mp hg
  have hgBeq : g • B = B := MulAction.mem_stabilizer_iff.mp hgB
  refine Subgroup.mem_inf.mpr ⟨hgM, MulAction.mem_stabilizer_iff.mpr ?_⟩
  have hmem : B ∈ g • S := by
    rw [← hgBeq]
    exact Finset.smul_mem_smul_finset hB
  exact sextet_eq_of_mem (isSextet_smul hgM hS) hS hmem hB

theorem card_MS_le {S : Finset (Finset (Fin 24))}
    (hS : IsSextet S) : Nat.card ↥(MY M24g S) ≤ 138240 := by
  have hSpos : 0 < S.card := by rw [hS.1]; norm_num
  obtain ⟨B, hB⟩ := Finset.card_pos.mp hSpos
  have hB4 : B.card = 4 := hS.2.1 B hB
  let M : Subgroup S24 := MY M24g S
  let MB : Subgroup S24 := MY M24g B
  have hMB_le : MB ≤ M := stab_tetrad_le_MY_sextet hS hB
  have horbit_sub : MulAction.orbit (↥M) B ⊆ (S : Set (Finset (Fin 24))) := by
    intro T hT
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hT
    have hgS : (g : S24) • S = S :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp g.2).2
    have hmem : (g : S24) • B ∈ (g : S24) • S := Finset.smul_mem_smul_finset hB
    rw [hgS] at hmem
    simpa only [Subgroup.smul_def, Finset.mem_coe] using hmem
  have horbit_le : (MulAction.orbit (↥M) B).ncard ≤ 6 := by
    have h := Set.ncard_le_ncard horbit_sub S.finite_toSet
    rwa [Set.ncard_coe_finset, hS.1] at h
  have hstab_le : Nat.card (MulAction.stabilizer (↥M) B) ≤ 23040 := by
    have hle : MulAction.stabilizer (↥M) B ≤ MB.subgroupOf M := by
      intro k hk
      change ((k : ↥M) : S24) ∈ MB
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp k.2).1, MulAction.mem_stabilizer_iff.mpr ?_⟩
      have hk' : k • B = B := MulAction.mem_stabilizer_iff.mp hk
      rwa [Subgroup.smul_def] at hk'
    calc Nat.card (MulAction.stabilizer (↥M) B) ≤ Nat.card ↥(MB.subgroupOf M) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card ↥MB := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMB_le).toEquiv
      _ = 23040 := card_MY_tetrad hB4
  have hOS : Nat.card (MulAction.stabilizer (↥M) B) * (MulAction.orbit (↥M) B).ncard =
      Nat.card ↥M := by
    have h := (MulAction.stabilizer (↥M) B).card_mul_index
    rw [MulAction.index_stabilizer] at h
    exact h
  change Nat.card ↥M ≤ 138240
  calc Nat.card ↥M = Nat.card (MulAction.stabilizer (↥M) B) * (MulAction.orbit (↥M) B).ncard :=
        hOS.symm
    _ ≤ 23040 * 6 := Nat.mul_le_mul hstab_le horbit_le
    _ = 138240 := by norm_num

end CFSG.Quasithin.AppendixH.H14
