module

public import CFSG.Quasithin.Background.I4Dihedral

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open DihedralGroup

theorem dih4_central : ∀ x : DihedralGroup 4, (∀ y, x * y = y * x) → x ≠ 1 → x = r 2 := by
  decide

theorem dih4_prod : ∀ x : DihedralGroup 4, ∃ a b : DihedralGroup 4, a * a = 1 ∧ b * b = 1 ∧
    x = a * b := by
  decide

theorem dih4_r_two : (r 2 : DihedralGroup 4) = r 1 * r 1 := by
  decide

theorem exists_sq_of_dihedral_centralizer {X : Type} [Group X] {t : X} (ht : orderOf t = 2)
    (e : ↥(Subgroup.centralizer ({t} : Set X)) ≃* DihedralGroup 4) : ∃ s : X, s * s = t := by
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    omega
  set t' : ↥(Subgroup.centralizer ({t} : Set X)) :=
    ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with ht'
  have hcent : ∀ y : DihedralGroup 4, e t' * y = y * e t' := by
    intro y
    obtain ⟨c, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  have h1 : e t' ≠ 1 := by
    intro h1
    exact ht1 (congrArg Subtype.val (e.injective (h1.trans e.map_one.symm)))
  have h2 : e t' = r 2 := dih4_central _ hcent h1
  refine ⟨((e.symm (r 1) : ↥(Subgroup.centralizer ({t} : Set X))) : X), ?_⟩
  have h3 : e.symm (r 1) * e.symm (r 1) = t' := by
    rw [← map_mul, ← dih4_r_two, ← h2, MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val h3

theorem exists_psl2_of_dihedral_centralizers
    {X : Type} [Group X] [Finite X] (hex : ∃ t : X, orderOf t = 2)
    (hD : ∀ t : X, orderOf t = 2 →
      Nonempty (↥(Subgroup.centralizer ({t} : Set X)) ≃* DihedralGroup 4)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F),
      (Fintype.card F = 7 ∨ Fintype.card F = 9) ∧
        Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ∀ t : X, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set X)) = 8 := by
    intro t ht
    obtain ⟨e⟩ := hD t ht
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hpgrp : ∀ t : X, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set X)) := by
    intro t ht
    exact IsPGroup.of_card (n := 3) (by rw [hcard t ht]; norm_num)
  obtain ⟨t0, ht0⟩ := hex
  have ht01 : t0 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht0
    omega
  obtain ⟨T, hTle⟩ := IsPGroup.exists_le_sylow (hpgrp t0 ht0)
  have ht0T : t0 ∈ (T : Subgroup X) := hTle (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hnt : Nontrivial ↥(T : Subgroup X) :=
    ⟨⟨t0, ht0T⟩, 1, fun h1 => ht01 (congrArg Subtype.val h1)⟩
  have hcenter : Nontrivial ↥(Subgroup.center ↥(T : Subgroup X)) :=
    IsPGroup.center_nontrivial T.isPGroup'
  obtain ⟨c, hc⟩ : ∃ c : ↥(Subgroup.center ↥(T : Subgroup X)), orderOf c = 2 := by
    refine exists_prime_orderOf_dvd_card' 2 ?_
    have hP : IsPGroup 2 ↥(Subgroup.center ↥(T : Subgroup X)) := T.isPGroup'.to_subgroup _
    rcases hP.card_eq_or_dvd with h1 | h1
    · exfalso
      have := Finite.one_lt_card_iff_nontrivial.mpr hcenter
      omega
    · exact h1
  set c' : ↥(T : Subgroup X) := (c : ↥(T : Subgroup X)) with hc'
  set z0 : X := (c' : X) with hz0
  have hz0o : orderOf z0 = 2 := by
    rw [hz0, Subgroup.orderOf_coe, hc', Subgroup.orderOf_coe, hc]
  have hzT : (T : Subgroup X) ≤ Subgroup.centralizer ({z0} : Set X) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp c.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hCpg : IsPGroup 2 (Subgroup.centralizer ({z0} : Set X)) := hpgrp z0 hz0o
  have hCT : Subgroup.centralizer ({z0} : Set X) = T := T.is_maximal' hCpg hzT
  obtain ⟨eC⟩ := hD z0 hz0o
  have hTiso : Nonempty (↥(T : Subgroup X) ≃* DihedralGroup 4) :=
    ⟨(MulEquiv.subgroupCongr hCT).symm.trans eC⟩
  have hG : ∀ M : Subgroup X, M.index ≠ 2 := by
    intro M hM
    have hinv : ∀ t : X, orderOf t = 2 → t ∈ M := by
      intro t ht
      obtain ⟨e⟩ := hD t ht
      obtain ⟨s, hs⟩ := exists_sq_of_dihedral_centralizer ht e
      rw [← hs]
      exact Subgroup.mul_self_mem_of_index_two hM s
    obtain ⟨eT⟩ := id hTiso
    have hTM : (T : Subgroup X) ≤ M := by
      intro g hg
      obtain ⟨a, b, ha, hb, hab⟩ := dih4_prod (eT ⟨g, hg⟩)
      have hmem : ∀ u : DihedralGroup 4, u * u = 1 → ((eT.symm u : ↥(T : Subgroup X)) : X) ∈ M := by
        intro u hu
        by_cases hu1 : u = 1
        · rw [hu1, map_one]; exact M.one_mem
        · apply hinv
          rw [Subgroup.orderOf_coe]
          have hu' : (eT.symm u) * (eT.symm u) = 1 := by rw [← map_mul, hu, map_one]
          have hne : eT.symm u ≠ 1 := fun h1 => hu1 (by simpa using congrArg eT h1)
          exact orderOf_eq_prime (by rw [← pow_two] at hu'; exact hu') hne
      have : g = ((eT.symm a : ↥(T : Subgroup X)) : X) * ((eT.symm b : ↥(T : Subgroup X)) : X) := by
        have h1 : (⟨g, hg⟩ : ↥(T : Subgroup X)) = eT.symm a * eT.symm b := by
          rw [← map_mul, ← hab, MulEquiv.symm_apply_apply]
        exact congrArg Subtype.val h1
      rw [this]
      exact M.mul_mem (hmem a ha) (hmem b hb)
    have hTcard : Nat.card (T : Subgroup X) = 8 := by
      obtain ⟨eT⟩ := id hTiso
      rw [Nat.card_congr eT.toEquiv, DihedralGroup.nat_card]
    have h8M : 8 ∣ Nat.card M := by
      rw [← hTcard]
      exact Subgroup.card_dvd_of_le hTM
    have hMX := M.card_mul_index
    rw [hM] at hMX
    have hX16 : 16 ∣ Nat.card X := by
      obtain ⟨k, hk⟩ := h8M
      exact ⟨k, by omega⟩
    have hTdvd : ¬ 2 ∣ (T : Subgroup X).index := Sylow.not_dvd_index T
    have hTX := (T : Subgroup X).card_mul_index
    rw [hTcard] at hTX
    obtain ⟨m, hm⟩ := hX16
    have : (T : Subgroup X).index * 8 = Nat.card X := by rw [← hTX]; ring
    apply hTdvd
    exact ⟨m, by omega⟩
  obtain ⟨F, hF, hFin, hodd, hFcard, hiso⟩ :=
    CFSG.Quasithin.I4.dihedral_core X hG T (n := 4) (by norm_num) hTiso hz0o hzT hCpg
  refine ⟨F, hF, hFin, ?_, hiso⟩
  omega

end CFSG.Quasithin.Kleidman.ThreeLocal
