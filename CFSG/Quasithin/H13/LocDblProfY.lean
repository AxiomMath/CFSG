module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Num

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Prof

open CFSG.Open CFSG.Quasithin.H13.K1262Two

theorem normal2_of_a6Config {X : Type} [Group X] [Finite X] {Y F : Subgroup X}
    (h : A6Config Y F) : ∀ K : Subgroup Y, K.Normal → K ≠ ⊤ → IsPGroup 2 K := by
  obtain ⟨hperf, ⟨φ, hφs, hφk⟩, -, -, -, -⟩ := h
  intro K hK hKtop
  have hO : IsPGroup 2 (CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : (K.map φ).Normal := hK.map φ hφs
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.map φ) with hbot | htop
  · refine IsPGroup.to_le hO ?_
    rw [← hφk]
    intro k hk
    rw [MonoidHom.mem_ker]
    have hmem : φ k ∈ K.map φ := Subgroup.mem_map_of_mem φ hk
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    apply hKtop
    have hsurj : Function.Surjective ((QuotientGroup.mk' K).comp (CFSG.pCore 2 ↥Y).subtype) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K q
      have hy : φ y ∈ K.map φ := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 hy
      refine ⟨⟨k⁻¹ * y, ?_⟩, ?_⟩
      · rw [← hφk, MonoidHom.mem_ker, map_mul, map_inv, hky, inv_mul_cancel]
      · have hk1 : (QuotientGroup.mk' K) k⁻¹ = 1 := (QuotientGroup.eq_one_iff k⁻¹).2 (K.inv_mem hk)
        show (QuotientGroup.mk' K) (k⁻¹ * y) = QuotientGroup.mk' K y
        rw [map_mul, hk1, one_mul]
    have hQ2 : IsPGroup 2 (↥Y ⧸ K) := hO.of_surjective _ hsurj
    haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.2 hperf
    have hsub : Subsingleton (↥Y ⧸ K) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isNilpotent (↥Y ⧸ K) hQ2.isNilpotent
    rw [eq_top_iff]
    intro y _
    have h1 : (QuotientGroup.mk' K y : ↥Y ⧸ K) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff y).1 h1

theorem card_of_a6Config_of_le {X : Type} [Group X] [Finite X] {Y F : Subgroup X}
    (h : A6Config Y F) (hF : 32 ≤ Nat.card F) : ∃ j : ℕ, 5 ≤ j ∧ Nat.card Y = 360 * 2 ^ j := by
  obtain ⟨j, hY, hFd⟩ := a6Config_card h
  refine ⟨j, ?_, hY⟩
  have hpos : 0 < 2 ^ j := by positivity
  have hle : Nat.card F ≤ 2 ^ j := Nat.le_of_dvd hpos hFd
  by_contra hj
  push Not at hj
  have h16 : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h16' : (2 : ℕ) ^ 4 = 16 := by norm_num
  omega

theorem nofix_of_a6Config {Γ : Type} [Group Γ] [Finite Γ] [MulAction Γ (Fin 24)] {Y F : Subgroup Γ}
    (h : A6Config Y F) (hF : 32 ≤ Nat.card F)
    (hstab : ∀ p : Fin 24, ¬ 2 ^ 8 ∣ Nat.card (MulAction.stabilizer Γ p)) :
    ∀ p : Fin 24, ∃ y ∈ Y, y • p ≠ p := by
  intro p
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj5, hY⟩ := card_of_a6Config_of_le h hF
  have hle : Y ≤ MulAction.stabilizer Γ p := fun y hy => MulAction.mem_stabilizer_iff.2 (hcon y hy)
  have hd1 : Nat.card Y ∣ Nat.card (MulAction.stabilizer Γ p) := Subgroup.card_dvd_of_le hle
  have hd2 : 360 * 2 ^ j ∣ Nat.card (MulAction.stabilizer Γ p) := by
    rw [← hY]
    exact hd1
  have h8 : 2 ^ 8 ∣ 360 * 2 ^ j := by
    have e : (2 : ℕ) ^ 8 = 8 * 2 ^ 5 := by norm_num
    rw [e]
    exact Nat.mul_dvd_mul (by norm_num) (Nat.pow_dvd_pow 2 hj5)
  exact hstab p (h8.trans hd2)

end CFSG.Quasithin.H13.LocDbl.M24Prof
