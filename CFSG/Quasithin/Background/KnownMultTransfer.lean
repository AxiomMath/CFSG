module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem mem_sylow_of_mem_center {p : ℕ} [Fact p.Prime] (P : Sylow p X) {a : X}
    (haZ : a ∈ Subgroup.center X) {k : ℕ} (hak : a ^ p ^ k = 1) : a ∈ (P : Subgroup X) := by
  have hp : IsPGroup p (Subgroup.zpowers a) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hak, one_zpow, Subgroup.coe_one]
  have hn : (Subgroup.zpowers a).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : g * a ^ m = a ^ m * g :=
      ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ haZ m)) g)
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) m
  exact hp.le_sylow_of_normal P (Subgroup.mem_zpowers a)

theorem mem_commutator_sylow_of_mem_center {p : ℕ} [Fact p.Prime] (P : Sylow p X) {a : X}
    (haZ : a ∈ Subgroup.center X) (haX : a ∈ commutator X) {k : ℕ} (hak : a ^ p ^ k = 1) :
    (⟨a, mem_sylow_of_mem_center P haZ hak⟩ : ↥(P : Subgroup X)) ∈
      commutator ↥(P : Subgroup X) := by
  classical
  set H : Subgroup X := (P : Subgroup X) with hH
  have haP : a ∈ H := mem_sylow_of_mem_center P haZ hak
  set ϕ : ↥H →* Abelianization ↥H := Abelianization.of with hϕ
  have hT : ϕ.transfer a = 1 := Abelianization.commutator_subset_ker _ haX
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * a ^ k * g₀ ∈ H → g₀⁻¹ * a ^ k * g₀ = a ^ k := by
    intro k g₀ _
    have hc : g₀ * a ^ k = a ^ k * g₀ :=
      (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ haZ k)) g₀
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  rw [MonoidHom.transfer_eq_pow ϕ a key] at hT
  have hmem : (⟨a ^ H.index, MonoidHom.transfer_eq_pow_aux a key⟩ : ↥H) ∈ commutator ↥H := by
    rw [← Abelianization.ker_of]
    exact hT
  have hpow : (⟨a ^ H.index, MonoidHom.transfer_eq_pow_aux a key⟩ : ↥H) =
      (⟨a, haP⟩ : ↥H) ^ H.index := Subtype.ext (by simp)
  rw [hpow] at hmem
  have hcop : Nat.Coprime H.index (orderOf (⟨a, haP⟩ : ↥H)) := by
    have hord : orderOf (⟨a, haP⟩ : ↥H) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hak))
    have hpi : Nat.Coprime H.index p :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr P.not_dvd_index))
    exact Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k hpi)
  exact Subgroup.zpowers_le_of_mem hmem (A4.mem_zpowers_pow_of_coprime hcop)

theorem eq_one_of_mem_center_of_isMulCommutative_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p X)
    (hP : IsMulCommutative ↥(P : Subgroup X)) {a : X} (haZ : a ∈ Subgroup.center X)
    (haX : a ∈ commutator X) {k : ℕ} (hak : a ^ p ^ k = 1) : a = 1 := by
  have h := mem_commutator_sylow_of_mem_center P haZ haX hak
  have hbot : commutator ↥(P : Subgroup X) = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_def, hP.is_comm.comm x y]
    group
  rw [hbot, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h
end CFSG.Quasithin
